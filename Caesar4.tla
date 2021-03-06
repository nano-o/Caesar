---------------------------- MODULE Caesar4 ----------------------------

(***************************************************************************)
(* Model-checking results:                                                 *)
(*                                                                         *)
(* With 3 acceptors, 2 ballots, MaxTime=1, and the following constraint:   *)
(*                                                                         *)
(*     \A b \in Ballot :  <<c1, b>> \notin join                            *)
(*                                                                         *)
(* 6.3M reachable states, 6 minutes 25 seconds on whitewhale, depth 43.    *)
(*                                                                         *)
(* With 3 acceptors, 2 ballots, MaxTime=1, and no constraint:              *)
(*                                                                         *)
(* 292M reachable states, 6 hours 5 minutes on whitewhale, depth 52.       *)
(*                                                                         *)
(* With 5 acceptors, 2 ballots, MaxTime=1, and the following constraint:   *)
(*                                                                         *)
(*     /\ \A x \in {2} : <<c1, <<0,x>>>> \notin DOMAIN propose             *)
(*     /\ \A p \in {p1,p2} : \A b \in Ballot : b \notin DOMAIN vote[p][c1] *)
(*     /\ \A b \in Ballot :  <<c1, b>> \notin join                         *)
(*                                                                         *)
(* Less than 850M reachable state (started with a weaker constraint,       *)
(* changed halfway through), depth 55.                                     *)
(*                                                                         *)
(* With 5 acceptors, 3 ballots, MaxTime=1, and the following constraint:   *)
(*                                                                         *)
(*     /\ \A x \in {2, 3} : <<c1, <<0,x>>>> \notin DOMAIN propose          *)
(*     /\ \A b \in Ballot :  <<c1, b>> \notin join                         *)
(*     /\ \A B \in {0,1,2} : \A x \in {2,3} : <<c2, <<B,x>>>> \notin DOMAIN propose *)
(*     /\ DOMAIN vote[p1][c2] = {}                                         *)
(*     /\ DOMAIN vote[p2][c1] = {}                                         *)
(*                                                                         *)
(* 41M reachable states, 21 hours on whitewhale, depth 58.                 *)
(*                                                                         *)
(* With 2 acceptors, 3 ballot, MaxTime=1, and no constraint: 41M reachable *)
(* states, 2 hours 51 minutes on quad-core laptop, depth 61.               *)
(*                                                                         *)
(***************************************************************************)

EXTENDS TLC, Sequences, Integers, Maps, Quorums, Commands

CONSTANT NumBallots

INSTANCE Ballots WITH SubBallots <- {1,2,3}

(***************************************************************************)
(* MaxTime bounds the timestamp that can be assigned to commands, but not  *)
(* to retries.                                                             *)
(***************************************************************************)
CONSTANTS MaxTime

Time == 1..MaxTime
    
(***********

--algorithm Caesar {

    variables
        \* maps an acceptor p and a command c to a ballot b, indicating that the acceptor p is in ballot b for command c:
        ballot = [p \in P |-> [c \in C |-> <<0,1>>]],
        \* maps an acceptor p and a command c to a map from ballot to vote:
        vote = [p \in P |-> [c \in C |-> <<>>]],
        \* Maps ballots to proposals
        propose = <<>>,
        \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c has been committed in ballot b
        \* with timestamp t and dependencies ds: 
        stable = <<>>,
        \* a set of pairs <<c,b>>, indicating that the ballot-b leader of c asks all acceptors to join ballot b:
        join = {}

    define {
    
        Status == {"pending", "stable", "accepted", "rejected"}
        
        Vote == [ts : Nat, status : Status, deps : SUBSET C]
        
        Propose == [ts : Time] \cup [ts : Nat, phase1Deps : SUBSET C] \cup [ts : Nat, deps : SUBSET C]
        
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> Vote]
            /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Propose]
            /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
            /\  join \in SUBSET (C \times Ballot)
        
        \* We use the letter B for major ballots. A ballot if of the form <<B, phase>>
        Phase1(B) == <<B,1>>
        Phase2(B) == <<B,2>>
        Phase3(B) == <<B,3>>
        
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}
        
        \* TRUE if c was seen in ballot b at p.
        SeenAt(c, b, p) == b \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
            IF bals # {}
            THEN Max(bals)
            ELSE Bot
        
        \* The vote for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, B, q) == 
            LET bals == {LastBal(c, Pred(Phase1(B)), p) : p \in q}
            IN Max(bals)
        
        \* The timestamp found at p in the vote for c in the highest ballot.
        TimeStampOf(c, p) == MaxVote(c,p).ts
        
        \* All the timestamps on acceptor p
        TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}
        
        \* All the commands at p which have a lower timestamp than <<c,t>>
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}
        
        \* The dependencies to include in the phase-1 reply of an acceptor.
        Phase1ReplyDeps(p, c, b, t) ==       
            IF "phase1Deps" \in DOMAIN propose[<<c, b>>]
            THEN 
                LET new ==  { c2 \in SeenCmds(p) : 
                    /\  <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>
                    /\  LET last == LastBal(c2, Max(Ballot), p)
                            status ==  vote[p][c2][last].status IN
                        \/  last = <<0,1>> /\  status = "stable"
                        \/  <<0,1>> \prec last /\ status \in {"accepted","pending","stable"} }
                IN propose[<<c, b>>].phase1Deps \cup new
            ELSE CmdsWithLowerT(p, c, t)
                            
        \* the set of acceptors in q that participated in ballot b of command c.
        ParticipatedIn(b, c, q) == {p \in q : b \in DOMAIN vote[p][c]}
        
        \* The local dependencies of c at p.
        Deps(c, p) == MaxVote(c, p).deps \ {c}
        
        \* c1 at timestamp t1 conflicts with c2 on p. 
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Deps(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ MaxVote(c2,p).status \notin {"stable","accepted"}
        
        \* command c with timestamp t is blocked on p.
        Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)
        
        \* Command c with timestamp t does not encounter any conflict on acceptor p.
        NoConflict(p, c, t) == \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2)
            
        \* The timestamp computed locally by an acceptor when it reject a command.
        RejectTimestamp(c, p) == GT(c, TimeStamps(p))
            
        \* The timestamp computed by a leader when it retries a command after a reject.
        RetryTimestamp(c, b, q) == GTE(c, {<<c, vote[p][c][b].ts>> : p \in q})
        
        \* Command c is pending in ballot b on all acceptors in quorum q.
        PendingOnQuorum(c, b, q) == \A p \in q : 
            /\  SeenAt(c, b, p)
            /\  vote[p][c][b].status = "pending"
            
        \* Command c has been reject by one acceptor among quorum q.
        RejectedOnQuorum(c, b, q) == 
            /\  \A p \in q : SeenAt(c, b, p)
            /\  \E p \in q : vote[p][c][b].status = "rejected"
        
        \* Command c has been accepted in ballot b by all acceptors in quorum q.
        AcceptedOnQuorum(c, b, q) == \A p \in q : 
            /\  SeenAt(c, b, p)
            /\  vote[p][c][b].status = "accepted"
        
        Rejected(c, ps, b) == \E p \in ps : vote[p][c][b].status = "rejected"
        
        VotedDeps(q, c, b) == UNION {vote[p][c][b].deps : p \in q}
        
        Pending(c, ps, b) == \A p \in ps : 
            vote[p][c][b].status \notin {"stable","rejected"}
        
        AVote(ps, c, b) == (LET p == CHOOSE p \in ps : TRUE IN vote[p][c][b])
        
        PossibleFastQuorums(q, ps) == {fq \in FastQuorum : fq \cap q \subseteq ps}
        
        ConfirmedIfFast(c, ps, fqs, b) ==                 
            LET deps == VotedDeps(ps, c, b)
            IN {c2 \in deps : (\A q \in fqs : 
                \E p \in q \cap ps : c2 \in vote[p][c][b].deps)}
                    
        (*******************************************************************)
        (* The two correctness properties, whose conjunction implies       *)
        (* correct SMR:                                                    *)
        (*******************************************************************)
        GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
            /\ <<c1,b1>> \in DOMAIN stable
            /\ <<c2,b2>> \in DOMAIN stable
            /\ c1 # c2 
            /\ <<c1, stable[<<c1,b1>>].ts>> \sqsubset <<c2, stable[<<c2,b2>>].ts>> 
            => c1 \in stable[<<c2,b2>>].deps
        
        Agreement == \A c \in C : \A b1,b2 \in Ballot :
            /\ <<c,b1>> \in DOMAIN stable
            /\ <<c,b2>> \in DOMAIN stable 
            => stable[<<c,b1>>].ts = stable[<<c,b2>>].ts    
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
    
    (***********************************************************************)
    (* Macros for the acceptor actions.                                    *)
    (***********************************************************************)
    
    macro BallotPre(c, b) {
        when IF Phase(b) = 1 THEN ballot[p][c] = b ELSE ballot[p][c] \prec b;
        when <<c, b>> \in DOMAIN propose;
        ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
    }
        
    macro Phase1Reply(p) {
        with (c \in C; B \in MajorBallot, b = Phase1(B)) {
            BallotPre(c,b);
            with (t = propose[<<c, b>>].ts) {
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                if (NoConflict(p, c, t)) {
                    vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "pending", deps |-> Phase1ReplyDeps(p, c, b, t)]>>]];
                } 
                else {
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  t2 = RejectTimestamp(c, p) ) {
                        \* Record the fact that the command was rejected with t2:
                        vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                            ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> CmdsWithLowerT(p, c, t2[2])]>>]];
                    }
                }
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; B \in MajorBallot, b = Phase2(B)) {
            BallotPre(c, b);
            with (t = propose[<<c,b>>].ts) {
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                if (NoConflict(p, c, t)) {
                    vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "pending", deps |-> propose[<<c,b>>].deps]>>]];
                }
                else {
                    with (t2 = RejectTimestamp(c, p)) {
                      vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> CmdsWithLowerT(p, c, t2[2])]>>]];
                    }
                }
            }
        }
    }
    
    macro Phase3Reply(p) {
        with (c \in C; B \in MajorBallot, b = Phase3(B)) {
            BallotPre(c,b); 
            with (t = propose[<<c,b>>].ts) {
                vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<b, [  
                    ts |-> t, status |-> "accepted", 
                    deps |-> CmdsWithLowerT(p, c, t) \cup propose[<<c,b>>].deps]>>]];
            }
        }
    }
    
    macro LearnStable(p) {
        with (c \in C; b \in Ballot) { 
            when ballot[p][c] \preceq b /\ <<c,b>> \in DOMAIN stable;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (s = stable[<<c,b>>]) {
                vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<b, [
                    status |-> "stable", 
                    ts |-> s.ts, 
                    deps |-> s.deps ]>>]];
            }
        }
    }    
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot (0) by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when ballot[p][c] \prec b;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
    (***********************************************************************)
    (* Macros for the leader actions.                                      *)
    (***********************************************************************)
    
    macro StartPhase1(c, B, t) {
        assert <<c,Phase1(B)>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>;
        goto end1;
    }
    
    macro StartPhase2(c, B, t, deps) {
        assert <<c,Phase2(B)>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,Phase2(B)>>, [ts |-> t, deps |-> deps]>>;
        goto end2;
    }
    
    macro StartPhase3(c, B, t, deps) {
        assert <<c,Phase3(B)>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,Phase3(B)>>, [ts |-> t, deps |-> deps]>>;
        goto end3;
    }
    
    macro StartBallot(c, B) {
        assert <<c,Phase1(B)>> \notin join;
        join := join \cup {<<c,Phase1(B)>>};
    }
    
    macro MakeStable(c, b, t, deps) {
        stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> deps]>>;
        goto decided;
    }
      
    (***********************************************************************)
    (* Specification of the acceptors:                                     *)
    (***********************************************************************)
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        Phase1Reply(self);
                    } or {
                        LearnStable(self);
                    } or {
                        Phase2Reply(self);
                    } or {
                        Phase3Reply(self);
                    } or {
                        JoinBallot(self);
                    }
                }
    }
    
    (***********************************************************************)
    (* Specification of the leaders:                                       *)
    (***********************************************************************)
    process (leader \in (C \times MajorBallot)) {
        start:  either { \* Initial proposal for the command.
                    when self[2] = 0;
        phase1:     with (t \in Time) {
                        StartPhase1(self[1], self[2], t)
                    }
                } or { \* Start a new ballot.
                    when self[2] > 0; \* Only start ballots greater than 0; 0 is started by default.
        startBal:   StartBallot(self[1],self[2]);
        recover:    with (q \in Quorum, c = self[1], B = self[2]) { \* recover major ballot B.
                        when \A p \in q : Phase1(B) \preceq ballot[p][c]; \* every p in the quorum is in b or higher.
                        \* no p \in q can be in Phase2(B) or Phase3(B), because only the leader of B can make them do that,
                        \* and it did not do it yet:
                        assert \A p \in q : ballot[p][c] \notin {Phase2(B),Phase3(B)};
                        with (maxBal = MaxBal(c, B, q); ps = ParticipatedIn(maxBal, c, q) ) {
                            assert maxBal[1] < B; \* Sanity check.
                            if (maxBal = Bot)  with (t \in Time) {
                                \* No acceptor in q has seen the command.
                                StartPhase1(c, B, t) 
                            }
                            else if (\E p \in ps : vote[p][c][maxBal].status = "stable") {
                                when FALSE; \* This case is not interesting
                            }
                            else if (Phase(maxBal) = 3)
                                with (v = AVote(ps, c, maxBal), t = v.ts, ds = v.deps) {
                                StartPhase3(c, B, t, ds);
                            }
                            else if (Phase(maxBal) \in {1,2} /\ Rejected(c, ps, maxBal))
                                with (t \in Time) { \* use an arbitrary timestamp.
                                \* An invariant at this point:
                                assert \A p \in P : c \in DOMAIN vote[p] =>
                                    \A b2 \in DOMAIN vote[p][c] : b2 \preceq maxBal =>
                                        vote[p][c][b2].status \notin {"accepted","stable"};
                                StartPhase1(c, B, t);
                            }
                            else if (Phase(maxBal) = 2 /\ Pending(c, ps, maxBal)) 
                                with (v = AVote(ps, c, maxBal), t = v.ts, ds = v.deps) {
                                assert \A p \in ps : vote[p][c][maxBal].status = "pending";
                                StartPhase2(c, B, t, ds);
                            }
                            else if (Phase(maxBal) = 1 /\ Pending(c, ps, maxBal)) 
                                with (t = AVote(ps, c, maxBal).ts) {
                                assert \A p \in ps : vote[p][c][maxBal].status = "pending";
                                if (\E p \in ps : "phase1Deps" \in DOMAIN vote[p][c][maxBal]) 
                                    \* Start phase1 with the same "phase1Deps" value:
                                    with (p = CHOOSE p \in ps : "phase1Deps" \in DOMAIN vote[p][c][maxBal]) {
                                    propose := propose ++ <<<<c,Phase1(B)>>, 
                                        [ts |-> t, phase1Deps |-> vote[p][c][maxBal].phase1Deps]>>;
                                }
                                else with (fqs = PossibleFastQuorums(q, ps)) { 
                                    if (fqs # {}) { 
                                        \* Start phase1 with a "phase1Deps" set:
                                        propose := propose ++ <<<<c,Phase1(B)>>, 
                                            [ts |-> t, phase1Deps |-> ConfirmedIfFast(c, ps, fqs, maxBal)]>>;
                                    }
                                    else { StartPhase1(c, B, t) }
                                }
                            }
                            else { 
                                assert FALSE; \* We must have covered all cases.
                            }
                        }
                    }
                };
        end1:   
                either { 
                    (* Fast decision *)
                    with (q \in FastQuorum, c = self[1], b = Phase1(self[2])) {
                        when PendingOnQuorum(c, b, q);
                        with (  ds = VotedDeps(q, c, b); t = propose[<<c,b>>].ts ) {
                            MakeStable(c, b, t, ds);
                        }
                    };
                } or {
                    (* there is a reject, trigger phase 3. *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when RejectedOnQuorum(c, b, q);
                        with (  ds = VotedDeps(q, c, b); t = RetryTimestamp(c, b, q) ) {
                            StartPhase3(c, b[1], t[2], ds);
                        }
                    }
                } or {
                    (* Timeout, trigger phase 2 *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when PendingOnQuorum(c, b, q);
                        with (  ds = VotedDeps(q, c, b); t = AVote(q, c, b).ts) {
                            assert \A p \in q : vote[p][c][b].ts = t;
                            StartPhase2(c, b[1], t, ds);
                        }
                    }
                };
        end2:   either {
                    (* Decision in phase 2 *)
                    with (q \in Quorum, c = self[1], b = Phase2(self[2])) {
                        when PendingOnQuorum(c, b, q);
                        with (v = AVote(q, c, b), ds = v.deps, t = v.ts) {
                            assert \A p \in q : vote[p][c][b].ts = t;
                            MakeStable(c, b, t, ds);
                        }
                    }
                } or {
                    (* Reject in phase 2, trigger phase 3 *)
                    with (q \in Quorum, c = self[1], b = Phase2(self[2])) {
                        when RejectedOnQuorum(c, b, q);
                        with (  ds = VotedDeps(q, c, b); t = RetryTimestamp(c, b, q) ) {
                            StartPhase3(c, b[1], t[2], ds);
                        }
                    }
                }; 
        end3:   (* Decide in phase 3 *)
                with (q \in Quorum, c = self[1], b = Phase3(self[2]) ) {
                    when AcceptedOnQuorum(c, b, q);
                    with (  ds = VotedDeps(q, c, b); t = propose[<<c,b>>].ts ) {
                        assert \A p \in q : vote[p][c][b].ts = t;
                        MakeStable(c, b, t, ds);
                    }
                };
        decided:skip 
    }
}

*)
\* BEGIN TRANSLATION
\* Label acc of process acc at line 326 col 17 changed to acc_
VARIABLES ballot, vote, propose, stable, join, pc

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}

Vote == [ts : Nat, status : Status, deps : SUBSET C]

Propose == [ts : Time] \cup [ts : Nat, phase1Deps : SUBSET C] \cup [ts : Nat, deps : SUBSET C]

TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> Vote]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Propose]
    /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
    /\  join \in SUBSET (C \times Ballot)


Phase1(B) == <<B,1>>
Phase2(B) == <<B,2>>
Phase3(B) == <<B,3>>


SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN vote[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE Bot


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, B, q) ==
    LET bals == {LastBal(c, Pred(Phase1(B)), p) : p \in q}
    IN Max(bals)


TimeStampOf(c, p) == MaxVote(c,p).ts


TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}


CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}


Phase1ReplyDeps(p, c, b, t) ==
    IF "phase1Deps" \in DOMAIN propose[<<c, b>>]
    THEN
        LET new ==  { c2 \in SeenCmds(p) :
            /\  <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>
            /\  LET last == LastBal(c2, Max(Ballot), p)
                    status ==  vote[p][c2][last].status IN
                \/  last = <<0,1>> /\  status = "stable"
                \/  <<0,1>> \prec last /\ status \in {"accepted","pending","stable"} }
        IN propose[<<c, b>>].phase1Deps \cup new
    ELSE CmdsWithLowerT(p, c, t)


ParticipatedIn(b, c, q) == {p \in q : b \in DOMAIN vote[p][c]}


Deps(c, p) == MaxVote(c, p).deps \ {c}


Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Deps(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxVote(c2,p).status \notin {"stable","accepted"}


Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)


NoConflict(p, c, t) == \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2)


RejectTimestamp(c, p) == GT(c, TimeStamps(p))


RetryTimestamp(c, b, q) == GTE(c, {<<c, vote[p][c][b].ts>> : p \in q})


PendingOnQuorum(c, b, q) == \A p \in q :
    /\  SeenAt(c, b, p)
    /\  vote[p][c][b].status = "pending"


RejectedOnQuorum(c, b, q) ==
    /\  \A p \in q : SeenAt(c, b, p)
    /\  \E p \in q : vote[p][c][b].status = "rejected"


AcceptedOnQuorum(c, b, q) == \A p \in q :
    /\  SeenAt(c, b, p)
    /\  vote[p][c][b].status = "accepted"

Rejected(c, ps, b) == \E p \in ps : vote[p][c][b].status = "rejected"

VotedDeps(q, c, b) == UNION {vote[p][c][b].deps : p \in q}

Pending(c, ps, b) == \A p \in ps :
    vote[p][c][b].status \notin {"stable","rejected"}

AVote(ps, c, b) == (LET p == CHOOSE p \in ps : TRUE IN vote[p][c][b])

PossibleFastQuorums(q, ps) == {fq \in FastQuorum : fq \cap q \subseteq ps}

ConfirmedIfFast(c, ps, fqs, b) ==
    LET deps == VotedDeps(ps, c, b)
    IN {c2 \in deps : (\A q \in fqs :
        \E p \in q \cap ps : c2 \in vote[p][c][b].deps)}





GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
    /\ <<c1,b1>> \in DOMAIN stable
    /\ <<c2,b2>> \in DOMAIN stable
    /\ c1 # c2
    /\ <<c1, stable[<<c1,b1>>].ts>> \sqsubset <<c2, stable[<<c2,b2>>].ts>>
    => c1 \in stable[<<c2,b2>>].deps

Agreement == \A c \in C : \A b1,b2 \in Ballot :
    /\ <<c,b1>> \in DOMAIN stable
    /\ <<c,b2>> \in DOMAIN stable
    => stable[<<c,b1>>].ts = stable[<<c,b2>>].ts


vars == << ballot, vote, propose, stable, join, pc >>

ProcSet == (P) \cup ((C \times MajorBallot))

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> <<0,1>>]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ join = {}
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "acc_"
                                        [] self \in (C \times MajorBallot) -> "start"]

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E B \in MajorBallot:
                           LET b == Phase1(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c, b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ IF NoConflict(self, c, t)
                                        THEN /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                        <<b, [ts |-> t, status |-> "pending", deps |-> Phase1ReplyDeps(self, c, b, t)]>>]]
                                        ELSE /\ LET t2 == RejectTimestamp(c, self) IN
                                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                          ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> CmdsWithLowerT(self, c, t2[2])]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ ballot[self][c] \preceq b /\ <<c,b>> \in DOMAIN stable
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET s == stable[<<c,b>>] IN
                                vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [
                                        status |-> "stable",
                                        ts |-> s.ts,
                                        deps |-> s.deps ]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajorBallot:
                           LET b == Phase2(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ IF NoConflict(self, c, t)
                                        THEN /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                        <<b, [ts |-> t, status |-> "pending", deps |-> propose[<<c,b>>].deps]>>]]
                                        ELSE /\ LET t2 == RejectTimestamp(c, self) IN
                                                  vote' =       [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                          ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> CmdsWithLowerT(self, c, t2[2])]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajorBallot:
                           LET b == Phase3(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [
                                          ts |-> t, status |-> "accepted",
                                          deps |-> CmdsWithLowerT(self, c, t) \cup propose[<<c,b>>].deps]>>]]
                 \/ /\ \E prop \in join:
                         LET c == prop[1] IN
                           LET b == prop[2] IN
                             /\ ballot[self][c] \prec b
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                    /\ vote' = vote
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << propose, stable, join >>

acc(self) == acc_(self)

start(self) == /\ pc[self] = "start"
               /\ \/ /\ self[2] = 0
                     /\ pc' = [pc EXCEPT ![self] = "phase1"]
                  \/ /\ self[2] > 0
                     /\ pc' = [pc EXCEPT ![self] = "startBal"]
               /\ UNCHANGED << ballot, vote, propose, stable, join >>

phase1(self) == /\ pc[self] = "phase1"
                /\ \E t \in Time:
                     /\ Assert(<<(self[1]),Phase1((self[2]))>> \notin DOMAIN propose, 
                               "Failure of assertion at line 295, column 9 of macro called at line 348, column 25.")
                     /\ propose' = propose ++ <<<<(self[1]),Phase1((self[2]))>>, [ts |-> t]>>
                     /\ pc' = [pc EXCEPT ![self] = "end1"]
                /\ UNCHANGED << ballot, vote, stable, join >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ Assert(<<(self[1]),Phase1((self[2]))>> \notin join, 
                            "Failure of assertion at line 313, column 9 of macro called at line 352, column 21.")
                  /\ join' = (join \cup {<<(self[1]),Phase1((self[2]))>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, propose, stable >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET B == self[2] IN
                          /\ \A p \in q : Phase1(B) \preceq ballot[p][c]
                          /\ Assert(\A p \in q : ballot[p][c] \notin {Phase2(B),Phase3(B)}, 
                                    "Failure of assertion at line 357, column 25.")
                          /\ LET maxBal == MaxBal(c, B, q) IN
                               LET ps == ParticipatedIn(maxBal, c, q) IN
                                 /\ Assert(maxBal[1] < B, 
                                           "Failure of assertion at line 359, column 29.")
                                 /\ IF maxBal = Bot
                                       THEN /\ \E t \in Time:
                                                 /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                           "Failure of assertion at line 295, column 9 of macro called at line 362, column 33.")
                                                 /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                                       ELSE /\ IF \E p \in ps : vote[p][c][maxBal].status = "stable"
                                                  THEN /\ FALSE
                                                       /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                       /\ UNCHANGED propose
                                                  ELSE /\ IF Phase(maxBal) = 3
                                                             THEN /\ LET v == AVote(ps, c, maxBal) IN
                                                                       LET t == v.ts IN
                                                                         LET ds == v.deps IN
                                                                           /\ Assert(<<c,Phase3(B)>> \notin DOMAIN propose, 
                                                                                     "Failure of assertion at line 307, column 9 of macro called at line 369, column 33.")
                                                                           /\ propose' = propose ++ <<<<c,Phase3(B)>>, [ts |-> t, deps |-> ds]>>
                                                                           /\ pc' = [pc EXCEPT ![self] = "end3"]
                                                             ELSE /\ IF Phase(maxBal) \in {1,2} /\ Rejected(c, ps, maxBal)
                                                                        THEN /\ \E t \in Time:
                                                                                  /\ Assert(   \A p \in P : c \in DOMAIN vote[p] =>
                                                                                            \A b2 \in DOMAIN vote[p][c] : b2 \preceq maxBal =>
                                                                                                vote[p][c][b2].status \notin {"accepted","stable"}, 
                                                                                            "Failure of assertion at line 374, column 33.")
                                                                                  /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                                            "Failure of assertion at line 295, column 9 of macro called at line 377, column 33.")
                                                                                  /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                                                  /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                        ELSE /\ IF Phase(maxBal) = 2 /\ Pending(c, ps, maxBal)
                                                                                   THEN /\ LET v == AVote(ps, c, maxBal) IN
                                                                                             LET t == v.ts IN
                                                                                               LET ds == v.deps IN
                                                                                                 /\ Assert(\A p \in ps : vote[p][c][maxBal].status = "pending", 
                                                                                                           "Failure of assertion at line 381, column 33.")
                                                                                                 /\ Assert(<<c,Phase2(B)>> \notin DOMAIN propose, 
                                                                                                           "Failure of assertion at line 301, column 9 of macro called at line 382, column 33.")
                                                                                                 /\ propose' = propose ++ <<<<c,Phase2(B)>>, [ts |-> t, deps |-> ds]>>
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "end2"]
                                                                                   ELSE /\ IF Phase(maxBal) = 1 /\ Pending(c, ps, maxBal)
                                                                                              THEN /\ LET t == AVote(ps, c, maxBal).ts IN
                                                                                                        /\ Assert(\A p \in ps : vote[p][c][maxBal].status = "pending", 
                                                                                                                  "Failure of assertion at line 386, column 33.")
                                                                                                        /\ IF \E p \in ps : "phase1Deps" \in DOMAIN vote[p][c][maxBal]
                                                                                                              THEN /\ LET p == CHOOSE p \in ps : "phase1Deps" \in DOMAIN vote[p][c][maxBal] IN
                                                                                                                        propose' =        propose ++ <<<<c,Phase1(B)>>,
                                                                                                                                   [ts |-> t, phase1Deps |-> vote[p][c][maxBal].phase1Deps]>>
                                                                                                                   /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                                              ELSE /\ LET fqs == PossibleFastQuorums(q, ps) IN
                                                                                                                        IF fqs # {}
                                                                                                                           THEN /\ propose' =        propose ++ <<<<c,Phase1(B)>>,
                                                                                                                                              [ts |-> t, phase1Deps |-> ConfirmedIfFast(c, ps, fqs, maxBal)]>>
                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                                                           ELSE /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                                                                                          "Failure of assertion at line 295, column 9 of macro called at line 399, column 44.")
                                                                                                                                /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                                                                                                /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                              ELSE /\ Assert(FALSE, 
                                                                                                             "Failure of assertion at line 403, column 33.")
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                                   /\ UNCHANGED propose
                 /\ UNCHANGED << ballot, vote, stable, join >>

end1(self) == /\ pc[self] = "end1"
              /\ \/ /\ \E q \in FastQuorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ PendingOnQuorum(c, b, q)
                             /\ LET ds == VotedDeps(q, c, b) IN
                                  LET t == propose[<<c,b>>].ts IN
                                    /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "decided"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ RejectedOnQuorum(c, b, q)
                             /\ LET ds == VotedDeps(q, c, b) IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 307, column 9 of macro called at line 422, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ PendingOnQuorum(c, b, q)
                             /\ LET ds == VotedDeps(q, c, b) IN
                                  LET t == AVote(q, c, b).ts IN
                                    /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                              "Failure of assertion at line 430, column 29.")
                                    /\ Assert(<<c,Phase2((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 301, column 9 of macro called at line 431, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase2((b[1]))>>, [ts |-> t, deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end2"]
                    /\ UNCHANGED stable
              /\ UNCHANGED << ballot, vote, join >>

end2(self) == /\ pc[self] = "end2"
              /\ \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase2(self[2]) IN
                             /\ PendingOnQuorum(c, b, q)
                             /\ LET v == AVote(q, c, b) IN
                                  LET ds == v.deps IN
                                    LET t == v.ts IN
                                      /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                                "Failure of assertion at line 440, column 29.")
                                      /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                      /\ pc' = [pc EXCEPT ![self] = "decided"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase2(self[2]) IN
                             /\ RejectedOnQuorum(c, b, q)
                             /\ LET ds == VotedDeps(q, c, b) IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 307, column 9 of macro called at line 449, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
              /\ UNCHANGED << ballot, vote, join >>

end3(self) == /\ pc[self] = "end3"
              /\ \E q \in Quorum:
                   LET c == self[1] IN
                     LET b == Phase3(self[2]) IN
                       /\ AcceptedOnQuorum(c, b, q)
                       /\ LET ds == VotedDeps(q, c, b) IN
                            LET t == propose[<<c,b>>].ts IN
                              /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                        "Failure of assertion at line 457, column 25.")
                              /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                              /\ pc' = [pc EXCEPT ![self] = "decided"]
              /\ UNCHANGED << ballot, vote, propose, join >>

decided(self) == /\ pc[self] = "decided"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, propose, stable, join >>

leader(self) == start(self) \/ phase1(self) \/ startBal(self)
                   \/ recover(self) \/ end1(self) \/ end2(self)
                   \/ end3(self) \/ decided(self)

Next == (\E self \in P: acc(self))
           \/ (\E self \in (C \times MajorBallot): leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Wed May 04 15:47:13 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
