---------------------------- MODULE Caesar4 ----------------------------

(****************************************************************************
Model-checking results:

With 5 acceptors, 2 ballots, MaxTime=1, and the following constraint:

    /\ \A x \in {2,3} : <<c1, <<0,x>>>> \notin DOMAIN propose
    /\ \A b \in Ballot :  <<c1, b>> \notin join
    /\ \A x \in {2,3} : <<c2, <<0,x>>>> \notin DOMAIN propose

36M reachable states, 8 hours on whitewhale, depth 49.

With 3 acceptors, 2 ballots, MaxTime=1, and the following constraint:

    \A b \in Ballot :  <<c1, b>> \notin join

4.7M reachable states, 5 minutes on whitewhale, depth 43.

With 3 acceptors, 2 ballots, MaxTime=1, and no constraint: 200M
reachable states, 3 hours 35 minutes on whitewhale, depth 52.

With 5 acceptors, 2 ballots, MaxTime=1, and the following constraint:

    /\ \A x \in {2} : <<c1, <<0,x>>>> \notin DOMAIN propose
    /\ \A b \in Ballot :  <<c1, b>> \notin join
    /\ \A x \in {1,3} : <<c2, <<1,x>>>> \notin DOMAIN propose
    /\ \A x \in {3} : <<c2, <<0,x>>>> \notin DOMAIN propose
    /\ \A A \in {A \in SUBSET P : \E q \in Quorum : q \subseteq A /\ q # A} :
        \E p \in A : DOMAIN vote[p][c1] = {}

****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, Sequences, Integers

(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
(***************************************************************************)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(***************************************************************************)
(* The image of a map                                                      *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* P is the set of acceptors.  MaxTime bounds the timestamp that can be    *)
(* assigned to proposals, but not to retries.  CmdId(c) must assign a      *)
(* natural number to a command.  It is used to break time in timestamps.   *)
(***************************************************************************)
CONSTANTS P, MaxTime, Quorum, FastQuorum, NumBallots, C, CmdId(_)

ASSUME NumBallots \in Nat /\ NumBallots >= 1

ASSUME \A c \in C : CmdId(c) \in Nat /\ \A c2 \in C : c # c2 => CmdId(c) # CmdId(c2)

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Ballots are of the form <<b,i>>, where b is the main ballot number and  *)
(* i the sub-ballot number.  Ballots are totally ordered:                  *)
(***************************************************************************)
MajorBallot == 0..(NumBallots-1)
Ballot == MajorBallot \times {1,2,3} \* We have three sub-ballots.

bal1 \prec bal2 == 
    IF bal1[1] = bal2[1]
    THEN bal1[2] < bal2[2]
    ELSE bal1[1] < bal2[1]

bal1 \preceq bal2 ==
    bal1 \prec bal2 \/ bal1 = bal2
    
(***************************************************************************)
(* The maximum element in a set of ballots.                                *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : y \preceq x

(***************************************************************************)
(* The predecessor of a ballot.                                            *)
(***************************************************************************)
Pred(b) == CASE 
    b[2] = 1 -> <<b[1]-1,3>>
[]  b[2] = 2 -> <<b[1],1>>
[]  b[2] = 3 -> <<b[1],2>>

(***************************************************************************)
(* Majority quorums and three fourths quorums.  For provinding concrete    *)
(* quorums to the model-checker.                                           *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

(***************************************************************************)
(* An ordering relation among pairs of the form <<c, timestamp>>.  Allows  *)
(* to break ties between timestamps by also using the command to compute   *)
(* the ordering.                                                           *)
(*                                                                         *)
(* CAUTION: C must not be a symmetrical set in TLC's configuration,        *)
(* because commands are ordered.                                           *)
(***************************************************************************)
ts1 \sqsubset ts2 == 
    IF ts1[2] = ts2[2] \* if same timestamp:
    THEN CmdId(ts1[1]) < CmdId(ts2[1]) \* break ties with command id.
    ELSE ts1[2] < ts2[2] \* else compare timestamps.

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
        
        Propose == [ts : Time] \cup [ts : Nat, must : SUBSET C] \cup [ts : Nat, deps : SUBSET C]
        
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> Vote]
            /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Propose]
            /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
            /\  join \in SUBSET (C \times Ballot)
        
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}
        
        \* TRUE if c was seen in ballot b at p.
        SeenAt(c, b, p) == b \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
            IF bals # {}
            THEN Max(bals)
            ELSE <<-1,3>>
        
        \* The vote for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, Pred(b), p) : p \in q}
            IN Max(bals)
        
        \* The timestamp found at p in the vote for c in the highest ballot.
        TimeStampOf(c, p) == MaxVote(c,p).ts
        
        TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}
        
        \* All the commands at p which have a lower timestamp than <<c,t>>
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}
        
        Phase1ReplyDeps(p, c, b, t) ==       
            IF "must" \in DOMAIN propose[<<c, b>>]
            THEN 
                LET new ==  { c2 \in SeenCmds(p) : 
                    /\  <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>
                    /\  LET last == LastBal(c2, Max(Ballot), p)
                            status ==  vote[p][c2][last].status IN
                        \/  last = <<0,1>> /\  status = "stable"
                        \/  <<0,1>> \prec last /\ status \in {"accepted","pending","stable"} }
                IN propose[<<c, b>>].must \cup new
            ELSE CmdsWithLowerT(p, c, t)
                            
        ParticipatedIn(b, c, q) == {p \in q : b \in DOMAIN vote[p][c]}
        
        Deps(c, p) == MaxVote(c, p).seen \ {c}
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Deps(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ MaxVote(c2,p).status \notin {"stable","accepted"}
        
        Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)
        
        Cmd(leader) == leader[1]
        Bal(leader) == leader[2] 
        
        NoConflict(p, c, t) == \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2)
        
        Phase1(B) == <<B,1>>
        Phase2(B) == <<B,2>>
        Phase3(B) == <<B,3>>
        Maj(b) == b[1]
        Phase(b) == b[2]
        
        (***************************************************************************)
        (* A timestamp for c strictly greater than the max of the timstamps xs.    *)
        (***************************************************************************)
        GT(c, xs) ==  
            LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
            IN IF CmdId(max[1]) < CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
            
        RejectTimestamp(c, p) == GT(c, TimeStamps(p))
        
        (***************************************************************************)
        (* A timestamp fo c greater than or equal to the max of the timstamps xs.  *)
        (***************************************************************************)
        GTE(c, xs) ==  
            LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
            IN IF CmdId(max[1]) <= CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
            
        RetryTimestamp(c, b, q) == GTE(c, {<<c, vote[p][c][b].ts>> : p \in q})
        
        ReachedQuorum(c, b, q) == \A p \in q : SeenAt(c, b, p)
        
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
        
        SeenBy(q, c, b) == UNION {vote[p][c][b].seen : p \in q}
        
        Pending(c, ps, b) == \A p \in ps : 
            vote[p][c][b].status \notin {"stable","rejected"}
        
        AVote(ps, c, b) == (LET p == CHOOSE p \in ps : TRUE IN vote[p][c][b])
                
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
                    with (deps = propose[<<c,b>>].deps) {
                        vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                            <<b, [ts |-> t, status |-> "pending", deps |-> deps]>>]];
                    }
                }
                else {
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  t2 = RejectTimestamp(c, p),
                            seen = CmdsWithLowerT(p, c, t2[2]) ) {
                      \* Record the fact that the command was rejected with t2:
                      vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> seen]>>]];
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
                    seen |-> CmdsWithLowerT(p, c, t) \cup propose[<<c,b>>].deps]>>]];
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
                    seen |-> s.deps ]>>]];
            }
        }
    }    
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot (0) by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when ballot[p][c] \prec b;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }

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
                        with (  \* the maximum ballot strictly less than Phase1(B) in which a vote was cast:
                                maxBal = MaxBal(c, Phase1(B), q);
                                \* get the set ps of acceptors in the quorum q who participated in the maximum ballot:
                                ps = ParticipatedIn(maxBal, c, q) ) {
                            assert maxBal[1] < B; \* Sanity check.
                            if (Maj(maxBal) = -1) { \* No acceptor in q has seen the command.
                                with (t \in Time) {
                                    StartPhase1(c, B, t)
                                }
                            }
                            else if (\E p \in ps : vote[p][c][maxBal].status = "stable") {
                                when FALSE; \* This case is not interesting
                            }
                            else if (Phase(maxBal) = 3) {
                                with (v = AVote(ps, c, maxBal), t = v.ts, ds = v.deps) {
                                    StartPhase3(c, B, t, ds);
                                }
                            }
                            else if (Phase(maxBal) \in {1,2} /\ Rejected(c, ps, maxBal)) {
                                \* An invariant at this point:
                                assert \A p2 \in P : c \in DOMAIN vote[p2] => 
                                    \A b2 \in DOMAIN vote[p2][c] : b2 \preceq maxBal => 
                                        vote[p2][c][b2].status \notin {"accepted","stable"};
                                with (t \in Time) { \* use an arbitrary timestamp.
                                    StartPhase1(c, B, t);
                                }
                            }
                            else if (Phase(maxBal) = 2 /\ Pending(c, ps, maxBal)) {
                                assert \A p2 \in ps : vote[p2][c][maxBal].status = "pending";
                                with (v = AVote(ps, c, maxBal), t = v.ts, ds = v.deps) {
                                    StartPhase2(c, B, t, ds);
                                }
                            }
                            else if (Phase(maxBal) = 1 /\ Pending(c, ps, maxBal)) {
                                assert \A p2 \in ps : vote[p2][c][maxBal].status = "pending";
                                with (  \* the set of fast quorums which could have seen a fast decision:
                                        fast = {q2 \in FastQuorum : q2 \cap q \subseteq ps}; 
                                        t = AVote(ps, c, maxBal).ts) { 
                                    if (fast # {}) { \* There might have been a fast decision
                                        \* must has the deps such that if there was a fast decision
                                        \* then those deps must be in the fast decision.
                                        with (  deps = SeenBy(ps, c, maxBal);
                                                must = {c2 \in deps : (\A q2 \in fast : 
                                                    \E p2 \in q2 \cap ps : 
                                                        c2 \in vote[p2][c][maxBal].seen)}) {
                                            assert <<c,Phase1(B)>> \notin DOMAIN propose;
                                            propose := propose ++ <<<<c,Phase1(B)>>, [ts |-> t, must |-> must]>>;
                                        }
                                    }
                                    else {
                                        StartPhase1(c, B, t)
                                    }
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
                        with (  ds = SeenBy(q, c, b); t = propose[<<c,b>>].ts ) {
                            MakeStable(c, b, t, ds);
                        }
                    };
                } or {
                    (* there is a reject, trigger phase 3. *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when RejectedOnQuorum(c, b, q);
                        with (  ds = SeenBy(q, c, b); t = RetryTimestamp(c, b, q) ) {
                            StartPhase3(c, b[1], t[2], ds);
                        }
                    }
                } or {
                    (* Timeout, trigger phase 2 *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when PendingOnQuorum(c, b, q);
                        with (  ds = SeenBy(q, c, b); t = AVote(q, c, b).ts) {
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
                        with (  ds = SeenBy(q, c, b); t = RetryTimestamp(c, b, q) ) {
                            StartPhase3(c, b[1], t[2], ds);
                        }
                    }
                }; 
        end3:   (* Decide in phase 3 *)
                with (q \in Quorum, c = self[1], b = Phase3(self[2]) ) {
                    when AcceptedOnQuorum(q, c, b);
                    with (  ds = SeenBy(q, c, b); t = propose[<<c,b>>].ts ) {
                        assert \A p \in q : vote[p][c][b].ts = t;
                        MakeStable(c, b, t, ds);
                    }
                };
        decided:skip 
    }
  
}

*)
\* BEGIN TRANSLATION
\* Label acc of process acc at line 384 col 17 changed to acc_
VARIABLES ballot, vote, propose, stable, join, pc

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}

Vote == [ts : Nat, status : Status, deps : SUBSET C]

Propose == [ts : Time] \cup [ts : Nat, must : SUBSET C] \cup [ts : Nat, deps : SUBSET C]

TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> Vote]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Propose]
    /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
    /\  join \in SUBSET (C \times Ballot)


SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN vote[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE <<-1,3>>


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, Pred(b), p) : p \in q}
    IN Max(bals)


TimeStampOf(c, p) == MaxVote(c,p).ts

TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}


CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}

Phase1ReplyDeps(p, c, b, t) ==
    IF "must" \in DOMAIN propose[<<c, b>>]
    THEN
        LET new ==  { c2 \in SeenCmds(p) :
            /\  <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>
            /\  LET last == LastBal(c2, Max(Ballot), p)
                    status ==  vote[p][c2][last].status IN
                \/  last = <<0,1>> /\  status = "stable"
                \/  <<0,1>> \prec last /\ status \in {"accepted","pending","stable"} }
        IN propose[<<c, b>>].must \cup new
    ELSE CmdsWithLowerT(p, c, t)

ParticipatedIn(b, c, q) == {p \in q : b \in DOMAIN vote[p][c]}

Deps(c, p) == MaxVote(c, p).seen \ {c}

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Deps(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxVote(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)

Cmd(leader) == leader[1]
Bal(leader) == leader[2]

NoConflict(p, c, t) == \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2)

Phase1(B) == <<B,1>>
Phase2(B) == <<B,2>>
Phase3(B) == <<B,3>>
Maj(b) == b[1]
Phase(b) == b[2]




GT(c, xs) ==
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
    IN IF CmdId(max[1]) < CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>>

RejectTimestamp(c, p) == GT(c, TimeStamps(p))




GTE(c, xs) ==
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
    IN IF CmdId(max[1]) <= CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>>

RetryTimestamp(c, b, q) == GTE(c, {<<c, vote[p][c][b].ts>> : p \in q})

ReachedQuorum(c, b, q) == \A p \in q : SeenAt(c, b, p)

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

SeenBy(q, c, b) == UNION {vote[p][c][b].seen : p \in q}

Pending(c, ps, b) == \A p \in ps :
    vote[p][c][b].status \notin {"stable","rejected"}

AVote(ps, c, b) == (LET p == CHOOSE p \in ps : TRUE IN vote[p][c][b])





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
                                        seen |-> s.deps ]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajorBallot:
                           LET b == Phase2(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ IF NoConflict(self, c, t)
                                        THEN /\ LET deps == propose[<<c,b>>].deps IN
                                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                          <<b, [ts |-> t, status |-> "pending", deps |-> deps]>>]]
                                        ELSE /\ LET t2 == RejectTimestamp(c, self) IN
                                                  LET seen == CmdsWithLowerT(self, c, t2[2]) IN
                                                    vote' =       [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                            ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> seen]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajorBallot:
                           LET b == Phase3(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [
                                          ts |-> t, status |-> "accepted",
                                          seen |-> CmdsWithLowerT(self, c, t) \cup propose[<<c,b>>].deps]>>]]
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
                               "Failure of assertion at line 353, column 9 of macro called at line 406, column 25.")
                     /\ propose' = propose ++ <<<<(self[1]),Phase1((self[2]))>>, [ts |-> t]>>
                     /\ pc' = [pc EXCEPT ![self] = "end1"]
                /\ UNCHANGED << ballot, vote, stable, join >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ Assert(<<(self[1]),Phase1((self[2]))>> \notin join, 
                            "Failure of assertion at line 371, column 9 of macro called at line 410, column 21.")
                  /\ join' = (join \cup {<<(self[1]),Phase1((self[2]))>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, propose, stable >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET B == self[2] IN
                          /\ \A p \in q : Phase1(B) \preceq ballot[p][c]
                          /\ Assert(\A p \in q : ballot[p][c] \notin {Phase2(B),Phase3(B)}, 
                                    "Failure of assertion at line 415, column 25.")
                          /\ LET maxBal == MaxBal(c, Phase1(B), q) IN
                               LET ps == ParticipatedIn(maxBal, c, q) IN
                                 /\ Assert(maxBal[1] < B, 
                                           "Failure of assertion at line 420, column 29.")
                                 /\ IF Maj(maxBal) = -1
                                       THEN /\ \E t \in Time:
                                                 /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                           "Failure of assertion at line 353, column 9 of macro called at line 423, column 37.")
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
                                                                                     "Failure of assertion at line 365, column 9 of macro called at line 431, column 37.")
                                                                           /\ propose' = propose ++ <<<<c,Phase3(B)>>, [ts |-> t, deps |-> ds]>>
                                                                           /\ pc' = [pc EXCEPT ![self] = "end3"]
                                                             ELSE /\ IF Phase(maxBal) \in {1,2} /\ Rejected(c, ps, maxBal)
                                                                        THEN /\ Assert(   \A p2 \in P : c \in DOMAIN vote[p2] =>
                                                                                       \A b2 \in DOMAIN vote[p2][c] : b2 \preceq maxBal =>
                                                                                           vote[p2][c][b2].status \notin {"accepted","stable"}, 
                                                                                       "Failure of assertion at line 436, column 33.")
                                                                             /\ \E t \in Time:
                                                                                  /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                                            "Failure of assertion at line 353, column 9 of macro called at line 440, column 37.")
                                                                                  /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                                                  /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                        ELSE /\ IF Phase(maxBal) = 2 /\ Pending(c, ps, maxBal)
                                                                                   THEN /\ Assert(\A p2 \in ps : vote[p2][c][maxBal].status = "pending", 
                                                                                                  "Failure of assertion at line 444, column 33.")
                                                                                        /\ LET v == AVote(ps, c, maxBal) IN
                                                                                             LET t == v.ts IN
                                                                                               LET ds == v.deps IN
                                                                                                 /\ Assert(<<c,Phase2(B)>> \notin DOMAIN propose, 
                                                                                                           "Failure of assertion at line 359, column 9 of macro called at line 446, column 37.")
                                                                                                 /\ propose' = propose ++ <<<<c,Phase2(B)>>, [ts |-> t, deps |-> ds]>>
                                                                                                 /\ pc' = [pc EXCEPT ![self] = "end2"]
                                                                                   ELSE /\ IF Phase(maxBal) = 1 /\ Pending(c, ps, maxBal)
                                                                                              THEN /\ Assert(\A p2 \in ps : vote[p2][c][maxBal].status = "pending", 
                                                                                                             "Failure of assertion at line 450, column 33.")
                                                                                                   /\ LET fast == {q2 \in FastQuorum : q2 \cap q \subseteq ps} IN
                                                                                                        LET t == AVote(ps, c, maxBal).ts IN
                                                                                                          IF fast # {}
                                                                                                             THEN /\ LET deps == SeenBy(ps, c, maxBal) IN
                                                                                                                       LET must ==    {c2 \in deps : (\A q2 \in fast :
                                                                                                                                   \E p2 \in q2 \cap ps :
                                                                                                                                       c2 \in vote[p2][c][maxBal].seen)} IN
                                                                                                                         /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                                                                                   "Failure of assertion at line 461, column 45.")
                                                                                                                         /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t, must |-> must]>>
                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                                             ELSE /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                                                                            "Failure of assertion at line 353, column 9 of macro called at line 466, column 41.")
                                                                                                                  /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                                                                                  /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                              ELSE /\ Assert(FALSE, 
                                                                                                             "Failure of assertion at line 471, column 33.")
                                                                                                   /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                                                                   /\ UNCHANGED propose
                 /\ UNCHANGED << ballot, vote, stable, join >>

end1(self) == /\ pc[self] = "end1"
              /\ \/ /\ \E q \in FastQuorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ PendingOnQuorum(c, b, q)
                             /\ LET ds == SeenBy(q, c, b) IN
                                  LET t == propose[<<c,b>>].ts IN
                                    /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "decided"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ RejectedOnQuorum(c, b, q)
                             /\ LET ds == SeenBy(q, c, b) IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 365, column 9 of macro called at line 490, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ PendingOnQuorum(c, b, q)
                             /\ LET ds == SeenBy(q, c, b) IN
                                  LET t == AVote(q, c, b).ts IN
                                    /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                              "Failure of assertion at line 498, column 29.")
                                    /\ Assert(<<c,Phase2((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 359, column 9 of macro called at line 499, column 29.")
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
                                                "Failure of assertion at line 508, column 29.")
                                      /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                      /\ pc' = [pc EXCEPT ![self] = "decided"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase2(self[2]) IN
                             /\ RejectedOnQuorum(c, b, q)
                             /\ LET ds == SeenBy(q, c, b) IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 365, column 9 of macro called at line 517, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
              /\ UNCHANGED << ballot, vote, join >>

end3(self) == /\ pc[self] = "end3"
              /\ \E q \in Quorum:
                   LET c == self[1] IN
                     LET b == Phase3(self[2]) IN
                       /\ AcceptedOnQuorum(q, c, b)
                       /\ LET ds == SeenBy(q, c, b) IN
                            LET t == propose[<<c,b>>].ts IN
                              /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                        "Failure of assertion at line 525, column 25.")
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
\* Last modified Mon May 02 17:45:26 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
