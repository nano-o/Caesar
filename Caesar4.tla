---------------------------- MODULE Caesar4 ----------------------------

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

(***************************************************************************)
(* Ballots are of the form <<b,i>>, where b is the main ballot number and  *)
(* i the sub-ballot number.  Ballots can be compared:                      *)
(***************************************************************************)
MajBallot == 0..(NumBallots-1)
Ballot == MajBallot \times {1,2,3} \* We have three sub-ballots.

bal1 \prec bal2 == 
    IF bal1[1] = bal2[1]
    THEN bal1[2] < bal2[2]
    ELSE bal1[1] < bal2[1]

bal1 \preceq bal2 ==
    bal1 \prec bal2 \/ bal1 = bal2
    
Pred(b) == CASE 
    b[2] = 1 -> <<b[1]-1,3>>
[]  b[2] = 2 -> <<b[1],1>>
[]  b[2] = 3 -> <<b[1],2>>

ASSUME \A c \in C : CmdId(c) \in Nat /\ \A c2 \in C : c # c2 => CmdId(c) # CmdId(c2)

Time == 1..MaxTime

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourths quorums.                             *)
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

(***************************************************************************)
(* The maximum element in a set of ballots.                                *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : y \preceq x

    
(***********

--algorithm Caesar { \* TODO: issue with timestamps: use <<c,t>> everywhere?

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
        \* For each pair <<c,b>>, a phase1Deps for the propose phase of the last case of the recovery...
        \* phase1Deps = <<>>

    define {
        
        Status == {"pending", "stable", "accepted", "rejected"}
        
        (*
        CmdInfo == [ts : Nat, deps : SUBSET C]
        CmdInfoWithStat == [ts : Nat, seen : SUBSET C, leaderDeps : SUBSET C, status: Status]
        *)
        
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
        
        \* All the commands at p which have a lower timestamp than <<c,t>> and a status in S
        LowerCmds(p, c, t, S) == {
            c2 \in SeenCmds(p) : vote[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
                /\ <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}
        
        ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]
        
        Deps(c, p) == MaxVote(c, p).seen \ {c}
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Deps(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ MaxVote(c2,p).status \notin {"stable","accepted"}
        
        Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)
                
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
        
        HasCmd(c, b, q) == \A p2 \in q : SeenAt(c, b, p2)
            
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
        with (c \in C; B \in MajBallot, b = Phase1(B)) {
            BallotPre(c,b);
            with (t = propose[<<c, b>>].ts) {
                \* when LastBal(c, b, p) \prec b; \* p has not participated yet in this ballot, but covered by BallotPre (\prec).
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                if (NoConflict(p, c, t)) { 
                    vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "pending", seen |-> CmdsWithLowerT(p, c, t), leaderDeps |-> {}]>>]];
                } 
                else {
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  t2 = RejectTimestamp(c, p) ) {
                        \* Record the fact that the command was rejected with t2:
                        vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                            ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> CmdsWithLowerT(p, c, t2[2]), leaderDeps |-> {}]>>]];
                    }
                }
                (*
                with (flag = IF <<c,Maj(b)>> \in DOMAIN phase1Deps THEN TRUE ELSE FALSE) {
                    if (NoConflict(p, c, t)) { 
                        with (seen = IF <<c,Maj(b)>> \in DOMAIN phase1Deps
                                THEN phase1Deps[<<c,Maj(b)>>] \cup LowerCmds(p, c, t, {"accepted", "stable", "pending"}) \* TODO
                                ELSE CmdsWithLowerT(p, c, t)) {
                            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                                <<b, [ts |-> t, status |-> "pending", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        }
                    } 
                    else {
                        \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                        with (  t2 = RejectTimestamp(c, p);
                                seen = IF <<c,Maj(b)>> \in DOMAIN phase1Deps
                                    THEN phase1Deps[<<c,Maj(b)>>] \cup LowerCmds(p, c, t2[2], {"accepted", "stable", "pending"}) \* TODO
                                    ELSE CmdsWithLowerT(p, c, t2[2]) ) {
                            \* Record the fact that the command was rejected with t2:
                            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                                ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        }
                    }
                }*)
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; B \in MajBallot, b = Phase2(B)) { 
            BallotPre(c, b);
            with (t = propose[<<c,b>>].ts) {
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                if (NoConflict(p, c, t)) {
                    with (deps = propose[<<c,b>>].deps) {
                        vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                            <<b, [ts |-> t, status |-> "pending", seen |-> {}, leaderDeps |-> deps]>>]];
                    }
                }
                else {
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  t2 = RejectTimestamp(c, p),
                            seen = CmdsWithLowerT(p, c, t2[2]) ) {
                      \* Record the fact that the command was rejected with t2:
                      vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> seen, leaderDeps |-> {}]>>]];
                    }
                }
            }
        }
    }
    
    macro Phase3Reply(p) {
        with (c \in C; B \in MajBallot, b = Phase3(B)) {
            BallotPre(c,b); 
            with (t = propose[<<c,b>>].ts) {
                vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<b, [  
                    ts |-> t, status |-> "accepted", 
                    seen |-> CmdsWithLowerT(p, c, t) \cup propose[<<c,b>>].deps, 
                    leaderDeps |-> propose[<<c,b>>].deps]>>]]; \* leaderDeps not used.
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
                    seen |-> s.deps, 
                    leaderDeps |-> s.deps ]>>]];
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
    }
    
    macro StartPhase3(c, B, t, deps) {
        assert <<c,Phase3(B)>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,Phase3(B)>>, [ts |-> t, deps |-> deps]>>;
    }
    
    macro StartPhase2(c, B, t, deps) {
        assert <<c,Phase2(B)>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,Phase2(B)>>, [ts |-> t, deps |-> deps]>>;
    }
    
    macro StartBallot(c, B) {
        assert <<c,Phase1(B)>> \notin join;
        join := join \cup {<<c,Phase1(B)>>};
    }
    
    macro MakeStable(c, b, t, deps) {
        stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> deps]>>;
    }
      
    \* Acceptors:
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
    
    process (leader \in (C \times MajBallot)) {
        start:  either { \* Initial proposal for the command.
                    when self[2] = 0;
        phase1:     with (t \in Time) {
                        StartPhase1(self[1], self[2], t)
                    }
                } or { \* Start a new ballot.
                    when self[2] > 0; \* Only start ballots greater than 0; 0 is started by default.
        startBal:   StartBallot(self[1],self[2]);
        recover:    with (q \in Quorum, c = self[1], B = self[2]) {
                        when \A p \in q : Phase1(B) \preceq ballot[p][c]; \* every p in the quorum is in b or higher.
                        assert \A p \in q : ballot[p][c] = Phase1(B) \/ Phase3(B) \prec ballot[p][c];
                        \* the maximum ballot strictly less than Phase1(B) in which a vote was cast:
                        with (maxBal = MaxBal(c, Phase1(B), q)) {
                            assert maxBal[1] < B;
                            if (Maj(maxBal) # -1) {
                                \* get the set ps of acceptors in the quorum q who participated in the maximum ballot.
                                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                                    either {
                                        \* All have status "accepted"
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"stable"}; \* there is no stable status.
                                        when vote[p][c][maxBal].status = "accepted"; \* Can only be a 3-subballot
                                        assert Phase(maxBal) = 3;
                                        with (e = vote[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            StartPhase3(c, B, t, ds);
                                            \* when FALSE;
                                            goto end3;
                                        }
                                    } or {
                                        \* There is one "rejected" and there is no accept or stable:
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable"}; 
                                        when vote[p][c][maxBal].status \in {"rejected"};
                                        assert Phase(maxBal) \in {1,2};
                                        assert \A p2 \in P : c \in DOMAIN vote[p2] => 
                                            \A b2 \in DOMAIN vote[p2][c] : b2 \preceq maxBal => vote[p2][c][b2].status \notin {"accepted","stable"};
                                        with (t \in Time) { \* use an arbitrary timestamp.
                                            StartPhase1(c, B, t);
                                            \* when FALSE;
                                        }
                                    } or {
                                        \* there is one "pending" in phase 2 and there is no accept or stable or reject:
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"};
                                        when Phase(maxBal) = 2 /\ vote[p][c][maxBal].status = "pending";
                                        assert \A p2 \in ps : vote[p][c][maxBal].status = "pending";
                                        with (e = vote[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            StartPhase2(c, B, t, ds);
                                            \* when FALSE;
                                            goto end2;
                                        } 
                                    } or {
                                        \* there is one "pending" in phase 1 and there is no accept or stable or reject:
                                        when Phase(maxBal) = 1;
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"};
                                        when vote[p][c][maxBal].status = "pending";
                                        assert \A p2 \in ps : vote[p][c][maxBal].status = "pending";
                                        (*
                                        with (deps = UNION {vote[p2][c][maxBal].seen : p2 \in ps}; 
                                                x = {c2 \in deps : (\A q2 \in FastQuorum :
                                                    (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in vote[p2][c][maxBal].seen))}) {
                                            phase1Deps := phase1Deps ++ <<<<c,B>>, x>>;
                                        }; *)
                                        StartPhase1(c, B, vote[p][c][maxBal].ts);
                                        \* when FALSE;
                                    } \* We should have covered all cases.
                                }
                            } else {
                                with (t \in Time) {
                                    StartPhase1(c, B, t);
                                    \* when FALSE;
                                }
                            }
                        }
                    }
                };
        end1:   either { 
                    (* Fast decision *)
                    with (q \in FastQuorum, c = self[1], b = Phase1(self[2])) {
                        when \A p \in q : b \in DOMAIN vote[p][c] 
                            /\ vote[p][c][b].status = "pending";
                        with (  ds = UNION {vote[p][c][b].seen : p \in q};
                                t = propose[<<c,b>>].ts ) {
                            MakeStable(c, b, t, ds);
                        }
                    };
                    goto d;
                } or {
                    (* there is a reject, trigger phase 3. *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when HasCmd(c, b, q); \* all acceptors in q have seen c in ballot b.
                        \* The leader receives a phase-1 "reject" message.
                        when \E p2 \in q : vote[p2][c][b].status = "rejected";
                        with (  ds = UNION {vote[p][c][b].seen : p \in q}, t = RetryTimestamp(c, b, q) ) {
                            StartPhase3(c, b[1], t[2], ds);
                            goto end3;
                        }
                    }
                } or {
                    (* Timeout, trigger phase 2 *)
                    with (q \in Quorum, c = self[1], b = Phase1(self[2])) {
                        when HasCmd(c, b, q);
                        when \A p2 \in q : vote[p2][c][b].status = "pending";
                        with (  ds = UNION {vote[p2][c][b].seen : p2 \in q},
                                p2 = CHOOSE p2 \in q : TRUE, t = vote[p2][c][b].ts) {
                            assert \A p \in q : vote[p][c][b].ts = t;
                            StartPhase2(c, b[1], t, ds);
                        }
                    };
        end2:       either {
                        (* Decision in phase 2 *)
                        with (q \in Quorum, c = self[1], b = Phase2(self[2])) {
                            when HasCmd(c, b, q);
                            when \A p2 \in q : vote[p2][c][b].status = "pending";
                            with (  p2 = CHOOSE p2 \in q : TRUE,
                                    ds = vote[p2][c][b].leaderDeps,
                                    t = vote[p2][c][b].ts) {
                                assert \A p \in q : vote[p][c][b].ts = t;
                                MakeStable(c, b, t, ds);
                                goto d; (* GOTO end *)
                            }
                        }
                    } or {
                        (* Reject in phase 2, trigger phase 3 *)
                        with (q \in Quorum, c = self[1], b = Phase2(self[2])) {
                            when HasCmd(c, b, q);
                            \* The leader receives a "reject" message.
                            when \E p2 \in q : vote[p2][c][b].status = "rejected";
                            with (  ds = UNION {vote[p2][c][b].seen : p2 \in q}, 
                                    t = RetryTimestamp(c, b, q) ) {
                                StartPhase3(c, b[1], t[2], ds);
                            }
                        }
                    };
        end3:       (* Decide in phase 3 *)
                    with (q \in Quorum, c = self[1], b = Phase3(self[2]) ) {
                        when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "accepted";
                        with (  ds = UNION {vote[p][c][b].seen : p \in q};
                                t = propose[<<c,b>>].ts ) {
                            assert \A p \in q : vote[p][c][b].ts = t;
                            MakeStable(c, b, t, ds);
                        }
                    }
                };
        d:      skip 
    }
  
}

*)
\* BEGIN TRANSLATION
\* Label acc of process acc at line 335 col 17 changed to acc_
VARIABLES ballot, vote, propose, stable, join, pc

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}







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


LowerCmds(p, c, t, S) == {
    c2 \in SeenCmds(p) : vote[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
        /\ <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}

ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]

Deps(c, p) == MaxVote(c, p).seen \ {c}

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Deps(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxVote(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)

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

HasCmd(c, b, q) == \A p2 \in q : SeenAt(c, b, p2)


vars == << ballot, vote, propose, stable, join, pc >>

ProcSet == (P) \cup ((C \times MajBallot))

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> <<0,1>>]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ join = {}
        /\ pc = [self \in ProcSet |-> CASE self \in P -> "acc_"
                                        [] self \in (C \times MajBallot) -> "start"]

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == Phase1(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c, b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ IF NoConflict(self, c, t)
                                        THEN /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                        <<b, [ts |-> t, status |-> "pending", seen |-> CmdsWithLowerT(self, c, t), leaderDeps |-> {}]>>]]
                                        ELSE /\ LET t2 == RejectTimestamp(c, self) IN
                                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                          ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> CmdsWithLowerT(self, c, t2[2]), leaderDeps |-> {}]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ ballot[self][c] \preceq b /\ <<c,b>> \in DOMAIN stable
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET s == stable[<<c,b>>] IN
                                vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [
                                        status |-> "stable",
                                        ts |-> s.ts,
                                        seen |-> s.deps,
                                        leaderDeps |-> s.deps ]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == Phase2(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ IF NoConflict(self, c, t)
                                        THEN /\ LET deps == propose[<<c,b>>].deps IN
                                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                          <<b, [ts |-> t, status |-> "pending", seen |-> {}, leaderDeps |-> deps]>>]]
                                        ELSE /\ LET t2 == RejectTimestamp(c, self) IN
                                                  LET seen == CmdsWithLowerT(self, c, t2[2]) IN
                                                    vote' =       [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                            ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> seen, leaderDeps |-> {}]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == Phase3(B) IN
                             /\ IF Phase(b) = 1 THEN ballot[self][c] = b ELSE ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [
                                          ts |-> t, status |-> "accepted",
                                          seen |-> CmdsWithLowerT(self, c, t) \cup propose[<<c,b>>].deps,
                                          leaderDeps |-> propose[<<c,b>>].deps]>>]]
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
                               "Failure of assertion at line 310, column 9 of macro called at line 354, column 25.")
                     /\ propose' = propose ++ <<<<(self[1]),Phase1((self[2]))>>, [ts |-> t]>>
                /\ pc' = [pc EXCEPT ![self] = "end1"]
                /\ UNCHANGED << ballot, vote, stable, join >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ Assert(<<(self[1]),Phase1((self[2]))>> \notin join, 
                            "Failure of assertion at line 325, column 9 of macro called at line 358, column 21.")
                  /\ join' = (join \cup {<<(self[1]),Phase1((self[2]))>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, propose, stable >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET B == self[2] IN
                          /\ \A p \in q : Phase1(B) \preceq ballot[p][c]
                          /\ Assert(\A p \in q : ballot[p][c] = Phase1(B) \/ Phase3(B) \prec ballot[p][c], 
                                    "Failure of assertion at line 361, column 25.")
                          /\ LET maxBal == MaxBal(c, Phase1(B), q) IN
                               /\ Assert(maxBal[1] < B, 
                                         "Failure of assertion at line 364, column 29.")
                               /\ IF Maj(maxBal) # -1
                                     THEN /\ LET ps == {p \in q : ParticipatedIn(maxBal, c, p)} IN
                                               \E p \in ps:
                                                 \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"stable"}
                                                    /\ vote[p][c][maxBal].status = "accepted"
                                                    /\ Assert(Phase(maxBal) = 3, 
                                                              "Failure of assertion at line 372, column 41.")
                                                    /\ LET e == vote[p][c][maxBal] IN
                                                         LET t == e.ts IN
                                                           LET ds == e.leaderDeps IN
                                                             /\ Assert(<<c,Phase3(B)>> \notin DOMAIN propose, 
                                                                       "Failure of assertion at line 315, column 9 of macro called at line 374, column 45.")
                                                             /\ propose' = propose ++ <<<<c,Phase3(B)>>, [ts |-> t, deps |-> ds]>>
                                                             /\ pc' = [pc EXCEPT ![self] = "end3"]
                                                 \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable"}
                                                    /\ vote[p][c][maxBal].status \in {"rejected"}
                                                    /\ Assert(Phase(maxBal) \in {1,2}, 
                                                              "Failure of assertion at line 382, column 41.")
                                                    /\ Assert(   \A p2 \in P : c \in DOMAIN vote[p2] =>
                                                              \A b2 \in DOMAIN vote[p2][c] : b2 \preceq maxBal => vote[p2][c][b2].status \notin {"accepted","stable"}, 
                                                              "Failure of assertion at line 383, column 41.")
                                                    /\ \E t \in Time:
                                                         /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                                   "Failure of assertion at line 310, column 9 of macro called at line 386, column 45.")
                                                         /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                                    /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                 \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"}
                                                    /\ Phase(maxBal) = 2 /\ vote[p][c][maxBal].status = "pending"
                                                    /\ Assert(\A p2 \in ps : vote[p][c][maxBal].status = "pending", 
                                                              "Failure of assertion at line 393, column 41.")
                                                    /\ LET e == vote[p][c][maxBal] IN
                                                         LET t == e.ts IN
                                                           LET ds == e.leaderDeps IN
                                                             /\ Assert(<<c,Phase2(B)>> \notin DOMAIN propose, 
                                                                       "Failure of assertion at line 320, column 9 of macro called at line 395, column 45.")
                                                             /\ propose' = propose ++ <<<<c,Phase2(B)>>, [ts |-> t, deps |-> ds]>>
                                                             /\ pc' = [pc EXCEPT ![self] = "end2"]
                                                 \/ /\ Phase(maxBal) = 1
                                                    /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"}
                                                    /\ vote[p][c][maxBal].status = "pending"
                                                    /\ Assert(\A p2 \in ps : vote[p][c][maxBal].status = "pending", 
                                                              "Failure of assertion at line 404, column 41.")
                                                    /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                              "Failure of assertion at line 310, column 9 of macro called at line 411, column 41.")
                                                    /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> (vote[p][c][maxBal].ts)]>>
                                                    /\ pc' = [pc EXCEPT ![self] = "end1"]
                                     ELSE /\ \E t \in Time:
                                               /\ Assert(<<c,Phase1(B)>> \notin DOMAIN propose, 
                                                         "Failure of assertion at line 310, column 9 of macro called at line 417, column 37.")
                                               /\ propose' = propose ++ <<<<c,Phase1(B)>>, [ts |-> t]>>
                                          /\ pc' = [pc EXCEPT ![self] = "end1"]
                 /\ UNCHANGED << ballot, vote, stable, join >>

end1(self) == /\ pc[self] = "end1"
              /\ \/ /\ \E q \in FastQuorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\  \A p \in q : b \in DOMAIN vote[p][c]
                                /\ vote[p][c][b].status = "pending"
                             /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                                  LET t == propose[<<c,b>>].ts IN
                                    stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                    /\ pc' = [pc EXCEPT ![self] = "d"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ HasCmd(c, b, q)
                             /\ \E p2 \in q : vote[p2][c][b].status = "rejected"
                             /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 315, column 9 of macro called at line 442, column 29.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase1(self[2]) IN
                             /\ HasCmd(c, b, q)
                             /\ \A p2 \in q : vote[p2][c][b].status = "pending"
                             /\ LET ds == UNION {vote[p2][c][b].seen : p2 \in q} IN
                                  LET p2 == CHOOSE p2 \in q : TRUE IN
                                    LET t == vote[p2][c][b].ts IN
                                      /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                                "Failure of assertion at line 453, column 29.")
                                      /\ Assert(<<c,Phase2((b[1]))>> \notin DOMAIN propose, 
                                                "Failure of assertion at line 320, column 9 of macro called at line 454, column 29.")
                                      /\ propose' = propose ++ <<<<c,Phase2((b[1]))>>, [ts |-> t, deps |-> ds]>>
                    /\ pc' = [pc EXCEPT ![self] = "end2"]
                    /\ UNCHANGED stable
              /\ UNCHANGED << ballot, vote, join >>

end2(self) == /\ pc[self] = "end2"
              /\ \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase2(self[2]) IN
                             /\ HasCmd(c, b, q)
                             /\ \A p2 \in q : vote[p2][c][b].status = "pending"
                             /\ LET p2 == CHOOSE p2 \in q : TRUE IN
                                  LET ds == vote[p2][c][b].leaderDeps IN
                                    LET t == vote[p2][c][b].ts IN
                                      /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                                "Failure of assertion at line 465, column 33.")
                                      /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                      /\ pc' = [pc EXCEPT ![self] = "d"]
                    /\ UNCHANGED propose
                 \/ /\ \E q \in Quorum:
                         LET c == self[1] IN
                           LET b == Phase2(self[2]) IN
                             /\ HasCmd(c, b, q)
                             /\ \E p2 \in q : vote[p2][c][b].status = "rejected"
                             /\ LET ds == UNION {vote[p2][c][b].seen : p2 \in q} IN
                                  LET t == RetryTimestamp(c, b, q) IN
                                    /\ Assert(<<c,Phase3((b[1]))>> \notin DOMAIN propose, 
                                              "Failure of assertion at line 315, column 9 of macro called at line 478, column 33.")
                                    /\ propose' = propose ++ <<<<c,Phase3((b[1]))>>, [ts |-> (t[2]), deps |-> ds]>>
                    /\ pc' = [pc EXCEPT ![self] = "end3"]
                    /\ UNCHANGED stable
              /\ UNCHANGED << ballot, vote, join >>

end3(self) == /\ pc[self] = "end3"
              /\ \E q \in Quorum:
                   LET c == self[1] IN
                     LET b == Phase3(self[2]) IN
                       /\ \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "accepted"
                       /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                            LET t == propose[<<c,b>>].ts IN
                              /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                        "Failure of assertion at line 487, column 29.")
                              /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
              /\ pc' = [pc EXCEPT ![self] = "d"]
              /\ UNCHANGED << ballot, vote, propose, join >>

d(self) == /\ pc[self] = "d"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << ballot, vote, propose, stable, join >>

leader(self) == start(self) \/ phase1(self) \/ startBal(self)
                   \/ recover(self) \/ end1(self) \/ end2(self)
                   \/ end3(self) \/ d(self)

Next == (\E self \in P: acc(self))
           \/ (\E self \in (C \times MajBallot): leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat Apr 30 17:47:45 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
