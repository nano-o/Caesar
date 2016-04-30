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

(***************************************************************************)
(* A timestamp for c strictly greater than the max of the timstamps xs.    *)
(***************************************************************************)
GT(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
    IN IF CmdId(max[1]) < CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 

(***************************************************************************)
(* A timestamp fo c greater than or equal to the max of the timstamps xs.  *)
(***************************************************************************)
GTE(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \sqsubset x
    IN IF CmdId(max[1]) <= CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
    
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
        join = {},
        \* For each pair <<c,b>>, a phase1Deps for the propose phase of the last case of the recovery...
        phase1Deps = <<>>

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
        Maxvote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, Pred(b), p) : p \in q}
            IN Max(bals)
        
        \* The timestamp found at p in the vote for c in the highest ballot.
        TimeStampOf(c, p) == Maxvote(c,p).ts
        
        TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}
        
        \* All the commands at p which have a lower timestamp than <<c,t>>
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}
        
        \* All the commands at p which have a lower timestamp than <<c,t>> and a status in S
        LowerCmds(p, c, t, S) == {
            c2 \in SeenCmds(p) : vote[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
                /\ <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}
        
        ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]
        
        Deps(c, p) == Maxvote(c, p).seen \ {c}
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Deps(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ Maxvote(c2,p).status \notin {"stable","accepted"}
        
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
        
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
        
    macro Phase1Reply(p) {
        with (c \in C; B \in MajBallot, b = <<B,1>>) {
            when ballot[p][c] \preceq b;
            when <<c, b>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = propose[<<c, b>>].ts) {
                when LastBal(c, b, p) \prec b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                with (flag = IF <<c,b[1]>> \in DOMAIN phase1Deps THEN TRUE ELSE FALSE) {                
                    either {
                        when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict. 
                        with (seen = IF <<c,b[1]>> \in DOMAIN phase1Deps
                                THEN phase1Deps[<<c,b[1]>>] \cup LowerCmds(p, c, t, {"accepted", "stable", "pending"}) \* TODO
                                ELSE CmdsWithLowerT(p, c, t)) {
                            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                                <<b, [ts |-> t, status |-> "pending", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        } 
                    } or {
                        when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                        \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                        with (  t2 = GT(c, TimeStamps(p));
                                seen = IF <<c,b[1]>> \in DOMAIN phase1Deps
                                    THEN phase1Deps[<<c,b[1]>>] \cup LowerCmds(p, c, t2[2], {"accepted", "stable", "pending"}) \* TODO
                                    ELSE CmdsWithLowerT(p, c, t2[2]) ) {
                            \* Record the fact that the command was rejected with t2:
                            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                                ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        }
                    }
                }
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; B \in MajBallot, b = <<B,2>>) { 
            when ballot[p][c] \prec b;
            when <<c, b>> \in DOMAIN propose;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = propose[<<c,b>>].ts) {
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                either {
                    when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                    with (deps = propose[<<c,b>>].deps) {
                        vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                            <<b, [ts |-> t, status |-> "pending", seen |-> {}, leaderDeps |-> deps]>>]];
                    }
                } or {
                    when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  t2 = GT(c, TimeStamps(p)),
                            seen = CmdsWithLowerT(p, c, t2[2]) ) {
                      \* Record the fact that the command was rejected with t2:
                      vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected-slow", seen |-> seen, leaderDeps |-> {}]>>]];
                    }
                }
            }
        }
    }
    
    macro Phase3Reply(p) {
        with (c \in C; B \in MajBallot, b = <<B,3>>) {
            when ballot[p][c] \preceq b;
            when <<c, b>> \in DOMAIN propose;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = propose[<<c,b>>].ts) {
                with (seen = CmdsWithLowerT(p, c, t) \cup propose[<<c,b>>].deps) {
                    vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "accepted", seen |-> seen, leaderDeps |-> propose[<<c,b>>].deps]>>]]; 
                }
            }
        }
    }
    
    macro LearnStable(p) {
        with (c \in C; b \in Ballot) { 
            when ballot[p][c] \preceq b;
            when <<c,b>> \in DOMAIN stable;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (s = stable[<<c,b>>]) {
                vote := [vote EXCEPT ![p] = 
                    [@ EXCEPT ![c] = @ ++ <<b, [status |-> "stable", 
                     ts |-> s.ts, seen |-> s.deps, leaderDeps |-> s.deps ]>>]];
            }
        }
    }    
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when ballot[p][c] \prec b;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
  
    process (leader \in (C \times MajBallot)) {
        start:  either {
        phase1:     with (t \in Time, b = <<0,1>>) {
                        when self[2] = 0;
                        when <<self[1],b>> \notin DOMAIN propose;
                        propose := propose ++ <<<<self[1],b>>, [ts |-> t]>> 
                    }
                } or {
        startBal:      
                    when self[2] > 0; \* Only start ballots greater than 0; 0 is started by default.
                    join := join \cup {<<self[1],<<self[2],1>>>>};
        recover:    
                    with (q \in Quorum, c = self[1], b = self[2]) {
                        when \A p \in q : <<b,1>> \preceq ballot[p][c]; \* every p in the quorum is in b or higher.
                        \* the maximum ballot strictly less than b in which a vote was cast:
                        with (maxBal = MaxBal(c, <<b,1>>, q)) {
                            if (maxBal[1] # -1) {
                                \* get the set ps of acceptors in the quorum q who participated in the maximum ballot.
                                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                                    either {
                                        \* All have status "accepted"
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"stable"}; \* there is no stable status.
                                        when vote[p][c][maxBal].status = "accepted"; \* Can only be a 3-subballot
                                        assert maxBal[2] = 3;
                                        with (e = vote[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            when <<c,<<b,3>>>> \notin DOMAIN propose;
                                            propose := propose ++ <<<<c,<<b,3>>>>, [ts |-> t, deps |-> ds]>>;
                                            \* when FALSE;
                                            goto end3;
                                        }
                                    } or {
                                        \* There is one "rejected" and there is no accept or stable:
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable"}; 
                                        when vote[p][c][maxBal].status \in {"rejected"};
                                        assert maxBal[2] \in {1,2};
                                        with (t \in Time) { \* use an arbitrary timestamp.
                                            when <<c,<<b,1>>>> \notin DOMAIN propose;
                                            propose := propose ++ <<<<c,<<b,1>>>>, [ts |-> t]>>;
                                            \* when FALSE;
                                        }
                                    } or {
                                        \* there is one "pending-slow" and there is no accept or stable or reject:
                                        when \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"};
                                        when maxBal[2] = 2 /\ vote[p][c][maxBal].status = "pending";
                                        with (e = vote[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            when <<c, <<b,2>>>> \notin DOMAIN propose;
                                            propose := propose ++ <<<<c,<<b,2>>>>, [ts |-> t, deps |-> ds]>>;
                                            \* when FALSE;
                                            goto end2;
                                        } 
                                    } or {
                                        \* there is one "pending-fast" and there is no accept or stable or reject:
                                        when \A p2 \in ps : 
                                            /\  vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"}
                                            /\  vote[p2][c][maxBal].status = "pending" => maxBal[2] = 1;
                                        when vote[p][c][maxBal].status = "pending";
                                        with (deps = UNION {vote[p2][c][maxBal].seen : p2 \in ps}; 
                                                wl = {c2 \in deps : (\A q2 \in FastQuorum :
                                                    (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in vote[p2][c][maxBal].seen))}) {
                                            phase1Deps := phase1Deps ++ <<<<c,b>>, wl>>;
                                        };
                                        when <<c,<<b,1>>>> \notin DOMAIN propose;
                                        propose := propose ++ <<<<c,<<b,1>>>>, [ts |-> vote[p][c][maxBal].ts]>>;
                                        \* when FALSE;
                                    }
                                }
                            } else {
                                \* No acceptor in ps saw the command.
                                \* In practice this should not happen if the new leader is in its received quorum.
                                \* Could happen if recovery is triggered by a client.
                                with (t \in Time) {
                                    when <<c,<<b,1>>>> \notin DOMAIN propose;
                                    propose := propose ++ <<<<c,<<b,1>>>>, [ts |-> t]>>;
                                    \* when FALSE;
                                }
                            }
                        }
                    }
                };
        end1:   either { 
        fastD:      (* Fast decision *)
                    with (q \in FastQuorum, c = self[1], b = <<self[2],1>>) {
                        when \A p \in q : b \in DOMAIN vote[p][c] 
                            /\ vote[p][c][b].status = "pending";
                        with (  ds = UNION {vote[p][c][b].seen : p \in q};
                                t = propose[<<c,b>>].ts ) {
                            stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                        }
                    };
                    goto d;
                } or {
                    (* there is a reject, trigger phase 3. *)
        rejectIn1:  with (q \in Quorum, c = self[1], b = <<self[2],1>>) {
                        when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
                        \* The leader receives a phase-1 "reject" message.
                        when \E p2 \in q : vote[p2][c][b].status = "rejected";
                        with (  (*ps = {p \in q : vote[p][c][b].status \in {"rejected", "pending"}}, \* use only information from phase 1.*)
                                ds = UNION {vote[p][c][b].seen : p \in q}, 
                                t = GTE(c, {<<c, vote[p][c][b].ts>> : p \in q})) {
                            \* Trigger phase 3:
                            propose := propose ++ <<<<c,<<b[1],3>>>>, [ts |-> t[2], deps |-> ds]>>;
                            goto end3; (* GOTO EndPhase3 *)
                        }
                    }
                } or { (* time out *)
        timeout:    with (q \in Quorum, c = self[1], b = <<self[2],1>>) {
                        when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
                        \* The leader triggers the slow path because it timed-out waiting for a fast quorum,
                        \* and it did not receive any "rejected" response to its proposal.
                        when \A p2 \in q : vote[p2][c][b].status = "pending";
                        with (  (*ps = {p \in q : vote[p][c][b].status \in {"rejected", "pending"}}, \* use only information from phase 1.*)
                                ds = UNION {vote[p2][c][b].seen : p2 \in q},
                                p2 = CHOOSE p2 \in q : TRUE,
                                t = vote[p2][c][b].ts) {
                            assert \A p \in q : vote[p][c][b].ts = t;
                            propose := propose ++ <<<<c,<<b[1],2>>>>, [ts |-> t, deps |-> ds]>>;
                        }
                    };
        end2:       either {
        slowD:          (* Decision in phase 2 *)
                        with (q \in Quorum, c = self[1], b = <<self[2],2>>) {
                            when \A p2 \in q : SeenAt(c, b, p2);
                            when \A p2 \in q : vote[p2][c][b].status = "pending";
                            with (  (* ds = UNION {vote[p2][c][b].seen : p2 \in q}, *)
                                    p2 = CHOOSE p2 \in q : TRUE,
                                    ds = vote[p2][c][b].leaderDeps,
                                    t = vote[p2][c][b].ts) {
                                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                                goto d; (* GOTO end *)
                            }
                        }
                    } or {
        rejectIn2:      (* Reject in phase 2 *)
                        (* TODO: can this ever happen? *)
                        with (q \in Quorum, c = self[1], b = <<self[2],2>>) {
                            when \A p2 \in q : SeenAt(c, b, p2);
                            \* The leader receives a "reject" message.
                            when \E p2 \in q : vote[p2][c][b].status = "rejected";
                            with (  (*ps = {p \in q : vote[p][c][b].status \in {"rejected", "pending"}}, \* use only information from phase 2.*)
                                    ds = UNION {vote[p2][c][b].seen : p2 \in q}, 
                                    t = GTE(c, {<<c, vote[p2][c][b].ts>> : p2 \in q})) {
                                propose := propose ++ <<<<c,<<b[1],3>>>>, [ts |-> t[2], deps |-> ds]>>;
                                assert FALSE;
                            }
                        }
                    };
        end3:       (* Decide in phase 3 *)
                    with (q \in Quorum, c = self[1], b = <<self[2],3>> ) {
                        when \A p \in q : b \in DOMAIN vote[p][c]
                            /\ vote[p][c][b].status = "accepted";
                        with (  ds = UNION {vote[p][c][b].seen : p \in q};
                                t = propose[<<c,b>>].ts ) {
                            stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                        }
                    }
                };
        d:      skip 
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
}

*)
\* BEGIN TRANSLATION
\* Label acc of process acc at line 444 col 17 changed to acc_
VARIABLES ballot, vote, propose, stable, join, phase1Deps, pc

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}







SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN vote[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE <<-1,3>>


Maxvote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, Pred(b), p) : p \in q}
    IN Max(bals)


TimeStampOf(c, p) == Maxvote(c,p).ts

TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}


CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}


LowerCmds(p, c, t, S) == {
    c2 \in SeenCmds(p) : vote[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
        /\ <<c2, TimeStampOf(c2,p)>> \sqsubset <<c,t>>}

ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]

Deps(c, p) == Maxvote(c, p).seen \ {c}

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \sqsubset <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Deps(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ Maxvote(c2,p).status \notin {"stable","accepted"}

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


vars == << ballot, vote, propose, stable, join, phase1Deps, pc >>

ProcSet == ((C \times MajBallot)) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> <<0,1>>]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ join = {}
        /\ phase1Deps = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times MajBallot) -> "start"
                                        [] self \in P -> "acc_"]

start(self) == /\ pc[self] = "start"
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "phase1"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "startBal"]
               /\ UNCHANGED << ballot, vote, propose, stable, join, phase1Deps >>

phase1(self) == /\ pc[self] = "phase1"
                /\ \E t \in Time:
                     LET b == <<0,1>> IN
                       /\ self[2] = 0
                       /\ <<self[1],b>> \notin DOMAIN propose
                       /\ propose' = propose ++ <<<<self[1],b>>, [ts |-> t]>>
                /\ pc' = [pc EXCEPT ![self] = "end1"]
                /\ UNCHANGED << ballot, vote, stable, join, phase1Deps >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ self[2] > 0
                  /\ join' = (join \cup {<<self[1],<<self[2],1>>>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, propose, stable, phase1Deps >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET b == self[2] IN
                          /\ \A p \in q : <<b,1>> \preceq ballot[p][c]
                          /\ LET maxBal == MaxBal(c, <<b,1>>, q) IN
                               IF maxBal[1] # -1
                                  THEN /\ LET ps == {p \in q : ParticipatedIn(maxBal, c, p)} IN
                                            \E p \in ps:
                                              \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"stable"}
                                                 /\ vote[p][c][maxBal].status = "accepted"
                                                 /\ Assert(maxBal[2] = 3, 
                                                           "Failure of assertion at line 306, column 41.")
                                                 /\ LET e == vote[p][c][maxBal] IN
                                                      LET t == e.ts IN
                                                        LET ds == e.leaderDeps IN
                                                          /\ <<c,<<b,3>>>> \notin DOMAIN propose
                                                          /\ propose' = propose ++ <<<<c,<<b,3>>>>, [ts |-> t, deps |-> ds]>>
                                                          /\ pc' = [pc EXCEPT ![self] = "end3"]
                                                 /\ UNCHANGED phase1Deps
                                              \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable"}
                                                 /\ vote[p][c][maxBal].status \in {"rejected"}
                                                 /\ Assert(maxBal[2] \in {1,2}, 
                                                           "Failure of assertion at line 317, column 41.")
                                                 /\ \E t \in Time:
                                                      /\ <<c,<<b,1>>>> \notin DOMAIN propose
                                                      /\ propose' = propose ++ <<<<c,<<b,1>>>>, [ts |-> t]>>
                                                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                 /\ UNCHANGED phase1Deps
                                              \/ /\ \A p2 \in ps : vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"}
                                                 /\ maxBal[2] = 2 /\ vote[p][c][maxBal].status = "pending"
                                                 /\ LET e == vote[p][c][maxBal] IN
                                                      LET t == e.ts IN
                                                        LET ds == e.leaderDeps IN
                                                          /\ <<c, <<b,2>>>> \notin DOMAIN propose
                                                          /\ propose' = propose ++ <<<<c,<<b,2>>>>, [ts |-> t, deps |-> ds]>>
                                                          /\ pc' = [pc EXCEPT ![self] = "end2"]
                                                 /\ UNCHANGED phase1Deps
                                              \/ /\  \A p2 \in ps :
                                                    /\  vote[p2][c][maxBal].status \notin {"accepted","stable","rejected"}
                                                    /\  vote[p2][c][maxBal].status = "pending" => maxBal[2] = 1
                                                 /\ vote[p][c][maxBal].status = "pending"
                                                 /\ LET deps == UNION {vote[p2][c][maxBal].seen : p2 \in ps} IN
                                                      LET wl ==  {c2 \in deps : (\A q2 \in FastQuorum :
                                                                (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in vote[p2][c][maxBal].seen))} IN
                                                        phase1Deps' = phase1Deps ++ <<<<c,b>>, wl>>
                                                 /\ <<c,<<b,1>>>> \notin DOMAIN propose
                                                 /\ propose' = propose ++ <<<<c,<<b,1>>>>, [ts |-> vote[p][c][maxBal].ts]>>
                                                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                                  ELSE /\ \E t \in Time:
                                            /\ <<c,<<b,1>>>> \notin DOMAIN propose
                                            /\ propose' = propose ++ <<<<c,<<b,1>>>>, [ts |-> t]>>
                                       /\ pc' = [pc EXCEPT ![self] = "end1"]
                                       /\ UNCHANGED phase1Deps
                 /\ UNCHANGED << ballot, vote, stable, join >>

end1(self) == /\ pc[self] = "end1"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "fastD"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "rejectIn1"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "timeout"]
              /\ UNCHANGED << ballot, vote, propose, stable, join, phase1Deps >>

fastD(self) == /\ pc[self] = "fastD"
               /\ \E q \in FastQuorum:
                    LET c == self[1] IN
                      LET b == <<self[2],1>> IN
                        /\  \A p \in q : b \in DOMAIN vote[p][c]
                           /\ vote[p][c][b].status = "pending"
                        /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                             LET t == propose[<<c,b>>].ts IN
                               stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
               /\ pc' = [pc EXCEPT ![self] = "d"]
               /\ UNCHANGED << ballot, vote, propose, join, phase1Deps >>

rejectIn1(self) == /\ pc[self] = "rejectIn1"
                   /\ \E q \in Quorum:
                        LET c == self[1] IN
                          LET b == <<self[2],1>> IN
                            /\ \A p2 \in q : SeenAt(c, b, p2)
                            /\ \E p2 \in q : vote[p2][c][b].status = "rejected"
                            /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                                 LET t == GTE(c, {<<c, vote[p][c][b].ts>> : p \in q}) IN
                                   /\ propose' = propose ++ <<<<c,<<b[1],3>>>>, [ts |-> t[2], deps |-> ds]>>
                                   /\ pc' = [pc EXCEPT ![self] = "end3"]
                   /\ UNCHANGED << ballot, vote, stable, join, phase1Deps >>

timeout(self) == /\ pc[self] = "timeout"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET b == <<self[2],1>> IN
                          /\ \A p2 \in q : SeenAt(c, b, p2)
                          /\ \A p2 \in q : vote[p2][c][b].status = "pending"
                          /\ LET ds == UNION {vote[p2][c][b].seen : p2 \in q} IN
                               LET p2 == CHOOSE p2 \in q : TRUE IN
                                 LET t == vote[p2][c][b].ts IN
                                   /\ Assert(\A p \in q : vote[p][c][b].ts = t, 
                                             "Failure of assertion at line 397, column 29.")
                                   /\ propose' = propose ++ <<<<c,<<b[1],2>>>>, [ts |-> t, deps |-> ds]>>
                 /\ pc' = [pc EXCEPT ![self] = "end2"]
                 /\ UNCHANGED << ballot, vote, stable, join, phase1Deps >>

end2(self) == /\ pc[self] = "end2"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "slowD"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "rejectIn2"]
              /\ UNCHANGED << ballot, vote, propose, stable, join, phase1Deps >>

slowD(self) == /\ pc[self] = "slowD"
               /\ \E q \in Quorum:
                    LET c == self[1] IN
                      LET b == <<self[2],2>> IN
                        /\ \A p2 \in q : SeenAt(c, b, p2)
                        /\ \A p2 \in q : vote[p2][c][b].status = "pending"
                        /\ LET p2 == CHOOSE p2 \in q : TRUE IN
                             LET ds == vote[p2][c][b].leaderDeps IN
                               LET t == vote[p2][c][b].ts IN
                                 /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                 /\ pc' = [pc EXCEPT ![self] = "d"]
               /\ UNCHANGED << ballot, vote, propose, join, phase1Deps >>

rejectIn2(self) == /\ pc[self] = "rejectIn2"
                   /\ \E q \in Quorum:
                        LET c == self[1] IN
                          LET b == <<self[2],2>> IN
                            /\ \A p2 \in q : SeenAt(c, b, p2)
                            /\ \E p2 \in q : vote[p2][c][b].status = "rejected"
                            /\ LET ds == UNION {vote[p2][c][b].seen : p2 \in q} IN
                                 LET t == GTE(c, {<<c, vote[p2][c][b].ts>> : p2 \in q}) IN
                                   /\ propose' = propose ++ <<<<c,<<b[1],3>>>>, [ts |-> t[2], deps |-> ds]>>
                                   /\ Assert(FALSE, 
                                             "Failure of assertion at line 425, column 33.")
                   /\ pc' = [pc EXCEPT ![self] = "end3"]
                   /\ UNCHANGED << ballot, vote, stable, join, phase1Deps >>

end3(self) == /\ pc[self] = "end3"
              /\ \E q \in Quorum:
                   LET c == self[1] IN
                     LET b == <<self[2],3>> IN
                       /\  \A p \in q : b \in DOMAIN vote[p][c]
                          /\ vote[p][c][b].status = "accepted"
                       /\ LET ds == UNION {vote[p][c][b].seen : p \in q} IN
                            LET t == propose[<<c,b>>].ts IN
                              stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
              /\ pc' = [pc EXCEPT ![self] = "d"]
              /\ UNCHANGED << ballot, vote, propose, join, phase1Deps >>

d(self) == /\ pc[self] = "d"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << ballot, vote, propose, stable, join, phase1Deps >>

leader(self) == start(self) \/ phase1(self) \/ startBal(self)
                   \/ recover(self) \/ end1(self) \/ fastD(self)
                   \/ rejectIn1(self) \/ timeout(self) \/ end2(self)
                   \/ slowD(self) \/ rejectIn2(self) \/ end3(self)
                   \/ d(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == <<B,1>> IN
                             /\ ballot[self][c] \preceq b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c, b>>].ts IN
                                  /\ LastBal(c, b, self) \prec b
                                  /\ \neg Blocked(self, c, t)
                                  /\ LET flag == IF <<c,b[1]>> \in DOMAIN phase1Deps THEN TRUE ELSE FALSE IN
                                       \/ /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                                          /\ LET seen ==      IF <<c,b[1]>> \in DOMAIN phase1Deps
                                                         THEN phase1Deps[<<c,b[1]>>] \cup LowerCmds(self, c, t, {"accepted", "stable", "pending"})
                                                         ELSE CmdsWithLowerT(self, c, t) IN
                                               vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                       <<b, [ts |-> t, status |-> "pending", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]]
                                       \/ /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                                          /\ LET t2 == GT(c, TimeStamps(self)) IN
                                               LET seen ==    IF <<c,b[1]>> \in DOMAIN phase1Deps
                                                           THEN phase1Deps[<<c,b[1]>>] \cup LowerCmds(self, c, t2[2], {"accepted", "stable", "pending"})
                                                           ELSE CmdsWithLowerT(self, c, t2[2]) IN
                                                 vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                         ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ ballot[self][c] \preceq b
                           /\ <<c,b>> \in DOMAIN stable
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET s == stable[<<c,b>>] IN
                                vote' =     [vote EXCEPT ![self] =
                                        [@ EXCEPT ![c] = @ ++ <<b, [status |-> "stable",
                                         ts |-> s.ts, seen |-> s.deps, leaderDeps |-> s.deps ]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == <<B,2>> IN
                             /\ ballot[self][c] \prec b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  /\ \neg Blocked(self, c, t)
                                  /\ \/ /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                                        /\ LET deps == propose[<<c,b>>].deps IN
                                             vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                     <<b, [ts |-> t, status |-> "pending", seen |-> {}, leaderDeps |-> deps]>>]]
                                     \/ /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                                        /\ LET t2 == GT(c, TimeStamps(self)) IN
                                             LET seen == CmdsWithLowerT(self, c, t2[2]) IN
                                               vote' =       [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                       ++ <<b, [ts |-> t2[2], status |-> "rejected-slow", seen |-> seen, leaderDeps |-> {}]>>]]
                 \/ /\ \E c \in C:
                         \E B \in MajBallot:
                           LET b == <<B,3>> IN
                             /\ ballot[self][c] \preceq b
                             /\ <<c, b>> \in DOMAIN propose
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                             /\ LET t == propose[<<c,b>>].ts IN
                                  LET seen == CmdsWithLowerT(self, c, t) \cup propose[<<c,b>>].deps IN
                                    vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                            <<b, [ts |-> t, status |-> "accepted", seen |-> seen, leaderDeps |-> propose[<<c,b>>].deps]>>]]
                 \/ /\ \E prop \in join:
                         LET c == prop[1] IN
                           LET b == prop[2] IN
                             /\ ballot[self][c] \prec b
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                    /\ vote' = vote
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << propose, stable, join, phase1Deps >>

acc(self) == acc_(self)

Next == (\E self \in (C \times MajBallot): leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat Apr 30 14:40:20 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
