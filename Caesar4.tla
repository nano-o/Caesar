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

ASSUME \A c \in C : CmdId(c) \in Nat /\ \A c2 \in C : c # c2 => CmdId(c) # CmdId(c2)

Time == 1..MaxTime

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == 0..(NumBallots-1)

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
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2] \* if same timestamp:
    THEN CmdId(ts1[1]) < CmdId(ts2[1]) \* break ties with command id.
    ELSE ts1[2] < ts2[2] \* else compare timestamps.

(***************************************************************************)
(* The maximum element in a set.                                           *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x >= y

(***************************************************************************)
(* A timestamp for c strictly greater than the max of the timstamps xs.    *)
(***************************************************************************)
GT(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    IN IF CmdId(max[1]) < CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 

(***************************************************************************)
(* A timestamp fo c greater than or equal to the max of the timstamps xs.  *)
(***************************************************************************)
GTE(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    IN IF CmdId(max[1]) <= CmdId(c) THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
    
(***********

--algorithm Caesar {

    variables
        \* maps an acceptor p and a command c to a ballot b, indicating that the acceptor p is in ballot b for command c:
        ballot = [p \in P |-> [c \in C |-> 0]],
        \* maps an acceptor p and a command c to a map from ballot to estimate:
        estimate = [p \in P |-> [c \in C |-> <<>>]],
        \* maps a pair <<c,b>> to a timestamp t, indicating that the proposal for command c in ballot b is timestamp t:
        phase1 = <<>>,
        phase2 = <<>>,
        \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c has been committed in ballot b
        \* with timestamp t and dependencies ds: 
        stable = <<>>,
        \* maps a pair <<c,b>> to a timestamp t and a set of dependencies ds, 
        \* indicating that c is to be retried in ballot b with timestamp t and dependencies ds.
        phase3 = <<>>,
        \* a set of pairs <<c,b>>, indicating that the ballot-b leader of c asks all acceptors to join ballot b:
        join = {},
        \* For each pair <<c,b>>, a phase1_deps for the propose phase of the last case of the recovery...
        phase1_deps = <<>>

    define {
        
        Status == {"pending-slow", "pending-fast", "stable", "accepted", "rejected"}
        
        CmdInfo == [ts : Nat, deps : SUBSET C]
        CmdInfoWithStat == [ts : Nat, seen : SUBSET C, leaderDeps : SUBSET C, status: Status]
        
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == {c \in C : DOMAIN estimate[p][c] # {}}
        
        \* TRUE if c was seen in ballot b at p.
        SeenAt(c, b, p) == b \in DOMAIN estimate[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == LET bals == {b \in DOMAIN estimate[p][c] : b <= max} IN
            IF bals # {}
            THEN Max(bals)
            ELSE -1
        
        \* The estimate for c on p in the highest c-ballot in which p participated. 
        MaxEstimate(c, p) == estimate[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, b-1, p) : p \in q}
            IN Max(bals)
        
        \* The timestamp found at p in the estimate for c in the highest ballot.
        TimeStampOf(c, p) == MaxEstimate(c,p).ts
        
        TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}
        
        \* All the commands at p which have a lower timestamp than <<c,t>>
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}
        
        LowerCmds(p, c, t, S) == {
            c2 \in C : DOMAIN estimate[p][c2] # {} /\ estimate[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
                /\ <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}
        
        ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]
        
        \* The predecessor set (or dependency set) of c at p.
        Deps2(c, p) == {c2 \in SeenCmds(p) : <<c2,TimeStampOf(c2,p)>> \prec <<c,TimeStampOf(c,p)>>}
        Seen(c, p) == MaxEstimate(c, p).seen \ {c}
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Seen(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}
        
        Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)
                
        GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
            /\ <<c1,b1>> \in DOMAIN stable 
            /\ <<c2,b2>> \in DOMAIN stable
            /\ c1 # c2 
            /\ <<c1, stable[<<c1,b1>>].ts>> \prec <<c2, stable[<<c2,b2>>].ts>> 
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
        with (c \in C; b \in Ballot) {
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase1; \* Only reply for a proposal in the current ballot.
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = phase1[<<c, b>>]) {
                when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                with (flag = IF <<c,b>> \in DOMAIN phase1_deps THEN TRUE ELSE FALSE) {                
                    either {
                        when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict. 
                        with (seen = IF <<c,b>> \in DOMAIN phase1_deps
                                THEN phase1_deps[<<c,b>>] \cup LowerCmds(p, c, t, {"accepted", "stable", "pending-slow"})
                                ELSE CmdsWithLowerT(p, c, t)) {
                            estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                                <<b, [ts |-> t, status |-> "pending-fast", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        } 
                    } or {
                        when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                        \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                        with (  t2 = GT(c, TimeStamps(p));
                                seen = IF <<c,b>> \in DOMAIN phase1_deps
                                    THEN phase1_deps[<<c,b>>] \cup LowerCmds(p, c, t2[2], {"accepted", "stable", "pending-slow"})
                                    ELSE CmdsWithLowerT(p, c, t2[2]) ) {
                            \* Record the fact that the command was rejected with t2:
                            estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                                ++ <<b, [ts |-> t2[2], status |-> "rejected-fast", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]];
                        }
                    }
                }
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase2;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = phase2[<<c,b>>].ts) {
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                \* Only reply if p has not seen c in b or has it pending-fast in b:
                when b \in DOMAIN estimate[p][c]
                    => estimate[p][c][b].status \in {"pending-fast"};
                (* with (seen = CmdsWithLowerT(p, c, t)) { *)     
                    either {
                        when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                        with (seen = phase2[<<c,b>>].deps) {
                            estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                                <<b, [ts |-> t, status |-> "pending-slow", seen |-> seen, leaderDeps |-> {}]>>]];
                        }
                    } or {
                        when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                        \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                        with (  t2 = GT(c, TimeStamps(p)),
                                seen = CmdsWithLowerT(p, c, t2[2]) ) {
                          \* Record the fact that the command was rejected with t2:
                          estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                            ++ <<b, [ts |-> t2[2], status |-> "rejected-slow", seen |-> seen, leaderDeps |-> {}]>>]];
                        }
                    }
                (* } *)
            }
        }
    }
    
    macro Phase3Reply(p) {
        with (c \in C; b \in Ballot) {
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase3;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            \* Only reply if p has not seen c in b or has it pending-fast in b:
            when b \in DOMAIN estimate[p][c]
                => estimate[p][c][b].status \in {"pending-fast","pending-slow","rejected-fast", "rejected-slow"};
            with (t = phase3[<<c,b>>].ts) {
                with (seen = CmdsWithLowerT(p, c, t) \cup phase3[<<c,b>>].deps) {
                    estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "accepted", seen |-> seen, leaderDeps |-> phase3[<<c,b>>].deps]>>]]; 
                }
            }
        }
    }
    
    macro LearnStable(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c,b>> \in DOMAIN stable;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (s = stable[<<c,b>>]) {
                estimate := [estimate EXCEPT ![p] = 
                    [@ EXCEPT ![c] = @ ++ <<b, [status |-> "stable", 
                     ts |-> s.ts, seen |-> s.deps, leaderDeps |-> s.deps ]>>]];
            }
        }
    }    
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    } 
    
    macro EndPhase3(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c]
                /\ estimate[p][c][b].status = "accepted";
            with (  ds = UNION {estimate[p][c][b].seen : p \in q};
                    t = phase3[<<c,b>>].ts ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
            }
        }
    }
        
    (*  

    macro EndPhase1(c, b) {
        with (q \in Quorum) {
            when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
            either {
                \* The leader receive a "reject" message.
                when \E p2 \in q : estimate[p2][c][b].status = "rejected";
                with (ds = UNION {estimate[p2][c][b].seen : p2 \in q}, 
                        t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) {
                    phase3 := phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                }
            } or {
                \* The leader triggers the slow path because it timed-out waiting for a fast quorum,
                \* and it did not receive any "rejected" response to its proposal.
                when \A p2 \in q : estimate[p2][c][b].status = "pending-fast";
                with (  ds = UNION {estimate[p2][c][b].seen : p2 \in q},
                        p2 = CHOOSE p2 \in q : TRUE,
                        t = estimate[p2][c][b].ts) {
                    phase2 := phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                }
            }
        }
    }
    

    macro EndPhase2(c, b) {
        with (q \in Quorum) {
            when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
            either {
                \* The leader receive a "reject" message.
                when \E p2 \in q : estimate[p2][c][b].status = "rejected";
                with (ds = UNION {estimate[p2][c][b].seen : p2 \in q}, 
                        t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) {
                    phase3 := phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                }
            } or {
                \* Decision:
                when \A p2 \in q : estimate[p2][c][b].status = "pending-slow";
                with (  ds = UNION {estimate[p2][c][b].seen : p2 \in q},
                        p2 = CHOOSE p2 \in q : TRUE,
                        t = estimate[p2][c][b].ts) {
                    stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                }
            }
        }
    }
    
    
    macro StartBallot(c, b) {
        assert b > 0; \* Only start ballots greater than 0; 0 is started by default.
        join := join \cup {<<c,b>>};
    }
    
    *)

    
    (*
    macro Recover(c, b) {
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
            \* the maximum ballot strictly less than b in which a vote was cast:
            with (maxBal = MaxBal(c, b, q)) {
                if (maxBal # -1) {
                    \* get the set ps of acceptors in the quorum q who participated in the maximum ballot.
                    with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                        either {
                            \* All have status "accepted"
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"stable"}; \* there is no stable status.
                            when estimate[p][c][maxBal].status = "accepted";
                            with (e = estimate[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                phase3 := phase3 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>; 
                            } 
                        } or {
                            \* There is one "rejected" and there is no accept or stable:
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}; 
                            when estimate[p][c][maxBal].status = "rejected";
                            with (t \in Time) { \* use an arbitrary timestamp.
                                Phase1(c, b, t);
                            }
                        } or {
                            \* there is one "pending" and there is no accept or stable or reject:
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected"};
                            when estimate[p][c][maxBal].status = "pending-slow";
                            with (e = estimate[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                phase2 := phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>; 
                            } 
                        } or {
                            \* there is one "pending" and there is no accept or stable or reject:
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected","pending-slow"};
                            when estimate[p][c][maxBal].status = "pending-fast";
                            with (deps = UNION {estimate[p2][c][maxBal].seen : p2 \in ps}; 
                                    wl = {c2 \in deps : (\A q2 \in FastQuorum :
                                        (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in estimate[p2][c][maxBal].seen)})) {
                                phase1_deps := phase1_deps ++ <<<<c,b>>, wl>>;
                            }; 
                            Phase1(c, b, estimate[p][c][maxBal].ts);
                        }
                    }
                } else {
                    \* No acceptor in ps saw the command.
                    \* In practice this should not happen if the new leader is in its received quorum.
                    \* Could happen if recovery is triggered by a client.
                    with (t \in Time) {
                       Phase1(c, b, t);
                    }
                }
            }
        }
    } *)
    
    process (initialLeader \in (C \times Ballot)) {
        start:  either {
        phase1:     with (t \in Time) {
                        when self[2] = 0;
                        when <<self[1],0>> \notin DOMAIN phase1;
                        phase1 := phase1 ++ <<<<self[1],0>>, t>>
                    }
                } or {
        startBal:      
                    when self[2] > 0; \* Only start ballots greater than 0; 0 is started by default.
                    join := join \cup {<<self[1],self[2]>>};
        recover:    
                    with (q \in Quorum, c = self[1], b = self[2]) {
                        when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
                        \* the maximum ballot strictly less than b in which a vote was cast:
                        with (maxBal = MaxBal(c, b, q)) {
                            if (maxBal # -1) {
                                \* get the set ps of acceptors in the quorum q who participated in the maximum ballot.
                                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                                    either {
                                        \* All have status "accepted"
                                        when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"stable"}; \* there is no stable status.
                                        when estimate[p][c][maxBal].status = "accepted";
                                        with (e = estimate[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            phase3 := phase3 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>; 
                                            \* when FALSE;
                                            goto end3;
                                        } 
                                    } or {
                                        \* There is one "rejected" and there is no accept or stable:
                                        when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}; 
                                        when estimate[p][c][maxBal].status \in {"rejected-slow","rejected-fast"};
                                        with (t \in Time) { \* use an arbitrary timestamp.
                                            when <<c,b>> \notin DOMAIN phase1;
                                            phase1 := phase1 ++ <<<<c,b>>, t>>;
                                            \* when FALSE;
                                        }
                                    } or {
                                        \* there is one "pending-slow" and there is no accept or stable or reject:
                                        when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected-slow","rejected-fast"};
                                        when estimate[p][c][maxBal].status = "pending-slow";
                                        with (e = estimate[p][c][maxBal], t = e.ts, ds = e.leaderDeps) {
                                            phase2 := phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                                            \* when FALSE;
                                            goto end2;
                                        } 
                                    } or {
                                        \* there is one "pending-fast" and there is no accept or stable or reject:
                                        when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected-slow","rejected-fast","pending-slow"};
                                        when estimate[p][c][maxBal].status = "pending-fast";
                                        with (deps = UNION {estimate[p2][c][maxBal].seen : p2 \in ps}; 
                                                wl = {c2 \in deps : (\A q2 \in FastQuorum :
                                                    (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in estimate[p2][c][maxBal].seen))}) {
                                            phase1_deps := phase1_deps ++ <<<<c,b>>, wl>>;
                                        };
                                        when <<c,b>> \notin DOMAIN phase1;
                                        phase1 := phase1 ++ <<<<c,b>>, estimate[p][c][maxBal].ts>>;
                                        \* when FALSE;
                                    }
                                }
                            } else {
                                \* No acceptor in ps saw the command.
                                \* In practice this should not happen if the new leader is in its received quorum.
                                \* Could happen if recovery is triggered by a client.
                                with (t \in Time) {
                                    when <<c,b>> \notin DOMAIN phase1;
                                    phase1 := phase1 ++ <<<<c,b>>, t>>;
                                    \* when FALSE;
                                }
                            }
                        }
                    }
                };
        end1:   either { 
        fastD:      (* Fast decision *)
                    with (q \in FastQuorum, c = self[1], b = self[2]) {
                        when \A p \in q : b \in DOMAIN estimate[p][c] 
                            /\ estimate[p][c][b].status = "pending-fast";
                        with (  ds = UNION {estimate[p][c][b].seen : p \in q};
                                t = phase1[<<c,b>>] ) {
                            stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                        }
                    };
                    goto d;
                } or {
                    (* there is a reject, trigger phase 3. *)
        rejectIn1:  with (q \in Quorum, c = self[1], b = self[2]) {
                        when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
                        \* The leader receives a phase-1 "reject" message.
                        when \E p2 \in q : estimate[p2][c][b].status = "rejected-fast";
                        with (  ps = {p \in q : estimate[p][c][b].status \in {"rejected-fast", "pending-fast"}}, \* use only information from phase 1.
                                ds = UNION {estimate[p][c][b].seen : p \in ps}, 
                                t = GTE(c, {<<c, estimate[p][c][b].ts>> : p \in ps})) {
                            \* Trigger phase 3:
                            phase3 := phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                            goto end3; (* GOTO EndPhase3 *)
                        }
                    }
                } or { (* time out *)
        timeout:    with (q \in Quorum, c = self[1], b = self[2]) {
                        when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
                        \* The leader triggers the slow path because it timed-out waiting for a fast quorum,
                        \* and it did not receive any "rejected" response to its proposal.
                        when \A p2 \in q : estimate[p2][c][b].status = "pending-fast";
                        with (  ps = {p \in q : estimate[p][c][b].status \in {"rejected-fast", "pending-fast"}}, \* use only information from phase 1.
                                ds = UNION {estimate[p2][c][b].seen : p2 \in ps},
                                p2 = CHOOSE p2 \in ps : TRUE,
                                t = estimate[p2][c][b].ts) {
                            assert \A p \in ps : estimate[p][c][b].ts = t;
                            phase2 := phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                            \* TODO: currently, deps is not used...
                        }
                    };
        end2:       either {
        slowD:          (* Decision in phase 2 *)
                        with (q \in Quorum, c = self[1], b = self[2]) {
                            when \A p2 \in q : SeenAt(c, b, p2);
                            when \A p2 \in q : estimate[p2][c][b].status = "pending-slow";
                            with (  ds = UNION {estimate[p2][c][b].seen : p2 \in q},
                                    p2 = CHOOSE p2 \in q : TRUE,
                                    t = estimate[p2][c][b].ts) {
                                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                                goto d; (* GOTO end *)
                            }
                        }
                    } or {
        rejectIn2:      (* Reject in phase 2 *)
                        (* TODO: can this ever happen? *)
                        with (q \in Quorum, c = self[1], b = self[2]) {
                            when \A p2 \in q : SeenAt(c, b, p2);
                            \* The leader receives a "reject" message.
                            when \E p2 \in q : estimate[p2][c][b].status = "rejected-slow";
                            with (  ps = {p \in q : estimate[p][c][b].status \in {"rejected-slow", "pending-slow"}}, \* use only information from phase 2.
                                    ds = UNION {estimate[p2][c][b].seen : p2 \in ps}, 
                                    t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in ps})) {
                                phase3 := phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                                assert FALSE;
                            }
                        }
                    };
        end3:       (* Decide in phase 3 *)
                    with (q \in Quorum, c = self[1], b = self[2] ) {
                        when \A p \in q : b \in DOMAIN estimate[p][c]
                            /\ estimate[p][c][b].status = "accepted";
                        with (  ds = UNION {estimate[p][c][b].seen : p \in q};
                                t = phase3[<<c,b>>].ts ) {
                            stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
                        }
                    }
                };
        d:      skip (* THE END *)
    }
    
    (*
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:     either {
                        when self[2] = 0; \* In ballot 0, directly propose.
        phase1:       with (t \in Time) { Phase1(self[1], 0, t); };
        endphase1:    either { FastDecision(self[1], 0); }
                      or { EndPhase1(self[1], 0); };
        x1:           either { 
                        EndPhase2(self[1], 0);
                        EndPhase3(self[1], 0); }
                      or {EndPhase3(self[1], 0);}; 
                    } or {
                        when self[2] > 0; 
                        \* In a non-zero ballot, we first have to determine a safe value to propose in the fast or slow path:
        startBal:       StartBallot(self[1], self[2]);
        recover:        Recover(self[1], self[2]);
        decide:         call Decide(self[1], self[2]); 
        decided:        skip; 
                    }
    }
    *)
    
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
\* Label phase1 of process initialLeader at line 398 col 26 changed to phase1_
\* Label acc of process acc at line 574 col 17 changed to acc_
VARIABLES ballot, estimate, phase1, phase2, stable, phase3, join, phase1_deps, 
          pc

(* define statement *)
Status == {"pending-slow", "pending-fast", "stable", "accepted", "rejected"}

CmdInfo == [ts : Nat, deps : SUBSET C]
CmdInfoWithStat == [ts : Nat, seen : SUBSET C, leaderDeps : SUBSET C, status: Status]


SeenCmds(p) == {c \in C : DOMAIN estimate[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN estimate[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN estimate[p][c] : b <= max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE -1


MaxEstimate(c, p) == estimate[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b-1, p) : p \in q}
    IN Max(bals)


TimeStampOf(c, p) == MaxEstimate(c,p).ts

TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}


CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}

LowerCmds(p, c, t, S) == {
    c2 \in C : DOMAIN estimate[p][c2] # {} /\ estimate[p][c2][LastBal(c2, Max(Ballot), p)].status \in S
        /\ <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}

ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]


Deps2(c, p) == {c2 \in SeenCmds(p) : <<c2,TimeStampOf(c2,p)>> \prec <<c,TimeStampOf(c,p)>>}
Seen(c, p) == MaxEstimate(c, p).seen \ {c}

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Seen(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)

GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
    /\ <<c1,b1>> \in DOMAIN stable
    /\ <<c2,b2>> \in DOMAIN stable
    /\ c1 # c2
    /\ <<c1, stable[<<c1,b1>>].ts>> \prec <<c2, stable[<<c2,b2>>].ts>>
    => c1 \in stable[<<c2,b2>>].deps

Agreement == \A c \in C : \A b1,b2 \in Ballot :
    /\ <<c,b1>> \in DOMAIN stable
    /\ <<c,b2>> \in DOMAIN stable
    => stable[<<c,b1>>].ts = stable[<<c,b2>>].ts

Cmd(leader) == leader[1]
Bal(leader) == leader[2]


vars == << ballot, estimate, phase1, phase2, stable, phase3, join, 
           phase1_deps, pc >>

ProcSet == ((C \times Ballot)) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> [c \in C |-> <<>>]]
        /\ phase1 = <<>>
        /\ phase2 = <<>>
        /\ stable = <<>>
        /\ phase3 = <<>>
        /\ join = {}
        /\ phase1_deps = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times Ballot) -> "start"
                                        [] self \in P -> "acc_"]

start(self) == /\ pc[self] = "start"
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "phase1_"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "startBal"]
               /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, 
                               phase3, join, phase1_deps >>

phase1_(self) == /\ pc[self] = "phase1_"
                 /\ \E t \in Time:
                      /\ self[2] = 0
                      /\ <<self[1],0>> \notin DOMAIN phase1
                      /\ phase1' = phase1 ++ <<<<self[1],0>>, t>>
                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                 /\ UNCHANGED << ballot, estimate, phase2, stable, phase3, 
                                 join, phase1_deps >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ self[2] > 0
                  /\ join' = (join \cup {<<self[1],self[2]>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, 
                                  phase3, phase1_deps >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET b == self[2] IN
                          /\ \A p \in q : ballot[p][c] >= b
                          /\ LET maxBal == MaxBal(c, b, q) IN
                               IF maxBal # -1
                                  THEN /\ LET ps == {p \in q : ParticipatedIn(maxBal, c, p)} IN
                                            \E p \in ps:
                                              \/ /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"stable"}
                                                 /\ estimate[p][c][maxBal].status = "accepted"
                                                 /\ LET e == estimate[p][c][maxBal] IN
                                                      LET t == e.ts IN
                                                        LET ds == e.leaderDeps IN
                                                          /\ phase3' = phase3 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                                          /\ pc' = [pc EXCEPT ![self] = "end3"]
                                                 /\ UNCHANGED <<phase1, phase2, phase1_deps>>
                                              \/ /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}
                                                 /\ estimate[p][c][maxBal].status \in {"rejected-slow","rejected-fast"}
                                                 /\ \E t \in Time:
                                                      /\ <<c,b>> \notin DOMAIN phase1
                                                      /\ phase1' = phase1 ++ <<<<c,b>>, t>>
                                                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                 /\ UNCHANGED <<phase2, phase3, phase1_deps>>
                                              \/ /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected-slow","rejected-fast"}
                                                 /\ estimate[p][c][maxBal].status = "pending-slow"
                                                 /\ LET e == estimate[p][c][maxBal] IN
                                                      LET t == e.ts IN
                                                        LET ds == e.leaderDeps IN
                                                          /\ phase2' = phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                                          /\ pc' = [pc EXCEPT ![self] = "end2"]
                                                 /\ UNCHANGED <<phase1, phase3, phase1_deps>>
                                              \/ /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected-slow","rejected-fast","pending-slow"}
                                                 /\ estimate[p][c][maxBal].status = "pending-fast"
                                                 /\ LET deps == UNION {estimate[p2][c][maxBal].seen : p2 \in ps} IN
                                                      LET wl ==  {c2 \in deps : (\A q2 \in FastQuorum :
                                                                (ps \cap q2) # {} => (\E p2 \in (ps \cap q2) : c2 \in estimate[p2][c][maxBal].seen))} IN
                                                        phase1_deps' = phase1_deps ++ <<<<c,b>>, wl>>
                                                 /\ <<c,b>> \notin DOMAIN phase1
                                                 /\ phase1' = phase1 ++ <<<<c,b>>, estimate[p][c][maxBal].ts>>
                                                 /\ pc' = [pc EXCEPT ![self] = "end1"]
                                                 /\ UNCHANGED <<phase2, phase3>>
                                  ELSE /\ \E t \in Time:
                                            /\ <<c,b>> \notin DOMAIN phase1
                                            /\ phase1' = phase1 ++ <<<<c,b>>, t>>
                                       /\ pc' = [pc EXCEPT ![self] = "end1"]
                                       /\ UNCHANGED << phase2, phase3, 
                                                       phase1_deps >>
                 /\ UNCHANGED << ballot, estimate, stable, join >>

end1(self) == /\ pc[self] = "end1"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "fastD"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "rejectIn1"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "timeout"]
              /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, phase3, 
                              join, phase1_deps >>

fastD(self) == /\ pc[self] = "fastD"
               /\ \E q \in FastQuorum:
                    LET c == self[1] IN
                      LET b == self[2] IN
                        /\  \A p \in q : b \in DOMAIN estimate[p][c]
                           /\ estimate[p][c][b].status = "pending-fast"
                        /\ LET ds == UNION {estimate[p][c][b].seen : p \in q} IN
                             LET t == phase1[<<c,b>>] IN
                               stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
               /\ pc' = [pc EXCEPT ![self] = "d"]
               /\ UNCHANGED << ballot, estimate, phase1, phase2, phase3, join, 
                               phase1_deps >>

rejectIn1(self) == /\ pc[self] = "rejectIn1"
                   /\ \E q \in Quorum:
                        LET c == self[1] IN
                          LET b == self[2] IN
                            /\ \A p2 \in q : SeenAt(c, b, p2)
                            /\ \E p2 \in q : estimate[p2][c][b].status = "rejected-fast"
                            /\ LET ps == {p \in q : estimate[p][c][b].status \in {"rejected-fast", "pending-fast"}} IN
                                 LET ds == UNION {estimate[p][c][b].seen : p \in ps} IN
                                   LET t == GTE(c, {<<c, estimate[p][c][b].ts>> : p \in ps}) IN
                                     /\ phase3' = phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>
                                     /\ pc' = [pc EXCEPT ![self] = "end3"]
                   /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, 
                                   join, phase1_deps >>

timeout(self) == /\ pc[self] = "timeout"
                 /\ \E q \in Quorum:
                      LET c == self[1] IN
                        LET b == self[2] IN
                          /\ \A p2 \in q : SeenAt(c, b, p2)
                          /\ \A p2 \in q : estimate[p2][c][b].status = "pending-fast"
                          /\ LET ps == {p \in q : estimate[p][c][b].status \in {"rejected-fast", "pending-fast"}} IN
                               LET ds == UNION {estimate[p2][c][b].seen : p2 \in ps} IN
                                 LET p2 == CHOOSE p2 \in ps : TRUE IN
                                   LET t == estimate[p2][c][b].ts IN
                                     /\ Assert(\A p \in ps : estimate[p][c][b].ts = t, 
                                               "Failure of assertion at line 504, column 29.")
                                     /\ phase2' = phase2 ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                 /\ pc' = [pc EXCEPT ![self] = "end2"]
                 /\ UNCHANGED << ballot, estimate, phase1, stable, phase3, 
                                 join, phase1_deps >>

end2(self) == /\ pc[self] = "end2"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "slowD"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "rejectIn2"]
              /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, phase3, 
                              join, phase1_deps >>

slowD(self) == /\ pc[self] = "slowD"
               /\ \E q \in Quorum:
                    LET c == self[1] IN
                      LET b == self[2] IN
                        /\ \A p2 \in q : SeenAt(c, b, p2)
                        /\ \A p2 \in q : estimate[p2][c][b].status = "pending-slow"
                        /\ LET ds == UNION {estimate[p2][c][b].seen : p2 \in q} IN
                             LET p2 == CHOOSE p2 \in q : TRUE IN
                               LET t == estimate[p2][c][b].ts IN
                                 /\ stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                                 /\ pc' = [pc EXCEPT ![self] = "d"]
               /\ UNCHANGED << ballot, estimate, phase1, phase2, phase3, join, 
                               phase1_deps >>

rejectIn2(self) == /\ pc[self] = "rejectIn2"
                   /\ \E q \in Quorum:
                        LET c == self[1] IN
                          LET b == self[2] IN
                            /\ \A p2 \in q : SeenAt(c, b, p2)
                            /\ \E p2 \in q : estimate[p2][c][b].status = "rejected-slow"
                            /\ LET ps == {p \in q : estimate[p][c][b].status \in {"rejected-slow", "pending-slow"}} IN
                                 LET ds == UNION {estimate[p2][c][b].seen : p2 \in ps} IN
                                   LET t == GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in ps}) IN
                                     /\ phase3' = phase3 ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>
                                     /\ Assert(FALSE, 
                                               "Failure of assertion at line 532, column 33.")
                   /\ pc' = [pc EXCEPT ![self] = "end3"]
                   /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, 
                                   join, phase1_deps >>

end3(self) == /\ pc[self] = "end3"
              /\ \E q \in Quorum:
                   LET c == self[1] IN
                     LET b == self[2] IN
                       /\  \A p \in q : b \in DOMAIN estimate[p][c]
                          /\ estimate[p][c][b].status = "accepted"
                       /\ LET ds == UNION {estimate[p][c][b].seen : p \in q} IN
                            LET t == phase3[<<c,b>>].ts IN
                              stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
              /\ pc' = [pc EXCEPT ![self] = "d"]
              /\ UNCHANGED << ballot, estimate, phase1, phase2, phase3, join, 
                              phase1_deps >>

d(self) == /\ pc[self] = "d"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << ballot, estimate, phase1, phase2, stable, phase3, 
                           join, phase1_deps >>

initialLeader(self) == start(self) \/ phase1_(self) \/ startBal(self)
                          \/ recover(self) \/ end1(self) \/ fastD(self)
                          \/ rejectIn1(self) \/ timeout(self) \/ end2(self)
                          \/ slowD(self) \/ rejectIn2(self) \/ end3(self)
                          \/ d(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c, b>> \in DOMAIN phase1
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET t == phase1[<<c, b>>] IN
                                /\ LastBal(c, b, self) < b
                                /\ \neg Blocked(self, c, t)
                                /\ LET flag == IF <<c,b>> \in DOMAIN phase1_deps THEN TRUE ELSE FALSE IN
                                     \/ /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                                        /\ LET seen ==      IF <<c,b>> \in DOMAIN phase1_deps
                                                       THEN phase1_deps[<<c,b>>] \cup LowerCmds(self, c, t, {"accepted", "stable", "pending-slow"})
                                                       ELSE CmdsWithLowerT(self, c, t) IN
                                             estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                         <<b, [ts |-> t, status |-> "pending-fast", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]]
                                     \/ /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                                        /\ LET t2 == GT(c, TimeStamps(self)) IN
                                             LET seen ==    IF <<c,b>> \in DOMAIN phase1_deps
                                                         THEN phase1_deps[<<c,b>>] \cup LowerCmds(self, c, t2[2], {"accepted", "stable", "pending-slow"})
                                                         ELSE CmdsWithLowerT(self, c, t2[2]) IN
                                               estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                           ++ <<b, [ts |-> t2[2], status |-> "rejected-fast", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c,b>> \in DOMAIN stable
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET s == stable[<<c,b>>] IN
                                estimate' =         [estimate EXCEPT ![self] =
                                            [@ EXCEPT ![c] = @ ++ <<b, [status |-> "stable",
                                             ts |-> s.ts, seen |-> s.deps, leaderDeps |-> s.deps ]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c, b>> \in DOMAIN phase2
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET t == phase2[<<c,b>>].ts IN
                                /\ \neg Blocked(self, c, t)
                                /\  b \in DOMAIN estimate[self][c]
                                   => estimate[self][c][b].status \in {"pending-fast"}
                                /\ \/ /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                                      /\ LET seen == phase2[<<c,b>>].deps IN
                                           estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                       <<b, [ts |-> t, status |-> "pending-slow", seen |-> seen, leaderDeps |-> {}]>>]]
                                   \/ /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                                      /\ LET t2 == GT(c, TimeStamps(self)) IN
                                           LET seen == CmdsWithLowerT(self, c, t2[2]) IN
                                             estimate' =           [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                         ++ <<b, [ts |-> t2[2], status |-> "rejected-slow", seen |-> seen, leaderDeps |-> {}]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c, b>> \in DOMAIN phase3
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\  b \in DOMAIN estimate[self][c]
                              => estimate[self][c][b].status \in {"pending-fast","pending-slow","rejected-fast", "rejected-slow"}
                           /\ LET t == phase3[<<c,b>>].ts IN
                                LET seen == CmdsWithLowerT(self, c, t) \cup phase3[<<c,b>>].deps IN
                                  estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                              <<b, [ts |-> t, status |-> "accepted", seen |-> seen, leaderDeps |-> phase3[<<c,b>>].deps]>>]]
                 \/ /\ \E prop \in join:
                         LET c == prop[1] IN
                           LET b == prop[2] IN
                             /\ b > ballot[self][c]
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                    /\ UNCHANGED estimate
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << phase1, phase2, stable, phase3, join, 
                              phase1_deps >>

acc(self) == acc_(self)

Next == (\E self \in (C \times Ballot): initialLeader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Fri Apr 29 13:35:13 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
