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
        
        (*******************************************************************)
        (* An invariant describing the type of the different variables.    *)
        (* Note that we extensively use maps (also called functions) keyed *)
        (* by pairs <c,b>, where c is a command and b a ballot, and where  *)
        (* the set of keys of the map dynamically grows.  The set of keys  *)
        (* of a map m is noted DOMAIN m.                                   *)
        (*******************************************************************)
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : estimate[p][c] \in [D -> CmdInfoWithStat]
            /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Nat]
            /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> CmdInfo]
            /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> CmdInfo]
            /\  join \subseteq (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : phase1_deps \in [D -> SUBSET C]
    
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
            
        (***************************************************************************)
        (* A few simple invariants.                                                *)
        (***************************************************************************)
        Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)
        
        Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in DOMAIN propose => <<c,b>> \in join
        
        (*******************************************************************)
        (* This invariant does not hold because some dependencies in deps  *)
        (* will be only eventually eliminated, whereas Pred2 eleminates    *)
        (* them as soon as they appear...  Can we use Pred2 instead of     *)
        (* Pred? We could if we did not need to keep the history of preds  *)
        (* to simulate receiving messages sent in a past state.            *)
        (*******************************************************************)
        Inv3 == \A c \in C, p \in P : 
            c \in SeenCmds(p) /\ MaxEstimate(c,p).status # "stable" => Seen(c,p) \subseteq Deps2(c,p)
        
        (*******************************************************************)
        (* The main correctness properties are GraphInvariant and          *)
        (* Agreement.  Their conjunction implies correct SMR.              *)
        (*******************************************************************)
                
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
 
 
    \* Models a the leader of ballot b for command c making a proposal.
    macro Phase1(c, b, t) {
        \* has not been proposed before in this ballot:
        when <<c,b>> \notin DOMAIN phase1;
        phase1 := phase1 ++ <<<<c,b>>, t>>
    }
    
    macro Phase1Reply(p) {
        with (c \in C; b \in Ballot) {
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase1; \* Only reply for a proposal in the current ballot.
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            with (t = phase1[<<c, b>>]) {
                when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                either {
                    when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                    with (seen = IF <<c,b>> \in DOMAIN phase1_deps
                            THEN phase1_deps[<<c,b>>] \cup LowerCmds(p, c, t, {"accepted", "stable", "pending-slow"})
                            ELSE CmdsWithLowerT(p, c, t);
                          flag = IF <<c,b>> \in DOMAIN phase1_deps THEN TRUE ELSE FALSE) {
                        estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                            <<b, [ts |-> t, status |-> "pending-fast", seen |-> seen, leaderDeps |-> {}, flag |-> flag]>>]]; 
                    }
                } or {
                    when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with ( t2 = GT(c, TimeStamps(p)) ) {
                      \* Record the fact that the command was rejected with t2 (but seen is useless here, as is leaderDeps):
                      estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> {}, leaderDeps |-> {}]>>]];
                    }
                }
            }
        }
    }
        
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] 
                /\ estimate[p][c][b].status = "pending-fast";
            with (  ds = UNION {estimate[p][c][b].seen : p \in q};
                    t = phase1[<<c,b>>] ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
            }
        }
    }

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
    
    macro Phase2Reply(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase2;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
            \* Only reply if p has not seen c in b or has it pending-fast in b:
            when b \in DOMAIN estimate[p][c]
                => estimate[p][c][b].status \in {"pending-fast"};                
            either {
                when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with (seen = CmdsWithLowerT(p, c, t)) {
                    estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                        <<b, [ts |-> t, status |-> "pending-slow", seen |-> seen, leaderDeps |-> {}]>>]]; 
                }
            } or {
                when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                with ( t2 = GT(c, TimeStamps(p)) ) {
                  \* Record the fact that the command was rejected with t2 (but seen is useless here, as is leaderDeps):
                  estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                    ++ <<b, [ts |-> t2[2], status |-> "rejected", seen |-> {}, leaderDeps |-> {}]>>]];
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
    
    macro Phase3Reply(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN phase3;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            \* Only reply if p has not seen c in b or has it pending-fast in b:
            when b \in DOMAIN estimate[p][c]
                => estimate[p][c][b].status \in {"pending-fast","pending-slow","rejected"};
            with (seen = CmdsWithLowerT(p, c, t) \cup phase3[<<c,b>>].deps) {
                estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                    <<b, [ts |-> t, status |-> "accepted", seen |-> seen, leaderDeps |-> phase3[<<c,b>>].deps]>>]]; 
            }
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
    
    macro StartBallot(c, b) {
        assert b > 0; \* Only start ballots greater than 0; 0 is started by default.
        join := join \cup {<<c,b>>};
    }
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
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
    }
    
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
                        JoinBallot(self);
                    }
                }
    }
    
}

*)


=============================================================================
\* Modification History
\* Last modified Thu Apr 28 19:11:04 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
