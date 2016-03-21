------------------------------ MODULE Caesar2 ------------------------------

(***************************************************************************)
(* Full specification of the Caesar algorithm.                             *)
(*                                                                         *)
(* The actions of the command leaders are specified by stating what the    *)
(* command leader of command c in ballot b does (called the ballot-b       *)
(* leader of c), but without identifying which acceptor the leader is,     *)
(* because that is not needed.                                             *)
(*                                                                         *)
(* The specification does not model the network.  Instead, information     *)
(* about the past states of the acceptors is kept and used to simulate     *)
(* receiving messages sent at a time in the past.  For example, the        *)
(* history of the acceptor's estimate of the timestamp and dependencies of *)
(* a command is kept in a variable mapping an acceptor and a ballot number *)
(* to an estimate.                                                         *)
(***************************************************************************)

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
        propose = <<>>,
        \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c has been committed in ballot b
        \* with timestamp t and dependencies ds: 
        stable = <<>>,
        \* maps a pair <<c,b>> to a timestamp t and a set of dependencies ds, 
        \* indicating that c is to be retried in ballot b with timestamp t and dependencies ds.
        retry = <<>>,
        \* a set of pairs <<c,b>>, indicating that the ballot-b leader of c asks all acceptors to join ballot b:
        join = {} 

    define {
        
        Status == {"pending", "stable", "accepted", "rejected"}
        
        CmdInfo == [ts : Nat, deps : SUBSET C]
        CmdInfoWithStat == [ts : Nat, deps : SUBSET C, status: Status]
        
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
        
        ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]
        
        \* The predecessor set (or dependency set) of c at p.
        Deps2(c, p) == {c2 \in SeenCmds(p) : <<c2,TimeStampOf(c2,p)>> \prec <<c,TimeStampOf(c,p)>>}
        Deps(c, p) == MaxEstimate(c, p).deps \ {c}
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Deps(c2,p)
        
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
            c \in SeenCmds(p) /\ MaxEstimate(c,p).status # "stable" => Deps(c,p) \subseteq Deps2(c,p)
        
        (***************************************************************************)
        (* This invariant must hold for the execution phase (not formalized here)  *)
        (* to be correct.                                                          *)
        (***************************************************************************)
        GraphInvariant == \A s1 \in DOMAIN stable, s2 \in DOMAIN stable : 
            LET c1 == s1[1]
                c2 == s2[1]
            IN  c1 # c2 /\ <<c1, stable[s1].ts>> \prec <<c2, stable[s2].ts>> =>
                    c1 \in stable[s2].deps
        
        (***************************************************************************)
        (* The agreement property.                                                 *)
        (***************************************************************************)
        
        (***************************************************************************)
        (* A command is executable if all its dependencies which have strictly     *)
        (* lower timestamp are also executable.                                    *)
        (***************************************************************************)
        RECURSIVE Executable(_)
        Executable(s) == 
            LET c == s[1]
                b == s[2] 
            IN  /\  <<c,b>> \in DOMAIN stable 
                /\  \A c2 \in stable[<<c,b>>].deps : 
                    /\  \E s2 \in DOMAIN stable : 
                        /\  s2[1] = c2
                        /\  (<<c2, stable[s2].ts>> \prec <<c, stable[s].ts>> => Executable(s2))
        
        StableTimeStamps == { s.ts : s \in Image(stable) }
        
        \* If c is stable and weak agreement holds (see below), this is the unique timestamp of c.
        TimeStamp(c) == CHOOSE ts \in StableTimeStamps : \E s \in DOMAIN stable :
            s[1] = c /\ stable[s].ts = ts
        
        \* The "real" dependencies of c when committed with timestamp t and dependencies ds, 
        \* i.e. ds minus the commands commited with a higher timestamp than t.
        RealDeps(c, t, ds) ==
                {d \in ds : <<d,TimeStamp(d)>> \prec <<c,t>> }
        
        (*******************************************************************)
        (* If a command c is made stable in two different ballots, then    *)
        (* its timestamp and real dependencies are the same in both.  Note *)
        (* that the actual dependency set might be different.              *)
        Agreement == \A c \in C : \A s1, s2 \in DOMAIN stable : 
            Executable(s1) /\ Executable(s2) /\ s1[1] = c /\ s2[1] = c 
                =>  /\  stable[s1].ts = stable[s2].ts
                    /\  RealDeps(c, TimeStamp(c), stable[s1].deps) = 
                            RealDeps(c, TimeStamp(c), stable[s2].deps) 
        
        WeakAgreement == \A c \in C : \A s1, s2 \in DOMAIN stable : 
            s1[1] = c /\ s2[1] = c => stable[s1].ts = stable[s2].ts
        
        }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
 
    \* Models a the leader of ballot b for command c making a proposal.
    macro Propose(c, b, t) {
        assert b \in Ballot /\ t \in Nat /\ c \in C;
        \* has not been proposed before in this ballot:
        when <<c,b>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,b>>, t>>
    }

    \* Models replying to a proposal with an ACK message.  
    macro AckPropose(p) {
        with (c \in C; b = ballot[p][c]) { 
            when <<c, b>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            with (t = propose[<<c, b>>]) {
                when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with ( ds = CmdsWithLowerT(p, c, t) \ {c} ) { \* Collect all commands with a lower timestamp.
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                    <<b, [ts |-> t, status |-> "pending", deps |-> ds]>>]];
                }
            }
        }
    }
    
    \* Models replying to a proposal with an ACK message.  
    macro RejectPropose(p) {
        with (c \in C; b = ballot[p][c]) {
            when <<c, b>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            with (t = propose[<<c, b>>]) {
                when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                with (  ds = SeenCmds(p) \ {c}; t2 = GT(c, TimeStamps(p)) ) { 
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ 
                    ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> ds]>>]];
                }
            }
        }
    }
    
    \* The leader triggers the slow path because it received a "rejected" response to its proposal. 
    macro RetryWhenRejected(c, b) {
        with (q \in Quorum) {
            when <<c,b>> \notin DOMAIN retry \cup DOMAIN stable;
            when \A p2 \in q : SeenAt(c, b, p2); \* p2 has seen c in ballot b.
            when \E p2 \in q : estimate[p2][c][b].status = "rejected";
            with (ds = UNION {estimate[p2][c][b].deps : p2 \in q}, 
                    t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) {
                retry := retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
            }
        }
    }
    
    \* The leader triggers the slow path because it timed-out waiting for a fast quorum,
    \* and it did not receive any "rejected" response to its proposal.
    macro RetryWhenTimeout(c, b) {
        with (q \in Quorum) {
            when <<c,b>> \notin DOMAIN retry \cup DOMAIN stable;
            when \A p2 \in q : SeenAt(c, b, p2) /\ estimate[p2][c][b].status = "accepted";
            with (ds = UNION {estimate[p2][c][b].deps : p2 \in q}, 
                    t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) { \* greater than has no effet. Do we need strictly greater?
                retry := retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
            }
        }
    }
    
    macro RetryAck(p) {
        with (c \in C, b = ballot[p][c]) {
            when <<c, b>> \in DOMAIN retry;
            \* Only reply if p has not seen c in b or has it pending or rejected in b:
            when b \in DOMAIN estimate[p][c] 
                => estimate[p][c][b].status \in {"pending", "rejected"};  
            with (e = retry[<<c, b>>]; ds = (CmdsWithLowerT(p, c, e.ts) \cup e.deps) \ {c}) { \* TODO: do we need the union with the local dependencies?
                estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                    <<b, [ts |-> e.ts, status |-> "accepted", deps |-> ds]>>]];
            }
        }
    }
    
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] 
                /\ estimate[p][c][b].status = "pending";
            with (  ds = UNION {estimate[p][c][b].deps : p \in q};
                    t = propose[<<c,b>>] ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
            }
        }
    }
     
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] 
                /\ estimate[p][c][b].status = "accepted";
            with (  ds = UNION {estimate[p][c][b].deps : p \in q};
                    t = retry[<<c,b>>].ts ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
            }
        }
    }
    
    macro LearnStable(p) {
        with (c \in C, b = ballot[p][c]) {
            when <<c,b>> \in DOMAIN stable;
            estimate := [estimate EXCEPT ![p] = 
                [@ EXCEPT ![c] = @ ++ <<b, stable[<<c,b>>] ++ <<"status", "stable">> >>]];
        }
    }
    
    macro StartBallot(c, b) {
        when b > 0; \* Only start ballots greater than 0; 0 is started by default.
        join := join \cup {<<c,b>>};
    }
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (prop \in join; c = prop[1], b = prop[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
    macro  RecoverAccepted(c, b) {
        when <<c,b>> \in join;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
            \* the maximum ballot strictly less than b in which a vote was cast:
            with (maxBal = MaxBal(c, b, q)) { 
                when maxBal # -1;
                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                    when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"stable"}; \* there is no stable.
                    when estimate[p][c][maxBal].status = "accepted";
                    with (e = estimate[p][c][maxBal], t = e.ts) {
                        retry := retry ++ <<<<c,b>>, t>>;
                    }
                }
            }
        }
    }
    
    macro  RecoverRejected(c, b) {
        when <<c,b>> \in join;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
            with (maxBal = MaxBal(c, b, q)) { \* the maximum ballot strictly less than b in which a vote was cast.
                when maxBal # -1;
                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                    \* there is no accept or stable:
                    when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}; 
                    when estimate[p][c][maxBal].status = "rejected"; \* there is one reject.
                    with (t \in Time) { \* use an arbitrary timestamp.
                        Propose(c, b, t);
                    }
                }
            }
        }
    }    
    
    macro  RecoverPending(c, b) {
        when <<c,b>> \in join;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
            with (maxBal = MaxBal(c, b, q)) { \* the maximum ballot strictly less than b in which a vote was cast.
                when maxBal # -1;
                with (ps = {p \in q : ParticipatedIn(maxBal, c, p)}; p \in ps) {
                    \* there is no accept or stable or reject:
                    when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected"}; 
                    when estimate[p][c][maxBal].status = "pending"; \* there is one pending.
                    Propose(c, b, estimate[p][c][maxBal].ts);
                }
            }
        }
    }
    
    \* In practice this should not happen if the new leader is in its received quorum. 
    \* Could happen if recovery is triggered by a client.
    macro RecoverNotSeen(c, b) { 
        when <<c,b>> \in join;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b; \* every p in the quorum is in b or higher.
            with (maxBal = MaxBal(c, b, q)) { \* the maximum ballot strictly less than b in which a vote was cast.
                when maxBal = -1; \* no acceptor ever saw c.
                with (t \in Time) {
                   Propose(c, b, t); 
                }        
            }
        }
    }
  
    process (leader \in C \times Ballot) {
        ldr:    while (TRUE) {
                    \* event loop of the ballot-b leader of command c:
                    with (c = self[1], b = self[2]) { 
                        either {
                            with (t \in Time) {
                                when b = 0; \* Direct proposals can only be made in ballot 0.
                                Propose(c, b, t); 
                            }
                        } or {
                            FastDecision(c, b);
                        } or {
                            RetryWhenRejected(c, b);
                        } or {
                            RetryWhenTimeout(c, b);
                        } or {
                            SlowDecision(c, b);
                        } or {
                            StartBallot(c, b);
                        } or {
                            RecoverAccepted(c, b);
                        } or {
                            RecoverRejected(c, b);
                        } or {
                            skip; \* RecoverPending(c, b);
                        } or {
                            RecoverNotSeen(c, b);
                        }
                    }
                }
    }
    
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        AckPropose(self);
                    } or {
                        RejectPropose(self);
                    } or {
                        LearnStable(self);
                    } or {
                        RetryAck(self);
                    } or {
                        JoinBallot(self);
                    }
                }
    }
    
}

*) 
\* BEGIN TRANSLATION
\* Label acc of process acc at line 473 col 17 changed to acc_
VARIABLES ballot, estimate, propose, stable, retry, join

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}

CmdInfo == [ts : Nat, deps : SUBSET C]
CmdInfoWithStat == [ts : Nat, deps : SUBSET C, status: Status]








TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : estimate[p][c] \in [D -> CmdInfoWithStat]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Nat]
    /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> CmdInfo]
    /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> CmdInfo]
    /\  join \subseteq (C \times Ballot)


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

ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]


Deps2(c, p) == {c2 \in SeenCmds(p) : <<c2,TimeStampOf(c2,p)>> \prec <<c,TimeStampOf(c,p)>>}
Deps(c, p) == MaxEstimate(c, p).deps \ {c}

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Deps(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)




Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)

Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in DOMAIN propose => <<c,b>> \in join








Inv3 == \A c \in C, p \in P :
    c \in SeenCmds(p) /\ MaxEstimate(c,p).status # "stable" => Deps(c,p) \subseteq Deps2(c,p)





GraphInvariant == \A s1 \in DOMAIN stable, s2 \in DOMAIN stable :
    LET c1 == s1[1]
        c2 == s2[1]
    IN  c1 # c2 /\ <<c1, stable[s1].ts>> \prec <<c2, stable[s2].ts>> =>
            c1 \in stable[s2].deps









RECURSIVE Executable(_)
Executable(s) ==
    LET c == s[1]
        b == s[2]
    IN  /\  <<c,b>> \in DOMAIN stable
        /\  \A c2 \in stable[<<c,b>>].deps :
            /\  \E s2 \in DOMAIN stable :
                /\  s2[1] = c2
                /\  (<<c2, stable[s2].ts>> \prec <<c, stable[s].ts>> => Executable(s2))

StableTimeStamps == { s.ts : s \in Image(stable) }


TimeStamp(c) == CHOOSE ts \in StableTimeStamps : \E s \in DOMAIN stable :
    s[1] = c /\ stable[s].ts = ts



RealDeps(c, t, ds) ==
        {d \in ds : <<d,TimeStamp(d)>> \prec <<c,t>> }





Agreement == \A c \in C : \A s1, s2 \in DOMAIN stable :
    Executable(s1) /\ Executable(s2) /\ s1[1] = c /\ s2[1] = c
        =>  /\  stable[s1].ts = stable[s2].ts
            /\  RealDeps(c, TimeStamp(c), stable[s1].deps) =
                    RealDeps(c, TimeStamp(c), stable[s2].deps)

WeakAgreement == \A c \in C : \A s1, s2 \in DOMAIN stable :
    s1[1] = c /\ s2[1] = c => stable[s1].ts = stable[s2].ts


vars == << ballot, estimate, propose, stable, retry, join >>

ProcSet == (C \times Ballot) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>
        /\ join = {}

leader(self) == /\ LET c == self[1] IN
                     LET b == self[2] IN
                       \/ /\ \E t \in Time:
                               /\ b = 0
                               /\ Assert(b \in Ballot /\ t \in Nat /\ c \in C, 
                                         "Failure of assertion at line 251, column 9 of macro called at line 447, column 33.")
                               /\ <<c,b>> \notin DOMAIN propose
                               /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry, join>>
                       \/ /\ \E q \in FastQuorum:
                               /\  \A p \in q : b \in DOMAIN estimate[p][c]
                                  /\ estimate[p][c][b].status = "pending"
                               /\ LET ds == UNION {estimate[p][c][b].deps : p \in q} IN
                                    LET t == propose[<<c,b>>] IN
                                      stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                          /\ UNCHANGED <<propose, retry, join>>
                       \/ /\ \E q \in Quorum:
                               /\ <<c,b>> \notin DOMAIN retry \cup DOMAIN stable
                               /\ \A p2 \in q : SeenAt(c, b, p2)
                               /\ \E p2 \in q : estimate[p2][c][b].status = "rejected"
                               /\ LET ds == UNION {estimate[p2][c][b].deps : p2 \in q} IN
                                    LET t == GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q}) IN
                                      retry' = retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>
                          /\ UNCHANGED <<propose, stable, join>>
                       \/ /\ \E q \in Quorum:
                               /\ <<c,b>> \notin DOMAIN retry \cup DOMAIN stable
                               /\ \A p2 \in q : SeenAt(c, b, p2) /\ estimate[p2][c][b].status = "accepted"
                               /\ LET ds == UNION {estimate[p2][c][b].deps : p2 \in q} IN
                                    LET t == GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q}) IN
                                      retry' = retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>
                          /\ UNCHANGED <<propose, stable, join>>
                       \/ /\ \E q \in Quorum:
                               /\  \A p \in q : b \in DOMAIN estimate[p][c]
                                  /\ estimate[p][c][b].status = "accepted"
                               /\ LET ds == UNION {estimate[p][c][b].deps : p \in q} IN
                                    LET t == retry[<<c,b>>].ts IN
                                      stable' = stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>
                          /\ UNCHANGED <<propose, retry, join>>
                       \/ /\ b > 0
                          /\ join' = (join \cup {<<c,b>>})
                          /\ UNCHANGED <<propose, stable, retry>>
                       \/ /\ <<c,b>> \in join
                          /\ \E q \in Quorum:
                               /\ \A p \in q : ballot[p][c] >= b
                               /\ LET maxBal == MaxBal(c, b, q) IN
                                    /\ maxBal # -1
                                    /\ LET ps == {p \in q : ParticipatedIn(maxBal, c, p)} IN
                                         \E p \in ps:
                                           /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"stable"}
                                           /\ estimate[p][c][maxBal].status = "accepted"
                                           /\ LET e == estimate[p][c][maxBal] IN
                                                LET t == e.ts IN
                                                  retry' = retry ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<propose, stable, join>>
                       \/ /\ <<c,b>> \in join
                          /\ \E q \in Quorum:
                               /\ \A p \in q : ballot[p][c] >= b
                               /\ LET maxBal == MaxBal(c, b, q) IN
                                    /\ maxBal # -1
                                    /\ LET ps == {p \in q : ParticipatedIn(maxBal, c, p)} IN
                                         \E p \in ps:
                                           /\ \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}
                                           /\ estimate[p][c][maxBal].status = "rejected"
                                           /\ \E t \in Time:
                                                /\ Assert(b \in Ballot /\ t \in Nat /\ c \in C, 
                                                          "Failure of assertion at line 251, column 9 of macro called at line 462, column 29.")
                                                /\ <<c,b>> \notin DOMAIN propose
                                                /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry, join>>
                       \/ /\ TRUE
                          /\ UNCHANGED <<propose, stable, retry, join>>
                       \/ /\ <<c,b>> \in join
                          /\ \E q \in Quorum:
                               /\ \A p \in q : ballot[p][c] >= b
                               /\ LET maxBal == MaxBal(c, b, q) IN
                                    /\ maxBal = -1
                                    /\ \E t \in Time:
                                         /\ Assert(b \in Ballot /\ t \in Nat /\ c \in C, 
                                                   "Failure of assertion at line 251, column 9 of macro called at line 466, column 29.")
                                         /\ <<c,b>> \notin DOMAIN propose
                                         /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry, join>>
                /\ UNCHANGED << ballot, estimate >>

acc(self) == /\ \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c, b>> \in DOMAIN propose
                          /\ LET t == propose[<<c, b>>] IN
                               /\ LastBal(c, b, self) < b
                               /\ \neg Blocked(self, c, t)
                               /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                               /\ LET ds == CmdsWithLowerT(self, c, t) \ {c} IN
                                    estimate' =           [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                <<b, [ts |-> t, status |-> "pending", deps |-> ds]>>]]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c, b>> \in DOMAIN propose
                          /\ LET t == propose[<<c, b>>] IN
                               /\ LastBal(c, b, self) < b
                               /\ \neg Blocked(self, c, t)
                               /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                               /\ LET ds == SeenCmds(self) \ {c} IN
                                    LET t2 == GT(c, TimeStamps(self)) IN
                                      estimate' =           [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                  ++ <<b, [ts |-> t2[2], status |-> "rejected", deps |-> ds]>>]]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c,b>> \in DOMAIN stable
                          /\ estimate' =         [estimate EXCEPT ![self] =
                                         [@ EXCEPT ![c] = @ ++ <<b, stable[<<c,b>>] ++ <<"status", "stable">> >>]]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c, b>> \in DOMAIN retry
                          /\  b \in DOMAIN estimate[self][c]
                             => estimate[self][c][b].status \in {"pending", "rejected"}
                          /\ LET e == retry[<<c, b>>] IN
                               LET ds == (CmdsWithLowerT(self, c, e.ts) \cup e.deps) \ {c} IN
                                 estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                             <<b, [ts |-> e.ts, status |-> "accepted", deps |-> ds]>>]]
                   /\ UNCHANGED ballot
                \/ /\ \E prop \in join:
                        LET c == prop[1] IN
                          LET b == prop[2] IN
                            /\ b > ballot[self][c]
                            /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                   /\ UNCHANGED estimate
             /\ UNCHANGED << propose, stable, retry, join >>

Next == (\E self \in C \times Ballot: leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Mar 21 16:17:22 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
