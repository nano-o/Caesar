------------------------------ MODULE Caesar3 ------------------------------

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
        \* maps an acceptor p, a command c, and a ballot to a timestamp and a status:
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
        join = {},
        \* maps an acceptor p and a command to a set of dependencies.
        deps = [p \in P |-> <<>>]

    define {
        
        Status == {"pending", "stable", "accepted", "rejected"}
        
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : estimate[p][c] \in [D -> [ts : Nat, status : Status]]
            /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Nat]
            /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> [ts : Nat, deps : SUBSET C]]
            /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
            /\  join \subseteq (C \times Ballot)
            /\  \A p \in P : \E D \in SUBSET C : deps[p] \in [D -> SUBSET C]
    
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == DOMAIN deps[p]
        
        \* A sanity check
        Inv3 == \A p \in P :
            DOMAIN deps[p] = {c \in C : DOMAIN estimate[p][c] # {}}
        
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
        
        TimeStamps(p) == {<<c, MaxEstimate(c,p).ts>> : c \in SeenCmds(p)}
        
        \* All the commands at p which have a lower timestamp than <<c,t>>
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, MaxEstimate(c2,p).ts>> \prec <<c,t>>}
        
        ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, MaxEstimate(c2,p).ts>>
            /\ c1 \notin deps[p][c2]
        
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
    macro Propose(c, b, t) {
        \* has not been proposed before in this ballot:
        when <<c,b>> \notin DOMAIN propose;
        propose := propose ++ <<<<c,b>>, t>>
    }
    
    \* Models replying to a proposal with an ACK message.
    macro Phase1Reply(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]]; \* Join the ballot if in a lower ballot.
            with (t = propose[<<c, b>>]) {
                when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                either {
                    when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                    with ( ds = CmdsWithLowerT(p, c, t) \ {c} ) { \* Collect all commands with a lower timestamp.
                      \* Add the command to the local deps (or overwrite if existing):
                      deps := [deps EXCEPT ![p] = @ ++ <<c, ds>>];
                      \* set the command as pending:
                      estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t, status |-> "pending"]>>]];
                    }
                } or {
                    when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                    \* Collect all commands received so far; compute a strict upper bound on their timestamp:
                    with (  ds = SeenCmds(p) \ {c}; t2 = GT(c, TimeStamps(p)) ) {
                      \* Add the command to the local deps (or overwrite if existing):
                      deps := [deps EXCEPT ![p] = @ ++ <<c, ds>>];
                      \* set the command as rejected:
                      estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @
                        ++ <<b, [ts |-> t2[2], status |-> "rejected"]>>]];
                    }
                }
            }
        }
    }
        
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] 
                /\ estimate[p][c][b].status = "pending";
            with (  ds = UNION {deps[p][c] : p \in q};
                    t = propose[<<c,b>>] ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>;
            }
        }
    }
        
    macro Phase2(c, b) {
        with (q \in Quorum) {
            when \A p2 \in q : SeenAt(c, b, p2); \* all acceptors in q have seen c in ballot b.
            either {
                \* The leader receive a "reject" message.
                when \E p2 \in q : estimate[p2][c][b].status = "rejected";
                with (ds = UNION {deps[p2][c] : p2 \in q}, 
                        t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) {
                    retry := retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                }
            } or {    
                \* The leader triggers the slow path because it timed-out waiting for a fast quorum,
                \* and it did not receive any "rejected" response to its proposal.
                when \A p2 \in q : estimate[p2][c][b].status = "pending";
                with (ds = UNION {deps[p2][c] : p2 \in q}, 
                        t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) { \* greater than has no effet. Do we need strictly greater?
                    retry := retry ++ <<<<c,b>>, [ts |-> t[2], deps |-> ds]>>;
                }
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; b \in Ballot) { 
            when b >= ballot[p][c];
            when <<c, b>> \in DOMAIN retry;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            \* Only reply if p has not seen c in b or has it pending or rejected in b:
            when b \in DOMAIN estimate[p][c] 
                => estimate[p][c][b].status \in {"pending", "rejected"};  
            with (e = retry[<<c, b>>]; seen = (CmdsWithLowerT(p, c, e.ts) \cup e.deps) \ {c}) { \* TODO: do we need the union with the local dependencies?
                estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ 
                    <<b, [ts |-> e.ts, status |-> "accepted"]>>]];
                deps := [deps EXCEPT ![p] = @ ++ <<c, seen>>]; \* TODO: seen or e.deps?
            }
        }
    }
     
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] 
                /\ estimate[p][c][b].status = "accepted";
            with (  ds = UNION {deps[p][c] : p \in q};
                    t = retry[<<c,b>>].ts ) {
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
                     ts |-> s.ts]>>]];
                deps := [deps EXCEPT ![p] = @ ++ <<c, s.deps>>];
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
                                retry := retry ++ <<<<c,b>>, [ts |-> t, deps |-> ds]>>; 
                            }
                        } or {
                            \* There is one "rejected" and there is no accept or stable:
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable"}; 
                            when estimate[p][c][maxBal].status = "rejected";
                            whitelist := whitelist ++ <<<<c,b>>, C>>;
                            with (t \in Time) { \* use an arbitrary timestamp.
                                Propose(c, b, t);
                            }
                        } or {
                            \* there is one "pending" and there is no accept or stable or reject:
                            when \A p2 \in ps : estimate[p2][c][maxBal].status \notin {"accepted","stable","rejected"}; 
                            when estimate[p][c][maxBal].status = "pending";
                            with (deps = UNION {estimate[p2][c][maxBal].seen : p2 \in ps};
                                    wl = {c2 \in deps : (\A q2 \in FastQuorum : (\E p2 \in (ps \cap q2) : c2 \in estimate[p2][c][maxBal].seen))}) {
                                whitelist := whitelist ++ <<<<c,b>>, wl>>;
                            }; 
                            Propose(c, b, estimate[p][c][maxBal].ts);
                        }
                    }
                } else {
                    \* No acceptor in ps saw the command.    
                    \* In practice this should not happen if the new leader is in its received quorum. 
                    \* Could happen if recovery is triggered by a client.
                    whitelist := whitelist ++ <<<<c,b>>, C>>;
                    with (t \in Time) {
                       Propose(c, b, t); 
                    }        
                }
            }
        }
    }
    
    \* Workflow of a decision:
    procedure Decide(com, bal) {
        decide:     either  { 
        decideFast:     FastDecision(com, bal);
                        \* assert FALSE;
                    } or {
        retry:          Phase2(com, bal);
        decideSlow:     SlowDecision(com, bal);
                        return; 
                    }
    }
     
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:     either {
                        when self[2] = 0; \* In ballot 0, directly propose.
        propose0:       with (t \in Time) { Propose(self[1], 0, t) };
        decide0:        call Decide(self[1], 0); 
        decided0:       skip; 
                    } or {
                        when self[2] > 0; 
                        \* In a non-zero ballot, we first have to determine a safe value to propose in the fast or slow path:
        startBal:       skip; \* StartBallot(self[1], self[2]);
        recover:        skip; \* Recover(self[1], self[2]);
        decide:         skip; \* call Decide(self[1], self[2]); 
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
                        skip; \* JoinBallot(self);
                    }
                }
    }
    
}

*)
\* BEGIN TRANSLATION
\* Label decide of procedure Decide at line 357 col 21 changed to decide_
\* Label retry of procedure Decide at line 234 col 14 changed to retry_
\* Label leader of process leader at line 369 col 21 changed to leader_
\* Label acc of process acc at line 386 col 17 changed to acc_
CONSTANT defaultInitValue
VARIABLES ballot, estimate, propose, stable, retry, join, deps, pc, stack

(* define statement *)
Status == {"pending", "stable", "accepted", "rejected"}

TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : estimate[p][c] \in [D -> [ts : Nat, status : Status]]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Nat]
    /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> [ts : Nat, deps : SUBSET C]]
    /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> [ts : Nat, deps : SUBSET C]]
    /\  join \subseteq (C \times Ballot)
    /\  \A p \in P : \E D \in SUBSET C : deps[p] \in [D -> SUBSET C]


SeenCmds(p) == DOMAIN deps[p]


Inv3 == \A p \in P :
    DOMAIN deps[p] = {c \in C : DOMAIN estimate[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN estimate[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN estimate[p][c] : b <= max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE -1


MaxEstimate(c, p) == estimate[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b-1, p) : p \in q}
    IN Max(bals)

TimeStamps(p) == {<<c, MaxEstimate(c,p).ts>> : c \in SeenCmds(p)}


CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, MaxEstimate(c2,p).ts>> \prec <<c,t>>}

ParticipatedIn(b, c, p) == b \in DOMAIN estimate[p][c]

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, MaxEstimate(c2,p).ts>>
    /\ c1 \notin deps[p][c2]

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)




Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)

Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in DOMAIN propose => <<c,b>> \in join






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

VARIABLES com, bal

vars == << ballot, estimate, propose, stable, retry, join, deps, pc, stack, 
           com, bal >>

ProcSet == ((C \times Ballot)) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>
        /\ join = {}
        /\ deps = [p \in P |-> <<>>]
        (* Procedure Decide *)
        /\ com = [ self \in ProcSet |-> defaultInitValue]
        /\ bal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times Ballot) -> "leader_"
                                        [] self \in P -> "acc_"]

decide_(self) == /\ pc[self] = "decide_"
                 /\ \/ /\ pc' = [pc EXCEPT ![self] = "decideFast"]
                    \/ /\ pc' = [pc EXCEPT ![self] = "retry_"]
                 /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                 join, deps, stack, com, bal >>

decideFast(self) == /\ pc[self] = "decideFast"
                    /\ \E q \in FastQuorum:
                         /\  \A p \in q : bal[self] \in DOMAIN estimate[p][com[self]]
                            /\ estimate[p][com[self]][bal[self]].status = "pending"
                         /\ LET ds == UNION {deps[p][com[self]] : p \in q} IN
                              LET t == propose[<<com[self],bal[self]>>] IN
                                stable' = stable ++ <<<<com[self],bal[self]>>, [ts |-> t, deps |-> ds]>>
                    /\ pc' = [pc EXCEPT ![self] = "Error"]
                    /\ UNCHANGED << ballot, estimate, propose, retry, join, 
                                    deps, stack, com, bal >>

retry_(self) == /\ pc[self] = "retry_"
                /\ \E q \in Quorum:
                     /\ \A p2 \in q : SeenAt(com[self], bal[self], p2)
                     /\ \/ /\ \E p2 \in q : estimate[p2][com[self]][bal[self]].status = "rejected"
                           /\ LET ds == UNION {deps[p2][com[self]] : p2 \in q} IN
                                LET t == GTE(com[self], {<<com[self], estimate[p2][com[self]][bal[self]].ts>> : p2 \in q}) IN
                                  retry' = retry ++ <<<<com[self],bal[self]>>, [ts |-> t[2], deps |-> ds]>>
                        \/ /\ \A p2 \in q : estimate[p2][com[self]][bal[self]].status = "pending"
                           /\ LET ds == UNION {deps[p2][com[self]] : p2 \in q} IN
                                LET t == GTE(com[self], {<<com[self], estimate[p2][com[self]][bal[self]].ts>> : p2 \in q}) IN
                                  retry' = retry ++ <<<<com[self],bal[self]>>, [ts |-> t[2], deps |-> ds]>>
                /\ pc' = [pc EXCEPT ![self] = "decideSlow"]
                /\ UNCHANGED << ballot, estimate, propose, stable, join, deps, 
                                stack, com, bal >>

decideSlow(self) == /\ pc[self] = "decideSlow"
                    /\ \E q \in Quorum:
                         /\  \A p \in q : bal[self] \in DOMAIN estimate[p][com[self]]
                            /\ estimate[p][com[self]][bal[self]].status = "accepted"
                         /\ LET ds == UNION {deps[p][com[self]] : p \in q} IN
                              LET t == retry[<<com[self],bal[self]>>].ts IN
                                stable' = stable ++ <<<<com[self],bal[self]>>, [ts |-> t, deps |-> ds]>>
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ com' = [com EXCEPT ![self] = Head(stack[self]).com]
                    /\ bal' = [bal EXCEPT ![self] = Head(stack[self]).bal]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << ballot, estimate, propose, retry, join, 
                                    deps >>

Decide(self) == decide_(self) \/ decideFast(self) \/ retry_(self)
                   \/ decideSlow(self)

leader_(self) == /\ pc[self] = "leader_"
                 /\ \/ /\ self[2] = 0
                       /\ pc' = [pc EXCEPT ![self] = "propose0"]
                    \/ /\ self[2] > 0
                       /\ pc' = [pc EXCEPT ![self] = "startBal"]
                 /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                 join, deps, stack, com, bal >>

propose0(self) == /\ pc[self] = "propose0"
                  /\ \E t \in Time:
                       /\ <<(self[1]),0>> \notin DOMAIN propose
                       /\ propose' = propose ++ <<<<(self[1]),0>>, t>>
                  /\ pc' = [pc EXCEPT ![self] = "decide0"]
                  /\ UNCHANGED << ballot, estimate, stable, retry, join, deps, 
                                  stack, com, bal >>

decide0(self) == /\ pc[self] = "decide0"
                 /\ /\ bal' = [bal EXCEPT ![self] = 0]
                    /\ com' = [com EXCEPT ![self] = self[1]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Decide",
                                                             pc        |->  "decided0",
                                                             com       |->  com[self],
                                                             bal       |->  bal[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "decide_"]
                 /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                 join, deps >>

decided0(self) == /\ pc[self] = "decided0"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                  join, deps, stack, com, bal >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                  join, deps, stack, com, bal >>

recover(self) == /\ pc[self] = "recover"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "decide"]
                 /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                 join, deps, stack, com, bal >>

decide(self) == /\ pc[self] = "decide"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "decided"]
                /\ UNCHANGED << ballot, estimate, propose, stable, retry, join, 
                                deps, stack, com, bal >>

decided(self) == /\ pc[self] = "decided"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, estimate, propose, stable, retry, 
                                 join, deps, stack, com, bal >>

leader(self) == leader_(self) \/ propose0(self) \/ decide0(self)
                   \/ decided0(self) \/ startBal(self) \/ recover(self)
                   \/ decide(self) \/ decided(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c, b>> \in DOMAIN propose
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET t == propose[<<c, b>>] IN
                                /\ LastBal(c, b, self) < b
                                /\ \neg Blocked(self, c, t)
                                /\ \/ /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                                      /\ LET ds == CmdsWithLowerT(self, c, t) \ {c} IN
                                           /\ deps' = [deps EXCEPT ![self] = @ ++ <<c, ds>>]
                                           /\ estimate' =           [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                          ++ <<b, [ts |-> t, status |-> "pending"]>>]]
                                   \/ /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                                      /\ LET ds == SeenCmds(self) \ {c} IN
                                           LET t2 == GT(c, TimeStamps(self)) IN
                                             /\ deps' = [deps EXCEPT ![self] = @ ++ <<c, ds>>]
                                             /\ estimate' =           [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @
                                                            ++ <<b, [ts |-> t2[2], status |-> "rejected"]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c,b>> \in DOMAIN stable
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LET s == stable[<<c,b>>] IN
                                /\ estimate' =         [estimate EXCEPT ![self] =
                                               [@ EXCEPT ![c] = @ ++ <<b, [status |-> "stable",
                                                ts |-> s.ts]>>]]
                                /\ deps' = [deps EXCEPT ![self] = @ ++ <<c, s.deps>>]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ b >= ballot[self][c]
                           /\ <<c, b>> \in DOMAIN retry
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\  b \in DOMAIN estimate[self][c]
                              => estimate[self][c][b].status \in {"pending", "rejected"}
                           /\ LET e == retry[<<c, b>>] IN
                                LET seen == (CmdsWithLowerT(self, c, e.ts) \cup e.deps) \ {c} IN
                                  /\ estimate' =         [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++
                                                 <<b, [ts |-> e.ts, status |-> "accepted"]>>]]
                                  /\ deps' = [deps EXCEPT ![self] = @ ++ <<c, seen>>]
                 \/ /\ TRUE
                    /\ UNCHANGED <<ballot, estimate, deps>>
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << propose, stable, retry, join, stack, com, bal >>

acc(self) == acc_(self)

Next == (\E self \in ProcSet: Decide(self))
           \/ (\E self \in (C \times Ballot): leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Mar 27 19:44:29 EDT 2016 by nano
\* Created Sun Mar 27 18:34:05 EDT 2016 by nano
