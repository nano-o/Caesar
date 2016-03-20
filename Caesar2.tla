------------------------------ MODULE Caesar2 ------------------------------

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
(* N is the number of processes, C the set of commands.                    *)
(***************************************************************************)
CONSTANTS N, MaxTime, Quorum, FastQuorum, NumBallots, NumCmds

ASSUME NumCmds \in Nat /\ NumCmds > 0

C == 0..(NumCmds-1)

ASSUME N \in Nat /\ N > 0

P ==  0..(N-1) 

Time == 1..MaxTime

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == 0..(NumBallots-1)

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourth quorums.                              *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}


(***************************************************************************)
(* An ordering relation among pairs of the form <<c, timestamp>>.  Allows  *)
(* to break ties between timestamps by also using the command to compute   *)
(* the ordering.                                                           *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

(***************************************************************************)
(* The maximum element in a set.                                           *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x >= y

(***************************************************************************)
(* A timestamp for c strictly greater than the max of the timstamps xs.    *)
(***************************************************************************)
GT(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    IN IF max[1] < c THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 

(***************************************************************************)
(* A timestamp fo c greater than or equal to the max of the timstamps xs.  *)
(***************************************************************************)
GTE(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    IN IF max[1] <= c THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
    
(***********

--algorithm Caesar {

    variables
        \* maps an acceptor p and a command c to a ballot b, indicating that the acceptor p is in ballot b for command c:
        ballot = [p \in P |-> [c \in C |-> 0]],
        \* maps an acceptor p and a command c to a map from ballot to estimate:
        estimate = [p \in P |-> [c \in C |-> <<>>]],
        \* maps a pair <<c,b>> to a timestamp t, indicating that the proposal for command c in ballot b is timestamp t:
        propose = <<>>,
        \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c has been committed in ballot b with timestamp t and dependencies ds: 
        stable = <<>>,
        \* maps a pair <<c,b>> to a timestamp t, indicating that c is to be retried in ballot b with timestamp t.
        retry = <<>>

    define {
    
        SeenCmds(p) == {c \in C : DOMAIN estimate[p][c] # {}}
        
        SeenAt(c, b, p) == b \in DOMAIN estimate[p][c]
        
        LastBal(c, p) == LET bals == DOMAIN estimate[p][c] IN
            IF bals # {}
            THEN Max(bals)
            ELSE -1
        
        MaxEstimate(c, p) == estimate[p][c][LastBal(c,p)]
        
        \* The timestamp found at p in the estimate for c in the highest ballot.
        TimeStampOf(c, p) == MaxEstimate(c,p).ts
        
        TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}
        
        CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}
        
        Pred(c, p) == MaxEstimate(c, p).pred
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
            /\ c1 \notin Pred(c2,p)
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}
        
        Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)
        
        }
 
    \* Models a the leader of ballot b for command c making a proposal.
    macro Propose(c, b, t) {
        assert b \in Ballot /\ t \in Nat /\ c \in C;
        \* has not been proposed before in this ballot:
        when \neg <<c,b>> \in DOMAIN propose;
        propose := propose ++ <<<<c,b>>, t>>
    }

    \* Models replying to a proposal with an ACK message.  
    macro AckPropose(p) {
        with (c \in C; bal = ballot[p][c]) { 
            when <<c, bal>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            with (t = propose[<<c, bal>>]) {
                when LastBal(c,p) < bal; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                when \forall c2 \in SeenCmds(p) : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with ( ds = CmdsWithLowerT(p, c, t) ) { \* Collect all commands with a lower timestamp.
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<bal, [ts |-> t, status |-> "pending", pred |-> ds]>>]];
                }
            }
        }
    }
    
    \* Models replying to a proposal with an ACK message.  
    macro RejectPropose(p) {
        with (c \in C; b = ballot[p][c]) {
            when <<c, b>> \in DOMAIN propose; \* Only reply for a proposal in the current ballot.
            with (t = propose[<<c, b>>]) {
                when LastBal(c,p) < b; \* p has not participated yet in this ballot.
                when \neg Blocked(self, c, t); \* No higher-timestamped command is blocking c.
                when \exists c2 \in SeenCmds(p) : Conflicts(p, c, t, c2); \* There is a conflict.
                with (  ds = SeenCmds(p); t2 = GT(c, TimeStamps(p)) ) { \* Collect all commands received so far; compute a strict upper bound on their timestamp.
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<b, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>]];
                }
            }
        }
    }
    
    macro Retry(c, b) {
        with (q \in Quorum) {
            when <<c,b>> \notin DOMAIN retry;
            when \A p2 \in q : SeenAt(c, b, p2); \* p2 has seen c in ballot b.
            when \E p2 \in q : estimate[p2][c][b].status = "rejected";
            with (ds = UNION {estimate[p2][c][b].pred : p2 \in q}, t = GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q})) {
                retry := retry ++ <<<<c,b>>, t[2]>>;
            }
        }
    }
    
    macro RetryAck(p) {
        with (c \in C, b = ballot[p][c]) {
            when <<c, b>> \in DOMAIN retry;
            when b \in DOMAIN estimate[p][c] => estimate[p][c][b].status \in {"pending", "rejected"}; \* Only reply if p has not seen c in b or has it pending or rejected in b. 
            with (t = retry[<<c, b>>]; ds = CmdsWithLowerT(p, c, t) ) {
                estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<b, [ts |-> t, status |-> "accepted", pred |-> ds]>>]];
            }
        }
    }
    
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN estimate[p][c] /\ estimate[p][c][b].status = "pending";
            with (  ds = UNION {estimate[p][c][b].pred : p \in q};
                    t = propose[<<c,b>>] ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>;
            }
        }
    }
     
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "accepted";
            with (  ds = UNION {estimate[p2][c].pred : p2 \in q} \ {c};
                    t = retry[<<c,b>>].ts ) {
                stable := stable ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>;
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
    
    \* Start recovery
    macro StartBallot(c, b) {
        when b > 0;
        when \E b2 \in Ballot : <<c,b2>> \in DOMAIN propose;
        recover := recover \cup {<<c,b>>};
    }
    
    macro JoinBallot(p) {
        with (l \in recover; c = l[1], b = l[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
            when c \in DOMAIN estimate[p] => estimate[p][c].status \notin RecoveryStatus;
            if (c \in DOMAIN estimate[p]) 
                estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = [@ EXCEPT !.status = "recovery-" \o estimate[p][c].status]]];
            \* Do not add c to the domain of estimate if it has not been seen, as otherwise we would need to respect the waiting condition.
        }
    }
    
    \* TODO: in the recovery we should use only the information of the highest ballot among the quorum received!
    \* For that we also need to know the last ballot in which an acceptor participated prior to joining its current ballot.
    
    macro  RecoverAccepted(c, b) {
        with (q \in Quorum; p \in q) {
            when \A p2 \in q : ballot[p2][c] = b;
            when \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p] 
                /\ estimate[p][c].status = "recovery-stable");
            when ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-accepted";
            with (info = estimate[p][c]; t = info.ts; ds = info.pred) {
                retry := retry ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>;
            }
        }
    }
    
    macro  RecoverRejected(c, b) {
        with (q \in Quorum; p \in q) { 
            when \A p2 \in q : ballot[p2][c] = b;
            when \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p] 
                /\ estimate[p][c].status \in {"recovery-accepted", "recovery-stable"});
            when ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-rejected";
            with (t \in Time) { \* use an arbitrary timestamp.
                Propose(c, b, t); 
            }
        }
    }
        
    macro  RecoverPending(c, b) {  
        with (q \in Quorum; p \in q) {
            when \A p2 \in q : ballot[p2][c] = b;
            when \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p] 
                /\ estimate[p][c].status \in {"recovery-accepted","recovery-rejected", "recovery-stable"});
            when ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-pending";
            Propose(c, b, estimate[p][c].ts); 
        }
    }
    
    macro  RecoverNotSeenCmds(c, b) { \* TODO: something's wrong, but what?
        with (q \in Quorum; p \in q) {
            when \A p2 \in q : ballot[p2][c] = b;
            when <<c,b>> \in recover /\ c \notin DOMAIN estimate[p]; \* This tells us that p is in recovery mode but has not seen c before.
            when \A p2 \in q : \neg (c \in DOMAIN estimate[p] 
                /\ estimate[p][c].status \in {"recovery-accepted","recovery-rejected", "recovery-pending", "recovery-stable"});
            with (t \in Time) {
                Propose(c, b, t); 
            }
        }
    }
  
    process (leader \in C \times Ballot) {
        ldr:    while (TRUE) {
                    with (c = self[1], b = self[2]) {
                        either {
                            with (t \in Time) { \* use an arbitrary timestamp.
                                Propose(c, 0, t); \* Always propose in ballot 0.
                            }
                        } or {
                            FastDecision(c, b);
                        } or {
                            Retry(c, b);
                        } (* or {
                            SlowDecision(c, b);
                        } or {
                            StartBallot(c, b);
                        } or {
                            RecoverAccepted(c, b);
                        } or {
                            RecoverRejected(c, b);
                        } or {
                            RecoverPending(c, b);
                        } or {
                            RecoverNotSeenCmds(c, b);
                        } *)
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
                    } (* or {
                        JoinBallot(self);
                    } *)
                }
    }
    
}

*) 
\* BEGIN TRANSLATION
\* Label acc of process acc at line 309 col 17 changed to acc_
VARIABLES ballot, estimate, propose, stable, retry

(* define statement *)
SeenCmds(p) == {c \in C : DOMAIN estimate[p][c] # {}}

SeenAt(c, b, p) == b \in DOMAIN estimate[p][c]

LastBal(c, p) == LET bals == DOMAIN estimate[p][c] IN
    IF bals # {}
    THEN Max(bals)
    ELSE -1

MaxEstimate(c, p) == estimate[p][c][LastBal(c,p)]


TimeStampOf(c, p) == MaxEstimate(c,p).ts

TimeStamps(p) == {<<c, TimeStampOf(c,p)>> : c \in SeenCmds(p)}

CmdsWithLowerT(p, c, t) == {c2 \in SeenCmds(p) : <<c2, TimeStampOf(c2,p)>> \prec <<c,t>>}

Pred(c, p) == MaxEstimate(c, p).pred

Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, TimeStampOf(c2,p)>>
    /\ c1 \notin Pred(c2,p)

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ MaxEstimate(c2,p).status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in SeenCmds(p) : Blocks(p, c, t, c2)


vars == << ballot, estimate, propose, stable, retry >>

ProcSet == (C \times Ballot) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> [c \in C |-> <<>>]]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>

leader(self) == /\ LET c == self[1] IN
                     LET b == self[2] IN
                       \/ /\ \E t \in Time:
                               /\ Assert(0 \in Ballot /\ t \in Nat /\ c \in C, 
                                         "Failure of assertion at line 126, column 9 of macro called at line 285, column 33.")
                               /\ \neg <<c,0>> \in DOMAIN propose
                               /\ propose' = propose ++ <<<<c,0>>, t>>
                          /\ UNCHANGED <<stable, retry>>
                       \/ /\ \E q \in FastQuorum:
                               /\ \A p \in q : b \in DOMAIN estimate[p][c] /\ estimate[p][c][b].status = "pending"
                               /\ LET ds == UNION {estimate[p][c][b].pred : p \in q} IN
                                    LET t == propose[<<c,b>>] IN
                                      stable' = stable ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, retry>>
                       \/ /\ \E q \in Quorum:
                               /\ <<c,b>> \notin DOMAIN retry
                               /\ \A p2 \in q : SeenAt(c, b, p2)
                               /\ \E p2 \in q : estimate[p2][c][b].status = "rejected"
                               /\ LET ds == UNION {estimate[p2][c][b].pred : p2 \in q} IN
                                    LET t == GTE(c, {<<c, estimate[p2][c][b].ts>> : p2 \in q}) IN
                                      retry' = retry ++ <<<<c,b>>, t[2]>>
                          /\ UNCHANGED <<propose, stable>>
                /\ UNCHANGED << ballot, estimate >>

acc(self) == /\ \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          /\ <<c, bal>> \in DOMAIN propose
                          /\ LET t == propose[<<c, bal>>] IN
                               /\ LastBal(c,self) < bal
                               /\ \neg Blocked(self, c, t)
                               /\ \forall c2 \in SeenCmds(self) : \neg Conflicts(self, c, t, c2)
                               /\ LET ds == CmdsWithLowerT(self, c, t) IN
                                    estimate' = [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<bal, [ts |-> t, status |-> "pending", pred |-> ds]>>]]
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c, b>> \in DOMAIN propose
                          /\ LET t == propose[<<c, b>>] IN
                               /\ LastBal(c,self) < b
                               /\ \neg Blocked(self, c, t)
                               /\ \exists c2 \in SeenCmds(self) : Conflicts(self, c, t, c2)
                               /\ LET ds == SeenCmds(self) IN
                                    LET t2 == GT(c, TimeStamps(self)) IN
                                      estimate' = [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>]]
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c,b>> \in DOMAIN stable
                          /\ estimate' =         [estimate EXCEPT ![self] =
                                         [@ EXCEPT ![c] = @ ++ <<b, stable[<<c,b>>] ++ <<"status", "stable">> >>]]
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c, b>> \in DOMAIN retry
                          /\ b \in DOMAIN estimate[self][c] => estimate[self][c][b].status \in {"pending", "rejected"}
                          /\ LET t == retry[<<c, b>>] IN
                               LET ds == CmdsWithLowerT(self, c, t) IN
                                 estimate' = [estimate EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<b, [ts |-> t, status |-> "accepted", pred |-> ds]>>]]
             /\ UNCHANGED << ballot, propose, stable, retry >>

Next == (\E self \in C \times Ballot: leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
   
Status == {"pending", "stable", "accepted", "rejected"}

CmdInfo == [ts : Nat, pred : SUBSET C]
CmdInfoWithStat == [ts : Nat, pred : SUBSET C, status: Status]

(***************************************************************************)
(* An invariant describing the type of the different variables.  Note that *)
(* we extensively use maps (also called functions) keyed by commands.  The *)
(* set of keys of a map m is noted DOMAIN m.                               *)
(***************************************************************************)
TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : estimate[p][c] \in [D -> CmdInfoWithStat]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Nat]
    /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> Nat]
    /\  \E D \in SUBSET (C \times Ballot) : stable \in [D -> CmdInfo]
    
(***************************************************************************)
(* A simple invariant.                                                     *)
(***************************************************************************)
Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c,p)

(***************************************************************************)
(* This invariant must hold for the execution phase (not formalized here)  *)
(* to be correct.                                                          *)
(***************************************************************************)
GraphInvariant == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ <<c1, stable[c1].ts>> \prec <<c2, stable[c2].ts>> =>
    c1 \in stable[c2].pred

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
        /\  \A c2 \in stable[<<c,b>>].pred : 
            /\  \E s2 \in DOMAIN stable : 
                /\  s2[1] = c2
                /\  (<<c2, stable[s2].ts>> \prec <<c, stable[s].ts>> => Executable(s2))

StableTimeStamps == { info.ts : info \in Image(stable) }

TimeStamp(c) == CHOOSE ts \in StableTimeStamps : \E s \in DOMAIN stable :
    s[1] = c /\ stable[s].ts = ts

RealDeps(c, t, ds) ==
        {d \in ds : <<d,TimeStamp(d)>> \prec <<c,t>> }

(***************************************************************************)
(* If a command c is made stable in two different ballots, then its        *)
(* timestamp and dependencies are the same in both.                        *)
(***************************************************************************)
Agreement == \A c \in C : \A s1, s2 \in DOMAIN stable : 
    Executable(s1) /\ Executable(s2) /\ s1[1] = c /\ s2[1] = c 
        =>  /\  stable[s1].ts = stable[s2].ts
            /\  RealDeps(c, TimeStamp(c), stable[s1].pred) = RealDeps(c, TimeStamp(c), stable[s2].pred) 

WeakAgreement == \A c \in C : \A s1, s2 \in DOMAIN stable : 
    s1[1] = c /\ s2[1] = c => stable[s1].ts = stable[s2].ts

=============================================================================
\* Modification History
\* Last modified Sun Mar 20 13:18:36 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
