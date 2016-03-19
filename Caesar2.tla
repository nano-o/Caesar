------------------------------ MODULE Caesar2 ------------------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences

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
(* An ordering relation among pairs of the form <<c, timestamp>>           *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

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
        ballot = [p \in P |-> [c \in C |-> 0]], \* map an acceptor p to a command c to a ballot b, indicating that the acceptor p is in ballot b for command c.
        estimate = [p \in P |-> <<>>], \* maps an acceptor p and a command c to the estimate of acceptor p for command c in ballot ballot[p][c].
        propose = <<>>, \* maps a pair <<c,b>> to a timestamp t, indicating that the proposal for command c in ballot b is timestamp t.
        stable = <<>>, \* maps a command c and a ballot b to a set of dependencies ds and a timestamp t, indicating that c has been committed in ballot b with timestamp t and dependencies ds. 
        retry = <<>>, \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c is to be retried with timestamp t and dependencies ds.
        recover = {} \* a set of pairs <<c,b>>. When <<c,v>> \in recover, it means that start-recovery messages have been sent for c in ballot b.  

    define {
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, estimate[p][c2].ts>>
            /\ c1 \notin estimate[p][c2].pred
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ estimate[p][c2].status \notin {"stable","accepted", "recovery-stable", "recovery-accepted"}
        
        Blocked(p, c, t) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c, t, c2)
        
        \* A timestamp (of the form <<c,t>>) greater than the greatest timestamp seen by p. 
        GTReceived(p, c) == 
            LET ts == {<<c2, estimate[p][c2].ts>> : c2 \in DOMAIN estimate[p]}
            IN GT(c, ts)
        
        CmdsWithLowerT(p, c, t) == {c2 \in DOMAIN estimate[p] : <<c2, estimate[p][c2].ts>> \prec <<c,t>>}
        
        RecoveryStatus == {"recovery-pending", "recovery-rejected", "recovery-stable", "recovery-accepted"}
        
        }
 
    \* Models making a proposal in a ballot.
    macro Propose(c, b, t) {
        \* has not been proposed before in this ballot:
        when \neg <<c,b>> \in DOMAIN propose;
        propose := propose ++ <<<<c,b>>, t>>
    }

    \* Models replying to a proposal with an ACK message.  
    macro AckPropose(p) {
        with (c \in C; bal = ballot[p][c]) {
            when <<c, bal>> \in DOMAIN propose;
            with (t = propose[<<c, ballot[p][c]>>]) {
                when c \in DOMAIN estimate[p] => estimate[p][c].status \in RecoveryStatus;
                when \neg Blocked(self, c, t);
                when \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with ( ds = CmdsWithLowerT(p, c, t) ) { 
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>];
                }
            }
        }
    }
    
    \* Models replying to a proposal with an ACK message.  
    macro RejectPropose(p) {
        with (c \in C; bal = ballot[p][c]) {
            when <<c, bal>> \in DOMAIN propose;
            with (t = propose[<<c, ballot[p][c]>>]) {
                when c \in DOMAIN estimate[p] => estimate[p][c].status \in RecoveryStatus;
                when \neg Blocked(self, c, t);
                when \exists c2 \in DOMAIN estimate[p] : Conflicts(p, c, t, c2); \* There is a conflict.
                with (  ds = DOMAIN estimate[p]; t2 = GTReceived(p, c) ) {
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>];
                }
            }
        }
    }
    
    macro Retry(c, b) {
        with (q \in Quorum) {
            when <<c,b>> \notin DOMAIN retry;
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2];
            when \E p2 \in q : estimate[p2][c].status = "rejected";
            with (ds = UNION {estimate[p2][c].pred : p2 \in q}, t = GTE(c, {<<c, estimate[p2][c].ts>> : p2 \in q})) {
                retry := retry ++ <<<<c,b>>, [ts |-> t[2], pred |-> ds]>>;
            }
        }
    }
    
    macro RetryAck(p) {
        with (c \in C) {
            with (bal = ballot[p][c]) {
                when <<c, bal>> \in DOMAIN retry;
                when c \in DOMAIN estimate[p] => estimate[p][c].status \in {"pending", "rejected"};
                with (info = retry[<<c, ballot[p][c]>>]; t = info.ts; ds = info.pred \cup CmdsWithLowerT(p, c, t) ) {
                    estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t, status |-> "accepted", pred |-> ds]>>];
                }
            }
        }
    }
    
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "pending";
            with (  ds = UNION {estimate[p2][c].pred : p2 \in q} \ {c};
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
        with (c \in C) {
            with (b = ballot[p][c]) {
                when <<c,b>> \in DOMAIN stable;
                estimate := [estimate EXCEPT ![p] = 
                    @ ++ <<c, stable[<<c,b>>] ++ <<"status", "stable">> >>];
            }
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
    
    macro  RecoverNotSeen(c, b) {
        with (q \in Quorum; p \in q) {
            when \A p2 \in q : ballot[p2][c] = b;
            when \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p] 
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
                        } or {
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
\* Label acc of process acc at line 288 col 17 changed to acc_
VARIABLES ballot, estimate, propose, stable, retry, recover

(* define statement *)
Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, estimate[p][c2].ts>>
    /\ c1 \notin estimate[p][c2].pred

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ estimate[p][c2].status \notin {"stable","accepted", "recovery-stable", "recovery-accepted"}

Blocked(p, c, t) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c, t, c2)


GTReceived(p, c) ==
    LET ts == {<<c2, estimate[p][c2].ts>> : c2 \in DOMAIN estimate[p]}
    IN GT(c, ts)

CmdsWithLowerT(p, c, t) == {c2 \in DOMAIN estimate[p] : <<c2, estimate[p][c2].ts>> \prec <<c,t>>}

RecoveryStatus == {"recovery-pending", "recovery-rejected", "recovery-stable", "recovery-accepted"}


vars == << ballot, estimate, propose, stable, retry, recover >>

ProcSet == (C \times Ballot) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> <<>>]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>
        /\ recover = {}

leader(self) == /\ LET c == self[1] IN
                     LET b == self[2] IN
                       \/ /\ \E t \in Time:
                               /\ \neg <<c,0>> \in DOMAIN propose
                               /\ propose' = propose ++ <<<<c,0>>, t>>
                          /\ UNCHANGED <<stable, retry, recover>>
                       \/ /\ \E q \in FastQuorum:
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "pending"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} \ {c} IN
                                    LET t == propose[<<c,b>>] IN
                                      stable' = stable ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, retry, recover>>
                       \/ /\ \E q \in Quorum:
                               /\ <<c,b>> \notin DOMAIN retry
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2]
                               /\ \E p2 \in q : estimate[p2][c].status = "rejected"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} IN
                                    LET t == GTE(c, {<<c, estimate[p2][c].ts>> : p2 \in q}) IN
                                      retry' = retry ++ <<<<c,b>>, [ts |-> t[2], pred |-> ds]>>
                          /\ UNCHANGED <<propose, stable, recover>>
                       \/ /\ \E q \in Quorum:
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "accepted"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} \ {c} IN
                                    LET t == retry[<<c,b>>].ts IN
                                      stable' = stable ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, retry, recover>>
                       \/ /\ b > 0
                          /\ \E b2 \in Ballot : <<c,b2>> \in DOMAIN propose
                          /\ recover' = (recover \cup {<<c,b>>})
                          /\ UNCHANGED <<propose, stable, retry>>
                       \/ /\ \E q \in Quorum:
                               \E p \in q:
                                 /\ \A p2 \in q : ballot[p2][c] = b
                                 /\  \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p]
                                    /\ estimate[p][c].status = "recovery-stable")
                                 /\ ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-accepted"
                                 /\ LET info == estimate[p][c] IN
                                      LET t == info.ts IN
                                        LET ds == info.pred IN
                                          retry' = retry ++ <<<<c,b>>, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, stable, recover>>
                       \/ /\ \E q \in Quorum:
                               \E p \in q:
                                 /\ \A p2 \in q : ballot[p2][c] = b
                                 /\  \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p]
                                    /\ estimate[p][c].status \in {"recovery-accepted", "recovery-stable"})
                                 /\ ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-rejected"
                                 /\ \E t \in Time:
                                      /\ \neg <<c,b>> \in DOMAIN propose
                                      /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry, recover>>
                       \/ /\ \E q \in Quorum:
                               \E p \in q:
                                 /\ \A p2 \in q : ballot[p2][c] = b
                                 /\  \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p]
                                    /\ estimate[p][c].status \in {"recovery-accepted","recovery-rejected", "recovery-stable"})
                                 /\ ballot[p][c] = b /\ c \in DOMAIN estimate[p] /\ estimate[p][c].status = "recovery-pending"
                                 /\ \neg <<c,b>> \in DOMAIN propose
                                 /\ propose' = propose ++ <<<<c,b>>, (estimate[p][c].ts)>>
                          /\ UNCHANGED <<stable, retry, recover>>
                       \/ /\ \E q \in Quorum:
                               \E p \in q:
                                 /\ \A p2 \in q : ballot[p2][c] = b
                                 /\  \A p2 \in q : \neg (ballot[p][c] = b /\ c \in DOMAIN estimate[p]
                                    /\ estimate[p][c].status \in {"recovery-accepted","recovery-rejected", "recovery-pending", "recovery-stable"})
                                 /\ \E t \in Time:
                                      /\ \neg <<c,b>> \in DOMAIN propose
                                      /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry, recover>>
                /\ UNCHANGED << ballot, estimate >>

acc(self) == /\ \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          /\ <<c, bal>> \in DOMAIN propose
                          /\ LET t == propose[<<c, ballot[self][c]>>] IN
                               /\ c \in DOMAIN estimate[self] => estimate[self][c].status \in RecoveryStatus
                               /\ \neg Blocked(self, c, t)
                               /\ \forall c2 \in DOMAIN estimate[self] : \neg Conflicts(self, c, t, c2)
                               /\ LET ds == CmdsWithLowerT(self, c, t) IN
                                    estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          /\ <<c, bal>> \in DOMAIN propose
                          /\ LET t == propose[<<c, ballot[self][c]>>] IN
                               /\ c \in DOMAIN estimate[self] => estimate[self][c].status \in RecoveryStatus
                               /\ \neg Blocked(self, c, t)
                               /\ \exists c2 \in DOMAIN estimate[self] : Conflicts(self, c, t, c2)
                               /\ LET ds == DOMAIN estimate[self] IN
                                    LET t2 == GTReceived(self, c) IN
                                      estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET b == ballot[self][c] IN
                          /\ <<c,b>> \in DOMAIN stable
                          /\ estimate' =         [estimate EXCEPT ![self] =
                                         @ ++ <<c, stable[<<c,b>>] ++ <<"status", "stable">> >>]
                   /\ UNCHANGED ballot
                \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          /\ <<c, bal>> \in DOMAIN retry
                          /\ c \in DOMAIN estimate[self] => estimate[self][c].status \in {"pending", "rejected"}
                          /\ LET info == retry[<<c, ballot[self][c]>>] IN
                               LET t == info.ts IN
                                 LET ds == info.pred \cup CmdsWithLowerT(self, c, t) IN
                                   estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t, status |-> "accepted", pred |-> ds]>>]
                   /\ UNCHANGED ballot
                \/ /\ \E l \in recover:
                        LET c == l[1] IN
                          LET b == l[2] IN
                            /\ b > ballot[self][c]
                            /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                            /\ c \in DOMAIN estimate[self] => estimate[self][c].status \notin RecoveryStatus
                            /\ IF c \in DOMAIN estimate[self]
                                  THEN /\ estimate' = [estimate EXCEPT ![self] = [@ EXCEPT ![c] = [@ EXCEPT !.status = "recovery-" \o estimate[self][c].status]]]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED estimate
             /\ UNCHANGED << propose, stable, retry, recover >>

Next == (\E self \in C \times Ballot: leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
   
Status == {"pending", "stable", "accepted", "rejected"} \cup RecoveryStatus

CmdInfo == [ts : Nat, pred : SUBSET C]
CmdInfoWithStat == [ts : Nat, pred : SUBSET C, status: Status]

(***************************************************************************)
(* An invariant describing the type of the different variables.  Note that *)
(* we extensively use maps (also called functions) keyed by commands.  The *)
(* set of keys of a map m is noted DOMAIN m.                               *)
(***************************************************************************)
TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P : \E D \in SUBSET C : estimate[p] \in [D -> CmdInfoWithStat \union {<<>>}]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Time]
    /\  \E D \in SUBSET C : stable \in [D -> CmdInfo]
    /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> CmdInfo]
    /\  recover \in SUBSET (C \times (Ballot \ {0}))

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
\* Last modified Sat Mar 19 18:24:13 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
