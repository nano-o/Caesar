---------------------------- MODULE EPaxosLight ----------------------------

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
(* Ballots are of the form <<b,i>>, where b is the main ballot number and  *)
(* i the sub-ballot number.  Ballots can be compared:                      *)
(***************************************************************************)
bal1 \prec bal2 == 
    IF bal1[1] = bal2[1]
    THEN bal1[2] < bal2[2]
    ELSE bal1[1] < bal2[1]

bal1 \preceq bal2 ==
    bal1 \prec bal2 \/ bal1 = bal2

(***************************************************************************)
(* P is the set of acceptors.  MaxTime bounds the timestamp that can be    *)
(* assigned to proposals, but not to retries.  CmdId(c) must assign a      *)
(* natural number to a command.  It is used to break time in timestamps.   *)
(***************************************************************************)
CONSTANTS P, Quorum, FastQuorum, NumBallots, C

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == (0..(NumBallots-1)) \times {1,2,3}

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourths quorums.                             *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == 
    {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

(***************************************************************************)
(* The maximum ballot in a set of ballots.                                 *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    
(***********

--algorithm EPaxosLight {

    variables
        ballot = [p \in P |-> [c \in C |-> <<0,1>>]],
        vote = [p \in P |-> [c \in C |-> <<>>]],
        joinBallot = {},
        propose = <<>>,

    define {
        
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> SUBSET C]
            /\  joinBallot \subseteq (C \times Ballot)
        
        \* TRUE if c was seen in ballot B.
        SeenAt(c, bal, p) == bal \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == 
            LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
                IF bals # {}
                THEN Max(bals)
                ELSE <<-1,-1>>
        
        \* The estimate for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, b-1, p) : p \in q}
            IN Max(bals)
            
        (***************************************************************************)
        (* A few simple invariants.                                                *)
        (***************************************************************************)
        Inv1 == \A p \in P : \A c \in C : LastBal(c, Max(Ballot), p) \preceq ballot[p][c]
        
        Inv3 == \A p \in P : \A c \in C :
            LET b == LastBal(c, Max(Ballot), p)
            IN  <<-1,-1>> \prec b => b \in DOMAIN vote[p][c]
            
        Cmd(leader) == leader[1]
        Bal(leader) == leader[2]
        
        Phase1Bals == (0..NumBallots) \times {1}
        Phase2Bals == (0..NumBallots) \times {2}
        Phase3Bals == (0..NumBallots) \times {3}
        
        Phase1SeenCmds(p) == {c \in C : \E bal \in Phase1Bals : bal \in DOMAIN vote[p][c]}
        Phase2SeenCmds(p, c) == {c2 \in C : \E bal \in Phase2Bals : 
            bal \in DOMAIN vote[p][c2] /\ c \notin vote[p][c2][bal]}
        
        Decided(c, deps) ==
            \/  \E b \in Phase1Bals : \E q \in FastQuorum : 
                    \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
            \/  \E b \in Phase2Bals  : \E q \in FastQuorum :
                    \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
            \/  \E b \in Phase3Bals : \E q \in Quorum :
                    \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
                    
        Decisions == {d \in C \times SUBSET C : Decided(d[1],d[2])}
        
        (*******************************************************************)
        (* The main correctness properties are GraphInvariant and          *)
        (* Agreement.  Their conjunction shoud imply correct State Machine *)
        (* Replication.                                                    *)
        (*******************************************************************)
                
        GraphInvariant == \A c1, c2 \in C : \A deps1, deps2 \in SUBSET C :
            /\  Decided(c1, deps1)
            /\  Decided(c2, deps2)
            /\ c1 # c2 
            =>  \/  c2 \in deps1
                \/  c1 \in deps2
        
        Agreement == \A c \in C : \A deps1, deps2 \in SUBSET C :
            /\ Decided(c, deps1)
            /\ Decided(c, deps2) 
            => deps1 = deps2
        
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
 
    (***********************************************************************)
    (* Phase1 can only be triggered when all values are safe.              *)
    (***********************************************************************)
    macro Phase1(c, bal) {
        assert bal[2] = 1;
        propose := propose ++ <<<<c,bal>>, {}>>;
    }
    
    macro Phase1Reply(p) {
        with (c \in C; bal \in Phase1Bals) {
            when <<c, bal>> \in DOMAIN propose /\ ballot[p][c] \preceq bal;
            when LastBal(c, bal, p) \prec bal; \* p has not participated yet in this ballot. 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<bal, Phase1SeenCmds(p)>>]];
            \* A response to a phase1Bal means joining phase2:
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = <<bal[1], 2>>]];
        }
    }
    
    macro Phase2(c, bal) {
        assert bal[2] = 2;
        with (q \in Quorum) {
            when \A p \in q : bal \preceq ballot[p][c];
            \* if c could have been decided fast:
            if (\E ds \in SUBSET C : \E q2 \in FastQuorum :
                        \A p \in q2 \cap q : vote[p][c][<<bal[1],1>>] = ds) {
                with (ds \in {ds \in SUBSET C : \E q2 \in FastQuorum :
                        \A p \in q2 \cap q : vote[p][c][<<bal[1],1>>] = ds}) {
                    propose := propose ++ <<<<c, bal>>, ds>>; \* Propose in phase 2
                }
            } else { \* propose in phase 3.
                propose := propose ++ <<<<c, <<bal[1],3>>>>, 
                    UNION {vote[p][c][<<bal[1],1>>] : p \in q}>>; 
            };
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; bal \in Phase2Bals) {
            when <<c, bal>> \in DOMAIN propose /\ ballot[p][c] \preceq bal;
            when LastBal(c, bal, p) \prec bal; \* p has not participated yet in this ballot. 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = 
                @ ++ <<bal, propose[<<c, bal>>] \cup Phase2SeenCmds(p, c)>>]]; \* union to guarantee that commands see each other.
            \* A response to a phase1Bal means joining phase 3:
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = <<bal[1], 3>>]];
        }
    }
    
    macro Phase3(c, bal) {
        assert bal[2] = 3;
        when <<c, bal>> \notin DOMAIN propose;
        with (q \in Quorum) {
            when \A p \in q : bal \preceq ballot[p][c];
            \* if c could have been decided fast:
            if (\E ds \in SUBSET C : \E q2 \in FastQuorum :
                        \A p \in q2 \cap q : vote[p][c][<<bal[1],2>>] = ds) {
                with (ds \in {ds \in SUBSET C : \E q2 \in FastQuorum :
                        \A p \in q2 \cap q : vote[p][c][<<bal[1],2>>] = ds}) {
                    propose := propose ++ <<<<c, bal>>, ds>>;
                }
            } else {
                propose := propose ++ <<<<c, <<bal[1],3>>>>, 
                    UNION {vote[p][c][<<bal[1],2>>] : p \in q}>>; \* union to guarantee that commands see each other.
            };
        }
    }
    
    macro Phase3Reply(p) {
        with (c \in C; bal \in Phase3Bals) {
            when <<c, bal>> \in DOMAIN propose /\ ballot[p][c] \preceq bal;
            when LastBal(c, bal, p) \prec bal; \* p has not participated yet in this ballot. 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = 
                @ ++ <<bal, propose[<<c, bal>>]>>]];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = <<bal[1], 3>>]];
        }
    }
    
    macro Recover(c, b) { \* TODO
        with (q \in Quorum; bal = <<b,1>>) {
            when \A p \in q : bal \preceq ballot[p][c];
            with (mbal = MaxBal(c, bal, q)) {
                if (mbal[2] = 1) {
                    skip; 
                } else if (mbal[2] = 2) {
                    skip; \* Here, how to guarantee that commands see each other? We may not have a full quorum...
                } else if (mbal[2] = 3) {
                    with (p \in {p \in P : LastBal(c, <<b-1,3>>, p) = mbal}) {
                        propose := propose ++ <<<<c, <<b,3>>>>, vote[p][c][mbal]>>;
                    }
                }
            }
        }
    }
    
    process (initLeader \in (C \times {0})) {
        propose:    Phase1(self[1], <<0,1>>);
        phase2:     Phase2(self[1], <<0,2>>);
        phase3:     Phase3(self[1], <<0,3>>);
    }
    
    \* Acceptors:
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        Phase1Reply(self);
                    } or {
                        Phase2Reply(self);
                    } or {
                        Phase3Reply(self);
                    } or {
                        skip; \* JoinBallot(self);
                    }
                }
    }
    
    (*
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:         either {
                            when self[2] = 0;
        b01:                Propose(self[1], 0);
                            either {
        b0fastD:                FastDecision(self[1], 0);
                            } or {
        b0phase2:               Phase2(self[1], 0);
        b0slowD:                SlowDecision(self[1], 0);
                            }
                        } or {
                            when self[2] > 0;
        startBal:           StartBallot(self[1], self[2]);
        recover:            Recover(self[1], self[2]);
        decide:             if (<<self[1], self[2]>> \in phase1) {
                                either {
        bNfastD:                   FastDecision(self[1], self[2]);
                                } or {
        bNphase2:                  Phase2(self[1], self[2]);
        bNslowD1:                  SlowDecision(self[1], self[2]);
                                }
                            } else {
        bNslowD2:               SlowDecision(self[1], self[2]);
                            }
                        }
    }
    *)
    
}

*)
\* BEGIN TRANSLATION
\* Label propose of process initLeader at line 147 col 9 changed to propose_
\* Label acc of process acc at line 244 col 17 changed to acc_
VARIABLES ballot, vote, joinBallot, propose, pc

(* define statement *)
TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> SUBSET C]
    /\  joinBallot \subseteq (C \times Ballot)


SeenAt(c, bal, p) == bal \in DOMAIN vote[p][c]


LastBal(c, max, p) ==
    LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
        IF bals # {}
        THEN Max(bals)
        ELSE <<-1,-1>>


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b-1, p) : p \in q}
    IN Max(bals)




Inv1 == \A p \in P : \A c \in C : LastBal(c, Max(Ballot), p) \preceq ballot[p][c]

Inv3 == \A p \in P : \A c \in C :
    LET b == LastBal(c, Max(Ballot), p)
    IN  <<-1,-1>> \prec b => b \in DOMAIN vote[p][c]

Cmd(leader) == leader[1]
Bal(leader) == leader[2]

Phase1Bals == (0..NumBallots) \times {1}
Phase2Bals == (0..NumBallots) \times {2}
Phase3Bals == (0..NumBallots) \times {3}

Phase1SeenCmds(p) == {c \in C : \E bal \in Phase1Bals : bal \in DOMAIN vote[p][c]}
Phase2SeenCmds(p, c) == {c2 \in C : \E bal \in Phase2Bals :
    bal \in DOMAIN vote[p][c2] /\ c \notin vote[p][c2][bal]}

Decided(c, deps) ==
    \/  \E b \in Phase1Bals : \E q \in FastQuorum :
            \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
    \/  \E b \in Phase2Bals  : \E q \in FastQuorum :
            \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
    \/  \E b \in Phase3Bals : \E q \in Quorum :
            \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps

Decisions == {d \in C \times SUBSET C : Decided(d[1],d[2])}







GraphInvariant == \A c1, c2 \in C : \A deps1, deps2 \in SUBSET C :
    /\  Decided(c1, deps1)
    /\  Decided(c2, deps2)
    /\ c1 # c2
    =>  \/  c2 \in deps1
        \/  c1 \in deps2

Agreement == \A c \in C : \A deps1, deps2 \in SUBSET C :
    /\ Decided(c, deps1)
    /\ Decided(c, deps2)
    => deps1 = deps2


vars == << ballot, vote, joinBallot, propose, pc >>

ProcSet == ((C \times {0})) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> <<0,1>>]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ joinBallot = {}
        /\ propose = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times {0}) -> "propose_"
                                        [] self \in P -> "acc_"]

propose_(self) == /\ pc[self] = "propose_"
                  /\ Assert((<<0,1>>)[2] = 1, 
                            "Failure of assertion at line 147, column 9 of macro called at line 237, column 21.")
                  /\ propose' = propose ++ <<<<(self[1]),(<<0,1>>)>>, {}>>
                  /\ pc' = [pc EXCEPT ![self] = "phase2"]
                  /\ UNCHANGED << ballot, vote, joinBallot >>

phase2(self) == /\ pc[self] = "phase2"
                /\ Assert((<<0,2>>)[2] = 2, 
                          "Failure of assertion at line 162, column 9 of macro called at line 238, column 21.")
                /\ \E q \in Quorum:
                     /\ \A p \in q : (<<0,2>>) \preceq ballot[p][(self[1])]
                     /\ IF \E ds \in SUBSET C : \E q2 \in FastQuorum :
                                   \A p \in q2 \cap q : vote[p][(self[1])][<<(<<0,2>>)[1],1>>] = ds
                           THEN /\ \E ds \in      {ds \in SUBSET C : \E q2 \in FastQuorum :
                                             \A p \in q2 \cap q : vote[p][(self[1])][<<(<<0,2>>)[1],1>>] = ds}:
                                     propose' = propose ++ <<<<(self[1]), (<<0,2>>)>>, ds>>
                           ELSE /\ propose' =        propose ++ <<<<(self[1]), <<(<<0,2>>)[1],3>>>>,
                                              UNION {vote[p][(self[1])][<<(<<0,2>>)[1],1>>] : p \in q}>>
                /\ pc' = [pc EXCEPT ![self] = "phase3"]
                /\ UNCHANGED << ballot, vote, joinBallot >>

phase3(self) == /\ pc[self] = "phase3"
                /\ Assert((<<0,3>>)[2] = 3, 
                          "Failure of assertion at line 191, column 9 of macro called at line 239, column 21.")
                /\ <<(self[1]), (<<0,3>>)>> \notin DOMAIN propose
                /\ \E q \in Quorum:
                     /\ \A p \in q : (<<0,3>>) \preceq ballot[p][(self[1])]
                     /\ IF \E ds \in SUBSET C : \E q2 \in FastQuorum :
                                   \A p \in q2 \cap q : vote[p][(self[1])][<<(<<0,3>>)[1],2>>] = ds
                           THEN /\ \E ds \in      {ds \in SUBSET C : \E q2 \in FastQuorum :
                                             \A p \in q2 \cap q : vote[p][(self[1])][<<(<<0,3>>)[1],2>>] = ds}:
                                     propose' = propose ++ <<<<(self[1]), (<<0,3>>)>>, ds>>
                           ELSE /\ propose' =        propose ++ <<<<(self[1]), <<(<<0,3>>)[1],3>>>>,
                                              UNION {vote[p][(self[1])][<<(<<0,3>>)[1],2>>] : p \in q}>>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ballot, vote, joinBallot >>

initLeader(self) == propose_(self) \/ phase2(self) \/ phase3(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E bal \in Phase1Bals:
                           /\ <<c, bal>> \in DOMAIN propose /\ ballot[self][c] \preceq bal
                           /\ LastBal(c, bal, self) \prec bal
                           /\ vote' = [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<bal, Phase1SeenCmds(self)>>]]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = <<bal[1], 2>>]]
                 \/ /\ \E c \in C:
                         \E bal \in Phase2Bals:
                           /\ <<c, bal>> \in DOMAIN propose /\ ballot[self][c] \preceq bal
                           /\ LastBal(c, bal, self) \prec bal
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] =
                                      @ ++ <<bal, propose[<<c, bal>>] \cup Phase2SeenCmds(self, c)>>]]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = <<bal[1], 3>>]]
                 \/ /\ \E c \in C:
                         \E bal \in Phase3Bals:
                           /\ <<c, bal>> \in DOMAIN propose /\ ballot[self][c] \preceq bal
                           /\ LastBal(c, bal, self) \prec bal
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] =
                                      @ ++ <<bal, propose[<<c, bal>>]>>]]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = <<bal[1], 3>>]]
                 \/ /\ TRUE
                    /\ UNCHANGED <<ballot, vote>>
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << joinBallot, propose >>

acc(self) == acc_(self)

Next == (\E self \in (C \times {0}): initLeader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Apr 06 02:20:39 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
