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
(* P is the set of acceptors.  MaxTime bounds the timestamp that can be    *)
(* assigned to proposals, but not to retries.  CmdId(c) must assign a      *)
(* natural number to a command.  It is used to break time in timestamps.   *)
(***************************************************************************)
CONSTANTS P, Quorum, FastQuorum, NumBallots, C, CmdId(_)

ASSUME \A c \in C : 
    /\  CmdId(c) \in Nat 
    /\  \A c2 \in C : c # c2 => CmdId(c) # CmdId(c2)

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == 0..(NumBallots-1)

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
(* The maximum element in a set.                                           *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x >= y
    
(***********

--algorithm EPaxosLight {

    variables
        ballot = [p \in P |-> [c \in C |-> 0]],
        vote = [p \in P |-> [c \in C |-> <<>>]],
        phase1 = {},
        phase2 = <<>>,
        committed = <<>>,
        joinBallot = {}

    define {
        
        Status == {"pending1", "accepted"}
        CmdInfo == [status : Status, deps : SUBSET C]
        
        (*******************************************************************)
        (* An invariant describing the type of the different variables.    *)
        (* Note that we extensively use maps (also called functions) keyed *)
        (* by pairs <c,b>, where c is a command and b a ballot, and where  *)
        (* the set of keys of the map dynamically grows.  The set of keys  *)
        (* of a map m is noted DOMAIN m.                                   *)
        (*******************************************************************)
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> CmdInfo]
            /\  phase1 \in SUBSET (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : phase2 \in [D -> SUBSET C]
            /\  joinBallot \subseteq (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : committed \in [D -> SUBSET C]
    
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}
        
        \* TRUE if c was seen in ballot b at p.
        SeenAt(c, b, p) == b \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b <= max} IN
            IF bals # {}
            THEN Max(bals)
            ELSE -1
        
        \* The estimate for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, b-1, p) : p \in q}
            IN Max(bals)
        
        ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]
            
        (***************************************************************************)
        (* A few simple invariants.                                                *)
        (***************************************************************************)
        Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)
        
        Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in phase1 => <<c,b>> \in joinBallot
        
        Inv3 == \A p \in P : \A c \in C : 
            LET b == LastBal(c, Max(Ballot), p)
            IN  b >= 0 => b \in DOMAIN vote[p][c]
        
        (*******************************************************************)
        (* The main correctness properties are GraphInvariant and          *)
        (* Agreement.  Their conjunction shoud imply correct State Machine *)
        (* Replication.                                                    *)
        (*******************************************************************)
                
        GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
            /\ <<c1,b1>> \in DOMAIN committed 
            /\ <<c2,b2>> \in DOMAIN committed
            /\ c1 # c2 
            =>  \/  c2 \in committed[<<c1,b1>>]
                \/  c1 \in committed[<<c2,b2>>]
        
        Agreement == \A c \in C : \A b1,b2 \in Ballot : 
            /\ <<c,b1>> \in DOMAIN committed
            /\ <<c,b2>> \in DOMAIN committed 
            => committed[<<c,b1>>] = committed[<<c,b2>>]

        Cmd(leader) == leader[1]
        Bal(leader) == leader[2]
        
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
 
    macro Phase1(c, b) {
        when <<c,b>> \notin phase1;
        phase1 := phase1 \cup {<<c,b>>}
    }
    
    macro Phase1Reply(p) {
        with (c \in C; b \in Ballot) { 
            when <<c, b>> \in phase1;
            when b >= ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]]; \* Join the ballot if lagging.
            when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                ++ <<b, [status |-> "pending1", deps |-> SeenCmds(p)]>>]];
            
        }
    }

    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1";
            with (ds \in {ds \in SUBSET C : \A p \in q : vote[p][c][b].deps = ds}) {
                committed := committed ++ <<<<c,b>>, ds>>;
            }
        }
    }
    
    macro Phase2(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1";
            with (ds = UNION {vote[p][c][b].deps : p \in q}) {
                phase2 := phase2 ++ <<<<c,b>>, ds>>;
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; b \in Ballot) { 
            when <<c, b>> \in DOMAIN phase2;
            when b >= ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]]; \* Join the ballot if lagging.
            when b \notin DOMAIN vote[p][c] \/ (b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1"); 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                ++ <<b, [status |-> "accepted", deps |-> phase2[<<c,b>>] ]>>]];
            
        }
    }
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "accepted";
            with (ds \in {ds \in SUBSET C : \A p \in q : vote[p][c][b].deps = ds}) {
                committed := committed ++ <<<<c,b>>, ds>>;
            }
        }
    }
        
    macro StartBallot(c, b) {
        assert b > 0; \* Only start ballots greater than 0; 0 is started by default.
        joinBallot := joinBallot \cup {<<c,b>>};
    }
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (ball \in joinBallot; c = ball[1], b = ball[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
    macro Recover(com, bal) {
        when <<com,bal>> \in joinBallot;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][com] >= bal;
            with (mb = MaxBal(com, bal, q); ps = {p \in q : mb \in DOMAIN vote[p][com]}) {
                if (ps = {}) {
                    phase1 := phase1 \cup {<<com,bal>>};
                } else {
                    when ps \in Quorum;
                    phase2 := phase2 ++ <<<<com,bal>>, UNION {vote[p][com][mb].deps : p \in ps}>>;
                }
            };
        }
    }
    
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:         either {
                            when self[2] = 0;
        b01:                Phase1(self[1], 0);
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
    
    \* Acceptors:
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        Phase1Reply(self);
                    } or {
                        Phase2Reply(self);
                    } or {
                        JoinBallot(self);
                    }
                }
    }
    
}

*)
\* BEGIN TRANSLATION
\* Label leader of process leader at line 222 col 25 changed to leader_
\* Label acc of process acc at line 250 col 17 changed to acc_
VARIABLES ballot, vote, phase1, phase2, committed, joinBallot, pc

(* define statement *)
Status == {"pending1", "accepted"}
CmdInfo == [status : Status, deps : SUBSET C]








TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> CmdInfo]
    /\  phase1 \in SUBSET (C \times Ballot)
    /\  \E D \in SUBSET (C \times Ballot) : phase2 \in [D -> SUBSET C]
    /\  joinBallot \subseteq (C \times Ballot)
    /\  \E D \in SUBSET (C \times Ballot) : committed \in [D -> SUBSET C]


SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN vote[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b <= max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE -1


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b-1, p) : p \in q}
    IN Max(bals)

ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]




Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)

Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in phase1 => <<c,b>> \in joinBallot

Inv3 == \A p \in P : \A c \in C :
    LET b == LastBal(c, Max(Ballot), p)
    IN  b >= 0 => b \in DOMAIN vote[p][c]







GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
    /\ <<c1,b1>> \in DOMAIN committed
    /\ <<c2,b2>> \in DOMAIN committed
    /\ c1 # c2
    =>  \/  c2 \in committed[<<c1,b1>>]
        \/  c1 \in committed[<<c2,b2>>]

Agreement == \A c \in C : \A b1,b2 \in Ballot :
    /\ <<c,b1>> \in DOMAIN committed
    /\ <<c,b2>> \in DOMAIN committed
    => committed[<<c,b1>>] = committed[<<c,b2>>]

Cmd(leader) == leader[1]
Bal(leader) == leader[2]


vars == << ballot, vote, phase1, phase2, committed, joinBallot, pc >>

ProcSet == ((C \times Ballot)) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ phase1 = {}
        /\ phase2 = <<>>
        /\ committed = <<>>
        /\ joinBallot = {}
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times Ballot) -> "leader_"
                                        [] self \in P -> "acc_"]

leader_(self) == /\ pc[self] = "leader_"
                 /\ \/ /\ self[2] = 0
                       /\ pc' = [pc EXCEPT ![self] = "b01"]
                    \/ /\ self[2] > 0
                       /\ pc' = [pc EXCEPT ![self] = "startBal"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                                 joinBallot >>

b01(self) == /\ pc[self] = "b01"
             /\ <<(self[1]),0>> \notin phase1
             /\ phase1' = (phase1 \cup {<<(self[1]),0>>})
             /\ \/ /\ pc' = [pc EXCEPT ![self] = "b0fastD"]
                \/ /\ pc' = [pc EXCEPT ![self] = "b0phase2"]
             /\ UNCHANGED << ballot, vote, phase2, committed, joinBallot >>

b0fastD(self) == /\ pc[self] = "b0fastD"
                 /\ \E q \in FastQuorum:
                      /\ \A p \in q : 0 \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][0].status = "pending1"
                      /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][0].deps = ds}:
                           committed' = committed ++ <<<<(self[1]),0>>, ds>>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

b0phase2(self) == /\ pc[self] = "b0phase2"
                  /\ \E q \in Quorum:
                       /\ \A p \in q : 0 \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][0].status = "pending1"
                       /\ LET ds == UNION {vote[p][(self[1])][0].deps : p \in q} IN
                            phase2' = phase2 ++ <<<<(self[1]),0>>, ds>>
                  /\ pc' = [pc EXCEPT ![self] = "b0slowD"]
                  /\ UNCHANGED << ballot, vote, phase1, committed, joinBallot >>

b0slowD(self) == /\ pc[self] = "b0slowD"
                 /\ \E q \in Quorum:
                      /\ \A p \in q : 0 \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][0].status = "accepted"
                      /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][0].deps = ds}:
                           committed' = committed ++ <<<<(self[1]),0>>, ds>>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ Assert((self[2]) > 0, 
                            "Failure of assertion at line 194, column 9 of macro called at line 233, column 29.")
                  /\ joinBallot' = (joinBallot \cup {<<(self[1]),(self[2])>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, phase1, phase2, committed >>

recover(self) == /\ pc[self] = "recover"
                 /\ <<(self[1]),(self[2])>> \in joinBallot
                 /\ \E q \in Quorum:
                      /\ \A p \in q : ballot[p][(self[1])] >= (self[2])
                      /\ LET mb == MaxBal((self[1]), (self[2]), q) IN
                           LET ps == {p \in q : mb \in DOMAIN vote[p][(self[1])]} IN
                             IF ps = {}
                                THEN /\ phase1' = (phase1 \cup {<<(self[1]),(self[2])>>})
                                     /\ UNCHANGED phase2
                                ELSE /\ ps \in Quorum
                                     /\ phase2' = phase2 ++ <<<<(self[1]),(self[2])>>, UNION {vote[p][(self[1])][mb].deps : p \in ps}>>
                                     /\ UNCHANGED phase1
                 /\ pc' = [pc EXCEPT ![self] = "decide"]
                 /\ UNCHANGED << ballot, vote, committed, joinBallot >>

decide(self) == /\ pc[self] = "decide"
                /\ IF <<self[1], self[2]>> \in phase1
                      THEN /\ \/ /\ pc' = [pc EXCEPT ![self] = "bNfastD"]
                              \/ /\ pc' = [pc EXCEPT ![self] = "bNphase2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "bNslowD2"]
                /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                                joinBallot >>

bNslowD2(self) == /\ pc[self] = "bNslowD2"
                  /\ \E q \in Quorum:
                       /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "accepted"
                       /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                            committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

bNfastD(self) == /\ pc[self] = "bNfastD"
                 /\ \E q \in FastQuorum:
                      /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "pending1"
                      /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                           committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

bNphase2(self) == /\ pc[self] = "bNphase2"
                  /\ \E q \in Quorum:
                       /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "pending1"
                       /\ LET ds == UNION {vote[p][(self[1])][(self[2])].deps : p \in q} IN
                            phase2' = phase2 ++ <<<<(self[1]),(self[2])>>, ds>>
                  /\ pc' = [pc EXCEPT ![self] = "bNslowD1"]
                  /\ UNCHANGED << ballot, vote, phase1, committed, joinBallot >>

bNslowD1(self) == /\ pc[self] = "bNslowD1"
                  /\ \E q \in Quorum:
                       /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "accepted"
                       /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                            committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

leader(self) == leader_(self) \/ b01(self) \/ b0fastD(self)
                   \/ b0phase2(self) \/ b0slowD(self) \/ startBal(self)
                   \/ recover(self) \/ decide(self) \/ bNslowD2(self)
                   \/ bNfastD(self) \/ bNphase2(self) \/ bNslowD1(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ <<c, b>> \in phase1
                           /\ b >= ballot[self][c]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LastBal(c, b, self) < b
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                      ++ <<b, [status |-> "pending1", deps |-> SeenCmds(self)]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ <<c, b>> \in DOMAIN phase2
                           /\ b >= ballot[self][c]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ b \notin DOMAIN vote[self][c] \/ (b \in DOMAIN vote[self][c] /\ vote[self][c][b].status = "pending1")
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                      ++ <<b, [status |-> "accepted", deps |-> phase2[<<c,b>>] ]>>]]
                 \/ /\ \E ball \in joinBallot:
                         LET c == ball[1] IN
                           LET b == ball[2] IN
                             /\ b > ballot[self][c]
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                    /\ vote' = vote
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << phase1, phase2, committed, joinBallot >>

acc(self) == acc_(self)

Next == (\E self \in (C \times Ballot): leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Apr 05 15:29:36 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
