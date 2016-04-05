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
        
        Status == {"pending1", "pending2"}
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
        
        Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in DOMAIN phase1 => <<c,b>> \in joinBallot
        
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
    
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:     Phase1(self[1], self[2]);
    }
    
    \* Acceptors:
    process (acc \in P) {
        acc:    while (TRUE) {
                    Phase1Reply(self);
                }
    }
    
}

*)
\* BEGIN TRANSLATION
\* Label leader of process leader at line 135 col 9 changed to leader_
\* Label acc of process acc at line 158 col 17 changed to acc_
VARIABLES ballot, vote, phase1, phase2, committed, joinBallot, pc

(* define statement *)
Status == {"pending1", "pending2"}
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

Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in DOMAIN phase1 => <<c,b>> \in joinBallot







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
                 /\ <<(self[1]),(self[2])>> \notin phase1
                 /\ phase1' = (phase1 \cup {<<(self[1]),(self[2])>>})
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, phase2, committed, joinBallot >>

leader(self) == leader_(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \E c \in C:
                   \E b \in Ballot:
                     /\ <<c, b>> \in phase1
                     /\ b >= ballot[self][c]
                     /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                     /\ LastBal(c, b, self) < b
                     /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                ++ <<b, [status |-> "pending1", deps |-> SeenCmds(self)]>>]]
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << phase1, phase2, committed, joinBallot >>

acc(self) == acc_(self)

Next == (\E self \in (C \times Ballot): leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Apr 05 13:29:27 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
