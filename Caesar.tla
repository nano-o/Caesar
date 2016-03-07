------------------------------- MODULE Caesar -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, C, MaxTs

ASSUME N \in Nat /\ N > 0

TimeStamp == 1..MaxTs

P ==  1..N

VARIABLES time, seen, proposed, phase1Ack, phase1Reject
   
Status == {"pending","stable","accepted","rejected"}
    
CmdWithTs == [cmd : C, ts : P \times TimeStamp]

ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

TypeInvariant ==
    /\ time \in [P -> Nat]
    /\ \E D \in SUBSET C : proposed \in [D -> P \times TimeStamp]
    /\ \forall p \in P :
        /\ \E D \in SUBSET C : seen[p] \in [D -> [ts: P \times TimeStamp, status: Status, pred: SUBSET C]]
        /\ \E D \in SUBSET C : phase1Ack[p] \in [D -> [ts : P \times TimeStamp, pred : SUBSET C]]
        /\ \E D \in SUBSET C : phase1Reject[p] \in [D -> [ts : P \times TimeStamp, pred : SUBSET C]]

Init ==
    /\ time = [p \in P |-> 1]
    /\ seen = [p \in P |-> <<>>]
    /\ proposed = <<>>
    /\ phase1Ack = [p \in P |-> <<>>]
    /\ phase1Reject = [p \in P |-> <<>>]

Propose(p, c) == 
    /\ \forall c2 \in DOMAIN proposed : c2 # c \* no duplicate commands
    /\ proposed' = [c2 \in DOMAIN proposed \cup {c} |-> 
        IF c2 = c THEN <<p,time[p]>> ELSE proposed[c2]]
    /\ time' = [time EXCEPT ![p] = @ + 1] \* increment the local time of p to avoid having two proposals with the same timestamp.
    /\ time[p]' \in TimeStamp 
    /\ UNCHANGED <<seen, phase1Ack, phase1Reject>>

Conflicts(p, c1, c2) == \* c1 must be in seen[p] and c2 must be in proposed
    /\ proposed[c2] \prec seen[p][c1].ts
    /\ c2 \notin seen[p][c1].pred

Blocks(p, c1, c2) == 
    /\ Conflicts(p,c1,c2)
    /\ seen[p][c1].status \notin {"stable","accepted"}

RcvPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  \forall c2 \in DOMAIN seen[p] : \neg Blocks(p, c2, c) \* The wait condition
    /\  IF \exists c2 \in DOMAIN seen[p] : Conflicts(p, c2, c)
        THEN LET 
                cStatus == "rejected"
                cDeps == DOMAIN seen[p]
                cTs == proposed[c] 
            IN
                /\ phase1Reject' = [phase1Reject EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                    IF c2 = c THEN [ts |-> cTs, pred |-> cDeps]
                    ELSE @[c2]]]
                /\ seen' = [seen EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                        IF c2 = c THEN [ts |-> cTs, status |-> cStatus, pred |-> cDeps]
                        ELSE @[c2]]]
                /\ UNCHANGED phase1Ack
        ELSE LET
                cStatus == "pending"
                cTs == proposed[c] 
                cDeps == {c2 \in DOMAIN seen[p] : seen[p][c2].ts \prec cTs} 
            IN
                /\ phase1Ack' = [phase1Ack EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                    IF c2 = c THEN [ts |-> cTs, pred |-> cDeps]
                    ELSE @[c2]]]
                /\ seen' = [seen EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                        IF c2 = c THEN [ts |-> cTs, status |-> cStatus, pred |-> cDeps]
                        ELSE @[c2]]]
                /\ UNCHANGED phase1Reject
    /\ UNCHANGED <<proposed, time>>

Tick(p) == 
    /\ time' = [time EXCEPT ![p] = @+1]
    /\ time[p]' \in TimeStamp
    /\ UNCHANGED <<proposed, seen, phase1Ack, phase1Reject>>
    
Next == \E p \in P : 
    \/  \E c \in C : Propose(p,c)
    \/  RcvPropose(p)
    \/  Tick(p)
        
    


=============================================================================
\* Modification History
\* Last modified Mon Mar 07 12:53:27 EST 2016 by nano
\* Created Mon Mar 07 11:08:24 EST 2016 by nano
