-------------------------------- MODULE wpaxos-------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT Quorum1, Quorum2, Objects, Leaders, Nodes, MaxSlot, MaxBallot

(******************************************************************************
* Quorum Assumption
******************************************************************************)
ASSUME QuorumAssumption ==
        /\ \A Q \in Quorum1 : Q \subseteq Nodes
        /\ \A Q \in Quorum2 : Q \subseteq Nodes
        /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

(******************************************************************************
* Node Assumption
******************************************************************************)                          
ASSUME NodeAssumption == /\ \A n \in Nodes : n \in Nat
                         /\ \A l \in Leaders : l \in Nat

(******************************************************************************
* Ballots and Slots
******************************************************************************)
Ballot == 0..MaxBallot
Slots == 1..MaxSlot
       
VARIABLE msgs, ballots, accepted, slot

vars == <<msgs, ballots, accepted, slot>>

Send(m) == msgs' = msgs \cup {m}

Init ==  /\ msgs = {}
         /\ ballots = [n \in Nodes |-> [o \in Objects |-> 0]]
         /\ accepted = [n \in Nodes |-> [o \in Objects |-> {}]]        
         /\ slot = [n \in Nodes |-> [o \in Objects |-> 0]]
         
(******************************************************************************
* Quorum 1 for object k is satisfied when all nodes in some Quorum 1 Q have
* send an "ack" message to the leader l with the same ballot number b
* Here we provide ballot b and object k to check if Quorum 1 has been
* satisfied
******************************************************************************)  
Q1Satisfied(b, l, k, Q) == 
         /\ \A a \in Q : 
            /\ \E m \in msgs :
                /\ m.type="ack" 
                /\ m.obj = k 
                /\ m.node = a 
                /\ m.leader = l 
                /\ m.bal = b
          
(******************************************************************************
* Quorum 2 for object k, ballot b and slos s is satisfied when all nodes in
* some Quorum 2 Q have send an "accept" message to the leader l with the same
* ballot number b and slot s.
* Satisfying Quorum 2 means that the command for object k in slot b has 
* been decided
******************************************************************************)    
Q2Satisfied(b, s, l, k, Q) == 
         /\ \A a \in Q : 
            /\ \E m \in msgs :
                /\ m.type="accepted" 
                /\ m.obj = k 
                /\ m.node = a 
                /\ m.leader = l 
                /\ m.bal = b 
                /\ m.slot.slot = s                         
                     
SendPrepare(n, k) == 
    /\ Send([type |-> "prepare", 
            leader |-> n, 
            obj |-> k, 
            bal |-> ballots[n][k] + 1])
    /\ UNCHANGED <<ballots, accepted, slot>>
    
ReplyPrepare(n, l, msg) == 
    /\ ballots' = [ballots EXCEPT ![n][msg.obj] = msg.bal]
    /\ Send([type |-> "ack",
            leader |-> msg.leader, 
            bal |-> msg.bal, 
            node |-> n, 
            obj |-> msg.obj, 
            acc |-> accepted[n][msg.obj]])
    /\ UNCHANGED <<accepted, slot>> 
  
SendAccept(l, k) ==     
    /\ \/ /\ \E m \in msgs : 
            /\ m.type = "ack" 
            /\ m.leader = l 
            /\ m.obj = k 
            /\ \E s \in m.acc :
                /\ \A s2 \in m.acc : s.slot >= s2.slot
                /\ s.slot > slot[l][k]
                /\ slot[l][k] < MaxSlot
                /\ slot' = [slot EXCEPT ![l][k] = s.slot + 1]  
                /\ Send([type |-> "accept", 
                        leader |-> l, 
                        bal |-> ballots[l][k], 
                        obj |-> k, 
                        slot |-> [slot |-> slot'[l][k], 
                                  val |-> (slot'[l][k]) * l]])          
       \/ /\ ~ \E m \in msgs : 
              /\ m.type = "ack" 
              /\ m.leader = l 
              /\ m.obj = k 
              /\ \E s \in m.acc :
                  /\ s.slot > slot[l][k]
          /\ slot[l][k] < MaxSlot
          /\ slot' = [slot EXCEPT ![l][k] = @ + 1]  
          /\ Send([type |-> "accept", 
                  leader |-> l, 
                  bal |-> ballots[l][k], 
                  obj |-> k, 
                  slot |-> [slot |-> slot'[l][k], val |-> (slot'[l][k]) * l]])           
       \/ /\ \E m \in msgs : 
            /\ m.type = "ack" 
            /\ m.leader = l 
            /\ m.obj = k 
            /\ \E s \in m.acc :
                /\ Send([type |-> "accept", 
                        leader |-> l, 
                        bal |-> ballots[l][k], 
                        obj |-> k, 
                        slot |-> [slot |-> s.slot, val |-> s.val]])   
          /\ UNCHANGED <<slot>>       
    /\ UNCHANGED <<ballots, accepted>>        
        
ReplyAccept(n, msg) ==
    /\ accepted' = 
        [accepted EXCEPT ![n][msg.obj] = @ \cup {[slot |-> msg.slot.slot, 
                                                 val |-> msg.slot.val, 
                                                 bal |-> msg.bal, 
                                                 obj |->msg.obj]}]
    /\ ballots' = [ballots EXCEPT ![n][msg.obj] = msg.bal]
    /\ Send([type |-> "accepted", 
            leader |-> msg.leader, 
            node |-> n, 
            bal |-> msg.bal, 
            obj |-> msg.obj, 
            slot |-> msg.slot])
    /\ UNCHANGED <<slot>>  
            
\* possible actions: 
Next == 
        \* send prepare
        \/ \E n \in Leaders : \E k \in Objects : 
            /\ ballots[n][k] + 1 \in Ballot
            /\ SendPrepare(n, k)
        \* ack prepare
        \/ \E q \in Quorum1 : \E n \in Nodes : \E l \in Leaders : \E m \in msgs : 
            /\ m.type = "prepare"
            /\ m.bal > ballots[n][m.obj] 
            /\ n \in q
            /\ l \in q
            /\ ReplyPrepare(n, l, m)
        \* send accept
        \/ \E Q1 \in Quorum1 : \E l \in Leaders : \E k \in Objects : 
            /\ Q1Satisfied(ballots[l][k], l, k, Q1)
            /\ SendAccept(l, k)      
        \* reply to accept     
        \/ \E q \in Quorum2 : \E n \in Nodes : \E m \in msgs :
            /\ m.type = "accept"
            /\ m.bal >= ballots[n][m.obj]
            /\ n \in q
            /\ m.leader \in q
            /\ ReplyAccept(n, m)
              
NoDecided == 
    \A l \in Leaders : 
        \A b \in Ballot :
            \A s \in Slots : 
                \A k \in Objects : 
                    \E q \in Quorum2 : 
                        /\ l \in q 
                        /\ Q2Satisfied(b, s, l, k, q) = FALSE
  
NoDifferentDecided == 
    ~ (\E m \in msgs : 
        /\ m.type = "accepted"
        /\ \E q2 \in Quorum2 :
            /\ m.leader \in q2 
            /\ Q2Satisfied(m.bal, m.slot.slot, m.leader, m.obj, q2)
            /\ \E m2 \in msgs : 
                /\ m2.type = "accepted"
                /\ m2.leader # m.leader
                /\ m2.obj = m.obj
                /\ m2.slot.slot = m.slot.slot
                /\ \E m2q2 \in Quorum2 :
                    /\ m2.leader \in m2q2 
                    /\ Q2Satisfied(m2.bal, m2.slot.slot, m2.leader, m2.obj, m2q2)
                    /\ m2.slot.val # m.slot.val)                   
       
=============================================================================
