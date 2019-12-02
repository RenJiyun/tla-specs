-----MODULE WriteThroughCache-----
EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES wmem,ctl, buf, cache, memQ
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)
M == INSTANCE InternalMemory WITH mem <- wmem
-----------------------------------

Init ==
    /\ M!IIint
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ memQ = <<>>
   
TypeInvariant ==
    /\ wmem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
    /\ buf \in [Proc -> MReq \/ Val \/ {NoVal}]
    /\ cache \in [Proc -> [Adr -> Val \/ NoVal]]
    /\ memQ \in Seq(Proc \X MReq)
    
\* 定义了缓存的一致性
Coherence ==
    \A p, q \in Proc, a \in Adr:
        (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])
---------------------------































===================