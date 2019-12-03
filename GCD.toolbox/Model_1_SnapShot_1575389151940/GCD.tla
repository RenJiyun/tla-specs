-------------------------------- MODULE GCD --------------------------------

EXTENDS Naturals

VARIABLES a, b

GCDInit == 
    /\ a = 12
    /\ b = 8

GCDNext ==
    \/ /\ a' = IF a > b THEN a - b
            ELSE a
       /\ b' = b
    \/ /\ b' = IF a < b THEN b - a
            ELSE b
       /\ a' = a


Invariant ==
    a # b


=============================================================================
\* Modification History
\* Last modified Wed Dec 04 00:05:35 CST 2019 by ren
\* Last modified Tue Dec 03 17:28:43 CST 2019 by wozai
\* Created Tue Dec 03 17:21:10 CST 2019 by wozai
