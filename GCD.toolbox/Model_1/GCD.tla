-------------------------------- MODULE GCD --------------------------------

EXTENDS Naturals

VARIABLES a, b

GCDInit == 
    /\ a = 15
    /\ b = 10

GCDNext ==
    \/ a' = IF a > b THEN a - b
            ELSE a
    \/ b' = IF a < b THEN b - a
            ELSE b




=============================================================================
\* Modification History
\* Last modified Tue Dec 03 17:28:43 CST 2019 by wozai
\* Created Tue Dec 03 17:21:10 CST 2019 by wozai
