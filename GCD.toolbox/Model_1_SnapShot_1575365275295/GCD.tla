-------------------------------- MODULE GCD --------------------------------

EXTENDS Naturals

VARIABLES a, b

GCDInit == 
    /\ a = 18
    /\ b = 12

GCDNext ==
    \/ a' = IF a > b THEN a - b
            ELSE a
    \/ b' = IF a < b THEN b - a
            ELSE b




=============================================================================
\* Modification History
\* Last modified Tue Dec 03 17:27:34 CST 2019 by wozai
\* Created Tue Dec 03 17:21:10 CST 2019 by wozai
