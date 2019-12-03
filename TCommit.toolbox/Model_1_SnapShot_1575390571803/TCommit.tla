---- MODULE TCommit ----

\* 代表所有的资源管理器
CONSTANT RM    

\* 代表资源管理器的状态
VARIABLE rmState  

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* 初始状态下，所有的资源管理器状态都是working，也就是rmState = ["working", "working", "working", "working"]        
TCInit == rmState = [r \in RM |-> "working"]

\* 是否可以提交
canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed" 

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r)  == \/ /\ rmState[r] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![r] = "committed"]
              \/ /\ rmState[r] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

\* 系统状态可以往下迁移当且仅当存在一个资源管理器，它要么做出prepare的回应，要么做出提交或者终止的决定
TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

\* 事务的一致性是指所有的资源管理器要么全部提交要么全部终止
TCConsistent ==  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)

=====