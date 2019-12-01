-------MODULE TwoPhase----


CONSTANT RM  \* The set of resource managers

VARIABLES
  rmState,       \* 资源管理器的状态
  tmState,       \* 事务管理器的状态
  tmPrepared,    \* 用于事务管理器记录已经准备好的资源管理器
  msgs           \* 记录资源管理器和事务管理器之间收发的消息
            

\* 一共有三种类型的消息：1. 资源管理器向事务管理器发送Prepared消息 2. 事务管理器向所有资源管理器发送Commit消息 3. 事务管理器向资源管理器发送Abort消息
\* 但是Messages定义了整个过程的所有消息
Messages == [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   
TPTypeOK ==  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "done"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

\* 定义初始状态
TPInit ==   
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}

\* 事务管理器收到某个资源管理器发送过来的Prepared消息
TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

\* 事务管理器发送Commit消息
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* 事务管理器发送Abort消息
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>


\* 资源管理器发送Prepared消息
RMPrepare(r) == 
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>
 
\* 资源管理器选择Abort
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* 资源管理器收到Commit消息
RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* 资源管理器收到Abort消息
RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>


\* 定义转移函数
\* 系统状态可以转移，当且仅当：
\* 1. 事务管理器发送commit消息给资源管理器
\* 2. 事务管理器发送abort消息给资源管理器
\* 3. 资源管理器
TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E r \in RM : 
       TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
         \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>

THEOREM TPSpec => []TPTypeOK

INSTANCE TCommit 

THEOREM TPSpec => TCSpec






============================