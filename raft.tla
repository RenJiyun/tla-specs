--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* 代表所有的节点
CONSTANTS Server

\* 代表可以进入日志的所有值
CONSTANTS Value

\* 代表节点的状态：跟随者，候选者，领导者
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* 消息类型
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs










----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log

\* 记录每一个节点已经应用过的日志记录点
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>










----
\* 帮助函数


\* 定义法定集合
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term


\* 在msgs的基础上增加一个msg
\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)


\* 在msgs的基础上去除一个msg
\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs


\* 发送消息就是在全局消息中增加一个消息
\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)


\* 去除一个消息就是在全局消息中去除一个消息
\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)


\* 回复消息是在全局消息中减少一个请求消息，但是增加一个响应消息
\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))


\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y



















----
\* Define initial values for all variables

\* 定义全局初始状态
InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
                   
                   
\* 定义各个节点的初始状态
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
                  
\* 定义候选者的初始状态                  
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
                     

\* 定义领导者的初始状态
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  
                  
\* 定义节点日志和提交点的初始状态
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
             
               
\* 定义初始状态
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars





----
\* 定义状态转移函数的各个子函数


\* 节点重启
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]                     \* 状态变更为跟随者
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]                  \* 清空该节点投票响应记录
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]                    \* 清空该节点的投票授予记录
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]       \* 清空投票日志
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]     \* 重置nextIndex
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]    \* 重置matchIndex
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]                      \* 重置commitIndex
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections>>


\* 节点超时，开启新一轮的投票
\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]                           \* 变更状态为候选者
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]      \* 任期号自增1
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]                           
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]                \* 清空该节点的投票响应记录
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]                  
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]     \* 重置投票日志
              /\ UNCHANGED <<messages, leaderVars, logVars>>



\* 节点i向节点j发送投票请求
\* 消息报文结构为：
\* 1. 消息类型
\* 2. 发送方的任期号
\* 3. 最后一条日志的任期号
\* 4. 最后一条日志的index
\* 5. 发送方标识
\* 6. 接收方标识
\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]                            \* 节点j尚未给出过该轮投票的响应
    /\ Send([mtype         |-> RequestVoteRequest,           \* 发送消息
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>


\* 节点成为领导者
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum                                      \* 获取法定人数的选票
    /\ state'      = [state EXCEPT ![i] = Leader]                     \* 变更状态为领导者
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =                         \* 设置nextIndex，设置为自己的日志数+1
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =                         \* 将所有的matchIndex设置为0，之后会进行沟通
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup                                     \* 将此次选举加入成功选举的集合中
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>


\* 接受客户端请求
\* 规格有一个好处：它跟时间无关，比如在具体的实现中，处理客户端请求，在领导者节点追加完日志后，
\* 接下来一定会向跟随者进行日志复制，但是规格没有这种连续性，而这恰恰很好的刻画了并行性
\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader                                           \* 只有领导者才可以接受客户端请求
    /\ LET entry == [term  |-> currentTerm[i],                     \* 追加日志
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>


\* 向前移动提交点
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader                                                             
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :                                      \* 定义Agree函数
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>




----
\* 消息处理器
\* i = recipient, j = sender, m = message


\* 处理投票消息：节点j将消息m发送给节点i
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])             
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
                    
        \* 计算是否授予选票：1. 
        grant == /\ m.mterm = currentTerm[i]                                    
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>



\* 处理投票响应消息
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>



\* 处理日志复制消息
\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, logVars>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* 定义状态转移函数
\* 有以下几种情形会发生状态的转移：
\* 1. 有节点重启
\* 2. 有节点超时
\* 3. 有节点发送投票请求
\* 4. 有节点成为新的领导者
\* 5. 有客户端请求
\* 6. 推进提交点
\* 7. 追加日志
\* 8. 收到消息
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
