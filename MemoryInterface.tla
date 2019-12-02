-----MODULE MemoryInterface----
VARIABLE memInt
CONSTANTS Send(_, _, _, _),   \* 表示处理器向内存发送请求
           Reply(_, _, _, _),  \* 表示内存响应处理器请求
           InitMemInt,         \* 代表内存的状态
           Proc,               \* 代表处理器
           Adr,                \* 代表内存地址  
           Val                 \* 代表内存的值

ASSUME \A p, d, miOld, miNew: /\ Send(p, d, miOld, miNew) \in BOOLEAN
                              /\ Reply(p, d, miOld, miNew) \in BOOLEAN     
----------------------

MReq == [op: {"Rd"}, adr: Adr] \/ [op: {"Wr"}, adr: Adr, val: Val]
NoVal == CHOOSE v : v \notin Val
============