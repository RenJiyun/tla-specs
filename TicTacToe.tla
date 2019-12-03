------------MODULE TicTacToe----------

EXTENDS Sequences, Naturals

CONSTANTS A, B
CONSTANT nil

VARIABLE NextTurn

VARIABLE board
VARIABLES rows, cols, diags


\* 行不变式
RowInvariant ==
    /\ \A row \in rows: 
            LET rowVal == {board[i]: i \in row}                    
            IN rowVal \subseteq {0, nil} \/ rowVal \subseteq {1, nil}
    
\* 列不变式  
ColInvariant == 
    /\ \A col \in cols: 
            LET colVal == {board[i]: i \in col}
            IN colVal \subseteq {0, nil} \/ colVal \subseteq {1, nil}


\* 对角线不变式
DiagInvariant ==
    /\ \A diag \in diags: 
            LET diagVal == {board[i]: i \in diag}
            IN diagVal \subseteq {0, nil} \/ diagVal \subseteq {1, nil}


TicTacToeInvariant == 
    /\ RowInvariant
    /\ ColInvariant
    /\ DiagInvariant  
--------------------------------

TicTacToeInit ==   
    /\ NextTurn = A
    /\ board = [i \in (1..9) |-> nil]
    /\ rows = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}}            \* 哪些位置构成行
    /\ cols = {{1, 4, 7}, {2, 5, 8}, {3, 6, 9}}            \* 哪些位置构成列
    /\ diags = {{1, 5, 9}, {3, 5, 7}}                      \* 哪些位置构成对角线




put(p, val) == 
    /\ board' = [board EXCEPT ![p] = val]


Aplay(p) == 
    /\ NextTurn = A
    /\ p \in (1..9)
    /\ board[p] = nil
    /\ put(p, 0)
    /\ NextTurn' = B
  
  
Bplay(p) ==
    /\ NextTurn = B
    /\ p \in (1..9)
    /\ board[p] = nil
    /\ put(p, 1)
    /\ NextTurn' = A
    
Done == 
    /\ \A p \in (1..9): board[p] # nil
    /\ UNCHANGED <<NextTurn, board>>
   
TicTacToeNext == 
    /\ \E p \in (1..9): Aplay(p) \/ Bplay(p) \/ Done
    /\ UNCHANGED <<rows, cols, diags>>
    

  














==================================