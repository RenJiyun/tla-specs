------------MODULE TicTacToe----------

EXTENDS Sequences, Naturals

VARIABLE NextTurn

VARIABLE board
VARIABLES rows, cols, diags



RowInvariant ==
    /\ \A row \in rows: 
            LET rowVal == [i \in row |-> board[i]]
            IN rowVal \in Seq({0, 2}) \/ rowVal \in Seq({1, 2})
    
    
ColInvariant == 
    /\ \A col \in cols: 
            LET colVal == [i \in col |-> board[i]]
            IN colVal \in Seq({0, 2}) \/ colVal \in Seq({1, 2})


DiagInvariant ==
    /\ \A diag \in diags: 
            LET diagVal == [i \in diag |-> board[i]]
            IN diagVal \in Seq({0, 2}) \/ diagVal \in Seq({1, 2})


TicTacToeInvariant == 
    /\ RowInvariant
    /\ ColInvariant
    /\ DiagInvariant  
--------------------------------

TicTacToeInit ==   
    /\ NextTurn = "A"
    /\ board = [i \in (1..9) |-> 2]
    /\ rows = {<<1, 2, 3>>, <<4, 5, 6>>, <<7, 8, 9>>}
    /\ cols = {<<1, 4, 7>>, <<2, 5, 8>>, <<3, 6, 9>>}
    /\ diags = {<<1, 5, 9>>, <<3, 5, 7>>}




put(p, val) == 
    /\ board' = [board EXCEPT ![p] = val]


Aplay(p) == 
    /\ NextTurn = "A"
    /\ p \in (1..9)
    /\ board[p] = 2
    /\ put(p, 0)
    /\ NextTurn' = "B"
  
  
Bplay(p) ==
    /\ NextTurn = "B"
    /\ p \in (1..9)
    /\ board[p] = 2
    /\ put(p, 1)
    /\ NextTurn' = "A"
    
Done == 
    /\ \A p \in (1..9): board[p] # 2
    /\ UNCHANGED <<NextTurn, board>>
   
TicTacToeNext == 
    /\ \E p \in (1..9): Aplay(p) \/ Bplay(p) \/ Done
    /\ UNCHANGED <<rows, cols, diags>>
    

  














==================================