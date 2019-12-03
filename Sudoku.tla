-------------MODULE Sudoku-------------

EXTENDS Naturals

VARIABLE sudoku

VARIABLES rows, cols, diags, blocks




SudokuInit == 
    /\ sudoku = [i \in (1..81) |-> "nil"]
    /\ rows = 
    






SudokuNext == 
    \E p \in (1..81), val \in (1..9): /\ sudoku[p] = "nil"
                                      /\ [sudoku EXCEPT ![p] = val]
        
        
RowInvariant ==
    \A row \in rows: row = {1, 2, 3, 4, 5, 6, 7, 8, 9}


ColInvariant == 
    \A col \in cols: col = {1, 2, 3, 4, 5, 6, 7, 8, 9}


DiagInvariant == 
    \A diag \in diags: diag = {1, 2, 3, 4, 5, 6, 7, 8, 9}
    
BlockInvariant == 
    \A block \in blocks: block = {1, 2, 3, 4, 5, 6, 7, 8, 9}
    


SudokuInvariant ==
    /\ RowInvariant 
    /\ ColInvariant
    /\ DiagInvariant
    /\ BlockInvariant
    
                     




=========================