-------------MODULE Sudoku-------------

EXTENDS Naturals


CONSTANT nil

VARIABLE sudoku

VARIABLES rows, cols, diags, blocks




SudokuInit == 
    /\ sudoku = [i \in (1..81) |-> nil]
    /\ rows = [i \in (1..9) |-> [j \in (1..9) |-> i * j]]
    /\ cols = [i \in (1..9) |-> [j \in (1..9) |-> i +  (j - 1) * 9]]
    /\ diags = {{1, 11, 21, 31, 41, 51, 61, 71, 81}, {9, 17, 25, 33, 41, 49, 57, 65, 73}}
    /\ blocks = [i \in {11, 14, 17, 38, 41, 44, 65, 68, 71} |-> {i-10, i-9, i-8, i-1, i, i+1, i+8, i+9, i+10}]
    




SudokuNext == 
    CHOOSE p \in (1..81): CHOOSE val \in (1..9): 
                                      /\ sudoku[p] = nil
                                      /\ sudoku' = [sudoku EXCEPT ![p] = val]
                                      /\ UNCHANGED <<rows, cols, diags, blocks>>
        
        
RowInvariant ==
    \A i \in (1..9): 
        \A m, n \in (1..9): \/ sudoku[rows[i][m]] # sudoku[rows[i][n]]
                            \/ (sudoku[rows[i][m]] = nil /\ sudoku[rows[i][n]] = nil)
                            \/ m = n
        

ColInvariant == 
    \A i \in (1..9): 
        \A m, n \in (1..9): \/ sudoku[rows[i][m]] # sudoku[rows[i][n]]
                            \/ (sudoku[rows[i][m]] = nil /\ sudoku[rows[i][n]] = nil)
                            \/ m = n


DiagInvariant == 
    \A diag \in diags: 
        \A m, n \in diag: \/ sudoku[m] # sudoku[n]
                          \/ (sudoku[m] = nil /\ sudoku[n] = nil)
                          \/ m = n
    
BlockInvariant == 
    \A i \in DOMAIN blocks: 
        \A m, n \in blocks[i]: \/ sudoku[m] # sudoku[n]
                               \/ (sudoku[m] = nil /\ sudoku[n] = nil)
                               \/ m = n
    


SudokuInvariant ==
    /\ RowInvariant 
    /\ ColInvariant
    /\ DiagInvariant
    /\ BlockInvariant
    
                     




=========================