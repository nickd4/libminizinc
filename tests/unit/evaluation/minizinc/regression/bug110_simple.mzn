% RUNS ON mzn20_fd
% RUNS ON mzn-fzn_fd
% RUNS ON mzn20_fd_linear
% RUNS ON mzn20_mip

% vim: et ts=4
% Cut down version of MiniZinc bug 110.
% When flattened with mzn2fzn 1.1 this model results in negative
% (and more generally out-of-bounds) array accesses.

array[1..5,1..5] of var 0..2: board;

constraint 
 forall(row,col in 1..5) ( 
   ( board[row, col] = 1 ->
       forall(i in 1..5) (
          (((row-i > 0) /\ (col-i > 0)) -> (board[row-i,col-i] < 2))  
        )
   )
);

solve satisfy;

output ["board = ", show(board), ";\n"];
