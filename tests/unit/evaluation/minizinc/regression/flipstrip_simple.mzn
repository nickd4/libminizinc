% RUNS ON mzn20_fd
% RUNS ON mzn-fzn_fd
% flipstrip
% miniimize the number of moves to turn all bools to true

array[1..1] of bool: pos = [false];

var 1..1: f1;

constraint false \/ not pos[f1];
 
solve satisfy;

output [ "f1 = ",show(f1),";\n" ];
