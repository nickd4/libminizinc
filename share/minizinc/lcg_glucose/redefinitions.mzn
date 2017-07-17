include "bool_element1d.mzn";
include "var_bool_element1d.mzn";
include "int_element1d.mzn";
include "var_int_element1d.mzn";

% annotations for alldifferent
annotation feydy;

% annotations for search spec
annotation restart(int: restart_type, int: restart_first, float: restart_inc);
annotation activity;
annotation circulation_split;
annotation min_cost_flow_split;

predicate array_bool_element(var int: x, array[int] of bool: a, var bool: y) =
bool_element1d(index_set(a), a, x, y);

predicate array_var_bool_element(var int: x, array[int] of var bool: a, var bool: y) =
var_bool_element1d(index_set(a), a, x, y);

predicate array_int_element(var int: x, array[int] of int: a, var int: y) =
int_element1d(index_set(a), a, x, y);

predicate array_var_int_element(var int: x, array[int] of var int: a, var int: y) =
var_int_element1d(index_set(a), a, x, y);
