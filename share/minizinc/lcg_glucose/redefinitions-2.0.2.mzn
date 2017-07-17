% This file contains redefinitions of standard builtins for version 2.0.2
% that can be overridden by solvers.

include "bool_element1d.mzn";
include "var_bool_element1d.mzn";
include "bool_element2d.mzn";
include "var_bool_element2d.mzn";
include "int_element1d.mzn";
include "var_int_element1d.mzn";
include "int_element2d.mzn";
include "var_int_element2d.mzn";

predicate symmetry_breaking_constraint(var bool: b) = b;

predicate redundant_constraint(var bool: b) = b;



predicate array_var_bool_element_nonshifted(var int: idx, array[int] of bool: x, var bool: c) =
  bool_element1d(index_set(x), array1d(x), idx, c);
predicate array_var_bool_element_nonshifted(var int: idx, array[int] of var bool: x, var bool: c) =
  var_bool_element1d(index_set(x), array1d(x), idx, c);

% Nick 2D version with index not flattened to 1D
predicate array_var_bool_element_nonshifted(var int: idx1, var int: idx2, array[int,int] of bool: x, var bool: c) =
  let {
    int: dim = card(index_set_2of2(x));
    int: min_flat = min(index_set_1of2(x))*dim+min(index_set_2of2(x))-1;
  } in
  bool_element2d(index_set_1of2(x), index_set_2of2(x), array1d(x), idx1, idx2, c);
predicate array_var_bool_element_nonshifted(var int: idx1, var int: idx2, array[int,int] of var bool: x, var bool: c) =
  let {
    int: dim = card(index_set_2of2(x));
    int: min_flat = min(index_set_1of2(x))*dim+min(index_set_2of2(x))-1;
  } in
  var_bool_element2d(index_set_1of2(x), index_set_2of2(x), array1d(x), idx1, idx2, c);

predicate array_var_int_element_nonshifted(var int: idx, array[int] of int: x, var int: c) =
  int_element1d(index_set(x), array1d(x), idx, c);
predicate array_var_int_element_nonshifted(var int: idx, array[int] of var int: x, var int: c) =
  var_int_element1d(index_set(x), array1d(x), idx, c);

% Nick 2D version with index not flattened to 1D
predicate array_var_int_element_nonshifted(var int: idx1, var int: idx2, array[int,int] of int: x, var int: c) =
  let {
    int: dim = card(index_set_2of2(x));
    int: min_flat = min(index_set_1of2(x))*dim+min(index_set_2of2(x))-1;
  } in
  int_element2d(index_set_1of2(x), index_set_2of2(x), array1d(x), idx1, idx2, c);
predicate array_var_int_element_nonshifted(var int: idx1, var int: idx2, array[int,int] of var int: x, var int: c) =
  let {
    int: dim = card(index_set_2of2(x));
    int: min_flat = min(index_set_1of2(x))*dim+min(index_set_2of2(x))-1;
  } in
  var_int_element2d(index_set_1of2(x), index_set_2of2(x), array1d(x), idx1, idx2, c);

predicate array_var_float_element_nonshifted(var int: idx, array[int] of var float: x, var float: c) =
  array_var_float_element((idx-(min(index_set(x))-1))::domain,array1d(x),c);

predicate array_var_set_element_nonshifted(var int: idx, array[int] of var set of int: x, var set of int: c) =
  array_var_set_element((idx-(min(index_set(x))-1))::domain,array1d(x),c);
