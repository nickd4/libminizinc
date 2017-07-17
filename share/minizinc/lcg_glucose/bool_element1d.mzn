predicate bool_element1d(
  set of int: x_domain,
  array[int] of bool: a,
  var int: x,
  var bool: y
) =
x in x_domain /\
% this does not work well because MiniZinc integerizes the domain:
%forall (i in dom(y)) (
%  (y = i) = exists (j in x_domain where array1d(x_domain, a)[j] = i) (x = j)
%);
y = forall (j in x_domain where not array1d(x_domain, a)[j]) (x != j) /\
y = exists (j in x_domain where array1d(x_domain, a)[j]) (x = j);
