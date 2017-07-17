predicate var_int_element1d(
  set of int: x_domain,
  array[int] of var int: a,
  var int: x,
  var int: y
) =
x in x_domain /\
forall (i in x_domain) (
  (x = i) -> (y = array1d(x_domain, a)[i])
);
