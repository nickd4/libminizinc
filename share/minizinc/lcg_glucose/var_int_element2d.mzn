predicate var_int_element2d(
  set of int: x_domain,
  set of int: y_domain,
  array[int] of var int: a,
  var int: x,
  var int: y,
  var int: z
) =
x in x_domain /\
y in y_domain /\
forall (i in x_domain, j in y_domain) (
  (x = i /\ y = j) -> (z = array2d(x_domain, y_domain, a)[i, j])
);
