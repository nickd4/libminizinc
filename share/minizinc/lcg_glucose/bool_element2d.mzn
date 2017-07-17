% this is not really used at the moment, as it's commented out in builtins.mzn
predicate bool_element2d(
  set of int: x_domain,
  set of int: y_domain,
  array[int] of bool: a,
  var int: x,
  var int: y,
  var bool: z
) =
x in x_domain /\
y in y_domain /\
% this does not work well because MiniZinc integerizes the domain:
%forall (i in dom(z)) (
%  (z = i) = exists (
%    j in x_domain,
%    k in y_domain
%    where array2d(x_domain, y_domain, a)[j, k] = i
%  ) (
%    x = j /\ y = k
%  )
%);
z = forall (
  j in x_domain,
  k in y_domain
  where not array2d(x_domain, y_domain, a)[j, k]
) (
  not (x = j /\ y = k)
) /\
z = exists (
  j in x_domain,
  k in y_domain
  where array2d(x_domain, y_domain, a)[j, k]
) (
  x = j /\ y = k
);
