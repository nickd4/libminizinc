include "circulation.mzn";
include "min_cost_flow.mzn";

predicate network_flow(
  array[int, 1..2] of int: arc, 
  array[int] of int: balance,
  array[int] of var int: flow
) =
circulation(
  [
    sum (j in 1..length(flow) where arc[j, 1] = i) (flow[j]) -
    sum (j in 1..length(flow) where arc[j, 2] = i) (flow[j]) =
    balance[i]
  | i in 1..length(balance)
  ]
);

predicate network_flow_cost(
  array[int, 1..2] of int: arc, 
  array[int] of int: balance,
  array[int] of int: weight,
  array[int] of var int: flow,
  var int: cost
) =
cost <= sum (i in 1..length(flow)) (weight[i] * flow[i]) /\
min_cost_flow(
  cost >= sum (i in 1..length(flow)) (weight[i] * flow[i]),
  [
    sum (j in 1..length(flow) where arc[j, 1] = i) (flow[j]) -
    sum (j in 1..length(flow) where arc[j, 2] = i) (flow[j]) =
    balance[i]
  | i in 1..length(balance)
  ]
);
