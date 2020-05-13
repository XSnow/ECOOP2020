Definition disjointSpec A B :=
  forall C, sub A C -> sub B C -> topLike C.

Definition consistencySpec v1 v2 :=
  forall A v1' v2', TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.
