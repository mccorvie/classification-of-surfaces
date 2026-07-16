# Exact Lean Eval orientable and nonorientable relations

Let `ClosedUnitDisc` be the metric closed ball of radius one in the complex plane and let
`bdyPtOfReal r = exp(2πir)` be its boundary parametrization. Define the orientable relation by the
three constructor families `a`, `b`, and `c` from the trusted Lean Eval file, with denominators
`4p + 3n`. Define the nonorientable relation by its `a` and `c` constructor families, with
denominators `2p + 3n`.

These definitions should replace, under the same public names, the local `PUnit` carriers and
bottom relations. This is required for comparator-equivalence: a theorem about the current local
quotients is a theorem about a point, not the benchmark's surface representatives.
