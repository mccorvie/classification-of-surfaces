# Generic Radó induction step

Let `T` satisfy the Radó invariant and let `c` be the next boundary-faithful chart. If the chart core
is already contained in the interior of `T.support`, reuse `T`. If the old absorbed set is contained
in the interior of the chart patch, use the patch. In the remaining case, apply the face-family
gluing constructor and prove the strengthened invariant for its output.

The current theorem already proves the first two cases. The final case must use a data-rich gluing
result; merely obtaining an opaque partial triangulation cannot establish edge-valence or
dual-connectivity preservation.
