/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.Brouwer
import ClassificationOfSurfaces.Surface

/-!
# Boundary invariance for C0 surface charts

This file discharges the `ChartBoundaryInvariant` interface for topological surface charts.
The plane has invariance of domain by `Moise.instBrouwerFixedPointPlane` and the general
invariance-of-domain theorem.  Steven Sivek's chart-independence argument then shows that a
manifold-boundary point is sent to the frontier of the model range by every chart containing it.
The frontier of the chart's extended target follows because its interior is contained in the
interior of the model range.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open InvarianceOfDomain Set

/-- C0 invariance of the boundary stratum for surface charts, derived from planar invariance of
domain. -/
instance chartBoundaryInvariant_of_invarianceOfDomain
    (S : Type*) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S] :
    ChartBoundaryInvariant S where
  chartAt_extend_mem_frontier_target_of_boundary := by
    intro x y hySource hyBoundary
    let I := modelWithCornersEuclideanHalfSpace 2
    let f := chartAt (EuclideanHalfSpace 2) x
    change f.extend I y ∈ frontier (f.extend I).target
    have hyFrontierRange : f.extend I y ∈ frontier (Set.range I) := by
      exact (isBoundaryPoint_iff_any_chart I (f := f) hySource).mp hyBoundary
    have hyTarget : f.extend I y ∈ (f.extend I).target := by
      apply (f.extend I).map_source
      rwa [f.extend_source]
    apply (mem_frontier_iff_notMem_interior hyTarget).2
    intro hyInterior
    have hyNotInteriorRange : f.extend I y ∉ interior (Set.range I) :=
      (mem_frontier_iff_notMem_interior (Set.mem_range_self (f y))).1 hyFrontierRange
    exact hyNotInteriorRange (f.interior_extend_target_subset_interior_range hyInterior)

end ClassificationOfSurfaces
end Topology
end LeanEval
