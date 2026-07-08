/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Surface hypotheses

This file records the manifold assumptions used by the Lean Eval target.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Topological invariance of the boundary stratum for C0 half-space charts.

This is the explicit extra hypothesis isolating the hard pure-topology theorem: a point that is a
mathlib manifold-boundary point is sent by every preferred half-space chart containing it to the
frontier of that chart's extended target.  Mathlib proves this automatically for positive
regularity, but the C0 case is the deferred invariance-of-boundary project. -/
class ChartBoundaryInvariant (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] where
  chartAt_extend_mem_frontier_target_of_boundary :
    ∀ (x : S) {y : S},
      y ∈ (chartAt (EuclideanHalfSpace 2) x).source →
      y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S →
      (chartAt (EuclideanHalfSpace 2) x).extend (modelWithCornersEuclideanHalfSpace 2) y ∈
        frontier
          (((chartAt (EuclideanHalfSpace 2) x).extend
            (modelWithCornersEuclideanHalfSpace 2)).target)

instance chartBoundaryInvariant_of_contMDiff
    (S : Type*) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S] :
    ChartBoundaryInvariant S where
  chartAt_extend_mem_frontier_target_of_boundary := by
    intro x y hySource hyBoundary
    let I := modelWithCornersEuclideanHalfSpace 2
    exact
      (I.isBoundaryPoint_iff_of_mem_atlas (M := S) (n := 1) (by norm_num)
        (chart_mem_atlas (EuclideanHalfSpace 2) x) hySource).mp hyBoundary

/-- The Eval topological hypotheses plus the current C0 boundary-invariance bridge.

Most theorem statements should keep using the typeclass hypotheses directly. This wrapper is useful
for blueprint references and for APIs that want to pass the full Eval-surface bundle as data. -/
structure EvalSurface (S : Type*) [TopologicalSpace S] where
  t2 : T2Space S
  connected : ConnectedSpace S
  compact : CompactSpace S
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  manifold : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S
  boundaryInvariant : ChartBoundaryInvariant S

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
variable [ChartBoundaryInvariant S]

/-- Package the active typeclass hypotheses as an `EvalSurface`. -/
def evalSurface : EvalSurface S where
  t2 := inferInstance
  connected := inferInstance
  compact := inferInstance
  charted := inferInstance
  manifold := inferInstance
  boundaryInvariant := inferInstance

/-- Marker theorem packaging the active Eval and boundary-invariance assumptions. -/
theorem eval_surface_hypotheses : Nonempty (EvalSurface S) :=
  ⟨evalSurface S⟩

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
