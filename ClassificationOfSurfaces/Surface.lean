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

/-- The exact topological hypotheses from the Lean Eval problem, packaged as an optional wrapper.

Most theorem statements should keep using the typeclass hypotheses directly. This wrapper is useful
for blueprint references and for APIs that want to pass the full Eval-surface bundle as data. -/
structure EvalSurface (S : Type*) [TopologicalSpace S] where
  t2 : T2Space S
  connected : ConnectedSpace S
  compact : CompactSpace S
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  manifold : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- Package the active typeclass hypotheses as an `EvalSurface`. -/
def evalSurface : EvalSurface S where
  t2 := inferInstance
  connected := inferInstance
  compact := inferInstance
  charted := inferInstance
  manifold := inferInstance

/-- Marker theorem packaging the exact topological assumptions in the eval statement. -/
theorem eval_surface_hypotheses : Nonempty (EvalSurface S) :=
  ⟨evalSurface S⟩

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
