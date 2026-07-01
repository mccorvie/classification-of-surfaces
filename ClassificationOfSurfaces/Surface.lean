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

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- Marker theorem for the exact topological assumptions in the eval statement. -/
theorem eval_surface_hypotheses : True := by
  trivial

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
