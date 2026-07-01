/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.NormalForm

/-!
# Lean Eval target theorem

This file contains the public theorem matching the Lean Eval problem statement.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Every compact connected Hausdorff topological 2-manifold with boundary is homeomorphic to the
sphere, an orientable normal-form quotient, or a non-orientable normal-form quotient. -/
theorem classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) := by
  have _htriangulable : Triangulable S := compact_surface_triangulable S
  sorry

end ClassificationOfSurfaces
end Topology
end LeanEval
