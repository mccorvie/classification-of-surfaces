/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.NormalForm
import ClassificationOfSurfaces.GeometricTriangulationRealization

/-!
# Lean Eval target theorem

This file contains the public theorem matching the Lean Eval problem statement.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Every compact connected Hausdorff topological 2-manifold with boundary is homeomorphic to the
concrete representative selected by some admissible normal form. -/
theorem exists_homeomorphic_normalForm (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ N : NormalForm,
      N.IsEvalAdmissible ∧ Nonempty (S ≃ₜ N.Representative) := by
  let P := compact_eval_surface_finiteCyclicPresentation S
  let validP := compact_eval_surface_finiteCyclicPresentation_isSurfaceValid S
  have connectedP : P.IsConnected :=
    compact_eval_surface_finiteCyclicPresentation_isConnected S
  obtain ⟨hPS⟩ :=
    compact_eval_surface_polygonalRealization_homeomorphic_surface S
  obtain ⟨N, hN, ⟨hPN⟩⟩ :=
    P.exists_homeomorphic_normalForm validP connectedP
  exact ⟨N, hN, ⟨hPS.symm.trans hPN⟩⟩

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
  obtain ⟨N, hN, hSN⟩ := exists_homeomorphic_normalForm S
  cases N with
  | sphere => exact Or.inl hSN
  | orientable p n => exact Or.inr ⟨p, n, Or.inl ⟨hN, hSN⟩⟩
  | nonOrientable p n => exact Or.inr ⟨p, n, Or.inr ⟨hN, hSN⟩⟩

/-- Blueprint-facing spelling of `classification_of_surfaces`. -/
theorem topological_classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) :=
  classification_of_surfaces S

end ClassificationOfSurfaces
end Topology
end LeanEval
