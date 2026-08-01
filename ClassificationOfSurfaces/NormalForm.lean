/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicCanonicalRealization
import ClassificationOfSurfaces.FiniteCyclicSphereRealization
import ClassificationOfSurfaces.FiniteCyclicTerminalNormalization

/-!
# Faithful normal-form classification

This file composes the Gallier--Xu normalization of a valid connected finite-cyclic presentation
with the exact realization homeomorphisms for the three canonical endpoints.  Every type in this
chain is a faithful polygonal quotient.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace NormalForm

/-- The canonical presentation of an admissible normal form realizes its selected topological
representative. -/
noncomputable def canonicalRealizationHomeomorph
    (N : NormalForm) (hN : N.IsEvalAdmissible) :
    N.canonicalPresentation.PolygonalRealization
        (N.canonicalPresentation_isSurfaceValid hN) ≃ₜ
      N.Representative := by
  cases N with
  | sphere => exact canonicalSphereRealizationHomeomorph
  | orientable p n => exact canonicalOrientableRealizationHomeomorph hN
  | nonOrientable p n => exact canonicalNonOrientableRealizationHomeomorph hN

end NormalForm

namespace FiniteCyclicPresentation.NormalizationResult

/-- A normalization result identifies the input realization with the concrete representative
selected by its normal-form index. -/
noncomputable def representativeHomeomorph
    {P : FiniteCyclicPresentation.ValidPresentation}
    (result : FiniteCyclicPresentation.NormalizationResult P) :
    P.presentation.PolygonalRealization P.valid ≃ₜ
      result.normalForm.Representative :=
  result.realizationHomeomorph.trans
    (result.normalForm.canonicalRealizationHomeomorph result.admissible)

end FiniteCyclicPresentation.NormalizationResult

/-- A valid connected finite-cyclic presentation has an admissible normal form whose concrete
representative is homeomorphic to its faithful polygonal realization. -/
theorem FiniteCyclicPresentation.exists_homeomorphic_normalForm
    (P : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid) (connectedP : P.IsConnected) :
    ∃ N : NormalForm,
      N.IsEvalAdmissible ∧
        Nonempty (P.PolygonalRealization validP ≃ₜ N.Representative) := by
  let result :=
    FiniteCyclicPresentation.normalizeConnectedToCanonical
      ⟨P, validP⟩ connectedP
  exact
    ⟨result.normalForm, result.admissible,
      ⟨result.representativeHomeomorph⟩⟩

/-- A valid connected finite-cyclic presentation has one of the exact Eval representatives.

This is the compatibility form of `FiniteCyclicPresentation.exists_homeomorphic_normalForm`,
with the indexed representative expanded into the nested disjunction required by Lean-Eval. -/
theorem FiniteCyclicPresentation.hasEvalRepresentative
    (P : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid) (connectedP : P.IsConnected) :
    Nonempty (P.PolygonalRealization validP ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧
            Nonempty (P.PolygonalRealization validP ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧
            Nonempty (P.PolygonalRealization validP ≃ₜ Quot (NonOrientableRel p n))) := by
  obtain ⟨N, hN, hPN⟩ :=
    P.exists_homeomorphic_normalForm validP connectedP
  cases N with
  | sphere => exact Or.inl hPN
  | orientable p n => exact Or.inr ⟨p, n, Or.inl ⟨hN, hPN⟩⟩
  | nonOrientable p n => exact Or.inr ⟨p, n, Or.inr ⟨hN, hPN⟩⟩

end ClassificationOfSurfaces
end Topology
end LeanEval
