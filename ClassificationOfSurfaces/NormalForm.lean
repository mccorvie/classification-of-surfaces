/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplex
import ClassificationOfSurfaces.Representatives

/-!
# Normal-form reduction

This file owns the combinatorial part of the project: finite cell complexes reduce, via the allowed
Gallier-Xu transformations, to one of the normal forms appearing in the eval theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The normal forms that actually appear in the Lean Eval conclusion.

The orientable sphere is represented by the separate sphere branch, so an orientable polygonal
normal form must have a handle or a boundary component; nonorientable forms must have at least one
crosscap. -/
def NormalForm.IsEvalAdmissible : NormalForm → Prop
  | NormalForm.sphere => True
  | NormalForm.orientable handles boundaryComponents =>
      1 ≤ handles ∨ 1 ≤ boundaryComponents
  | NormalForm.nonOrientable crosscaps _boundaryComponents => 1 ≤ crosscaps

/-- A surface cell complex realizes the quotient space attached to a named normal form.

This is the local target for the Gallier--Xu canonical-complex construction.  The current
representative quotient spaces are still placeholders, but the predicate already has the final
homeomorphism shape needed by the Eval theorem. -/
def SurfaceCellComplex.RealizesNormalForm (K : SurfaceCellComplex) : NormalForm → Prop
  | NormalForm.sphere => Nonempty (K.Realization ≃ₜ SphereRepresentative)
  | NormalForm.orientable handles boundaryComponents =>
      Nonempty (K.Realization ≃ₜ Quot (OrientableRel handles boundaryComponents))
  | NormalForm.nonOrientable crosscaps boundaryComponents =>
      Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel crosscaps boundaryComponents))

/-- Data that a surface cell complex has been reduced to a named normal form.

The representative cell complex is still abstract until the Gallier--Xu canonical complexes are
implemented, but the relation is no longer the proposition `True`: it carries a concrete
cell-complex representative, a realization-preserving equivalence witness, and a witness that the
representative realizes the named Eval quotient. -/
def SurfaceCellComplex.HasNormalForm (K : SurfaceCellComplex) (N : NormalForm) : Prop :=
  ∃ representative : SurfaceCellComplex,
    K.Equivalent representative ∧ representative.RealizesNormalForm N

/-- Compatibility spelling for the initial scaffold namespace. -/
abbrev CellComplex.HasNormalForm (K : CellComplex) (N : NormalForm) : Prop :=
  SurfaceCellComplex.HasNormalForm K N

/-- Build normal-form data when the complex itself already realizes the named quotient. -/
theorem SurfaceCellComplex.hasNormalFormOfRealizes (K : SurfaceCellComplex) (N : NormalForm)
    (h : K.RealizesNormalForm N) :
    K.HasNormalForm N :=
  ⟨K, ⟨Homeomorph.refl K.Realization⟩, h⟩

/-- Combinatorial bridge: every finite connected surface cell complex reduces to normal form. -/
theorem surface_cell_complex_reduces_to_normal_form (K : SurfaceCellComplex) :
    ∃ N : NormalForm, N.IsEvalAdmissible ∧ K.HasNormalForm N := by
  sorry

/-- Compatibility spelling for the initial scaffold theorem name. -/
theorem cell_complex_reduces_to_normal_form (K : CellComplex) :
    ∃ N : NormalForm, N.IsEvalAdmissible ∧ K.HasNormalForm N :=
  surface_cell_complex_reduces_to_normal_form K

/-- Convert a named normal-form witness to the disjunction shape used by the Eval statement. -/
theorem SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm
    {K : SurfaceCellComplex} {N : NormalForm}
    (hN : N.IsEvalAdmissible) (h : K.HasNormalForm N) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) := by
  rcases h with ⟨_representative, hEquivalent, hRealizes⟩
  rcases hEquivalent with ⟨hKR⟩
  cases N with
  | sphere =>
      rcases hRealizes with ⟨hRS⟩
      exact Or.inl ⟨hKR.trans hRS⟩
  | orientable handles boundaryComponents =>
      rcases hRealizes with ⟨hRQ⟩
      exact Or.inr
        ⟨handles, boundaryComponents, Or.inl ⟨hN, ⟨hKR.trans hRQ⟩⟩⟩
  | nonOrientable crosscaps boundaryComponents =>
      rcases hRealizes with ⟨hRQ⟩
      exact Or.inr
        ⟨crosscaps, boundaryComponents, Or.inr ⟨hN, ⟨hKR.trans hRQ⟩⟩⟩

/-- Final combinatorial output in the shape needed by the eval theorem, before transporting across
homeomorphisms from the triangulation step. -/
theorem SurfaceCellComplex.hasEvalRepresentative (K : SurfaceCellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) := by
  rcases surface_cell_complex_reduces_to_normal_form K with ⟨N, hN, hK⟩
  exact SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm hN hK

/-- Compatibility spelling for the initial scaffold theorem name. -/
theorem cell_complex_has_eval_representative (K : CellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) :=
  SurfaceCellComplex.hasEvalRepresentative K

end ClassificationOfSurfaces
end Topology
end LeanEval
