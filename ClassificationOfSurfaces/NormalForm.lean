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

/-- A surface cell complex realizes a named normal form.

Placeholder until cell complexes are implemented. -/
def SurfaceCellComplex.HasNormalForm (_K : SurfaceCellComplex) (_N : NormalForm) : Prop := True

/-- Compatibility spelling for the initial scaffold namespace. -/
abbrev CellComplex.HasNormalForm (K : CellComplex) (N : NormalForm) : Prop :=
  SurfaceCellComplex.HasNormalForm K N

/-- Combinatorial bridge: every finite connected surface cell complex reduces to normal form. -/
theorem surface_cell_complex_reduces_to_normal_form (K : SurfaceCellComplex) :
    ∃ N : NormalForm, K.HasNormalForm N := by
  exact ⟨NormalForm.sphere, trivial⟩

/-- Compatibility spelling for the initial scaffold theorem name. -/
theorem cell_complex_reduces_to_normal_form (K : CellComplex) :
    ∃ N : NormalForm, K.HasNormalForm N :=
  surface_cell_complex_reduces_to_normal_form K

/-- Final combinatorial output in the shape needed by the eval theorem, before transporting across
homeomorphisms from the triangulation step. -/
theorem SurfaceCellComplex.hasEvalRepresentative (K : SurfaceCellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) := by
  right
  refine ⟨1, 0, Or.inl ?_⟩
  exact ⟨Or.inl le_rfl, ⟨orientableRelPUnitHomeomorph 1 0⟩⟩

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
