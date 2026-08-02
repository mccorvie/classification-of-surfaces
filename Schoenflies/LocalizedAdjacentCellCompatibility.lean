import Schoenflies.LocalizedCellHomeomorphisms

/-!
# Compatibility of adjacent localized collar cells

The cell fillings are constructed independently.  Their boundary
parameter control nevertheless makes them agree exactly on the radial cut
shared by a cell and its cyclic successor.  The statements allow arbitrary
membership proofs so they can be applied directly inside a closed-cover
gluing argument.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {k : ℕ} {a b : LevelAddress k}

/-- Forward cell maps agree pointwise on a common radial cut whenever the
second cell begins at the first cell's successor label. -/
theorem localizedCellHomeomorph_agree_on_commonCut
    (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b)
    (hnext : C.next = b) (t : unitInterval)
    (hC : (I.levelLocalizedAnnularCrosscut k b).path t ∈
      C.disk.closedRegion)
    (hD : (I.levelLocalizedAnnularCrosscut k b).path t ∈
      D.disk.closedRegion) :
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k b).path t, hC⟩ : Plane) =
      (D.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k b).path t, hD⟩ : Plane) := by
  subst b
  calc
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k C.next).path t, hC⟩ : Plane) =
        (I.levelTargetAnnularCrosscut k C.next).path t := by
      simpa only [] using C.cellHomeomorph_apply_successorCut t
    _ = (D.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k C.next).path t, hD⟩ :
          Plane) := by
      symm
      simpa only [] using D.cellHomeomorph_apply_initialCut t

/-- The inverse cell maps likewise agree on the corresponding target radial
cut. -/
theorem localizedCellHomeomorph_symm_agree_on_commonCut
    (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b)
    (hnext : C.next = b) (t : unitInterval)
    (hC : (I.levelTargetAnnularCrosscut k b).path t ∈
      C.targetAttachmentPresentation.disk.closedRegion)
    (hD : (I.levelTargetAnnularCrosscut k b).path t ∈
      D.targetAttachmentPresentation.disk.closedRegion) :
    (C.cellHomeomorph.symm
        ⟨(I.levelTargetAnnularCrosscut k b).path t, hC⟩ : Plane) =
      (D.cellHomeomorph.symm
        ⟨(I.levelTargetAnnularCrosscut k b).path t, hD⟩ : Plane) := by
  subst b
  let x := (I.levelLocalizedAnnularCrosscut k C.next).path t
  have hxC : x ∈ C.disk.closedRegion := by
    exact C.decomposition_secondPath_mem_disk_closedRegion t
  have hxD : x ∈ D.disk.closedRegion := by
    exact D.decomposition_firstPath_mem_disk_closedRegion t
  have hmapC : C.cellHomeomorph ⟨x, hxC⟩ =
      ⟨(I.levelTargetAnnularCrosscut k C.next).path t, hC⟩ := by
    apply Subtype.ext
    exact C.cellHomeomorph_apply_successorCut t
  have hmapD : D.cellHomeomorph ⟨x, hxD⟩ =
      ⟨(I.levelTargetAnnularCrosscut k C.next).path t, hD⟩ := by
    apply Subtype.ext
    exact D.cellHomeomorph_apply_initialCut t
  rw [← hmapC, ← hmapD,
    C.cellHomeomorph.symm_apply_apply,
    D.cellHomeomorph.symm_apply_apply]

end JordanCircle.InitialAngularArcs

end

end Schoenflies
