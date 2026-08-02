import Schoenflies.LocalizedJordanAnnularOrder
import Schoenflies.StandardPolygonalCollars

/-!
# Standard target cells carrying the original boundary labels

The cut-free arc selected on the original Jordan curve is transported to
two consecutive homothetic target boundaries.  Radial segments at its
endpoints then give a standard polygonal annular cell with exactly the same
labels as the localized source cell.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

private abbrev targetDisk (n : ℕ) : PolygonalCircle :=
  StandardPolygonalCollars.disk n

/-- Transport the cell's oriented original-Jordan split to target boundary
`n`. -/
noncomputable def targetBoundarySplit (n : ℕ) :
    (targetDisk n).toJordanCircle.TwoBoundaryArcPaths
      (homothetyPoint (radius n) (I.levelTargetBoundaryPoint a))
      (homothetyPoint (radius n)
        (I.levelTargetBoundaryPoint C.next)) :=
  (C.jordanCellBoundarySplit.mapCarrier
      (jordanToDiskBoundaryHomeomorph J n)).cast
    (by
      simp only [jordanToDiskBoundaryHomeomorph_apply]
      rfl)
    (by
      simp only [jordanToDiskBoundaryHomeomorph_apply]
      rfl)

theorem other_levelTargetPoint_mem_boundarySplit_second
    (n : ℕ) (c : LevelAddress k) (hca : c ≠ a)
    (hcnext : c ≠ C.next) :
    homothetyPoint (radius n) (I.levelTargetBoundaryPoint c) ∈
      range (C.targetBoundarySplit n).second := by
  obtain ⟨t, ht⟩ :=
    C.other_jordanOuterPoint_mem_cellBoundarySplit_second c hca hcnext
  refine ⟨t, ?_⟩
  change (jordanToDiskBoundaryHomeomorph J n
      ⟨C.jordanCellBoundarySplit.second t, _⟩ : Plane) = _
  rw [jordanToDiskBoundaryHomeomorph_apply]
  congr 1
  have hsub :
      (⟨C.jordanCellBoundarySplit.second t,
        C.jordanCellBoundarySplit.second_range_subset_carrier
          ⟨t, rfl⟩⟩ : J.carrier) =
        ⟨(I.levelLocalizedJordanAnnularCrosscut k c).outerPoint,
          (I.levelLocalizedJordanAnnularCrosscut k c).outerPoint_mem⟩ :=
    Subtype.ext ht
  rw [hsub]
  rfl

/-- The synchronized target separator pair at source shell level `k`. -/
noncomputable def targetSeparator :
    PolygonalCircle.AnnularCrosscut.SeparatorPair
      (I.levelTargetAnnularCrosscut k a)
      (I.levelTargetAnnularCrosscut k C.next) where
  innerSplit := C.targetBoundarySplit (k + 1)
  outerSplit := C.targetBoundarySplit (k + 2)

/-- The target radial annulus equipped with the transported complementary
boundary paths. -/
noncomputable def targetDecomposition :
    PolygonalCircle.AnnularCellDecomposition
      (targetDisk (k + 1)) (targetDisk (k + 2)) where
  first := I.levelTargetAnnularCrosscut k a
  second := I.levelTargetAnnularCrosscut k C.next
  separator := C.targetSeparator
  nested := disk_strictlyNested (k + 1)
  disjoint := I.pairwise_disjoint_levelTargetAnnularCrosscut k C.next_ne
  outerPoints_ne := by
    intro h
    exact C.next_ne <| I.levelTargetBoundaryPoint_injective k <|
      (homothetyHomeomorph (radius (k + 2))
        (radius_pos (k + 2)).ne').injective <| by
          simpa only [homothetyHomeomorph_apply,
            JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
            JordanCircle.InitialAngularArcs.levelTargetOuterMark] using h
  innerPoints_ne := by
    intro h
    exact C.next_ne <| I.levelTargetBoundaryPoint_injective k <|
      (homothetyHomeomorph (radius (k + 1))
        (radius_pos (k + 1)).ne').injective <| by
          simpa only [homothetyHomeomorph_apply,
            JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
            JordanCircle.InitialAngularArcs.levelTargetInnerMark] using h
  first_segment := by
    change range (Path.segment
      (I.levelTargetOuterMark k a) (I.levelTargetInnerMark k a)) = _
    exact Path.range_segment _ _
  second_segment := by
    change range (Path.segment
      (I.levelTargetOuterMark k C.next)
      (I.levelTargetInnerMark k C.next)) = _
    exact Path.range_segment _ _

def targetFirstAlternative : Prop :=
  (targetDisk (k + 1)).interiorRegion ⊆
    (C.targetSeparator.circle₀
      (disk_strictlyNested (k + 1))
      (I.pairwise_disjoint_levelTargetAnnularCrosscut k
        C.next_ne)).inside

theorem target_separatorSide :
    C.targetFirstAlternative ∨
      (targetDisk (k + 1)).interiorRegion ⊆
        (C.targetSeparator.circle₁
          (disk_strictlyNested (k + 1))
          (I.pairwise_disjoint_levelTargetAnnularCrosscut k
            C.next_ne)).inside := by
  rcases C.targetSeparator.innerInterior_separatorSide_dichotomy
      (disk_strictlyNested (k + 1))
      (I.pairwise_disjoint_levelTargetAnnularCrosscut k C.next_ne)
      (C.targetDecomposition.first_segment)
      (C.targetDecomposition.second_segment) with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

theorem targetSecondAlternative_of_not_first
    (h : ¬ C.targetFirstAlternative) :
    (targetDisk (k + 1)).interiorRegion ⊆
      (C.targetSeparator.circle₁
        (disk_strictlyNested (k + 1))
        (I.pairwise_disjoint_levelTargetAnnularCrosscut k
          C.next_ne)).inside :=
  C.target_separatorSide.resolve_left h

/-- The radially transported target cell, attached to target disk `k + 1`
along the image of the selected original Jordan arc. -/
noncomputable def targetAttachmentPresentation :
    PolygonalDiskAttachment.Presentation
      (targetDisk (k + 1)).closedRegion := by
  classical
  exact if h : C.targetFirstAlternative then
      C.targetDecomposition.attachmentPresentation₁ h
    else C.targetDecomposition.attachmentPresentation₀
      (C.targetSecondAlternative_of_not_first h)

theorem range_targetAttachmentPresentation_shared :
    range C.targetAttachmentPresentation.shared =
      range (C.targetBoundarySplit (k + 1)).first := by
  classical
  by_cases h : C.targetFirstAlternative
  · rw [targetAttachmentPresentation, dif_pos h]
    rfl
  · rw [targetAttachmentPresentation, dif_neg h]
    rfl

end JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

end

end Schoenflies
