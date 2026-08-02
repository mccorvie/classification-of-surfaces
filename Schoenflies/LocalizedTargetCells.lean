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

/-- From the first genuine refinement level onward, the synchronized radial
target splits select the first separator alternative.  A third retained
mark lies on the second path at both radii, ruling out the alternative which
would put it on the first outer path. -/
theorem targetFirstAlternative_of_one_le (hk : 1 ≤ k) :
    C.targetFirstAlternative := by
  have hinnerInjective : Injective fun c : LevelAddress k =>
      (I.levelTargetAnnularCrosscut k c).innerPoint := by
    intro c d hcd
    apply I.levelTargetBoundaryPoint_injective k
    apply (homothetyHomeomorph (radius (k + 1))
      (radius_pos (k + 1)).ne').injective
    simpa only [homothetyHomeomorph_apply,
      JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
      JordanCircle.InitialAngularArcs.levelTargetInnerMark] using hcd
  have houterInjective : Injective fun c : LevelAddress k =>
      (I.levelTargetAnnularCrosscut k c).outerPoint := by
    intro c d hcd
    apply I.levelTargetBoundaryPoint_injective k
    apply (homothetyHomeomorph (radius (k + 2))
      (radius_pos (k + 2)).ne').injective
    simpa only [homothetyHomeomorph_apply,
      JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
      JordanCircle.InitialAngularArcs.levelTargetOuterMark] using hcd
  have hinnerSecond : ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
      (I.levelTargetAnnularCrosscut k c).innerPoint ∈
        range C.targetSeparator.innerSplit.second := by
    intro c hca hcnext
    exact C.other_levelTargetPoint_mem_boundarySplit_second
      (k + 1) c hca hcnext
  have hcyclic := C.targetSeparator.family_cyclicCompatibility
    (I.levelTargetAnnularCrosscut k) C.next_ne
    (disk_strictlyNested (k + 1))
    (I.pairwise_disjoint_levelTargetAnnularCrosscut k)
    hinnerInjective houterInjective
    C.targetDecomposition.first_segment
    C.targetDecomposition.second_segment hinnerSecond
  rcases hcyclic with hfirst | hsecond
  · exact hfirst.1
  · have hpairCard :
        ({a, C.next} : Finset (LevelAddress k)).card <
          (Finset.univ : Finset (LevelAddress k)).card := by
      rw [Finset.card_univ]
      calc
        ({a, C.next} : Finset (LevelAddress k)).card ≤
            ({C.next} : Finset (LevelAddress k)).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
        _ < Fintype.card (LevelAddress k) :=
          lt_of_lt_of_le (by norm_num)
            (three_le_card_levelAddress k hk)
    obtain ⟨c, _hcuniv, hc⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hpairCard
    have hc' : c ≠ a ∧ c ≠ C.next := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hc
    have hcFirst :
        (I.levelTargetAnnularCrosscut k c).outerPoint ∈
          range (C.targetBoundarySplit (k + 2)).first := by
      have h := hsecond.2 c hc'.1 hc'.2
      change (I.levelTargetAnnularCrosscut k c).outerPoint ∈
        range (C.targetBoundarySplit (k + 2)).first.symm at h
      simpa only [Path.symm_range] using h
    have hcSecond :
        (I.levelTargetAnnularCrosscut k c).outerPoint ∈
          range (C.targetBoundarySplit (k + 2)).second :=
      C.other_levelTargetPoint_mem_boundarySplit_second
        (k + 2) c hc'.1 hc'.2
    have hcEnds :
        (I.levelTargetAnnularCrosscut k c).outerPoint ∈
          ({(I.levelTargetAnnularCrosscut k a).outerPoint,
            (I.levelTargetAnnularCrosscut k C.next).outerPoint} :
              Set Plane) := by
      have hoverlap := (C.targetBoundarySplit (k + 2)).overlap
      change range (C.targetBoundarySplit (k + 2)).first ∩
          range (C.targetBoundarySplit (k + 2)).second =
        ({(I.levelTargetAnnularCrosscut k a).outerPoint,
          (I.levelTargetAnnularCrosscut k C.next).outerPoint} :
            Set Plane) at hoverlap
      rw [← hoverlap]
      exact ⟨hcFirst, hcSecond⟩
    rcases hcEnds with hca | hcnext
    · exact False.elim (hc'.1 (houterInjective hca))
    · exact False.elim
        (hc'.2 (houterInjective (Set.mem_singleton_iff.mp hcnext)))

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

theorem targetAttachmentPresentation_exposedSecondCoordinate
    (t : unitInterval) :
    C.targetAttachmentPresentation.exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedSecondCoordinate t) =
      C.targetDecomposition.second.path.symm t := by
  classical
  by_cases h : C.targetFirstAlternative
  · rw [targetAttachmentPresentation, dif_pos h]
    exact C.targetDecomposition.exposedPath_exposedSecondCoordinate _ t
  · rw [targetAttachmentPresentation, dif_neg h]
    exact C.targetDecomposition.exposedPath_exposedSecondCoordinate _ t

theorem targetAttachmentPresentation_exposedFirstCoordinate
    (t : unitInterval) :
    C.targetAttachmentPresentation.exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedFirstCoordinate t) =
      C.targetDecomposition.first.path t := by
  classical
  by_cases h : C.targetFirstAlternative
  · rw [targetAttachmentPresentation, dif_pos h]
    exact C.targetDecomposition.exposedPath_exposedFirstCoordinate _ t
  · rw [targetAttachmentPresentation, dif_neg h]
    exact C.targetDecomposition.exposedPath_exposedFirstCoordinate _ t

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
