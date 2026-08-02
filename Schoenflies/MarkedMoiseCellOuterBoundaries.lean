import Schoenflies.MarkedMoiseCellHomeomorphisms
import Schoenflies.MoiseBandFilledDisk
import Schoenflies.CyclicTargetCellGeometry

/-!
# Complementary paths on marked Moise cells

The arbitrary complementary path chosen when a marked cell boundary is
split is not geometrically mysterious: on the source it lies on the child
polygon, and on the canonical target it is exactly the elementary outer
boundary arc.  These facts identify the outer restriction of the glued band
homeomorphism.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private abbrev parentDisk
    (_L : RecursiveInsideCollarStep.Later F hn) : PolygonalCircle :=
  F.synchronizedPolygonalCircle hn

private abbrev childDisk : PolygonalCircle :=
  L.next.family.forgetObstacle.synchronizedPolygonalCircle
    L.next.one_le_level

theorem adjacentMoiseBandInnerSeamPoint_mem_childCarrier
    (a : LevelAddress n) :
    (L.adjacentMoiseBandInnerSeamPoint a : Plane) ∈ L.childDisk.carrier := by
  apply L.extremeChildJunction_subset_childCarrier a
  rcases (I.levelRightHair a).deeperPoint_eq_left_or_right
      (L.adjacentMoiseBandRightRawPoint a)
      (L.adjacentMoiseBandLeftRawPoint a) with h | h
  · rw [show (L.adjacentMoiseBandInnerSeamPoint a : Plane) =
      L.adjacentMoiseBandRightRawPoint a by exact congrArg Subtype.val h]
    exact left_mem_segment ℝ _ _
  · rw [show (L.adjacentMoiseBandInnerSeamPoint a : Plane) =
      L.adjacentMoiseBandLeftRawPoint a by exact congrArg Subtype.val h]
    exact right_mem_segment ℝ _ _

/-- A side seam reaches the child polygon only at its inner endpoint. -/
theorem adjacentMoiseBandSideSeam_inter_childCarrier
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a ∩ L.childDisk.carrier =
      {(L.adjacentMoiseBandInnerSeamPoint a : Plane)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSeam, hxChild⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hxInner
    have hxParent : x ≠
        (L.adjacentMoiseBandParentPoint a : Plane) := by
      intro hx
      have hxParentClosed : x ∈ L.parentDisk.closedRegion := by
        rw [L.parentDisk.closedRegion_eq_union]
        exact Or.inr <| by
          rw [hx]
          change F.rightSynchronizedPoint a ∈ L.parentDisk.carrier
          rw [F.carrier_synchronizedPolygonalCircle hn]
          exact Set.mem_iUnion.mpr
            ⟨a, Path.target_mem_range (F.synchronizedCrosscutPath a)⟩
      have hxParentInterior :=
        L.parentClosedRegion_subset_childInteriorRegion houtward hxParentClosed
      exact Set.disjoint_left.mp
        (PolygonalCircle.carrier_disjoint_interiorRegion L.childDisk)
        hxChild hxParentInterior
    have hxOpen : x ∈ openSegment ℝ
        (L.adjacentMoiseBandInnerSeamPoint a : Plane)
        (L.adjacentMoiseBandParentPoint a : Plane) :=
      mem_openSegment_of_ne_left_right
        (fun h => hxInner h.symm) (fun h => hxParent h.symm) <| by
        rwa [← L.adjacentMoiseBandSideSeam_eq_segment a]
    have hxAdjacent :=
      L.openSideSeam_subset_interior_adjacentClosedRegions
        a (houtward a) (houtward (nextLevelAddress n a)) hxOpen
    have hxFilled : x ∈ interior L.moiseFilledDisk := by
      apply interior_mono _ hxAdjacent
      intro y hy
      right
      rcases hy with hyCurrent | hyNext
      · exact Set.mem_iUnion.mpr ⟨a, hyCurrent⟩
      · exact Set.mem_iUnion.mpr
          ⟨nextLevelAddress n a, hyNext⟩
    have hxChildInterior : x ∈ L.childDisk.interiorRegion := by
      rw [← L.childDisk.interior_closedRegion,
        ← L.moiseFilledDisk_eq_childClosedRegion houtward]
      exact hxFilled
    exact Set.disjoint_left.mp
      (PolygonalCircle.carrier_disjoint_interiorRegion L.childDisk)
      hxChild hxChildInterior
  · intro x hx
    have hxEq : x =
        (L.adjacentMoiseBandInnerSeamPoint a : Plane) :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨by
      rw [L.adjacentMoiseBandSideSeam_eq_segment]
      exact left_mem_segment ℝ _ _,
      L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier a⟩

/-- A child-carrier point lying on one marked source cell belongs to the
complementary boundary path selected for that cell. -/
theorem childCarrier_inter_moiseBandCellCarrier_subset_boundarySplitSecond
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (a : LevelAddress n) :
    L.childDisk.carrier ∩ (L.moiseBandPolygonalCircle a).carrier ⊆
      range (L.moiseCellBoundarySplit a).second := by
  rintro x ⟨hxChild, hxCell⟩
  have hxEither : x ∈ range (L.moiseCellBoundarySplit a).first ∨
      x ∈ range (L.moiseCellBoundarySplit a).second := by
    have hxJordan : x ∈
        (L.moiseBandPolygonalCircle a).toJordanCircle.carrier := by
      simpa only [(L.moiseBandPolygonalCircle a).carrier_toJordanCircle]
        using hxCell
    rw [← (L.moiseCellBoundarySplit a).cover] at hxJordan
    exact hxJordan
  rcases hxEither with hxFirst | hxSecond
  · rw [L.moiseCellBoundarySplit_first,
      L.range_moiseCellInnerBoundaryPath] at hxFirst
    have hxEndpoint : x =
        (L.adjacentMoiseBandInnerSeamPoint (prevLevelAddress n a) : Plane) ∨
      x = (L.adjacentMoiseBandInnerSeamPoint a : Plane) := by
      rcases hxFirst with hxIncoming | hxParent | hxOutgoing
      · have hxInter : x ∈
          L.adjacentMoiseBandSideSeam (prevLevelAddress n a) ∩
            L.childDisk.carrier := ⟨by
          rw [← L.range_incomingMoiseBandSideSeamPath]
          exact hxIncoming, hxChild⟩
        left
        exact Set.mem_singleton_iff.mp <| by
          rw [← L.adjacentMoiseBandSideSeam_inter_childCarrier
            houtward (prevLevelAddress n a)]
          exact hxInter
      · have hxParentCarrier : x ∈ L.parentDisk.carrier := by
          rw [F.carrier_synchronizedPolygonalCircle hn]
          exact Set.mem_iUnion.mpr ⟨a, hxParent⟩
        have hxParentClosed : x ∈ L.parentDisk.closedRegion := by
          rw [L.parentDisk.closedRegion_eq_union]
          exact Or.inr hxParentCarrier
        have hxInterior :=
          L.parentClosedRegion_subset_childInteriorRegion houtward hxParentClosed
        exact False.elim <| Set.disjoint_left.mp
          (PolygonalCircle.carrier_disjoint_interiorRegion L.childDisk)
          hxChild hxInterior
      · have hxInter : x ∈ L.adjacentMoiseBandSideSeam a ∩
            L.childDisk.carrier := ⟨by
          rw [Path.symm_range] at hxOutgoing
          rw [← L.range_adjacentMoiseBandSideSeamPath]
          exact hxOutgoing, hxChild⟩
        right
        exact Set.mem_singleton_iff.mp <| by
          rw [← L.adjacentMoiseBandSideSeam_inter_childCarrier houtward a]
          exact hxInter
    have hxEnds : x ∈
        ({(L.adjacentMoiseBandInnerSeamPoint
              (prevLevelAddress n a) : Plane),
          (L.adjacentMoiseBandInnerSeamPoint a : Plane)} : Set Plane) :=
      hxEndpoint
    rw [← (L.moiseCellBoundarySplit a).overlap] at hxEnds
    exact hxEnds.2
  · exact hxSecond

/-- Conversely, the arbitrary complementary source path stays on the child
polygon. -/
theorem range_moiseCellBoundarySplit_second_subset_childCarrier
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (a : LevelAddress n) :
    range (L.moiseCellBoundarySplit a).second ⊆ L.childDisk.carrier := by
  intro x hxSecond
  have hxCell : x ∈ (L.moiseBandPolygonalCircle a).carrier := by
    simpa only [← (L.moiseBandPolygonalCircle a).carrier_toJordanCircle]
      using (L.moiseCellBoundarySplit a).second_range_subset_carrier hxSecond
  rw [L.moiseBandPolygonalCircle_carrier,
    L.moiseBandCarrier_eq_parent_left_child_right] at hxCell
  rcases hxCell with hxParent | hxLeft | hxChild | hxRight
  · have hxFirst : x ∈ range (L.moiseCellBoundarySplit a).first := by
      rw [L.moiseCellBoundarySplit_first,
        L.range_moiseCellInnerBoundaryPath]
      right
      left
      rwa [← L.parentMoiseCarrier_eq_crosscutRange a]
    have hxEnds : x ∈
        ({(L.adjacentMoiseBandInnerSeamPoint
              (prevLevelAddress n a) : Plane),
          (L.adjacentMoiseBandInnerSeamPoint a : Plane)} : Set Plane) := by
      rw [← (L.moiseCellBoundarySplit a).overlap]
      exact ⟨hxFirst, hxSecond⟩
    rcases hxEnds with hx | hx
    · rw [hx]
      exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _
  · have hxCases :=
      L.moiseBandLeftSideCarrier_next_subset_childCarrier_union_sideSeam
        (prevLevelAddress n a)
    change x ∈ L.moiseBandLeftSideCarrier a at hxLeft
    have hxCases' : x ∈ L.childDisk.carrier ∪
        L.adjacentMoiseBandSideSeam (prevLevelAddress n a) := by
      apply hxCases
      simpa only [nextLevelAddress_prevLevelAddress] using hxLeft
    rcases hxCases' with hxChild | hxSeam
    · exact hxChild
    · have hxFirst : x ∈ range (L.moiseCellBoundarySplit a).first := by
        rw [L.moiseCellBoundarySplit_first,
          L.range_moiseCellInnerBoundaryPath]
        left
        rw [L.range_incomingMoiseBandSideSeamPath]
        exact hxSeam
      have hxEnds : x ∈
          ({(L.adjacentMoiseBandInnerSeamPoint
                (prevLevelAddress n a) : Plane),
            (L.adjacentMoiseBandInnerSeamPoint a : Plane)} : Set Plane) := by
        rw [← (L.moiseCellBoundarySplit a).overlap]
        exact ⟨hxFirst, hxSecond⟩
      rcases hxEnds with hx | hx
      · rw [hx]
        exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _
  · exact L.childMoiseCarrier_subset_childCarrier a hxChild
  · rcases L.moiseBandRightSideCarrier_subset_childCarrier_union_sideSeam
        a hxRight with hxChild | hxSeam
    · exact hxChild
    · have hxFirst : x ∈ range (L.moiseCellBoundarySplit a).first := by
        rw [L.moiseCellBoundarySplit_first,
          L.range_moiseCellInnerBoundaryPath]
        right
        right
        rw [Path.symm_range, L.range_adjacentMoiseBandSideSeamPath]
        exact hxSeam
      have hxEnds : x ∈
          ({(L.adjacentMoiseBandInnerSeamPoint
                (prevLevelAddress n a) : Plane),
            (L.adjacentMoiseBandInnerSeamPoint a : Plane)} : Set Plane) := by
        rw [← (L.moiseCellBoundarySplit a).overlap]
        exact ⟨hxFirst, hxSecond⟩
      rcases hxEnds with hx | hx
      · rw [hx]
        exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact L.adjacentMoiseBandInnerSeamPoint_mem_childCarrier _

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The complementary path in a canonical target cell is precisely its
elementary arc on the outer standard polygon. -/
theorem range_indexedTargetCellBoundarySplit_second
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) (a : LevelAddress n) :
    range (I.indexedTargetCellBoundarySplit m a).second =
      range (I.indexedTargetBoundarySplit (m + 1) a).first := by
  let p := (I.indexedTargetBoundarySplit (m + 1) a).first
  have hpCarrier : range p ⊆
      (I.cyclicTargetAttachmentPresentation m a).disk.toJordanCircle.carrier := by
    rw [(I.cyclicTargetAttachmentPresentation m a).disk.carrier_toJordanCircle]
    intro x hx
    rw [(I.cyclicTargetAttachmentPresentation m a).carrier_eq,
      I.range_cyclicTargetAttachmentPresentation_exposed m hn]
    exact Or.inr (Or.inr (Or.inl hx))
  have hpCases :=
    (I.indexedTargetCellBoundarySplit m a).range_eq_first_or_second_of_path
      p (I.indexedTargetBoundarySplit (m + 1) a).first_injective hpCarrier
  rcases hpCases with hpFirst | hpSecond
  · exfalso
    have hinnerFirst : I.indexedTargetMark m a ∈
        range (I.indexedTargetCellBoundarySplit m a).first := by
      rw [I.indexedTargetCellBoundarySplit_first]
      refine ⟨ThreePiecePath.firstCoordinate 1, ?_⟩
      rw [I.indexedTargetCellInnerBoundaryPath_firstCoordinate]
      exact (I.indexedTargetAnnularCrosscut m a).path.target
    have hinnerOuter : I.indexedTargetMark m a ∈ (disk (m + 1)).carrier := by
      simpa only [(disk (m + 1)).carrier_toJordanCircle] using
        (I.indexedTargetBoundarySplit (m + 1) a).first_range_subset_carrier
          (by rw [hpFirst]; exact hinnerFirst)
    have hinnerClosed : I.indexedTargetMark m a ∈ (disk m).closedRegion := by
      rw [(disk m).closedRegion_eq_union]
      exact Or.inr (I.indexedTargetMark_mem m a)
    exact Set.disjoint_left.mp
      (PolygonalCircle.carrier_disjoint_interiorRegion (disk (m + 1)))
      hinnerOuter (disk_strictlyNested m hinnerClosed)
  · exact hpSecond.symm

theorem range_indexedTargetCellBoundarySplit_second_subset_outerCarrier
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) (a : LevelAddress n) :
    range (I.indexedTargetCellBoundarySplit m a).second ⊆
      (disk (m + 1)).carrier := by
  rw [I.range_indexedTargetCellBoundarySplit_second m hn a]
  simpa only [(disk (m + 1)).carrier_toJordanCircle] using
    (I.indexedTargetBoundarySplit (m + 1) a).first_range_subset_carrier

end JordanCircle.InitialAngularArcs

end

end Schoenflies
