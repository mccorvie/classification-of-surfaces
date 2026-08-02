import Schoenflies.MoiseBandChildCarrier
import Schoenflies.MoiseBandCellCyclicAttachments
import Schoenflies.MoiseBandCellParentSeams

/-!
# Recognizing the boundary of a filled recursive Moise band

Assume each recursive cell has the outward orientation certified by its exact
intersection with the preceding polygonal disk.  The parent crosscuts and the
overlapping parts of adjacent cell sides are then internal seams.  The only
remaining boundary pieces lie on the next synchronized polygon.  Finitely
many polygon vertices and seam endpoints are removed during the local
argument and restored by regular-closed density.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private abbrev parentDisk (_L : RecursiveInsideCollarStep.Later F hn) :
    PolygonalCircle :=
  F.synchronizedPolygonalCircle hn

private abbrev childDisk : PolygonalCircle :=
  L.next.family.forgetObstacle.synchronizedPolygonalCircle
    L.next.one_le_level

/-- The finite set omitted while cancelling open parent and adjacent seams. -/
def moiseBandExceptionalSet : Set Plane :=
  range L.parentDisk.vertex ∪
    ⋃ a : LevelAddress n,
      ({F.leftSynchronizedPoint a, F.rightSynchronizedPoint a,
        (L.adjacentMoiseBandInnerSeamPoint a : Plane)} : Set Plane)

theorem moiseBandExceptionalSet_finite :
    L.moiseBandExceptionalSet.Finite := by
  have hseams : (⋃ a : LevelAddress n,
      ({F.leftSynchronizedPoint a, F.rightSynchronizedPoint a,
        (L.adjacentMoiseBandInnerSeamPoint a : Plane)} :
        Set Plane)).Finite :=
    Set.finite_iUnion fun _ => by simp
  exact (Set.finite_range L.parentDisk.vertex).union hseams

/-- Away from the finite exceptional set, every parent-polygon point is
swallowed by the parent disk and its corresponding outward cell. -/
theorem parentCarrier_sdiff_exceptional_subset_interior_moiseFilledDisk
    (hinter : ∀ a : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle a).closedRegion =
        range (F.synchronizedCrosscutPath a)) :
    L.parentDisk.carrier \ L.moiseBandExceptionalSet ⊆
      interior L.moiseFilledDisk := by
  rintro x ⟨hxParent, hxNotExceptional⟩
  have hxNotVertex : x ∉ range L.parentDisk.vertex := by
    intro hx
    exact hxNotExceptional (Or.inl hx)
  rw [F.carrier_synchronizedPolygonalCircle hn] at hxParent
  obtain ⟨a, hxCross⟩ := Set.mem_iUnion.mp hxParent
  have hxLeft : x ≠ F.leftSynchronizedPoint a := by
    intro hx
    apply hxNotExceptional
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨a, by simp [hx]⟩
  have hxRight : x ≠ F.rightSynchronizedPoint a := by
    intro hx
    apply hxNotExceptional
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨a, by simp [hx]⟩
  have hxInterior := L.parentCrosscut_mem_interior_parent_union_cell
    a (hinter a) hxCross hxNotVertex hxLeft hxRight
  apply interior_mono _ hxInterior
  intro y hy
  rcases hy with hyParent | hyCell
  · exact Or.inl hyParent
  · exact Or.inr <| Set.mem_iUnion.mpr ⟨a, hyCell⟩

/-- Away from its two endpoints, an adjacent side seam is swallowed by the
two cyclically adjacent closed cells. -/
theorem sideSeam_sdiff_exceptional_subset_interior_moiseFilledDisk
    (hinter : ∀ a : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle a).closedRegion =
        range (F.synchronizedCrosscutPath a))
    (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a \ L.moiseBandExceptionalSet ⊆
      interior L.moiseFilledDisk := by
  rintro x ⟨hxSeam, hxNotExceptional⟩
  have hxInner : x ≠ (L.adjacentMoiseBandInnerSeamPoint a : Plane) := by
    intro hx
    apply hxNotExceptional
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨a, by simp [hx]⟩
  have hxParent : x ≠ (L.adjacentMoiseBandParentPoint a : Plane) := by
    change x ≠ F.rightSynchronizedPoint a
    intro hx
    apply hxNotExceptional
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨a, by simp [hx]⟩
  have hxSegment : x ∈ segment ℝ
      (L.adjacentMoiseBandInnerSeamPoint a : Plane)
      (L.adjacentMoiseBandParentPoint a : Plane) := by
    rwa [← L.adjacentMoiseBandSideSeam_eq_segment a]
  have hxOpen : x ∈ openSegment ℝ
      (L.adjacentMoiseBandInnerSeamPoint a : Plane)
      (L.adjacentMoiseBandParentPoint a : Plane) :=
    mem_openSegment_of_ne_left_right hxInner.symm hxParent.symm hxSegment
  have hxInterior := L.openSideSeam_subset_interior_adjacentClosedRegions
    a (hinter a) (hinter (nextLevelAddress n a)) hxOpen
  apply interior_mono _ hxInterior
  intro y hy
  apply Or.inr
  rcases hy with hyCurrent | hyNext
  · exact Set.mem_iUnion.mpr ⟨a, hyCurrent⟩
  · exact Set.mem_iUnion.mpr ⟨nextLevelAddress n a, hyNext⟩

/-- Once the finite seam exceptions are deleted, every frontier point of the
filled Moise band lies on the child polygon. -/
theorem frontier_sdiff_moiseBandExceptionalSet_subset_childCarrier
    (hinter : ∀ a : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle a).closedRegion =
        range (F.synchronizedCrosscutPath a)) :
    frontier L.moiseFilledDisk \ L.moiseBandExceptionalSet ⊆
      L.childDisk.carrier := by
  rintro x ⟨hxFrontier, hxNotExceptional⟩
  have hxCandidate :=
    L.frontier_moiseFilledDisk_subset_parent_union_cells hxFrontier
  have hinteriorParent (hx : x ∈ L.parentDisk.carrier) :
      x ∈ interior L.moiseFilledDisk :=
    L.parentCarrier_sdiff_exceptional_subset_interior_moiseFilledDisk
      hinter ⟨hx, hxNotExceptional⟩
  have hinteriorSeam (a : LevelAddress n)
      (hx : x ∈ L.adjacentMoiseBandSideSeam a) :
      x ∈ interior L.moiseFilledDisk :=
    L.sideSeam_sdiff_exceptional_subset_interior_moiseFilledDisk
      hinter a ⟨hx, hxNotExceptional⟩
  rcases hxCandidate with hxParent | hxCells
  · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
      (hinteriorParent hxParent) hxFrontier
  · obtain ⟨a, hxCell⟩ := Set.mem_iUnion.mp hxCells
    rw [L.moiseBandCarrier_eq_parent_leftSide_child_rightSide a] at hxCell
    rcases hxCell with hxParent | hxLeft | hxChild | hxRight
    · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
        (hinteriorParent <| by
          rw [F.carrier_synchronizedPolygonalCircle hn]
          exact Set.mem_iUnion.mpr ⟨a, by
            rwa [← L.parentMoiseCarrier_eq_crosscutRange a]⟩)
        hxFrontier
    · let p := prevLevelAddress n a
      have hxLeft' : x ∈
          L.moiseBandLeftSideCarrier (nextLevelAddress n p) := by
        simpa only [p, nextLevelAddress_prevLevelAddress] using hxLeft
      rcases
          L.moiseBandLeftSideCarrier_next_subset_childCarrier_union_sideSeam
            p hxLeft' with hxChild | hxSeam
      · exact hxChild
      · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
          (hinteriorSeam p hxSeam) hxFrontier
    · exact L.childMoiseCarrier_subset_childCarrier a hxChild
    · rcases
          L.moiseBandRightSideCarrier_subset_childCarrier_union_sideSeam
            a hxRight with hxChild | hxSeam
      · exact hxChild
      · exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier
          (hinteriorSeam a hxSeam) hxFrontier

/-- The finite exceptional set cannot contribute isolated frontier points;
therefore the entire filled-band frontier lies on the child polygon. -/
theorem frontier_moiseFilledDisk_subset_childCarrier
    (hinter : ∀ a : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle a).closedRegion =
        range (F.synchronizedCrosscutPath a)) :
    frontier L.moiseFilledDisk ⊆ L.childDisk.carrier := by
  have hclosed : IsClosed L.moiseFilledDisk :=
    L.isCompact_moiseFilledDisk.isClosed
  have hdense : frontier L.moiseFilledDisk ⊆
      closure (frontier L.moiseFilledDisk \ L.moiseBandExceptionalSet) :=
    frontier_subset_closure_sdiff_finite_of_regularClosed
      hclosed L.closure_interior_moiseFilledDisk
        L.moiseBandExceptionalSet_finite
  have hchildClosed : IsClosed L.childDisk.carrier :=
    L.childDisk.isCompact_carrier.isClosed
  exact hdense.trans <| by
    have hclosure := closure_mono
      (L.frontier_sdiff_moiseBandExceptionalSet_subset_childCarrier hinter)
    rwa [hchildClosed.closure_eq] at hclosure

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
