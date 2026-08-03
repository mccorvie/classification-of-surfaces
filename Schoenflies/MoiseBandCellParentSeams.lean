import Schoenflies.MoiseBandCellAttachments
import Schoenflies.JordanThetaRegions
import Schoenflies.LocallyStraightSets

/-!
# Cancelling the parent seams of recursive Moise cells

An outward-oriented Moise cell meets the preceding polygonal disk exactly
along its synchronized parent crosscut.  Away from the finitely many parent
vertices and the two crosscut endpoints, that common arc is locally a line.
The two disks have disjoint open interiors, so the common arc is swallowed
by their union and cannot contribute to its frontier.
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

/-- Symmetrically to `moiseBandAttachmentPresentation`, view the preceding
polygonal disk as attached to one oriented Moise cell along their common
parent crosscut. -/
noncomputable def parentAttachmentPresentation
    (a : LevelAddress n)
    (hinter : L.parentDisk.closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a)) :
    PolygonalDiskAttachment.Presentation
      (L.moiseBandPolygonalCircle a).closedRegion := by
  let K := L.moiseBandPolygonalCircle a
  let p := F.synchronizedCrosscutPath a
  have hpCarrier : range p ⊆ L.parentDisk.carrier := by
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact fun _ hx => Set.mem_iUnion.mpr ⟨a, hx⟩
  exact PolygonalDiskAttachment.Presentation.ofClosedRegionInter
    K L.parentDisk p (F.synchronizedCrosscutPath_injective a)
      (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)
      hpCarrier (by simpa only [Set.inter_comm] using hinter)

theorem range_parentAttachmentPresentation_shared
    (a : LevelAddress n)
    (hinter : L.parentDisk.closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a)) :
    range (L.parentAttachmentPresentation a hinter).shared =
      range (F.synchronizedCrosscutPath a) := by
  unfold parentAttachmentPresentation
  rw [PolygonalDiskAttachment.Presentation.range_ofClosedRegionInter_shared]

/-- A nonexceptional point of a parent crosscut is interior to the old disk
together with the cell which replaces that crosscut. -/
theorem parentCrosscut_mem_interior_parent_union_cell
    (a : LevelAddress n)
    (hinter : L.parentDisk.closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a))
    {z : Plane} (hzCross : z ∈ range (F.synchronizedCrosscutPath a))
    (hzNotVertex : z ∉ range L.parentDisk.vertex)
    (hzLeft : z ≠ F.leftSynchronizedPoint a)
    (hzRight : z ≠ F.rightSynchronizedPoint a) :
    z ∈ interior (L.parentDisk.closedRegion ∪
      (L.moiseBandPolygonalCircle a).closedRegion) := by
  let P := L.parentDisk
  let Q := L.moiseBandPolygonalCircle a
  let DQ := L.moiseBandAttachmentPresentation a hinter
  let DP := L.parentAttachmentPresentation a hinter
  have hzCarrierP : z ∈ P.carrier := by
    dsimp only [P]
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr ⟨a, hzCross⟩
  obtain ⟨i, hzOpen⟩ :=
    PolygonalCircle.exists_openEdge_of_mem_carrier_not_vertex
      P hzCarrierP hzNotVertex
  obtain ⟨rP, hrP, hlocalP⟩ :=
    polygonalCircle_exists_local_determinantLine P hzOpen
  let d : Plane := P.vertex (i + 1) - P.vertex i
  have hlocalP' : ball z rP ∩ P.carrier =
      ball z rP ∩ determinantLine z d := by
    simpa only [d] using hlocalP
  have hzSharedP : z ∈ range DP.shared := by
    rw [L.range_parentAttachmentPresentation_shared a hinter]
    exact hzCross
  have hzNotExposedP : z ∉ range DP.exposed := by
    intro hzExposed
    have hzEnds : z ∈ ({DP.startPoint, DP.endPoint} : Set Plane) := by
      rw [← DP.boundary_overlap]
      exact ⟨hzSharedP, hzExposed⟩
    have hstart : DP.startPoint = F.leftSynchronizedPoint a := by
      dsimp only [DP, parentAttachmentPresentation]
      simp
    have hend : DP.endPoint = F.rightSynchronizedPoint a := by
      dsimp only [DP, parentAttachmentPresentation]
      simp
    rw [hstart, hend] at hzEnds
    exact hzEnds.elim hzLeft hzRight
  have hlocalShared : ∃ r : ℝ, 0 < r ∧
      ball z r ∩ range DP.shared =
        ball z r ∩ determinantLine z d := by
    apply exists_local_determinantLine_of_union_compact_avoid
      (C := range DP.exposed)
    · have hdisk : DP.disk = P := by
        dsimp only [DP, parentAttachmentPresentation, P]
        simp
      rw [← DP.carrier_eq, hdisk]
      exact ⟨rP, hrP, hlocalP'⟩
    · exact isCompact_range DP.exposed.continuous
    · exact hzNotExposedP
  have hzSharedQ : z ∈ range DQ.shared := by
    unfold DQ moiseBandAttachmentPresentation
    rw [PolygonalDiskAttachment.Presentation.range_ofClosedRegionInter_shared]
    exact hzCross
  have hzNotExposedQ : z ∉ range DQ.exposed := by
    intro hzExposed
    have hzEnds : z ∈ ({DQ.startPoint, DQ.endPoint} : Set Plane) := by
      rw [← DQ.boundary_overlap]
      exact ⟨hzSharedQ, hzExposed⟩
    have hstart : DQ.startPoint = F.leftSynchronizedPoint a := by
      dsimp only [DQ, moiseBandAttachmentPresentation]
      simp
    have hend : DQ.endPoint = F.rightSynchronizedPoint a := by
      dsimp only [DQ, moiseBandAttachmentPresentation]
      simp
    rw [hstart, hend] at hzEnds
    exact hzEnds.elim hzLeft hzRight
  have hlocalSharedQ : ∃ r : ℝ, 0 < r ∧
      ball z r ∩ range DQ.shared =
        ball z r ∩ determinantLine z d := by
    have hDPRange : range DP.shared =
        range (F.synchronizedCrosscutPath a) := by
      dsimp only [DP]
      exact L.range_parentAttachmentPresentation_shared a hinter
    have hDQRange : range DQ.shared =
        range (F.synchronizedCrosscutPath a) := by
      unfold DQ moiseBandAttachmentPresentation
      rw [PolygonalDiskAttachment.Presentation.range_ofClosedRegionInter_shared]
    rw [hDPRange] at hlocalShared
    rw [hDQRange]
    exact hlocalShared
  obtain ⟨rQ, hrQ, hlocalQ⟩ :=
    exists_local_determinantLine_union_of_compact_avoid hlocalSharedQ
      (isCompact_range DQ.exposed.continuous) hzNotExposedQ
  have hcarrierQ : ball z rQ ∩ Q.carrier =
      ball z rQ ∩ determinantLine z d := by
    have hdisk : DQ.disk = Q := by
      dsimp only [DQ, moiseBandAttachmentPresentation, Q]
      simp
    rw [← hdisk, DQ.carrier_eq]
    exact hlocalQ
  have hdisjoint : Disjoint P.toJordanCircle.inside
      Q.toJordanCircle.inside := by
    rw [P.inside_toJordanCircle, Q.inside_toJordanCircle,
      Set.disjoint_left]
    intro x hxP hxQ
    have hxInter : x ∈ P.closedRegion ∩ Q.closedRegion := by
      constructor <;> rw [PolygonalCircle.closedRegion_eq_union]
      · exact Or.inl hxP
      · exact Or.inl hxQ
    have hxCross : x ∈ range (F.synchronizedCrosscutPath a) := by
      simpa only [P, Q] using hinter ▸ hxInter
    have hxCarrier : x ∈ P.carrier := by
      dsimp only [P]
      rw [F.carrier_synchronizedPolygonalCircle hn]
      exact Set.mem_iUnion.mpr ⟨a, hxCross⟩
    exact P.toJordanCircle.inside_subset_compl
      (by rwa [P.inside_toJordanCircle])
      (by rwa [P.carrier_toJordanCircle])
  let r := min rP rQ
  have hr : 0 < r := lt_min hrP hrQ
  have hlocalP'' : ball z r ∩ P.toJordanCircle.carrier =
      ball z r ∩ determinantLine z d := by
    rw [P.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_left _ _) hlocalP'
  have hlocalQ' : ball z r ∩ Q.toJordanCircle.carrier =
      ball z r ∩ determinantLine z d := by
    rw [Q.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_right _ _) hcarrierQ
  have hzInterior :=
    JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
      hdisjoint hr (by simpa only [P.carrier_toJordanCircle] using hzCarrierP)
      hlocalP'' hlocalQ'
  change z ∈ interior (closure P.interiorRegion ∪ closure Q.interiorRegion)
  simpa only [P.inside_toJordanCircle, Q.inside_toJordanCircle] using hzInterior

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
