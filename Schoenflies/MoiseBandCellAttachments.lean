import Schoenflies.MoiseBandCellCover
import Schoenflies.TopologicalDiskAttachment
import Schoenflies.TwoBoundaryArcRigidity

/-!
# Recursive Moise cells as relative disk attachments

Once the metric side choice is known, a Moise band cell meets the old disk
in exactly one synchronized parent crosscut.  This file upgrades that set
identity to the `PolygonalDiskAttachment.Presentation` consumed by the
existing relative Alexander-extension and closed-cover gluing machinery.
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

/-- An oriented recursive Moise cell, expressed by its exact intersection
with the preceding disk, is an honest relative disk attachment. -/
noncomputable def moiseBandAttachmentPresentation
    (a : LevelAddress n)
    (hinter : L.parentDisk.closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a)) :
    PolygonalDiskAttachment.Presentation L.parentDisk.closedRegion := by
  let K := L.moiseBandPolygonalCircle a
  let p := F.synchronizedCrosscutPath a
  have hpCarrier : range p ⊆ K.toJordanCircle.carrier := by
    rw [K.carrier_toJordanCircle]
    rw [L.moiseBandPolygonalCircle_carrier a]
    exact L.parentCrosscutRange_subset_moiseBandCarrier a
  have hxCarrier : F.leftSynchronizedPoint a ∈ K.toJordanCircle.carrier :=
    hpCarrier (Path.source_mem_range p)
  have hyCarrier : F.rightSynchronizedPoint a ∈ K.toJordanCircle.carrier :=
    hpCarrier (Path.target_mem_range p)
  let S := Classical.choice <| K.toJordanCircle.exists_twoBoundaryArcPaths
    hxCarrier hyCarrier (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)
  have hranges := S.range_eq_first_or_second_of_path p
    (F.synchronizedCrosscutPath_injective a) hpCarrier
  by_cases hfirst : range p = range S.first
  · exact {
      disk := K
      startPoint := F.leftSynchronizedPoint a
      endPoint := F.rightSynchronizedPoint a
      shared := p
      exposed := S.second
      shared_injective := F.synchronizedCrosscutPath_injective a
      exposed_injective := S.second_injective
      boundary_overlap := by rw [hfirst, S.overlap]
      carrier_eq := by
        rw [← K.carrier_toJordanCircle, ← S.cover, hfirst]
      base_closed := L.parentDisk.isCompact_closedRegion.isClosed
      base_inter_disk := hinter }
  · have hsecond : range p = range S.second :=
      hranges.resolve_left hfirst
    exact {
      disk := K
      startPoint := F.leftSynchronizedPoint a
      endPoint := F.rightSynchronizedPoint a
      shared := p
      exposed := S.first.symm
      shared_injective := F.synchronizedCrosscutPath_injective a
      exposed_injective :=
        S.first_injective.comp unitInterval.symm_bijective.injective
      boundary_overlap := by
        rw [Path.symm_range, hsecond, Set.inter_comm, S.overlap]
      carrier_eq := by
        rw [← K.carrier_toJordanCircle, ← S.cover, hsecond,
          Path.symm_range, Set.union_comm]
      base_closed := L.parentDisk.isCompact_closedRegion.isClosed
      base_inter_disk := hinter }

/-- The shrinking-cell ball estimate and a diameter witness supply the
orientation input to the general attachment presentation. -/
noncomputable def moiseBandAttachmentPresentationOfCellBall
    (a : LevelAddress n) {c : Plane} {rho : ℝ}
    (hcell : (L.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall c rho)
    (hseparated : ∃ x ∈ L.parentDisk.closedRegion,
      ∃ y ∈ L.parentDisk.closedRegion, 2 * rho < dist x y) :
    PolygonalDiskAttachment.Presentation L.parentDisk.closedRegion :=
  L.moiseBandAttachmentPresentation a <|
    L.parentClosedRegion_inter_moiseBandClosedRegion_of_cell_ball
      a hcell hseparated

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
