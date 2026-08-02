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

namespace Path

/-- An injective path contained in the range of another injective path, with
the same ordered endpoints, has the same range. -/
private theorem range_eq_of_subset_range {x y : Plane}
    (p q : Path x y) (_hp : Injective p) (hq : Injective q)
    (hsub : range p ⊆ range q) :
    range p = range q := by
  let toRange : unitInterval → range q := fun t => ⟨q t, ⟨t, rfl⟩⟩
  have htoRangeContinuous : Continuous toRange :=
    q.continuous.subtype_mk _
  have htoRangeBijective : Function.Bijective toRange := by
    constructor
    · intro s t hst
      apply hq
      exact congrArg Subtype.val hst
    · rintro ⟨z, t, rfl⟩
      exact ⟨t, rfl⟩
  let e₀ : unitInterval ≃ range q :=
    Equiv.ofBijective toRange htoRangeBijective
  let e : unitInterval ≃ₜ range q :=
    Continuous.homeoOfEquivCompactToT2 (f := e₀) htoRangeContinuous
  let f : unitInterval → unitInterval := fun t =>
    e.symm ⟨p t, hsub ⟨t, rfl⟩⟩
  have he (t : unitInterval) : (e t : Plane) = q t := rfl
  have hef (t : unitInterval) : (e (f t) : Plane) = p t := by
    exact congrArg Subtype.val <|
      e.apply_symm_apply ⟨p t, hsub ⟨t, rfl⟩⟩
  have hf : Continuous f := by
    exact e.symm.continuous.comp <| p.continuous.subtype_mk _
  have hf_zero : f 0 = 0 := by
    apply e.injective
    apply Subtype.ext
    rw [hef, he, p.source, q.source]
  have hf_one : f 1 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [hef, he, p.target, q.target]
  apply Set.Subset.antisymm hsub
  rintro z ⟨t, rfl⟩
  have hpreconnected : IsPreconnected (range f) :=
    by simpa only [Set.image_univ] using
      isPreconnected_univ.image f hf.continuousOn
  have ht : t ∈ range f := by
    apply hpreconnected.Icc_subset
        (show (0 : unitInterval) ∈ range f by
          exact ⟨0, hf_zero⟩)
        (show (1 : unitInterval) ∈ range f by
          exact ⟨1, hf_one⟩)
    exact t.2
  obtain ⟨s, hs⟩ := ht
  refine ⟨s, ?_⟩
  have hes : e (f s) = e t := congrArg e hs
  exact (hef s).symm.trans <| (congrArg Subtype.val hes).trans (he t)

end Path

namespace JordanCircle.TwoBoundaryArcPaths

/-- An injective path in a Jordan carrier between the splitting endpoints
is exactly one of the two complementary boundary arcs. -/
theorem range_eq_first_or_second_of_path
    {J : JordanCircle} {x y : Plane}
    (S : J.TwoBoundaryArcPaths x y) (p : Path x y)
    (hp : Injective p) (hcarrier : range p ⊆ J.carrier) :
    range p = range S.first ∨ range p = range S.second := by
  have havoid : Disjoint
      (p '' Set.Ioo (0 : unitInterval) 1) ({x, y} : Set Plane) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ (hzx | hzy)
    · have ht0 : t = 0 := hp (by simpa only [p.source] using hzx)
      exact (ne_of_gt ht.1) ht0
    · rw [Set.mem_singleton_iff] at hzy
      have ht1 : t = 1 := hp (by simpa only [p.target] using hzy)
      exact (ne_of_lt ht.2) ht1
  rcases S.range_subset_first_or_second_of_interior_disjoint
      p hcarrier havoid with hfirst | hsecond
  · exact Or.inl (Path.range_eq_of_subset_range
      p S.first hp S.first_injective hfirst)
  · exact Or.inr (Path.range_eq_of_subset_range
      p S.second.symm hp
        (S.second_injective.comp unitInterval.symm_bijective.injective)
        (by simpa only [Path.symm_range] using hsecond) |>.trans
          (Path.symm_range S.second))

end JordanCircle.TwoBoundaryArcPaths

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
