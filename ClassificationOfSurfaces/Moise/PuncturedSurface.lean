/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.ChartExtraction
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Punctured surface charts

The disk and half-disk models used by the Moise construction remain path-connected after
deleting finitely many points.  The disk case transports the corresponding theorem for the
Euclidean plane through `Homeomorph.unitBall`.  For a half-disk, we delete the finite preimage
under the fold from the doubled disk, connect there, and fold the resulting path back.

These local results are the input for proving that a connected surface remains connected after
deleting a finite set.  That theorem, in turn, rules out multiple dual components in a completed
surface triangulation.
-/

open Set Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Fold the open unit disk onto the open half-disk. -/
def foldDiskToHalfDisk :
    ChartKind.disk.modelRegion → ChartKind.halfDisk.modelRegion :=
  fun p => ⟨(foldPlaneToHalfSpace p).1, by
    constructor
    · have hp : (p : Plane) ∈ Metric.ball 0 1 := by
        simpa [ChartKind.modelRegion] using p.2
      simpa only [Metric.mem_ball, dist_zero_right, norm_foldPlaneToHalfSpace] using hp
    · exact (foldPlaneToHalfSpace p).2⟩

/-- Folding the disk onto the half-disk is continuous. -/
theorem continuous_foldDiskToHalfDisk : Continuous foldDiskToHalfDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp
    (continuous_foldPlaneToHalfSpace.comp continuous_subtype_val)

/-- The inverse image of a finite set under the disk fold is finite.  Each fiber is contained in
the two-point set consisting of a point and its reflection across the boundary line. -/
theorem finite_preimage_foldDiskToHalfDisk
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    (foldDiskToHalfDisk ⁻¹' s).Finite := by
  apply hs.preimage'
  intro q hq
  let candidates : Set Plane := {q.1, reflectAcrossHalfPlaneBoundary q.1}
  have hcandidates : candidates.Finite := by
    exact (Set.finite_singleton _).insert _
  have hpreCandidates :
      ((Subtype.val : ChartKind.disk.modelRegion → Plane) ⁻¹' candidates).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hcandidates
  apply hpreCandidates.subset
  intro p hp
  change foldDiskToHalfDisk p = q at hp
  have hval : (foldPlaneToHalfSpace (p : Plane)).1 = (q : Plane) :=
    congrArg Subtype.val hp
  have h0 : |(p : Plane) 0| = (q : Plane) 0 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 0) hval
  have h1 : (p : Plane) 1 = (q : Plane) 1 := by
    simpa [foldPlaneToHalfSpace] using congrArg (fun z : Plane => z 1) hval
  have hq0 : 0 ≤ (q : Plane) 0 := q.2.2
  rcases (abs_eq hq0).mp h0 with hpos | hneg
  · change (p : Plane) ∈ candidates
    exact Set.mem_insert_iff.mpr (Or.inl (plane_ext hpos h1))
  · change (p : Plane) ∈ candidates
    apply Set.mem_insert_iff.mpr
    right
    apply Set.mem_singleton_iff.mpr
    apply plane_ext
    · simpa [reflectAcrossHalfPlaneBoundary] using hneg
    · simpa [reflectAcrossHalfPlaneBoundary] using h1

/-- Folding the disk onto the half-disk is surjective. -/
theorem surjective_foldDiskToHalfDisk :
    Function.Surjective foldDiskToHalfDisk := by
  intro q
  let p : ChartKind.disk.modelRegion := ⟨q.1, by
    simpa [ChartKind.modelRegion] using q.2.1⟩
  refine ⟨p, Subtype.ext ?_⟩
  apply plane_ext
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, abs_of_nonneg q.2.2, p]
  · simp [foldDiskToHalfDisk, foldPlaneToHalfSpace, p]

/-- An open disk with finitely many points deleted is path-connected. -/
theorem diskModel_compl_finite_isPathConnected
    (s : Set ChartKind.disk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let e : Plane ≃ₜ ChartKind.disk.modelRegion := Homeomorph.unitBall
  rw [← e.isPathConnected_preimage]
  rw [preimage_compl]
  apply Set.Countable.isPathConnected_compl_of_one_lt_rank
  · apply Module.one_lt_rank_of_one_lt_finrank
    simp [Plane]
  · exact (Set.Finite.preimage e.injective.injOn hs).countable

/-- An open half-disk with finitely many points deleted is path-connected. -/
theorem halfDiskModel_compl_finite_isPathConnected
    (s : Set ChartKind.halfDisk.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  have hpre : (foldDiskToHalfDisk ⁻¹' s).Finite :=
    finite_preimage_foldDiskToHalfDisk s hs
  have hpath :
      IsPathConnected ((foldDiskToHalfDisk ⁻¹' s)ᶜ) :=
    diskModel_compl_finite_isPathConnected _ hpre
  have himage := hpath.image continuous_foldDiskToHalfDisk
  rw [← preimage_compl,
    Set.image_preimage_eq _ surjective_foldDiskToHalfDisk] at himage
  exact himage

/-- Either Moise chart model remains path-connected after deleting finitely many points. -/
theorem ChartKind.isPathConnected_compl_finite
    (k : ChartKind) (s : Set k.modelRegion) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  cases k with
  | disk => exact diskModel_compl_finite_isPathConnected s hs
  | halfDisk => exact halfDiskModel_compl_finite_isPathConnected s hs

/-- The underlying planar model region remains path-connected after deleting a finite ambient
set. -/
theorem ChartKind.isPathConnected_modelRegion_diff_finite
    (k : ChartKind) (s : Set Plane) (hs : s.Finite) :
    IsPathConnected (k.modelRegion \ s) := by
  let t : Set k.modelRegion :=
    (Subtype.val : k.modelRegion → Plane) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    k.isPathConnected_compl_finite t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- A Moise chart domain, as a subtype, remains path-connected after deleting finitely many
points. -/
theorem isPathConnected_compl_finite_subtype
    (s : Set c.domain) (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let t : Set c.kind.modelRegion := c.chart.symm ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage c.chart.symm.injective.injOn hs
  have hmodel : IsPathConnected tᶜ :=
    c.kind.isPathConnected_compl_finite t ht
  have hpre : IsPathConnected (c.chart ⁻¹' tᶜ) :=
    c.chart.isPathConnected_preimage.mpr hmodel
  have heq : c.chart ⁻¹' t = s := by
    ext x
    simp [t]
  rw [preimage_compl, heq] at hpre
  exact hpre

/-- The ambient chart domain remains path-connected after deleting a finite subset of the
surface. -/
theorem isPathConnected_domain_diff_finite
    (s : Set S) (hs : s.Finite) :
    IsPathConnected (c.domain \ s) := by
  let t : Set c.domain := (Subtype.val : c.domain → S) ⁻¹' s
  have ht : t.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn hs
  have hpath : IsPathConnected tᶜ :=
    c.isPathConnected_compl_finite_subtype t ht
  have himage := hpath.image continuous_subtype_val
  convert himage using 1
  ext x
  simp [t]

end MoiseChart

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
