import Schoenflies.LevelBoundarySplits
import Schoenflies.StandardPolygonalCollars

/-!
# Standard radial crosscuts with independent stage and address indices

The recursive Moise construction chooses a binary subdivision depth at each
collar stage, and that depth need not be the stage number.  The original
standard-target API used one index for both roles.  This file separates them:
`m` selects the consecutive radial target disks, while `a : LevelAddress n`
selects the boundary label carried by the radial cut.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The copy at radial stage `m` of a retained boundary label at an
independent binary level. -/
def indexedTargetMark (m : ℕ) {n : ℕ} (a : LevelAddress n) : Plane :=
  homothetyPoint (radius m) (I.levelTargetBoundaryPoint a)

theorem indexedTargetMark_mem (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    I.indexedTargetMark m a ∈ (disk m).carrier := by
  rw [disk_carrier]
  exact ⟨I.levelTargetBoundaryPoint a,
    I.levelTargetBoundaryPoint_mem a, by
      simp only [homothetyHomeomorph_apply, indexedTargetMark]⟩

theorem indexedTargetMark_injective (m n : ℕ) :
    Injective (fun a : LevelAddress n => I.indexedTargetMark m a) := by
  intro a b hab
  apply I.levelTargetBoundaryPoint_injective n
  apply (homothetyHomeomorph (radius m) (radius_pos m).ne').injective
  simpa only [homothetyHomeomorph_apply, indexedTargetMark] using hab

theorem indexedTargetMark_succ_ne (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    I.indexedTargetMark (m + 1) a ≠ I.indexedTargetMark m a := by
  intro h
  have hinnerClosed : I.indexedTargetMark m a ∈ (disk m).closedRegion := by
    rw [(disk m).closedRegion_eq_union]
    exact Or.inr (I.indexedTargetMark_mem m a)
  have hinnerOuterInterior : I.indexedTargetMark m a ∈
      (disk (m + 1)).interiorRegion :=
    disk_strictlyNested m hinnerClosed
  exact Set.disjoint_left.mp
    (Schoenflies.PolygonalCircle.carrier_disjoint_interiorRegion
      (disk (m + 1)))
    (h ▸ I.indexedTargetMark_mem (m + 1) a) hinnerOuterInterior

/-- The radial cut carrying address `a` across target shell `m`. -/
def indexedTargetAnnularCrosscut (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    PolygonalCircle.AnnularCrosscut (disk m) (disk (m + 1)) where
  outerPoint := I.indexedTargetMark (m + 1) a
  innerPoint := I.indexedTargetMark m a
  path := Path.segment (I.indexedTargetMark (m + 1) a)
    (I.indexedTargetMark m a)
  path_injective := Path.segment_injective_of_ne
    (I.indexedTargetMark_succ_ne m a)
  outerPoint_mem := I.indexedTargetMark_mem (m + 1) a
  innerPoint_mem := I.indexedTargetMark_mem m a
  range_inter_outer := by
    rw [Path.range_segment]
    exact radialBand_inter_outerCarrier m
      (I.levelTargetBoundaryPoint_mem a)
  range_inter_inner := by
    rw [Path.range_segment]
    exact radialBand_inter_innerCarrier m
      (I.levelTargetBoundaryPoint_mem a)
  range_subset_closedShell := by
    rw [Path.range_segment]
    exact radialBand_subset_closedShell m
      (I.levelTargetBoundaryPoint_mem a)

theorem range_indexedTargetAnnularCrosscut (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    range (I.indexedTargetAnnularCrosscut m a).path =
      radialBand m (I.levelTargetBoundaryPoint a) := by
  exact Path.range_segment _ _

theorem pairwise_disjoint_indexedTargetAnnularCrosscut (m n : ℕ) :
    Pairwise fun a b : LevelAddress n =>
      Disjoint (range (I.indexedTargetAnnularCrosscut m a).path)
        (range (I.indexedTargetAnnularCrosscut m b).path) := by
  intro a b hab
  rw [I.range_indexedTargetAnnularCrosscut,
    I.range_indexedTargetAnnularCrosscut]
  apply disjoint_radialBands (radius_pos m)
    (radius_lt_succ m).le (radius_lt_one (m + 1))
    (I.levelTargetBoundaryPoint_mem a)
    (I.levelTargetBoundaryPoint_mem b)
  exact fun h => hab (I.levelTargetBoundaryPoint_injective n h)

end JordanCircle.InitialAngularArcs

end

end Schoenflies
