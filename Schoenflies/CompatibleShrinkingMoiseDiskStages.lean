import Schoenflies.CompatibleDiskStages
import Schoenflies.MarkedMoiseBandBoundaries
import Schoenflies.ShrinkingMoiseBandHomeomorphisms
import Schoenflies.MoiseBoundaryDrift

/-!
# Compatible disk stages from the shrinking Moise bands

After the eventual outward-orientation threshold, each consecutive pair in
the recursively shrinking collar sequence bounds a marked Moise band.  This
file glues those bands recursively, retaining exact agreement on every
earlier closed polygonal disk.
-/

namespace Schoenflies

open Metric Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Absolute shrinking-collar band used at recursive disk stage `n`.
The recursive presentation is deliberate: its successor equation aligns
definitionally with the dependent successor collar record. -/
def shrinkingCompatibleBandIndex (I : J.InitialAngularArcs) : ℕ → ℕ
  | 0 => max I.shrinkingMoiseBandStartIndex 6
  | n + 1 => shrinkingCompatibleBandIndex I n + 1

/-- Source disk at recursive stage `n`.  Band `N+n` begins at shrinking
collar stage `N+n+1`, hence the offset by one. -/
abbrev shrinkingCompatibleStageSourceDisk (n : ℕ) : PolygonalCircle :=
  (I.shrinkingInsideCollarStage
    (I.shrinkingCompatibleBandIndex n + 1)).circle

/-- The target disks begin at the first standard polygonal disk and grow by
one radial shell at every recursive stage. -/
abbrev shrinkingCompatibleStageTargetDisk
    (_I : J.InitialAngularArcs) (n : ℕ) : PolygonalCircle :=
  disk n

/-- The actual dependent `Later` record whose marked band is used at
recursive stage `n`.  Naming it once keeps subsequent boundary-drift
statements independent of the implementation lets used to construct it. -/
noncomputable abbrev shrinkingCompatibleBandParentStage (n : ℕ) :=
  let k := I.shrinkingCompatibleBandIndex n
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  InsideCollarStage.ofLater I S₀ L₀

noncomputable abbrev shrinkingCompatibleBand (n : ℕ) :=
  let k := I.shrinkingCompatibleBandIndex n
  I.nextInsideCollarLater (k + 1)
    (I.shrinkingCompatibleBandParentStage n)

theorem shrinkingCompatibleBandIndex_ge (n : ℕ) :
    I.shrinkingMoiseBandStartIndex ≤ I.shrinkingCompatibleBandIndex n := by
  induction n with
  | zero => exact Nat.le_max_left _ _
  | succ n ih =>
      simpa only [shrinkingCompatibleBandIndex] using ih.trans (Nat.le_succ _)

theorem six_le_shrinkingCompatibleBandIndex (n : ℕ) :
    6 ≤ I.shrinkingCompatibleBandIndex n := by
  induction n with
  | zero => exact Nat.le_max_right _ _
  | succ n ih =>
      simpa only [shrinkingCompatibleBandIndex] using ih.trans (Nat.le_succ _)

/-- The subdivision level of the `k`th shrinking collar is at least `k+1`. -/
theorem succ_le_shrinkingInsideCollarStage_level (k : ℕ) :
    k + 1 ≤ (I.shrinkingInsideCollarStage k).level := by
  induction k with
  | zero => simpa using (I.shrinkingInsideCollarStage 0).one_le_level
  | succ k ih =>
      have hstrict := I.shrinkingInsideCollarStage_level_strict k
      omega

theorem six_le_shrinkingCompatibleBandParentStage_level (n : ℕ) :
    6 ≤ (I.shrinkingCompatibleBandParentStage n).level := by
  let k := I.shrinkingCompatibleBandIndex n
  have hk := I.succ_le_shrinkingInsideCollarStage_level (k + 1)
  have h6 := I.six_le_shrinkingCompatibleBandIndex n
  change 6 ≤
    (InsideCollarStage.ofLater I (I.shrinkingInsideCollarStage k)
      (I.nextInsideCollarLater k (I.shrinkingInsideCollarStage k))).level
  change 6 ≤ (I.shrinkingInsideCollarStage (k + 1)).level
  omega

/-- Every named compatible band has the eventual outward orientation needed
by marked-cell gluing. -/
theorem shrinkingCompatibleBand_outward (n : ℕ) :
    ∀ c : LevelAddress (I.shrinkingCompatibleBandParentStage n).level,
      (I.shrinkingCompatibleBandParentStage n).circle.closedRegion ∩
          ((I.shrinkingCompatibleBand n).moiseBandPolygonalCircle c).closedRegion =
        Set.range
          ((I.shrinkingCompatibleBandParentStage n).family
            |>.synchronizedCrosscutPath c) := by
  let k := I.shrinkingCompatibleBandIndex n
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  change ∀ c : LevelAddress L₀.next.level,
    L₀.next.circle.closedRegion ∩
        (L₁.moiseBandPolygonalCircle c).closedRegion =
      Set.range (L₀.next.family.forgetObstacle.synchronizedCrosscutPath c)
  exact I.shrinkingMoiseBandStartIndex_spec k
    (I.shrinkingCompatibleBandIndex_ge n)

/-- Raw inner boundary parametrization of compatible band `n`. -/
noncomputable def shrinkingCompatibleRawInnerBoundaryHomeomorph (n : ℕ) :
    (I.shrinkingCompatibleStageSourceDisk n).carrier ≃ₜ
      (I.shrinkingCompatibleStageTargetDisk n).carrier :=
  (I.shrinkingCompatibleBand n).markedMoiseRawInnerBoundaryHomeomorph n
    (I.shrinkingCompatibleBand_outward n)

/-- Raw outer boundary parametrization of compatible band `n`. -/
noncomputable def shrinkingCompatibleRawOuterBoundaryHomeomorph (n : ℕ) :
    (I.shrinkingCompatibleStageSourceDisk (n + 1)).carrier ≃ₜ
      (I.shrinkingCompatibleStageTargetDisk (n + 1)).carrier :=
  (I.shrinkingCompatibleBand n).markedMoiseRawOuterBoundaryHomeomorph n
    (I.shrinkingCompatibleBand_outward n)

theorem angularDriftBound_lt_two {k : ℕ} (hk : 6 ≤ k) :
    2 * ((2 / 3 : ℝ) ^ k * max I.first.width I.second.width) < 2 := by
  have hpow : (2 / 3 : ℝ) ^ k ≤ (2 / 3 : ℝ) ^ 6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hwidth : max I.first.width I.second.width < 2 * Real.pi :=
    max_lt I.first.width_lt_turn I.second.width_lt_turn
  have hwidthNonneg : 0 ≤ max I.first.width I.second.width :=
    I.first.width_pos.le.trans (le_max_left _ _)
  calc
    2 * ((2 / 3 : ℝ) ^ k * max I.first.width I.second.width) ≤
        2 * ((2 / 3 : ℝ) ^ 6 * max I.first.width I.second.width) := by
      gcongr
    _ < 2 * ((2 / 3 : ℝ) ^ 6 * (2 * Real.pi)) := by
      gcongr
    _ < 2 := by
      norm_num
      nlinarith [Real.pi_lt_four]

/-- In master angular coordinates, the correction required at stage `n+1`
is exactly the raw mismatch between the preceding and current Moise bands. -/
theorem angularBoundaryCorrection_rawMismatch (n : ℕ) :
    angularBoundaryCorrection (n + 1)
        ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph (n + 1)).symm.trans
          (I.shrinkingCompatibleRawOuterBoundaryHomeomorph n)) =
      rawAngularBoundaryMismatch
        (I.shrinkingCompatibleBand n) (I.shrinkingCompatibleBand (n + 1)) n
        (I.shrinkingCompatibleBand_outward n)
        (I.shrinkingCompatibleBand_outward (n + 1)) := by
  rfl

theorem dist_angularBoundaryCorrection_rawMismatch_lt_two
    (n : ℕ) (u : sphere (0 : Plane) 1) :
    dist
        (angularBoundaryCorrection (n + 1)
          ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph (n + 1)).symm.trans
            (I.shrinkingCompatibleRawOuterBoundaryHomeomorph n)) u) u < 2 := by
  rw [I.angularBoundaryCorrection_rawMismatch n]
  exact (dist_rawAngularBoundaryMismatch_apply_le
    (I.shrinkingCompatibleBand n) (I.shrinkingCompatibleBand (n + 1)) n
    (I.shrinkingCompatibleBand_outward n)
    (I.shrinkingCompatibleBand_outward (n + 1)) u).trans_lt <|
      I.angularDriftBound_lt_two
        (I.six_le_shrinkingCompatibleBandParentStage_level n)

/-- Boundary parametrization retained after stage `n`: initially the raw
inner map, and thereafter the raw outer map of the preceding band. -/
noncomputable def shrinkingCompatibleExpectedBoundaryHomeomorph :
    (n : ℕ) → (I.shrinkingCompatibleStageSourceDisk n).carrier ≃ₜ
      (I.shrinkingCompatibleStageTargetDisk n).carrier
  | 0 => I.shrinkingCompatibleRawInnerBoundaryHomeomorph 0
  | n + 1 => I.shrinkingCompatibleRawOuterBoundaryHomeomorph n

/-- Every correction required by the damped recursion is short.  The first
one is the identity; every successor is a single raw Moise mismatch. -/
theorem shrinkingCompatibleExpectedBoundaryCorrection_short (n : ℕ) :
    ∀ u,
      angularBoundaryCorrection n
          ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph n).symm.trans
            (I.shrinkingCompatibleExpectedBoundaryHomeomorph n)) u ≠
        SphereShortIsotopy.antipode u := by
  cases n with
  | zero =>
      intro u hu
      have hid :
          angularBoundaryCorrection 0
              ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph 0).symm.trans
                (I.shrinkingCompatibleExpectedBoundaryHomeomorph 0)) u = u := by
        simp only [shrinkingCompatibleExpectedBoundaryHomeomorph,
          angularBoundaryCorrection, Homeomorph.trans_apply,
          Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
      rw [hid] at hu
      have hdist := SphereShortIsotopy.dist_antipode_self u
      rw [← hu, dist_self] at hdist
      norm_num at hdist
  | succ n =>
      apply SphereShortIsotopy.ne_antipode_of_dist_lt_two
      intro u
      simpa only [shrinkingCompatibleExpectedBoundaryHomeomorph] using
        I.dist_angularBoundaryCorrection_rawMismatch_lt_two n u

/-- Consecutive source disks are strictly nested after the chosen eventual
orientation threshold. -/
theorem shrinkingCompatibleStageSourceDisk_strictlyNested (n : ℕ) :
    (I.shrinkingCompatibleStageSourceDisk n).closedRegion ⊆
      (I.shrinkingCompatibleStageSourceDisk (n + 1)).interiorRegion := by
  let k := I.shrinkingCompatibleBandIndex n
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  have h := L₁.parentClosedRegion_subset_childInteriorRegion
    (I.shrinkingMoiseBandStartIndex_spec k
      (I.shrinkingCompatibleBandIndex_ge n))
  change L₀.next.circle.closedRegion ⊆ L₁.next.circle.interiorRegion at h
  simpa only [shrinkingCompatibleStageSourceDisk,
    shrinkingCompatibleBandIndex, k, S₀, L₀, S₁, L₁,
    I.shrinkingInsideCollarStage_succ, nextInsideCollarStage,
    InsideCollarStage.circle_ofLater, Nat.succ_eq_add_one,
    Nat.add_assoc] using h

/-- The first compatible disk map is the Alexander extension of the exact
inner-boundary restriction of the first retained shrinking Moise band. -/
def initialShrinkingCompatibleClosedDiskHomeomorph :
    PolygonalCircle.CompatibleClosedDiskHomeomorph
      (I.shrinkingCompatibleStageSourceDisk 0)
      (I.shrinkingCompatibleStageTargetDisk 0) := by
  let k := I.shrinkingCompatibleBandIndex 0
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  let houtward := I.shrinkingMoiseBandStartIndex_spec k
    (I.shrinkingCompatibleBandIndex_ge 0)
  have b := L₁.markedMoiseRawInnerBoundaryHomeomorph 0 houtward
  change L₀.next.circle.carrier ≃ₜ (disk 0).carrier at b
  change PolygonalCircle.CompatibleClosedDiskHomeomorph L₀.next.circle (disk 0)
  exact PolygonalCircle.CompatibleClosedDiskHomeomorph.ofBoundary _ _ b

set_option maxRecDepth 2000 in
/-- Add the next shrinking Moise band while preserving the preceding disk
map exactly. -/
def nextShrinkingCompatibleClosedDiskHomeomorph (n : ℕ)
    (D : PolygonalCircle.CompatibleClosedDiskHomeomorph
      (I.shrinkingCompatibleStageSourceDisk n)
      (I.shrinkingCompatibleStageTargetDisk n))
    (hshort : ∀ u,
      angularBoundaryCorrection n
          ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph n).symm.trans
            D.boundaryHomeomorph) u ≠
        SphereShortIsotopy.antipode u) :
    PolygonalCircle.CompatibleClosedDiskHomeomorph
      (I.shrinkingCompatibleStageSourceDisk (n + 1))
      (I.shrinkingCompatibleStageTargetDisk (n + 1)) := by
  exact D.extendAcrossShell
    (I.shrinkingCompatibleStageSourceDisk_strictlyNested n)
    (disk_strictlyNested n)
    ((I.shrinkingCompatibleBand n).dampedCompatibleMarkedMoiseBandHomeomorph
      n (I.shrinkingCompatibleBand_outward n) D.boundaryHomeomorph hshort)
    (I.shrinkingCompatibleRawOuterBoundaryHomeomorph n)
    ((I.shrinkingCompatibleBand n)
      |>.dampedCompatibleMarkedMoiseBandHomeomorph_apply_innerCarrier
        n (I.shrinkingCompatibleBand_outward n) D.boundaryHomeomorph hshort)
    ((I.shrinkingCompatibleBand n)
      |>.dampedCompatibleMarkedMoiseBandHomeomorph_apply_outerCarrier
        n (I.shrinkingCompatibleBand_outward n) D.boundaryHomeomorph hshort)

set_option maxRecDepth 2000 in
/-- Adding one shrinking band leaves the old closed-disk map unchanged. -/
theorem nextShrinkingCompatibleClosedDiskHomeomorph_apply_old (n : ℕ)
    (D : PolygonalCircle.CompatibleClosedDiskHomeomorph
      (I.shrinkingCompatibleStageSourceDisk n)
      (I.shrinkingCompatibleStageTargetDisk n))
    (hshort : ∀ u,
      angularBoundaryCorrection n
          ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph n).symm.trans
            D.boundaryHomeomorph) u ≠
        SphereShortIsotopy.antipode u)
    (x : (I.shrinkingCompatibleStageSourceDisk n).closedRegion) :
    ((I.nextShrinkingCompatibleClosedDiskHomeomorph n D hshort).homeomorph
        ⟨x, PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
          _ _ (I.shrinkingCompatibleStageSourceDisk_strictlyNested n) x.2⟩ :
      Plane) = D.homeomorph x := by
  unfold nextShrinkingCompatibleClosedDiskHomeomorph
  apply
    PolygonalCircle.CompatibleClosedDiskHomeomorph.extendAcrossShell_apply_old

/-- A recursive disk stage together with the nonaccumulating boundary
invariant forced by the damped correction. -/
structure ShrinkingCompatibleClosedDiskStage (n : ℕ) where
  diskHomeomorph : PolygonalCircle.CompatibleClosedDiskHomeomorph
    (I.shrinkingCompatibleStageSourceDisk n)
    (I.shrinkingCompatibleStageTargetDisk n)
  boundary_eq : diskHomeomorph.boundaryHomeomorph =
    I.shrinkingCompatibleExpectedBoundaryHomeomorph n

set_option maxRecDepth 2000 in
noncomputable def initialShrinkingCompatibleClosedDiskStage :
    I.ShrinkingCompatibleClosedDiskStage 0 where
  diskHomeomorph := I.initialShrinkingCompatibleClosedDiskHomeomorph
  boundary_eq := by rfl

set_option maxRecDepth 2000 in
noncomputable def nextShrinkingCompatibleClosedDiskStage (n : ℕ)
    (D : I.ShrinkingCompatibleClosedDiskStage n) :
    I.ShrinkingCompatibleClosedDiskStage (n + 1) := by
  have hshort : ∀ u,
      angularBoundaryCorrection n
          ((I.shrinkingCompatibleRawInnerBoundaryHomeomorph n).symm.trans
            D.diskHomeomorph.boundaryHomeomorph) u ≠
        SphereShortIsotopy.antipode u := by
    rw [D.boundary_eq]
    exact I.shrinkingCompatibleExpectedBoundaryCorrection_short n
  refine ⟨I.nextShrinkingCompatibleClosedDiskHomeomorph n
    D.diskHomeomorph hshort, ?_⟩
  rfl

/-- Recursive compatible maps with their damped-boundary invariant. -/
noncomputable def shrinkingCompatibleClosedDiskStage :
    (n : ℕ) → I.ShrinkingCompatibleClosedDiskStage n
  | 0 => I.initialShrinkingCompatibleClosedDiskStage
  | n + 1 => I.nextShrinkingCompatibleClosedDiskStage n
      (shrinkingCompatibleClosedDiskStage n)

/-- Recursive compatible maps on all retained shrinking polygonal disks. -/
noncomputable def shrinkingCompatibleClosedDiskHomeomorphStage :
    (n : ℕ) → PolygonalCircle.CompatibleClosedDiskHomeomorph
      (I.shrinkingCompatibleStageSourceDisk n)
      (I.shrinkingCompatibleStageTargetDisk n)
  | n => (I.shrinkingCompatibleClosedDiskStage n).diskHomeomorph

/-- Consecutive recursive stages agree exactly on the preceding closed
source disk. -/
theorem shrinkingCompatibleClosedDiskHomeomorphStage_succ_apply_old
    (n : ℕ) (x : (I.shrinkingCompatibleStageSourceDisk n).closedRegion) :
    ((I.shrinkingCompatibleClosedDiskHomeomorphStage (n + 1)).homeomorph
        ⟨x, PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
          _ _ (I.shrinkingCompatibleStageSourceDisk_strictlyNested n) x.2⟩ :
      Plane) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph x := by
  change
    ((I.nextShrinkingCompatibleClosedDiskHomeomorph n
        (I.shrinkingCompatibleClosedDiskStage n).diskHomeomorph _).homeomorph
      ⟨x, PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
        _ _ (I.shrinkingCompatibleStageSourceDisk_strictlyNested n) x.2⟩ :
      Plane) =
        (I.shrinkingCompatibleClosedDiskStage n).diskHomeomorph.homeomorph x
  apply I.nextShrinkingCompatibleClosedDiskHomeomorph_apply_old

/-- The source disks form an increasing sequence. -/
theorem shrinkingCompatibleStageSourceDisk_closedRegion_mono
    {m n : ℕ} (hmn : m ≤ n) :
    (I.shrinkingCompatibleStageSourceDisk m).closedRegion ⊆
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
      exact ih.trans <|
        PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
          _ _ (I.shrinkingCompatibleStageSourceDisk_strictlyNested n)

/-- The standard target disks form an increasing sequence. -/
theorem shrinkingCompatibleStageTargetDisk_closedRegion_mono
    {m n : ℕ} (hmn : m ≤ n) :
    (I.shrinkingCompatibleStageTargetDisk m).closedRegion ⊆
      (I.shrinkingCompatibleStageTargetDisk n).closedRegion := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
      exact ih.trans <|
        PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
          _ _ (disk_strictlyNested n)

/-- Every later finite-stage map agrees with an earlier map on the whole
earlier source disk. -/
theorem shrinkingCompatibleClosedDiskHomeomorphStage_apply_of_le
    {m n : ℕ} (hmn : m ≤ n)
    (x : (I.shrinkingCompatibleStageSourceDisk m).closedRegion) :
    ((I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
        ⟨x, I.shrinkingCompatibleStageSourceDisk_closedRegion_mono hmn x.2⟩ :
      Plane) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      let xn : (I.shrinkingCompatibleStageSourceDisk n).closedRegion :=
        ⟨x, I.shrinkingCompatibleStageSourceDisk_closedRegion_mono hmn x.2⟩
      calc
        ((I.shrinkingCompatibleClosedDiskHomeomorphStage (n + 1)).homeomorph
            ⟨x, I.shrinkingCompatibleStageSourceDisk_closedRegion_mono
              (Nat.le.step hmn) x.2⟩ : Plane) =
            (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph xn := by
          exact I.shrinkingCompatibleClosedDiskHomeomorphStage_succ_apply_old n xn
        _ = (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph x := ih

/-- The inverse finite-stage maps satisfy the corresponding compatibility on
all earlier target disks. -/
theorem shrinkingCompatibleClosedDiskHomeomorphStage_symm_apply_of_le
    {m n : ℕ} (hmn : m ≤ n)
    (y : (I.shrinkingCompatibleStageTargetDisk m).closedRegion) :
    ((I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm
        ⟨y, I.shrinkingCompatibleStageTargetDisk_closedRegion_mono hmn y.2⟩ :
      Plane) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph.symm y := by
  let x := (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph.symm y
  have hforward := I.shrinkingCompatibleClosedDiskHomeomorphStage_apply_of_le
    hmn x
  have hmap :
      (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
          ⟨x, I.shrinkingCompatibleStageSourceDisk_closedRegion_mono
            hmn x.2⟩ =
        ⟨y, I.shrinkingCompatibleStageTargetDisk_closedRegion_mono
          hmn y.2⟩ := by
    apply Subtype.ext
    rw [hforward]
    exact congrArg Subtype.val <|
      (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph.apply_symm_apply y
  rw [← hmap,
    (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm_apply_apply]

theorem le_shrinkingCompatibleBandIndex (n : ℕ) :
    n ≤ I.shrinkingCompatibleBandIndex n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      simpa only [shrinkingCompatibleBandIndex] using Nat.succ_le_succ ih

/-- Every retained source disk stays inside the original Jordan region. -/
theorem shrinkingCompatibleStageSourceDisk_closedRegion_subset_inside
    (n : ℕ) :
    (I.shrinkingCompatibleStageSourceDisk n).closedRegion ⊆ J.inside :=
  I.shrinkingInsideCollarStage_closedRegion_subset_inside _

/-- The retained source carriers eventually lie in every prescribed closed
neighborhood of the Jordan curve.  This is the metric half of the source
exhaustion argument. -/
theorem eventually_shrinkingCompatibleStageSourceDisk_carrier_subset_cthickening
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (I.shrinkingCompatibleStageSourceDisk n).carrier ⊆
        cthickening δ J.carrier := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingInsideCollarStage_next_carrier_subset_cthickening hδ
  refine ⟨N, fun n hn => ?_⟩
  exact hN (I.shrinkingCompatibleBandIndex n)
    (hn.trans (I.le_shrinkingCompatibleBandIndex n))

end JordanCircle.InitialAngularArcs

end

end Schoenflies
