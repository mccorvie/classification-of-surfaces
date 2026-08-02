import Schoenflies.MoiseBandCellBounds
import Schoenflies.MoiseBandCellAttachments
import Schoenflies.MoiseBandCellInteriors
import Schoenflies.MoiseBandCellNonadjacency
import Schoenflies.MoiseBandFilledDisk
import Schoenflies.NestedCollarStages

/-!
# Uniformly shrinking cells in the recursive Moise bands

This specializes the two-step band estimate to the recursively selected
collars.  Bands after the initial one shrink at the explicit harmonic rate
used by `shrinkingInsideCollarStage`.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Starting from any packaged stage, first take successor `k`, and then
successor `k+1`.  Every Moise cell in the band between those two successors
is bounded by the sum of their prescribed quarter-buffer bounds. -/
theorem nextInsideCollarMoiseBandClosedRegion_subset_closedBall
    (k : ℕ) (S : I.InsideCollarStage)
    (a : LevelAddress (I.nextInsideCollarLater k S).next.level) :
    let S₁ := InsideCollarStage.ofLater I S
      (I.nextInsideCollarLater k S)
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    (L₁.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4) := by
  dsimp only
  let L₀ := I.nextInsideCollarLater k S
  let T := L₀.next
  let S₁ := InsideCollarStage.ofLater I S L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  have hcell : (L₁.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (T.buffer / 4 + L₁.next.buffer / 4) := by
    exact T.moiseBandClosedRegion_subset_closedBall L₁ a
  have h₀ : T.buffer ≤ successorBufferBound k := by
    exact I.nextInsideCollarLater_buffer_le k S
  have h₁ : L₁.next.buffer ≤ successorBufferBound (k + 1) := by
    exact I.nextInsideCollarLater_buffer_le (k + 1) S₁
  exact hcell.trans (closedBall_subset_closedBall (by linarith))

/-- The actual recursive sequence has the same bound on the band between
stages `k+1` and `k+2`. -/
theorem shrinkingMoiseBandClosedRegion_subset_closedBall
    (k : ℕ)
    (a : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level) :
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k)
      (I.nextInsideCollarLater k (I.shrinkingInsideCollarStage k))
    let L := I.nextInsideCollarLater (k + 1) S₁
    (L.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4) := by
  exact I.nextInsideCollarMoiseBandClosedRegion_subset_closedBall k
    (I.shrinkingInsideCollarStage k) a

/-- Uniform shrinking of all cells in sufficiently late Moise bands.  This
is the metric input for continuity of the eventual cellwise map at the
original Jordan boundary. -/
theorem eventually_shrinkingMoiseBandClosedRegion_subset_closedBall
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ a : LevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level,
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k)
        (I.nextInsideCollarLater k (I.shrinkingInsideCollarStage k))
      let L := I.nextInsideCollarLater (k + 1) S₁
      (L.moiseBandPolygonalCircle a).closedRegion ⊆
        closedBall (J.curvePoint (I.levelArc a).left : Plane) rho := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hrho
  refine ⟨N, ?_⟩
  intro k hk a
  have hmonotone : successorBufferBound k ≤ successorBufferBound N := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right hk 1
  have hsmall : successorBufferBound N < rho := by
    simpa [successorBufferBound, one_div] using hN
  have hnext : successorBufferBound (k + 1) ≤
      successorBufferBound k := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    norm_num
  have hkpos := successorBufferBound_pos k
  have hradius : successorBufferBound k / 4 +
      successorBufferBound (k + 1) / 4 ≤ rho := by
    calc
      successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4 ≤
          successorBufferBound k / 4 +
            successorBufferBound k / 4 := by linarith
      _ ≤ successorBufferBound k := by linarith
      _ ≤ successorBufferBound N := hmonotone
      _ ≤ rho := hsmall.le
  exact (I.shrinkingMoiseBandClosedRegion_subset_closedBall k a).trans
    (closedBall_subset_closedBall hradius)

/-- Once the prescribed buffer is smaller than half the distance between
the two initial subdivision marks, every cell in the corresponding recursive
band has the outward orientation.  In particular, it meets the preceding
closed polygonal disk in exactly its parent crosscut. -/
theorem shrinkingMoiseBand_parentClosedRegion_inter
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2)
    (a : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    L₀.next.circle.closedRegion ∩
        (L₁.moiseBandPolygonalCircle a).closedRegion =
      range (L₀.next.family.forgetObstacle.synchronizedCrosscutPath a) := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  let a₀ : LevelAddress L₀.next.level :=
    _root_.cast
      (congrArg LevelAddress (Nat.zero_add L₀.next.level))
      (leftmostDescendant
        (false, fun i : Fin 0 => Fin.elim0 i) L₀.next.level)
  let a₁ : LevelAddress L₀.next.level :=
    _root_.cast
      (congrArg LevelAddress (Nat.zero_add L₀.next.level))
      (leftmostDescendant
        (true, fun i : Fin 0 => Fin.elim0 i) L₀.next.level)
  let x := L₀.next.family.forgetObstacle.leftSynchronizedPoint a₀
  let y := L₀.next.family.forgetObstacle.leftSynchronizedPoint a₁
  have ha₀ : (I.levelArc a₀).left = I.first.left := by
    dsimp only [a₀]
    rw [I.levelArc_cast (Nat.zero_add L₀.next.level),
      I.levelArc_leftmostDescendant_left]
    rfl
  have ha₁ : (I.levelArc a₁).left = I.second.left := by
    dsimp only [a₁]
    rw [I.levelArc_cast (Nat.zero_add L₀.next.level),
      I.levelArc_leftmostDescendant_left]
    rfl
  apply L₁.parentClosedRegion_inter_moiseBandClosedRegion_of_cell_ball
      a (c := J.curvePoint (I.levelArc a).left)
      (rho := successorBufferBound k / 4 +
        successorBufferBound (k + 1) / 4)
  · exact I.shrinkingMoiseBandClosedRegion_subset_closedBall k a
  · refine ⟨x, ?_, y, ?_, ?_⟩
    · change x ∈ L₀.next.circle.closedRegion
      rw [L₀.next.circle.closedRegion_eq_union]
      apply Or.inr
      change x ∈
        (L₀.next.family.forgetObstacle.synchronizedPolygonalCircle
          L₀.next.one_le_level).carrier
      rw [L₀.next.family.forgetObstacle.carrier_synchronizedPolygonalCircle
        L₀.next.one_le_level]
      exact Set.mem_iUnion.mpr
        ⟨a₀, Path.source_mem_range
          (L₀.next.family.forgetObstacle.synchronizedCrosscutPath a₀)⟩
    · change y ∈ L₀.next.circle.closedRegion
      rw [L₀.next.circle.closedRegion_eq_union]
      apply Or.inr
      change y ∈
        (L₀.next.family.forgetObstacle.synchronizedPolygonalCircle
          L₀.next.one_le_level).carrier
      rw [L₀.next.family.forgetObstacle.carrier_synchronizedPolygonalCircle
        L₀.next.one_le_level]
      exact Set.mem_iUnion.mpr
        ⟨a₁, Path.source_mem_range
          (L₀.next.family.forgetObstacle.synchronizedCrosscutPath a₁)⟩
    · have hx : dist (J.curvePoint I.first.left : Plane) x ≤
          L₀.next.buffer / 4 := by
        rw [← ha₀]
        exact L₀.next.dist_leftBoundary_leftSynchronizedPoint_le a₀
      have hy : dist (J.curvePoint I.first.right : Plane) y ≤
          L₀.next.buffer / 4 := by
        have hy' :=
          L₀.next.dist_leftBoundary_leftSynchronizedPoint_le a₁
        rw [ha₁, ← I.adjacent] at hy'
        exact hy'
      have hbuffer : L₀.next.buffer ≤ successorBufferBound k :=
        I.nextInsideCollarLater_buffer_le k S₀
      have hnext : successorBufferBound (k + 1) ≤
          successorBufferBound k := by
        unfold successorBufferBound
        apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
        norm_num
      have hlower :
          dist (J.curvePoint I.first.left : Plane)
              (J.curvePoint I.first.right : Plane) ≤
            dist (J.curvePoint I.first.left : Plane) x +
              dist x y +
              dist y (J.curvePoint I.first.right : Plane) := by
        calc
          dist (J.curvePoint I.first.left : Plane)
              (J.curvePoint I.first.right : Plane) ≤
              dist (J.curvePoint I.first.left : Plane) x +
                dist x (J.curvePoint I.first.right : Plane) :=
            dist_triangle _ _ _
          _ ≤ dist (J.curvePoint I.first.left : Plane) x +
                (dist x y +
                  dist y (J.curvePoint I.first.right : Plane)) := by
            gcongr
            exact dist_triangle _ _ _
          _ = dist (J.curvePoint I.first.left : Plane) x +
                dist x y +
                dist y (J.curvePoint I.first.right : Plane) := by ring
      have hdist :
          dist (J.curvePoint I.first.left : Plane)
              (J.curvePoint I.first.right : Plane) -
              successorBufferBound k / 2 ≤ dist x y := by
        rw [dist_comm] at hy
        linarith
      have hdiameter :
          2 * (successorBufferBound k / 4 +
              successorBufferBound (k + 1) / 4) ≤
            successorBufferBound k := by
        linarith
      have hkpos := successorBufferBound_pos k
      linarith

/-- Under the late-stage size hypothesis, the preceding closed disk and all
cells of the recursive Moise band fill exactly the next closed polygonal
disk. -/
theorem shrinkingMoiseFilledDisk_eq_nextClosedRegion
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    L₁.moiseFilledDisk = L₁.next.circle.closedRegion := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.moiseFilledDisk_eq_childClosedRegion fun a =>
    I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall a

/-- Under the late-stage side choice, the cells themselves (without the
parent disk) are exactly the closed shell between the two consecutive
polygonal collars. -/
theorem shrinkingMoiseBandClosedCells_eq_closedShell
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    L₁.moiseBandClosedCells =
      PolygonalCircle.closedShell L₀.next.circle L₁.next.circle := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.moiseBandClosedCells_eq_closedShell fun a =>
    I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall a

/-- The filled-band identity and the stored carrier avoidance upgrade weak
containment to strict nesting of the two polygonal disks. -/
theorem shrinkingMoiseBand_parentClosedRegion_subset_nextInteriorRegion
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    L₀.next.circle.closedRegion ⊆ L₁.next.circle.interiorRegion := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  intro x hxParent
  have hxFilled : x ∈ L₁.moiseFilledDisk := Or.inl hxParent
  have hxChild : x ∈ L₁.next.circle.closedRegion := by
    rw [← I.shrinkingMoiseFilledDisk_eq_nextClosedRegion k hsmall]
    exact hxFilled
  rw [L₁.next.circle.closedRegion_eq_union] at hxChild
  exact hxChild.resolve_right fun hxCarrier =>
    Set.disjoint_left.mp L₁.next.carrier_disjoint hxParent hxCarrier

/-- The same late-stage estimate, packaged in the exact form consumed by
the relative disk-extension construction. -/
noncomputable def shrinkingMoiseBandAttachmentPresentation
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2)
    (a : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    PolygonalDiskAttachment.Presentation
      L₀.next.circle.closedRegion := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.moiseBandAttachmentPresentation a <|
    I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall a

/-- Under the same late-stage size hypothesis, consecutive closed cells in
the cyclic Moise band meet in exactly their common side seam. -/
theorem shrinkingMoiseBand_cellClosedRegion_inter_next
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2)
    (a : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    (L₁.moiseBandPolygonalCircle a).closedRegion ∩
        (L₁.moiseBandPolygonalCircle
          (nextLevelAddress L₀.next.level a)).closedRegion =
      L₁.adjacentMoiseBandSideSeam a := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.cellClosedRegion_inter_next a
    (I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall a)
    (I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall
      (nextLevelAddress L₀.next.level a))

/-- Under the late-stage size hypothesis, cyclically nonadjacent closed
cells in the selected Moise band are disjoint. -/
theorem shrinkingMoiseBand_disjoint_cellClosedRegion_of_nonadjacent
    (k : ℕ)
    (hsmall : successorBufferBound k <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2)
    (a d : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level)
    (had : a ≠ d)
    (hda : d ≠ nextLevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level a)
    (hadNext : a ≠ nextLevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level d) :
    let L₀ := I.nextInsideCollarLater k
      (I.shrinkingInsideCollarStage k)
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k) L₀
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    Disjoint (L₁.moiseBandPolygonalCircle a).closedRegion
      (L₁.moiseBandPolygonalCircle d).closedRegion := by
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.disjoint_cellClosedRegion_of_nonadjacent
    a d had hda hadNext
    (I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall a)
    (I.shrinkingMoiseBand_parentClosedRegion_inter k hsmall d)

/-- All sufficiently late recursive Moise cells therefore have the correct
side choice, uniformly over the finite address set at each level. -/
theorem eventually_shrinkingMoiseBand_parentClosedRegion_inter :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ a : LevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level,
      let L₀ := I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k) L₀
      let L₁ := I.nextInsideCollarLater (k + 1) S₁
      L₀.next.circle.closedRegion ∩
          (L₁.moiseBandPolygonalCircle a).closedRegion =
        range
          (L₀.next.family.forgetObstacle.synchronizedCrosscutPath a) := by
  have hdist : 0 < dist (J.curvePoint I.first.left : Plane)
      (J.curvePoint I.first.right : Plane) :=
    dist_pos.mpr I.first.endpoint_ne
  have hrho : 0 < dist (J.curvePoint I.first.left : Plane)
      (J.curvePoint I.first.right : Plane) / 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hrho
  refine ⟨N, ?_⟩
  intro k hk a
  apply I.shrinkingMoiseBand_parentClosedRegion_inter k
  have hmonotone : successorBufferBound k ≤
      successorBufferBound N := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right hk 1
  have hsmall : successorBufferBound N <
      dist (J.curvePoint I.first.left : Plane)
        (J.curvePoint I.first.right : Plane) / 2 := by
    simpa [successorBufferBound, one_div] using hN
  exact hmonotone.trans_lt hsmall

/-- All sufficiently late finite Moise cell unions are exactly the closed
shells between successive stages of the shrinking collar sequence. -/
theorem eventually_shrinkingMoiseBandClosedCells_eq_closedShell :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      let L₀ := I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k) L₀
      let L₁ := I.nextInsideCollarLater (k + 1) S₁
      L₁.moiseBandClosedCells =
        PolygonalCircle.closedShell L₀.next.circle L₁.next.circle := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingMoiseBand_parentClosedRegion_inter
  refine ⟨N, ?_⟩
  intro k hk
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.moiseBandClosedCells_eq_closedShell (hN k hk)

/-- All sufficiently late recursive bands strictly nest their parent
polygonal disk inside their child polygonal disk. -/
theorem eventually_shrinkingMoiseBand_parentClosedRegion_subset_nextInteriorRegion :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      let L₀ := I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k) L₀
      let L₁ := I.nextInsideCollarLater (k + 1) S₁
      L₀.next.circle.closedRegion ⊆
        L₁.next.circle.interiorRegion := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingMoiseBand_parentClosedRegion_inter
  refine ⟨N, ?_⟩
  intro k hk
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.parentClosedRegion_subset_childInteriorRegion (hN k hk)

/-- Stable sequence-facing form of eventual strict nesting.  This discharges
the planar-side obligation that was intentionally left out of
`InsideCollarStage`. -/
theorem eventually_shrinkingInsideCollarStage_strictlyNested :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (I.shrinkingInsideCollarStage k.succ).circle.closedRegion ⊆
        (I.shrinkingInsideCollarStage k.succ.succ).circle.interiorRegion := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingMoiseBand_parentClosedRegion_subset_nextInteriorRegion
  refine ⟨N, ?_⟩
  intro k hk
  have h := hN k hk
  simpa only [I.shrinkingInsideCollarStage_succ,
    nextInsideCollarStage, InsideCollarStage.circle_ofLater] using h

/-- Uniformly in every sufficiently late cyclic band, consecutive closed
cells overlap precisely in their shared side seam. -/
theorem eventually_shrinkingMoiseBand_cellClosedRegion_inter_next :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ a : LevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level,
      let L₀ := I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k) L₀
      let L₁ := I.nextInsideCollarLater (k + 1) S₁
      (L₁.moiseBandPolygonalCircle a).closedRegion ∩
          (L₁.moiseBandPolygonalCircle
            (nextLevelAddress L₀.next.level a)).closedRegion =
        L₁.adjacentMoiseBandSideSeam a := by
  obtain ⟨N, hN⟩ := I.eventually_shrinkingMoiseBand_parentClosedRegion_inter
  refine ⟨N, ?_⟩
  intro k hk a
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.cellClosedRegion_inter_next a
    (hN k hk a)
    (hN k hk (nextLevelAddress L₀.next.level a))

/-- Uniformly in every sufficiently late band, all cyclically nonadjacent
closed cells are disjoint. -/
theorem eventually_shrinkingMoiseBand_disjoint_cellClosedRegion_of_nonadjacent :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ a d : LevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level,
      a ≠ d →
      d ≠ nextLevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level a →
      a ≠ nextLevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level d →
      let L₀ := I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k) L₀
      let L₁ := I.nextInsideCollarLater (k + 1) S₁
      Disjoint (L₁.moiseBandPolygonalCircle a).closedRegion
        (L₁.moiseBandPolygonalCircle d).closedRegion := by
  obtain ⟨N, hN⟩ := I.eventually_shrinkingMoiseBand_parentClosedRegion_inter
  refine ⟨N, ?_⟩
  intro k hk a d had hda hadNext
  dsimp only
  let S₀ := I.shrinkingInsideCollarStage k
  let L₀ := I.nextInsideCollarLater k S₀
  let S₁ := InsideCollarStage.ofLater I S₀ L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  exact L₁.disjoint_cellClosedRegion_of_nonadjacent
    a d had hda hadNext (hN k hk a) (hN k hk d)

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
