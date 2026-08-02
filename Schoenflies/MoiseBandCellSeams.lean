import Schoenflies.MoiseBandCellCover

/-!
# Adjacent seams in a recursive Moise band

Successive Moise band cells use the same retained access hair.  Their two
extreme side segments end at the common parent synchronized point, so the
hair order makes the segments nested.  This file packages their intersection
as the local seam needed by the later finite gluing argument.
-/

namespace Schoenflies

open Metric Set Function AffineMap
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

/-- The extreme right retained-hair side of one recursive Moise cell. -/
noncomputable def moiseBandRightSideCarrier (a : LevelAddress n) : Set Plane :=
  segment ℝ
    (L.next.family.forgetObstacle.trimmedRightPoint
      (levelIndexOf L.next.level (L.rightmostAddress a)))
    (F.rightSynchronizedPoint a)

/-- The extreme left retained-hair side of one recursive Moise cell. -/
noncomputable def moiseBandLeftSideCarrier (a : LevelAddress n) : Set Plane :=
  segment ℝ (F.leftSynchronizedPoint a)
    (L.next.family.forgetObstacle.trimmedLeftPoint
      (levelIndexOf L.next.level (L.leftmostAddress a)))

/-- The side seam shared by a recursive Moise cell and its cyclic successor. -/
noncomputable def adjacentMoiseBandSideSeam (a : LevelAddress n) : Set Plane :=
  L.moiseBandRightSideCarrier a ∩
    L.moiseBandLeftSideCarrier (nextLevelAddress n a)

theorem moiseBandRightSideCarrier_subset (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a ⊆ L.moiseBandCarrier a := by
  simpa [moiseBandRightSideCarrier] using
    L.rawRightSide_subset_moiseBandCarrier a

theorem moiseBandLeftSideCarrier_subset (a : LevelAddress n) :
    L.moiseBandLeftSideCarrier a ⊆ L.moiseBandCarrier a := by
  simpa [moiseBandLeftSideCarrier] using
    L.rawLeftSide_subset_moiseBandCarrier a

theorem adjacentMoiseBandSideSeam_subset_left (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a ⊆ L.moiseBandCarrier a := by
  exact Set.inter_subset_left.trans (L.moiseBandRightSideCarrier_subset a)

theorem adjacentMoiseBandSideSeam_subset_right (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a ⊆
      L.moiseBandCarrier (nextLevelAddress n a) := by
  exact Set.inter_subset_right.trans
    (L.moiseBandLeftSideCarrier_subset (nextLevelAddress n a))

/-- The common parent synchronized endpoint lies on the adjacent seam. -/
theorem rightSynchronizedPoint_mem_adjacentMoiseBandSideSeam
    (a : LevelAddress n) :
    F.rightSynchronizedPoint a ∈ L.adjacentMoiseBandSideSeam a := by
  constructor
  · exact right_mem_segment ℝ _ _
  · rw [F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
    exact left_mem_segment ℝ _ _

/-- On their common retained hair the two adjacent side segments are nested.
Thus their intersection is exactly one of the two complete side segments,
with no hidden branching or extra component. -/
theorem adjacentMoiseBandSideSeam_eq_right_or_left
    (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a = L.moiseBandRightSideCarrier a ∨
      L.adjacentMoiseBandSideSeam a =
        L.moiseBandLeftSideCarrier (nextLevelAddress n a) := by
  let G := L.next.family.forgetObstacle
  let b := nextLevelAddress n a
  let c := L.rightmostAddress a
  let d := L.leftmostAddress b
  let H := I.levelRightHair a
  let x : H.carrier :=
    ⟨G.trimmedRightPoint (levelIndexOf L.next.level c), by
      rw [← L.rightmostAddress_rightHair_carrier a]
      exact (G.rightHairPoint c).2⟩
  have hab : I.LevelAdjacent a b := by
    dsimp only [b]
    exact I.levelAdjacent_nextLevelAddress n a
  let y : H.carrier :=
    ⟨G.trimmedLeftPoint (levelIndexOf L.next.level d), by
      rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq a b hab]
      rw [← L.leftmostAddress_leftHair_carrier b]
      exact (G.leftHairPoint d).2⟩
  let p : H.carrier :=
    ⟨F.rightSynchronizedPoint a,
      F.rightSynchronizedPoint_mem_rightHair a⟩
  have hxp : H.carrierParameter x < H.carrierParameter p := by
    dsimp only [H, x, p, c]
    exact L.rightmost_trimmed_carrierParameter_lt_parent a
  have hsync : F.rightSynchronizedPoint a =
      F.leftSynchronizedPoint b := by
    dsimp only [b]
    exact F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a
  have hyp : H.carrierParameter y < H.carrierParameter p := by
    apply H.carrierParameter_lt_of_dist_base_lt
    change dist (J.curvePoint (I.levelArc a).right : Plane)
        (G.trimmedLeftPoint (levelIndexOf L.next.level d)) <
      dist (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a)
    rw [hab, hsync]
    exact L.next.dist_child_trimmedLeft_lt_parent_left F hn b d
      (by simp [d, L.levelArc_leftmostAddress_left b])
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · right
    have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le x y p hxy hyp.le
    simpa only [adjacentMoiseBandSideSeam, moiseBandRightSideCarrier,
      moiseBandLeftSideCarrier, b, c, d, x, y, p, segment_symm, hsync]
      using hinter
  · left
    have hyx : H.carrierParameter y ≤ H.carrierParameter x :=
      le_of_not_ge hxy
    have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le y x p hyx hxp.le
    rw [Set.inter_comm] at hinter
    simpa only [adjacentMoiseBandSideSeam, moiseBandRightSideCarrier,
      moiseBandLeftSideCarrier, b, c, d, x, y, p, segment_symm, hsync]
      using hinter

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
