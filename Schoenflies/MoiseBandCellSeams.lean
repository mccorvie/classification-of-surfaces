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

/-- The raw endpoint on the right edge of the last child belonging to `a`,
regarded as a point of the retained right hair of `a`. -/
noncomputable def adjacentMoiseBandRightRawPoint (a : LevelAddress n) :
    (I.levelRightHair a).carrier :=
  ⟨L.next.family.forgetObstacle.trimmedRightPoint
      (levelIndexOf L.next.level (L.rightmostAddress a)), by
    rw [← L.rightmostAddress_rightHair_carrier a]
    exact (L.next.family.forgetObstacle.rightHairPoint
      (L.rightmostAddress a)).2⟩

/-- The raw endpoint on the left edge of the first child of the cyclic
successor, transported onto the same retained right hair of `a`. -/
noncomputable def adjacentMoiseBandLeftRawPoint (a : LevelAddress n) :
    (I.levelRightHair a).carrier :=
  ⟨L.next.family.forgetObstacle.trimmedLeftPoint
      (levelIndexOf L.next.level
        (L.leftmostAddress (nextLevelAddress n a))), by
    rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq a
      (nextLevelAddress n a) (I.levelAdjacent_nextLevelAddress n a)]
    rw [← L.leftmostAddress_leftHair_carrier (nextLevelAddress n a)]
    exact (L.next.family.forgetObstacle.leftHairPoint
      (L.leftmostAddress (nextLevelAddress n a))).2⟩

/-- The common parent synchronized endpoint on the retained hair. -/
noncomputable def adjacentMoiseBandParentPoint (a : LevelAddress n) :
    (I.levelRightHair a).carrier := by
  let _stage := L.next
  exact ⟨F.rightSynchronizedPoint a,
    F.rightSynchronizedPoint_mem_rightHair a⟩

/-- The deeper of the two raw child endpoints is the inner endpoint of the
overlap between the two parent-cell sides. -/
noncomputable def adjacentMoiseBandInnerSeamPoint (a : LevelAddress n) :
    (I.levelRightHair a).carrier :=
  (I.levelRightHair a).deeperPoint
    (L.adjacentMoiseBandRightRawPoint a)
    (L.adjacentMoiseBandLeftRawPoint a)

@[simp] theorem coe_adjacentMoiseBandRightRawPoint (a : LevelAddress n) :
    (L.adjacentMoiseBandRightRawPoint a : Plane) =
      L.next.family.forgetObstacle.trimmedRightPoint
        (levelIndexOf L.next.level (L.rightmostAddress a)) := rfl

@[simp] theorem coe_adjacentMoiseBandLeftRawPoint (a : LevelAddress n) :
    (L.adjacentMoiseBandLeftRawPoint a : Plane) =
      L.next.family.forgetObstacle.trimmedLeftPoint
        (levelIndexOf L.next.level
          (L.leftmostAddress (nextLevelAddress n a))) := rfl

@[simp] theorem coe_adjacentMoiseBandParentPoint (a : LevelAddress n) :
    (L.adjacentMoiseBandParentPoint a : Plane) =
      F.rightSynchronizedPoint a := rfl

theorem adjacentMoiseBandRightRawPoint_parameter_lt_parent
    (a : LevelAddress n) :
    (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandRightRawPoint a) <
      (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandParentPoint a) := by
  exact L.rightmost_trimmed_carrierParameter_lt_parent a

theorem adjacentMoiseBandLeftRawPoint_parameter_lt_parent
    (a : LevelAddress n) :
    (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandLeftRawPoint a) <
      (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandParentPoint a) := by
  let b := nextLevelAddress n a
  let G := L.next.family.forgetObstacle
  apply (I.levelRightHair a).carrierParameter_lt_of_dist_base_lt
  change dist (J.curvePoint (I.levelArc a).right : Plane)
      (G.trimmedLeftPoint
        (levelIndexOf L.next.level (L.leftmostAddress b))) <
    dist (J.curvePoint (I.levelArc a).right : Plane)
      (F.rightSynchronizedPoint a)
  have hab : I.LevelAdjacent a b := by
    dsimp only [b]
    exact I.levelAdjacent_nextLevelAddress n a
  have hsync : F.rightSynchronizedPoint a =
      F.leftSynchronizedPoint b := by
    dsimp only [b]
    exact F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a
  rw [hab, hsync]
  exact L.next.dist_child_trimmedLeft_lt_parent_left F hn b
    (L.leftmostAddress b)
    (by simp [L.levelArc_leftmostAddress_left b])

theorem adjacentMoiseBandInnerSeamPoint_parameter_lt_parent
    (a : LevelAddress n) :
    (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandInnerSeamPoint a) <
      (I.levelRightHair a).carrierParameter
        (L.adjacentMoiseBandParentPoint a) := by
  exact (I.levelRightHair a).deeperPoint_parameter_lt _ _ _
    (L.adjacentMoiseBandRightRawPoint_parameter_lt_parent a)
    (L.adjacentMoiseBandLeftRawPoint_parameter_lt_parent a)

/-- The extreme right retained-hair side of one recursive Moise cell. -/
noncomputable def moiseBandRightSideCarrier (a : LevelAddress n) : Set Plane :=
  segment ℝ (L.adjacentMoiseBandRightRawPoint a : Plane)
    (L.adjacentMoiseBandParentPoint a : Plane)

/-- The extreme left retained-hair side of one recursive Moise cell. -/
noncomputable def moiseBandLeftSideCarrier (a : LevelAddress n) : Set Plane :=
  segment ℝ (F.leftSynchronizedPoint a)
    (L.next.family.forgetObstacle.trimmedLeftPoint
      (levelIndexOf L.next.level (L.leftmostAddress a)))

/-- The side seam shared by a recursive Moise cell and its cyclic successor. -/
noncomputable def adjacentMoiseBandSideSeam (a : LevelAddress n) : Set Plane :=
  L.moiseBandRightSideCarrier a ∩
    L.moiseBandLeftSideCarrier (nextLevelAddress n a)

theorem moiseBandRightSideCarrier_eq_segment (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a =
      segment ℝ (L.adjacentMoiseBandRightRawPoint a : Plane)
        (L.adjacentMoiseBandParentPoint a : Plane) := rfl

theorem moiseBandLeftSideCarrier_next_eq_segment (a : LevelAddress n) :
    L.moiseBandLeftSideCarrier (nextLevelAddress n a) =
      segment ℝ (L.adjacentMoiseBandLeftRawPoint a : Plane)
        (L.adjacentMoiseBandParentPoint a : Plane) := by
  rw [moiseBandLeftSideCarrier, segment_symm]
  simp only [coe_adjacentMoiseBandLeftRawPoint,
    coe_adjacentMoiseBandParentPoint,
    F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]

theorem moiseBandRightSideCarrier_subset (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a ⊆ L.moiseBandCarrier a := by
  rw [L.moiseBandRightSideCarrier_eq_segment a]
  simpa only [coe_adjacentMoiseBandRightRawPoint,
    coe_adjacentMoiseBandParentPoint] using
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
  let H := I.levelRightHair a
  let x := L.adjacentMoiseBandRightRawPoint a
  let y := L.adjacentMoiseBandLeftRawPoint a
  let p := L.adjacentMoiseBandParentPoint a
  have hxp : H.carrierParameter x < H.carrierParameter p :=
    L.adjacentMoiseBandRightRawPoint_parameter_lt_parent a
  have hyp : H.carrierParameter y < H.carrierParameter p :=
    L.adjacentMoiseBandLeftRawPoint_parameter_lt_parent a
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · right
    have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le x y p hxy hyp.le
    rw [adjacentMoiseBandSideSeam,
      L.moiseBandRightSideCarrier_eq_segment a,
      L.moiseBandLeftSideCarrier_next_eq_segment a]
    exact hinter
  · left
    have hyx : H.carrierParameter y ≤ H.carrierParameter x :=
      le_of_not_ge hxy
    have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le y x p hyx hxp.le
    rw [Set.inter_comm] at hinter
    rw [adjacentMoiseBandSideSeam,
      L.moiseBandRightSideCarrier_eq_segment a,
      L.moiseBandLeftSideCarrier_next_eq_segment a]
    exact hinter

/-- Exact intrinsic description of the adjacent seam as the tail from the
deeper raw child endpoint to the common parent synchronized endpoint. -/
theorem adjacentMoiseBandSideSeam_eq_segment (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a =
      segment ℝ (L.adjacentMoiseBandInnerSeamPoint a : Plane)
        (L.adjacentMoiseBandParentPoint a : Plane) := by
  let H := I.levelRightHair a
  let x := L.adjacentMoiseBandRightRawPoint a
  let y := L.adjacentMoiseBandLeftRawPoint a
  let p := L.adjacentMoiseBandParentPoint a
  have hxp : H.carrierParameter x < H.carrierParameter p :=
    L.adjacentMoiseBandRightRawPoint_parameter_lt_parent a
  have hyp : H.carrierParameter y < H.carrierParameter p :=
    L.adjacentMoiseBandLeftRawPoint_parameter_lt_parent a
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le x y p hxy hyp.le
    rw [adjacentMoiseBandSideSeam,
      L.moiseBandRightSideCarrier_eq_segment a,
      L.moiseBandLeftSideCarrier_next_eq_segment a]
    change segment ℝ (x : Plane) (p : Plane) ∩
        segment ℝ (y : Plane) (p : Plane) =
      segment ℝ (H.deeperPoint x y : Plane) (p : Plane)
    rw [JordanCircle.InsideAccessHair.deeperPoint, if_pos hxy]
    exact hinter
  · have hyx : H.carrierParameter y ≤ H.carrierParameter x :=
      le_of_not_ge hxy
    have hinter :=
      H.tailSegment_inter_tailSegment_eq_of_parameter_le y x p hyx hxp.le
    rw [Set.inter_comm] at hinter
    rw [adjacentMoiseBandSideSeam,
      L.moiseBandRightSideCarrier_eq_segment a,
      L.moiseBandLeftSideCarrier_next_eq_segment a]
    change segment ℝ (x : Plane) (p : Plane) ∩
        segment ℝ (y : Plane) (p : Plane) =
      segment ℝ (H.deeperPoint x y : Plane) (p : Plane)
    rw [JordanCircle.InsideAccessHair.deeperPoint, if_neg hxy]
    exact hinter

theorem adjacentMoiseBandInnerSeamPoint_ne_parent (a : LevelAddress n) :
    (L.adjacentMoiseBandInnerSeamPoint a : Plane) ≠
      L.adjacentMoiseBandParentPoint a := by
  intro h
  have hsub : L.adjacentMoiseBandInnerSeamPoint a =
      L.adjacentMoiseBandParentPoint a := Subtype.ext h
  have hparam := congrArg (I.levelRightHair a).carrierParameter hsub
  exact (ne_of_lt
    (L.adjacentMoiseBandInnerSeamPoint_parameter_lt_parent a)) hparam

/-- Canonical affine parametrization of the complete adjacent-cell seam. -/
noncomputable def adjacentMoiseBandSideSeamPath (a : LevelAddress n) :
    Path (L.adjacentMoiseBandInnerSeamPoint a : Plane)
      (L.adjacentMoiseBandParentPoint a : Plane) :=
  Path.segment _ _

theorem range_adjacentMoiseBandSideSeamPath (a : LevelAddress n) :
    range (L.adjacentMoiseBandSideSeamPath a) =
      L.adjacentMoiseBandSideSeam a := by
  rw [adjacentMoiseBandSideSeamPath, Path.range_segment,
    L.adjacentMoiseBandSideSeam_eq_segment a]

theorem adjacentMoiseBandSideSeamPath_injective (a : LevelAddress n) :
    Injective (L.adjacentMoiseBandSideSeamPath a) :=
  Path.segment_injective_of_ne
    (L.adjacentMoiseBandInnerSeamPoint_ne_parent a)

theorem isCompact_adjacentMoiseBandSideSeam (a : LevelAddress n) :
    IsCompact (L.adjacentMoiseBandSideSeam a) := by
  rw [L.adjacentMoiseBandSideSeam_eq_segment a]
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem isConnected_adjacentMoiseBandSideSeam (a : LevelAddress n) :
    IsConnected (L.adjacentMoiseBandSideSeam a) := by
  rw [L.adjacentMoiseBandSideSeam_eq_segment a]
  exact (convex_segment
    (L.adjacentMoiseBandInnerSeamPoint a : Plane)
    (L.adjacentMoiseBandParentPoint a : Plane)).isConnected
      ⟨_, left_mem_segment ℝ _ _⟩

theorem adjacentMoiseBandSideSeam_subset_closedRegion_inter (a : LevelAddress n) :
    L.adjacentMoiseBandSideSeam a ⊆
      (L.moiseBandPolygonalCircle a).closedRegion ∩
        (L.moiseBandPolygonalCircle (nextLevelAddress n a)).closedRegion := by
  intro x hx
  constructor
  · rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
    exact Or.inr <| by
      rw [L.moiseBandPolygonalCircle_carrier a]
      exact L.adjacentMoiseBandSideSeam_subset_left a hx
  · rw [(L.moiseBandPolygonalCircle
      (nextLevelAddress n a)).closedRegion_eq_union]
    exact Or.inr <| by
      rw [L.moiseBandPolygonalCircle_carrier]
      exact L.adjacentMoiseBandSideSeam_subset_right a hx

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
