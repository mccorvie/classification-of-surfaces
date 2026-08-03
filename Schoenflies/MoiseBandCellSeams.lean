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

theorem moiseBandLeftSideCarrier_subset_leftHairCarrier
    (a : LevelAddress n) :
    L.moiseBandLeftSideCarrier a ⊆ (I.levelLeftHair a).carrier := by
  exact L.rawLeftSide_subset_leftHairCarrier a

theorem moiseBandRightSideCarrier_subset_rightHairCarrier
    (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a ⊆ (I.levelRightHair a).carrier := by
  simpa only [moiseBandRightSideCarrier,
    coe_adjacentMoiseBandRightRawPoint,
    coe_adjacentMoiseBandParentPoint] using
      L.rawRightSide_subset_rightHairCarrier a

/-- Any old crosscut can meet a retained left side only at that side's old
synchronized endpoint. -/
theorem parentMoiseCarrier_inter_leftSideCarrier_subset
    (b d : LevelAddress n) :
    L.parentMoiseCarrier b ∩ L.moiseBandLeftSideCarrier d ⊆
      ({F.leftSynchronizedPoint d} : Set Plane) := by
  intro x hx
  have hxRange : x ∈ range (F.synchronizedCrosscutPath b) := by
    rw [← L.parentMoiseCarrier_eq_crosscutRange b]
    exact hx.1
  have hxParent : x ∈ (F.synchronizedPolygonalCircle hn).carrier := by
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr ⟨b, hxRange⟩
  have hxBase : x ∈ segment ℝ
      (J.curvePoint (I.levelArc d).left : Plane)
      (F.leftSynchronizedPoint d) :=
    L.rawLeftSide_subset_parentBaseSegment d hx.2
  have hxInter : x ∈ segment ℝ
      (J.curvePoint (I.levelArc d).left : Plane)
      (F.leftSynchronizedPoint d) ∩
        (F.synchronizedPolygonalCircle hn).carrier :=
    ⟨hxBase, hxParent⟩
  rwa [L.leftBaseSegment_inter_parentCarrier d] at hxInter

/-- The analogous old-crosscut intersection with a retained right side. -/
theorem parentMoiseCarrier_inter_rightSideCarrier_subset
    (b d : LevelAddress n) :
    L.parentMoiseCarrier b ∩ L.moiseBandRightSideCarrier d ⊆
      ({F.rightSynchronizedPoint d} : Set Plane) := by
  intro x hx
  have hxRange : x ∈ range (F.synchronizedCrosscutPath b) := by
    rw [← L.parentMoiseCarrier_eq_crosscutRange b]
    exact hx.1
  have hxParent : x ∈ (F.synchronizedPolygonalCircle hn).carrier := by
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr ⟨b, hxRange⟩
  have hxBase : x ∈ segment ℝ
      (J.curvePoint (I.levelArc d).right : Plane)
      (F.rightSynchronizedPoint d) := by
    apply L.rawRightSide_subset_parentBaseSegment d
    simpa only [moiseBandRightSideCarrier,
      coe_adjacentMoiseBandRightRawPoint,
      coe_adjacentMoiseBandParentPoint] using hx.2
  have hxInter : x ∈ segment ℝ
      (J.curvePoint (I.levelArc d).right : Plane)
      (F.rightSynchronizedPoint d) ∩
        (F.synchronizedPolygonalCircle hn).carrier :=
    ⟨hxBase, hxParent⟩
  rwa [L.rightBaseSegment_inter_parentCarrier d] at hxInter

/-- Adjacent old-crosscut portions meet only at their synchronized endpoint. -/
theorem parentMoiseCarrier_inter_next (a : LevelAddress n) :
    L.parentMoiseCarrier a ∩
        L.parentMoiseCarrier (nextLevelAddress n a) =
      {F.rightSynchronizedPoint a} := by
  rw [L.parentMoiseCarrier_eq_crosscutRange a,
    L.parentMoiseCarrier_eq_crosscutRange (nextLevelAddress n a),
    F.range_synchronizedCrosscutPath_inter_next hn a]

/-- The left sides of two adjacent cells lie on distinct retained hairs. -/
theorem disjoint_moiseBandLeftSideCarrier_next (a : LevelAddress n) :
    Disjoint (L.moiseBandLeftSideCarrier a)
      (L.moiseBandLeftSideCarrier (nextLevelAddress n a)) :=
  (I.disjoint_levelLeftHairs_of_ne a (nextLevelAddress n a)
      (nextLevelAddress_ne n a).symm).mono
    (L.moiseBandLeftSideCarrier_subset_leftHairCarrier a)
    (L.moiseBandLeftSideCarrier_subset_leftHairCarrier
      (nextLevelAddress n a))

/-- The right sides of two adjacent cells lie on distinct retained hairs. -/
theorem disjoint_moiseBandRightSideCarrier_next (a : LevelAddress n) :
    Disjoint (L.moiseBandRightSideCarrier a)
      (L.moiseBandRightSideCarrier (nextLevelAddress n a)) :=
  (I.disjoint_levelRightHairs_of_ne a (nextLevelAddress n a)
      (nextLevelAddress_ne n a).symm).mono
    (L.moiseBandRightSideCarrier_subset_rightHairCarrier a)
    (L.moiseBandRightSideCarrier_subset_rightHairCarrier
      (nextLevelAddress n a))

/-- The nonshared pair of extreme sides of adjacent cells is disjoint. -/
theorem disjoint_moiseBandLeftSideCarrier_rightSideCarrier_next
    (a : LevelAddress n) :
    Disjoint (L.moiseBandLeftSideCarrier a)
      (L.moiseBandRightSideCarrier (nextLevelAddress n a)) := by
  apply (I.disjoint_levelRightHair_levelLeftHair_of_ne_next
      (nextLevelAddress n a) a
      (nextLevelAddress_next_ne n hn a).symm).symm.mono
  · exact L.moiseBandLeftSideCarrier_subset_leftHairCarrier a
  · exact L.moiseBandRightSideCarrier_subset_rightHairCarrier
      (nextLevelAddress n a)

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

/-- The common point of the two adjacent old crosscuts is part of their side
seam as well. -/
theorem parentMoiseCarrier_inter_next_subset_sideSeam
    (a : LevelAddress n) :
    L.parentMoiseCarrier a ∩
        L.parentMoiseCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxPoint : x ∈ ({F.rightSynchronizedPoint a} : Set Plane) := by
    rw [← L.parentMoiseCarrier_inter_next a]
    exact hx
  have hxEq : x = F.rightSynchronizedPoint a :=
    mem_singleton_iff.mp hxPoint
  subst x
  constructor
  · exact right_mem_segment ℝ _ _
  · rw [F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
    exact left_mem_segment ℝ _ _

theorem leftSynchronizedPoint_mem_parentMoiseCarrier
    (a : LevelAddress n) :
    F.leftSynchronizedPoint a ∈ L.parentMoiseCarrier a := by
  rw [L.parentMoiseCarrier_eq_crosscutRange a]
  exact Path.source_mem_range (F.synchronizedCrosscutPath a)

theorem rightSynchronizedPoint_mem_parentMoiseCarrier
    (a : LevelAddress n) :
    F.rightSynchronizedPoint a ∈ L.parentMoiseCarrier a := by
  rw [L.parentMoiseCarrier_eq_crosscutRange a]
  exact Path.target_mem_range (F.synchronizedCrosscutPath a)

/-! The four mixed old-crosscut/side intersections below all reduce to the
old-crosscut intersection.  Packaging them separately keeps the eventual
four-by-four carrier decomposition proof purely set-theoretic. -/

theorem parentMoiseCarrier_inter_leftSideCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.parentMoiseCarrier a ∩
        L.moiseBandLeftSideCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxPoint := L.parentMoiseCarrier_inter_leftSideCarrier_subset
    a (nextLevelAddress n a) hx
  have hxEq : x = F.leftSynchronizedPoint (nextLevelAddress n a) :=
    mem_singleton_iff.mp hxPoint
  subst x
  refine ⟨?_, hx.2⟩
  change F.leftSynchronizedPoint (nextLevelAddress n a) ∈
    segment ℝ (L.adjacentMoiseBandRightRawPoint a : Plane)
      (F.rightSynchronizedPoint a)
  rw [← F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
  exact right_mem_segment ℝ _ _

theorem parentMoiseCarrier_inter_rightSideCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.parentMoiseCarrier a ∩
        L.moiseBandRightSideCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxPoint := L.parentMoiseCarrier_inter_rightSideCarrier_subset
    a (nextLevelAddress n a) hx
  have hxEq : x = F.rightSynchronizedPoint (nextLevelAddress n a) :=
    mem_singleton_iff.mp hxPoint
  have hxParentNext : x ∈
      L.parentMoiseCarrier (nextLevelAddress n a) := by
    rw [hxEq]
    exact L.rightSynchronizedPoint_mem_parentMoiseCarrier
      (nextLevelAddress n a)
  exact L.parentMoiseCarrier_inter_next_subset_sideSeam a
    ⟨hx.1, hxParentNext⟩

theorem leftSideCarrier_inter_parentMoiseCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.moiseBandLeftSideCarrier a ∩
        L.parentMoiseCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxPoint := L.parentMoiseCarrier_inter_leftSideCarrier_subset
    (nextLevelAddress n a) a ⟨hx.2, hx.1⟩
  have hxEq : x = F.leftSynchronizedPoint a :=
    mem_singleton_iff.mp hxPoint
  have hxParent : x ∈ L.parentMoiseCarrier a := by
    rw [hxEq]
    exact L.leftSynchronizedPoint_mem_parentMoiseCarrier a
  exact L.parentMoiseCarrier_inter_next_subset_sideSeam a
    ⟨hxParent, hx.2⟩

theorem rightSideCarrier_inter_parentMoiseCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a ∩
        L.parentMoiseCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxPoint := L.parentMoiseCarrier_inter_rightSideCarrier_subset
    (nextLevelAddress n a) a ⟨hx.2, hx.1⟩
  have hxEq : x = F.rightSynchronizedPoint a :=
    mem_singleton_iff.mp hxPoint
  have hxParent : x ∈ L.parentMoiseCarrier a := by
    rw [hxEq]
    exact L.rightSynchronizedPoint_mem_parentMoiseCarrier a
  exact L.parentMoiseCarrier_inter_next_subset_sideSeam a
    ⟨hxParent, hx.2⟩

/-- The finer route of the left adjacent cell can meet the following cell's
left side only at the extreme raw endpoint; whenever that endpoint is
present, it already lies in the common side seam. -/
theorem childMoiseCarrier_inter_leftSideCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.childMoiseCarrier a ∩
        L.moiseBandLeftSideCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxHair : x ∈ (I.levelRightHair a).carrier := by
    rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq a
      (nextLevelAddress n a) (I.levelAdjacent_nextLevelAddress n a)]
    exact L.moiseBandLeftSideCarrier_subset_leftHairCarrier
      (nextLevelAddress n a) hx.2
  have hxRaw : x ∈
      ({L.next.family.forgetObstacle.trimmedRightPoint
        (levelIndexOf L.next.level (L.rightmostAddress a))} : Set Plane) :=
    L.childMoiseCarrier_inter_parentRightHair_subset a ⟨hx.1, hxHair⟩
  have hxEq : x =
      L.next.family.forgetObstacle.trimmedRightPoint
        (levelIndexOf L.next.level (L.rightmostAddress a)) :=
    mem_singleton_iff.mp hxRaw
  refine ⟨?_, hx.2⟩
  rw [moiseBandRightSideCarrier, hxEq]
  exact left_mem_segment ℝ _ _

/-- Symmetrically, the following cell's finer route can meet the preceding
cell's right side only at the following extreme raw endpoint, which is again
already in the common side seam. -/
theorem rightSideCarrier_inter_childMoiseCarrier_next_subset_sideSeam
    (a : LevelAddress n) :
    L.moiseBandRightSideCarrier a ∩
        L.childMoiseCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  have hxHair : x ∈
      (I.levelLeftHair (nextLevelAddress n a)).carrier := by
    rw [← I.levelRightHair_carrier_eq_levelLeftHair_of_eq a
      (nextLevelAddress n a) (I.levelAdjacent_nextLevelAddress n a)]
    exact L.moiseBandRightSideCarrier_subset_rightHairCarrier a hx.1
  have hxRaw : x ∈
      ({L.next.family.forgetObstacle.trimmedLeftPoint
        (levelIndexOf L.next.level
          (L.leftmostAddress (nextLevelAddress n a)))} : Set Plane) :=
    L.childMoiseCarrier_inter_parentLeftHair_subset
      (nextLevelAddress n a) ⟨hx.2, hxHair⟩
  have hxEq : x =
      L.next.family.forgetObstacle.trimmedLeftPoint
        (levelIndexOf L.next.level
          (L.leftmostAddress (nextLevelAddress n a))) :=
    mem_singleton_iff.mp hxRaw
  refine ⟨hx.1, ?_⟩
  rw [moiseBandLeftSideCarrier, hxEq]
  exact right_mem_segment ℝ _ _

/-- The two nonincident side/descendant pairs in adjacent cells are
disjoint.  This is where the cyclic ordering of complete descendant blocks
enters the carrier-overlap proof. -/
theorem disjoint_leftSideCarrier_childMoiseCarrier_next
    (a : LevelAddress n) :
    Disjoint (L.moiseBandLeftSideCarrier a)
      (L.childMoiseCarrier (nextLevelAddress n a)) :=
  (L.disjoint_parentLeftHair_childMoiseCarrier_next a).mono
    (L.moiseBandLeftSideCarrier_subset_leftHairCarrier a)
    Set.Subset.rfl

theorem disjoint_childMoiseCarrier_rightSideCarrier_next
    (a : LevelAddress n) :
    Disjoint (L.childMoiseCarrier a)
      (L.moiseBandRightSideCarrier (nextLevelAddress n a)) :=
  (L.disjoint_childMoiseCarrier_parentRightHair_next a).mono
    Set.Subset.rfl
    (L.moiseBandRightSideCarrier_subset_rightHairCarrier
      (nextLevelAddress n a))

/-- The four conceptual pieces of a band carrier, stated using the side
carrier names used throughout this file. -/
theorem moiseBandCarrier_eq_parent_leftSide_child_rightSide
    (a : LevelAddress n) :
    L.moiseBandCarrier a =
      L.parentMoiseCarrier a ∪
        (L.moiseBandLeftSideCarrier a ∪
          (L.childMoiseCarrier a ∪ L.moiseBandRightSideCarrier a)) := by
  simpa only [moiseBandLeftSideCarrier, moiseBandRightSideCarrier,
    coe_adjacentMoiseBandRightRawPoint,
    coe_adjacentMoiseBandParentPoint] using
      L.moiseBandCarrier_eq_parent_left_child_right a

/-- Adjacent recursive Moise boundary carriers have no overlap away from
their common retained-hair seam. -/
theorem moiseBandCarrier_inter_next_subset_sideSeam
    (a : LevelAddress n) :
    L.moiseBandCarrier a ∩
        L.moiseBandCarrier (nextLevelAddress n a) ⊆
      L.adjacentMoiseBandSideSeam a := by
  intro x hx
  rw [L.moiseBandCarrier_eq_parent_leftSide_child_rightSide a] at hx
  rw [L.moiseBandCarrier_eq_parent_leftSide_child_rightSide
    (nextLevelAddress n a)] at hx
  rcases hx.1 with hxP | hxL | hxC | hxR <;>
    rcases hx.2 with hyP | hyL | hyC | hyR
  · exact L.parentMoiseCarrier_inter_next_subset_sideSeam a ⟨hxP, hyP⟩
  · exact L.parentMoiseCarrier_inter_leftSideCarrier_next_subset_sideSeam
      a ⟨hxP, hyL⟩
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_parentMoiseCarrier_childMoiseCarrier a
        (nextLevelAddress n a)) hxP hyC
  · exact L.parentMoiseCarrier_inter_rightSideCarrier_next_subset_sideSeam
      a ⟨hxP, hyR⟩
  · exact L.leftSideCarrier_inter_parentMoiseCarrier_next_subset_sideSeam
      a ⟨hxL, hyP⟩
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_moiseBandLeftSideCarrier_next a) hxL hyL
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_leftSideCarrier_childMoiseCarrier_next a) hxL hyC
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_moiseBandLeftSideCarrier_rightSideCarrier_next a) hxL hyR
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_parentMoiseCarrier_childMoiseCarrier
        (nextLevelAddress n a) a) hyP hxC
  · exact L.childMoiseCarrier_inter_leftSideCarrier_next_subset_sideSeam
      a ⟨hxC, hyL⟩
  · exact False.elim <| Set.disjoint_left.mp
      (L.childMoiseCarrier_disjoint_of_ne
        (nextLevelAddress_ne n a).symm) hxC hyC
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_childMoiseCarrier_rightSideCarrier_next a) hxC hyR
  · exact L.rightSideCarrier_inter_parentMoiseCarrier_next_subset_sideSeam
      a ⟨hxR, hyP⟩
  · exact ⟨hxR, hyL⟩
  · exact L.rightSideCarrier_inter_childMoiseCarrier_next_subset_sideSeam
      a ⟨hxR, hyC⟩
  · exact False.elim <| Set.disjoint_left.mp
      (L.disjoint_moiseBandRightSideCarrier_next a) hxR hyR

/-- Exact boundary overlap of two cyclically adjacent recursive cells. -/
theorem moiseBandCarrier_inter_next (a : LevelAddress n) :
    L.moiseBandCarrier a ∩
        L.moiseBandCarrier (nextLevelAddress n a) =
      L.adjacentMoiseBandSideSeam a := by
  apply Set.Subset.antisymm
  · exact L.moiseBandCarrier_inter_next_subset_sideSeam a
  · intro x hx
    exact ⟨L.adjacentMoiseBandSideSeam_subset_left a hx,
      L.adjacentMoiseBandSideSeam_subset_right a hx⟩

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
