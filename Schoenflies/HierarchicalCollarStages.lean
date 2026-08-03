import Schoenflies.HierarchicalLevelHairs
import Schoenflies.RecursiveCollarStages

/-!
# Quantitative compatibility of successive collar levels

A recursive collar stage is chosen in a thin neighborhood of the original
Jordan curve and avoids the earlier polygonal disk.  This file exposes the
metric inequalities needed by Moise's retained-hair construction: an old
collar point is at least the separation buffer from every boundary point,
whereas each new synchronized endpoint is strictly closer to its local
boundary endpoint.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace InitialAngularArcs
namespace RecursiveInsideCollarStep

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {P : PolygonalCircle} (S : I.RecursiveInsideCollarStep P)

/-- An old-disk point is separated from every point of the original Jordan
carrier by at least the stored collar buffer. -/
theorem buffer_le_dist_of_mem_closedRegion_of_mem_carrier
    {x q : Plane} (hx : x ∈ P.closedRegion) (hq : q ∈ J.carrier) :
    S.buffer ≤ dist x q := by
  apply le_of_not_gt
  intro hdist
  have hxThick : x ∈ thickening S.buffer J.carrier := by
    rw [mem_thickening_iff]
    exact ⟨q, hq, hdist⟩
  exact Set.disjoint_left.mp S.buffer_separation hx hxThick

/-- The new left synchronized endpoint lies in the small closed cell around
the left boundary endpoint of its level arc. -/
theorem leftSynchronizedPoint_mem_cellClosedBall
    (b : LevelAddress S.level) :
    S.family.forgetObstacle.leftSynchronizedPoint b ∈
      closedBall (J.curvePoint (I.levelArc b).left : Plane)
        (S.buffer / 4) := by
  let G := S.family.forgetObstacle
  have hcarrier : G.leftSynchronizedPoint b ∈
      (G.exactSynchronizedAuxiliaryJordanCircle b).carrier :=
    G.range_synchronizedCrosscutPath_subset_exactAuxiliaryCarrier b
      (Path.source_mem_range (G.synchronizedCrosscutPath b))
  have hclosure : G.leftSynchronizedPoint b ∈
      closure (G.exactSynchronizedAuxiliaryJordanCircle b).inside := by
    rw [(G.exactSynchronizedAuxiliaryJordanCircle b).closure_inside]
    exact Or.inr hcarrier
  exact S.cell_near b hclosure

/-- The new right synchronized endpoint lies in the same small closed cell. -/
theorem rightSynchronizedPoint_mem_cellClosedBall
    (b : LevelAddress S.level) :
    S.family.forgetObstacle.rightSynchronizedPoint b ∈
      closedBall (J.curvePoint (I.levelArc b).left : Plane)
        (S.buffer / 4) := by
  let G := S.family.forgetObstacle
  have hcarrier : G.rightSynchronizedPoint b ∈
      (G.exactSynchronizedAuxiliaryJordanCircle b).carrier :=
    G.range_synchronizedCrosscutPath_subset_exactAuxiliaryCarrier b
      (Path.target_mem_range (G.synchronizedCrosscutPath b))
  have hclosure : G.rightSynchronizedPoint b ∈
      closure (G.exactSynchronizedAuxiliaryJordanCircle b).inside := by
    rw [(G.exactSynchronizedAuxiliaryJordanCircle b).closure_inside]
    exact Or.inr hcarrier
  exact S.cell_near b hclosure

/-- The right boundary endpoint of a new arc lies in its small closed cell. -/
theorem rightBoundaryPoint_mem_cellClosedBall
    (b : LevelAddress S.level) :
    (J.curvePoint (I.levelArc b).right : Plane) ∈
      closedBall (J.curvePoint (I.levelArc b).left : Plane)
        (S.buffer / 4) := by
  let G := S.family.forgetObstacle
  have hcarrier : (J.curvePoint (I.levelArc b).right : Plane) ∈
      (G.exactSynchronizedAuxiliaryJordanCircle b).carrier := by
    rw [G.carrier_exactSynchronizedAuxiliaryJordanCircle b]
    exact Or.inl (I.levelArc b).right_mem_curveArcPlane
  have hclosure : (J.curvePoint (I.levelArc b).right : Plane) ∈
      closure (G.exactSynchronizedAuxiliaryJordanCircle b).inside := by
    rw [(G.exactSynchronizedAuxiliaryJordanCircle b).closure_inside]
    exact Or.inr hcarrier
  exact S.cell_near b hclosure

/-- A new left synchronized endpoint is within one quarter-buffer of its
boundary base. -/
theorem dist_leftBoundary_leftSynchronizedPoint_le
    (b : LevelAddress S.level) :
    dist (J.curvePoint (I.levelArc b).left : Plane)
        (S.family.forgetObstacle.leftSynchronizedPoint b) ≤
      S.buffer / 4 := by
  simpa [mem_closedBall, dist_comm] using
    S.leftSynchronizedPoint_mem_cellClosedBall b

/-- A new right synchronized endpoint is within one half-buffer of its
boundary base.  Both points lie in the same quarter-buffer cell. -/
theorem dist_rightBoundary_rightSynchronizedPoint_le
    (b : LevelAddress S.level) :
    dist (J.curvePoint (I.levelArc b).right : Plane)
        (S.family.forgetObstacle.rightSynchronizedPoint b) ≤
      S.buffer / 2 := by
  have hbase := S.rightBoundaryPoint_mem_cellClosedBall b
  have hsync := S.rightSynchronizedPoint_mem_cellClosedBall b
  rw [mem_closedBall] at hbase hsync
  calc
    dist (J.curvePoint (I.levelArc b).right : Plane)
        (S.family.forgetObstacle.rightSynchronizedPoint b) ≤
        dist (J.curvePoint (I.levelArc b).right : Plane)
            (J.curvePoint (I.levelArc b).left : Plane) +
          dist (J.curvePoint (I.levelArc b).left : Plane)
            (S.family.forgetObstacle.rightSynchronizedPoint b) :=
      dist_triangle _ _ _
    _ ≤ S.buffer / 4 + S.buffer / 4 := by
      exact add_le_add hbase (by simpa [dist_comm] using hsync)
    _ = S.buffer / 2 := by ring

/-- A recursive next collar can always be chosen at a strictly later binary
subdivision depth than the current synchronized collar. -/
theorem exists_later
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n) :
    ∃ T : I.RecursiveInsideCollarStep
        (F.synchronizedPolygonalCircle hn),
      n < T.level := by
  obtain ⟨T, hT⟩ := I.exists_recursiveInsideCollarStep_atLeast
    (F.synchronizedPolygonalCircle hn)
    (F.closedRegion_synchronizedPolygonalCircle_subset_inside hn) (n + 1)
  exact ⟨T, by omega⟩

/-- A later synchronized collar can simultaneously be forced to use an
arbitrarily small positive separation buffer.  This is the quantitative
version used to make the recursive collar cells shrink at the Jordan
boundary. -/
theorem exists_later_with_buffer_le
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    {upper : ℝ} (hupper : 0 < upper) :
    ∃ T : I.RecursiveInsideCollarStep
        (F.synchronizedPolygonalCircle hn),
      n < T.level ∧ T.buffer ≤ upper := by
  obtain ⟨T, hT, hbuffer⟩ :=
    I.exists_recursiveInsideCollarStep_atLeast_with_buffer_le
      (F.synchronizedPolygonalCircle hn)
      (F.closedRegion_synchronizedPolygonalCircle_subset_inside hn)
      (n + 1) hupper
  exact ⟨T, by omega, hbuffer⟩

/-- A synchronized point on the earlier collar is at least one full buffer
away from its left boundary base. -/
theorem buffer_le_dist_parent_leftSynchronizedPoint
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn)) (a : LevelAddress n) :
    T.buffer ≤
      dist (J.curvePoint (I.levelArc a).left : Plane)
        (F.leftSynchronizedPoint a) := by
  rw [dist_comm]
  apply T.buffer_le_dist_of_mem_closedRegion_of_mem_carrier
  · rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
    apply Or.inr
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr
      ⟨a, Path.source_mem_range (F.synchronizedCrosscutPath a)⟩
  · exact (J.curvePoint (I.levelArc a).left).2

/-- The analogous full-buffer separation at the right endpoint. -/
theorem buffer_le_dist_parent_rightSynchronizedPoint
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn)) (a : LevelAddress n) :
    T.buffer ≤
      dist (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a) := by
  rw [dist_comm]
  apply T.buffer_le_dist_of_mem_closedRegion_of_mem_carrier
  · rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
    apply Or.inr
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr
      ⟨a, Path.target_mem_range (F.synchronizedCrosscutPath a)⟩
  · exact (J.curvePoint (I.levelArc a).right).2

/-- If a new arc has the same left boundary base as an old arc, its
synchronized endpoint is strictly shallower on that retained hair. -/
theorem dist_child_left_lt_parent_left
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).left : Plane) =
        (J.curvePoint (I.levelArc a).left : Plane)) :
    dist (J.curvePoint (I.levelArc a).left : Plane)
        (T.family.forgetObstacle.leftSynchronizedPoint b) <
      dist (J.curvePoint (I.levelArc a).left : Plane)
        (F.leftSynchronizedPoint a) := by
  have hchild := T.dist_leftBoundary_leftSynchronizedPoint_le b
  rw [hbase] at hchild
  have hparent := T.buffer_le_dist_parent_leftSynchronizedPoint F hn a
  nlinarith [T.buffer_pos]

/-- The corresponding strict shallowness at the right retained hair. -/
theorem dist_child_right_lt_parent_right
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).right : Plane) =
        (J.curvePoint (I.levelArc a).right : Plane)) :
    dist (J.curvePoint (I.levelArc a).right : Plane)
        (T.family.forgetObstacle.rightSynchronizedPoint b) <
      dist (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a) := by
  have hchild := T.dist_rightBoundary_rightSynchronizedPoint_le b
  rw [hbase] at hchild
  have hparent := T.buffer_le_dist_parent_rightSynchronizedPoint F hn a
  nlinarith [T.buffer_pos]

/-- The original trimmed left endpoint used in an individual Moise band
cell is also strictly shallower than the parent collar endpoint.  The
synchronized endpoint is not used here: its extension can overlap the
retained side hair. -/
theorem dist_child_trimmedLeft_lt_parent_left
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).left : Plane) =
        (J.curvePoint (I.levelArc a).left : Plane)) :
    dist (J.curvePoint (I.levelArc a).left : Plane)
        (T.family.forgetObstacle.trimmedLeftPoint
          (levelIndexOf T.level b)) <
      dist (J.curvePoint (I.levelArc a).left : Plane)
        (F.leftSynchronizedPoint a) := by
  let G := T.family.forgetObstacle
  have htrimReturn : G.trimmedLeftPoint (levelIndexOf T.level b) ∈
      G.synchronizedReturnSet b := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    exact Or.inr (Path.target_mem_range
      (G.trimmedPath (levelIndexOf T.level b)))
  have htrim := T.return_near b htrimReturn
  rw [mem_ball, hbase] at htrim
  have htrim' : dist (J.curvePoint (I.levelArc a).left : Plane)
      (G.trimmedLeftPoint (levelIndexOf T.level b)) < T.buffer / 4 := by
    simpa [dist_comm] using htrim
  have hparent := T.buffer_le_dist_parent_leftSynchronizedPoint F hn a
  nlinarith [T.buffer_pos, htrim']

/-- The original trimmed right endpoint used in an individual Moise band
cell is strictly shallower than the corresponding parent endpoint. -/
theorem dist_child_trimmedRight_lt_parent_right
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).right : Plane) =
        (J.curvePoint (I.levelArc a).right : Plane)) :
    dist (J.curvePoint (I.levelArc a).right : Plane)
        (T.family.forgetObstacle.trimmedRightPoint
          (levelIndexOf T.level b)) <
      dist (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a) := by
  let G := T.family.forgetObstacle
  have htrimReturn : G.trimmedRightPoint (levelIndexOf T.level b) ∈
      G.synchronizedReturnSet b := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    exact Or.inr (Path.source_mem_range
      (G.trimmedPath (levelIndexOf T.level b)))
  have htrim := T.return_near b htrimReturn
  rw [mem_ball] at htrim
  have hboundary := T.rightBoundaryPoint_mem_cellClosedBall b
  rw [mem_closedBall] at hboundary
  have hboundary' : dist
      (J.curvePoint (I.levelArc b).left : Plane)
      (J.curvePoint (I.levelArc b).right : Plane) ≤ T.buffer / 4 := by
    simpa [dist_comm] using hboundary
  have hchild : dist
      (G.trimmedRightPoint (levelIndexOf T.level b))
      (J.curvePoint (I.levelArc b).right : Plane) < T.buffer / 2 := by
    calc
      dist (G.trimmedRightPoint (levelIndexOf T.level b))
          (J.curvePoint (I.levelArc b).right : Plane) ≤
          dist (G.trimmedRightPoint (levelIndexOf T.level b))
              (J.curvePoint (I.levelArc b).left : Plane) +
            dist (J.curvePoint (I.levelArc b).left : Plane)
              (J.curvePoint (I.levelArc b).right : Plane) :=
        dist_triangle _ _ _
      _ < T.buffer / 2 := by nlinarith [T.buffer_pos, hboundary']
  rw [hbase] at hchild
  have hchild' : dist (J.curvePoint (I.levelArc a).right : Plane)
      (G.trimmedRightPoint (levelIndexOf T.level b)) < T.buffer / 2 := by
    simpa [dist_comm] using hchild
  have hparent := T.buffer_le_dist_parent_rightSynchronizedPoint F hn a
  nlinarith [T.buffer_pos, hchild']

/-- Metric shallowness becomes strict affine order on the common retained
left hair. -/
theorem child_left_carrierParameter_lt_parent
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).left : Plane) =
        (J.curvePoint (I.levelArc a).left : Plane))
    (hhair : (I.levelLeftHair b).carrier =
      (I.levelLeftHair a).carrier) :
    let child : (I.levelLeftHair a).carrier :=
      ⟨T.family.forgetObstacle.leftSynchronizedPoint b, by
        rw [← hhair]
        exact T.family.forgetObstacle.leftSynchronizedPoint_mem_leftHair b⟩
    let parent : (I.levelLeftHair a).carrier :=
      ⟨F.leftSynchronizedPoint a,
        F.leftSynchronizedPoint_mem_leftHair a⟩
    (I.levelLeftHair a).carrierParameter child <
      (I.levelLeftHair a).carrierParameter parent := by
  dsimp only
  apply (I.levelLeftHair a).carrierParameter_lt_of_dist_base_lt
  exact T.dist_child_left_lt_parent_left F hn a b hbase

/-- Metric shallowness becomes strict affine order on the common retained
right hair. -/
theorem child_right_carrierParameter_lt_parent
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    (T : I.RecursiveInsideCollarStep
      (F.synchronizedPolygonalCircle hn))
    (a : LevelAddress n) (b : LevelAddress T.level)
    (hbase :
      (J.curvePoint (I.levelArc b).right : Plane) =
        (J.curvePoint (I.levelArc a).right : Plane))
    (hhair : (I.levelRightHair b).carrier =
      (I.levelRightHair a).carrier) :
    let child : (I.levelRightHair a).carrier :=
      ⟨T.family.forgetObstacle.rightSynchronizedPoint b, by
        rw [← hhair]
        exact T.family.forgetObstacle.rightSynchronizedPoint_mem_rightHair b⟩
    let parent : (I.levelRightHair a).carrier :=
      ⟨F.rightSynchronizedPoint a,
        F.rightSynchronizedPoint_mem_rightHair a⟩
    (I.levelRightHair a).carrierParameter child <
      (I.levelRightHair a).carrierParameter parent := by
  dsimp only
  apply (I.levelRightHair a).carrierParameter_lt_of_dist_base_lt
  exact T.dist_child_right_lt_parent_right F hn a b hbase

/-- A recursive collar step together with the fact that its subdivision
level is strictly later than the parent synchronized level. -/
structure Later
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n) where
  next : I.RecursiveInsideCollarStep
    (F.synchronizedPolygonalCircle hn)
  later : n < next.level

theorem nonempty_later
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n) :
    Nonempty (Later F hn) := by
  obtain ⟨T, hT⟩ := exists_later F hn
  exact ⟨⟨T, hT⟩⟩

/-- Quantitative inhabitance of `Later`: the stored next collar can be
chosen with buffer at most `upper`. -/
theorem exists_later_buffer_le
    {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon) (hn : 1 ≤ n)
    {upper : ℝ} (hupper : 0 < upper) :
    ∃ L : Later F hn, L.next.buffer ≤ upper := by
  obtain ⟨T, hlater, hbuffer⟩ := exists_later_with_buffer_le F hn hupper
  exact ⟨⟨T, hlater⟩, hbuffer⟩

namespace Later

variable {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : Later F hn)

/-- The number of binary refinement generations skipped by this step. -/
def depth : ℕ := L.next.level - n

theorem parentLevel_add_depth : n + L.depth = L.next.level := by
  exact Nat.add_sub_of_le L.later.le

/-- The extreme left descendant, transported to the selected later level. -/
noncomputable def leftmostAddress (a : LevelAddress n) :
    LevelAddress L.next.level :=
  _root_.cast (congrArg LevelAddress L.parentLevel_add_depth)
    (leftmostDescendant a L.depth)

/-- The extreme right descendant, transported to the selected later level. -/
noncomputable def rightmostAddress (a : LevelAddress n) :
    LevelAddress L.next.level :=
  _root_.cast (congrArg LevelAddress L.parentLevel_add_depth)
    (rightmostDescendant a L.depth)

@[simp] theorem levelArc_leftmostAddress_left
    (a : LevelAddress n) :
    (I.levelArc (L.leftmostAddress a)).left =
      (I.levelArc a).left := by
  unfold leftmostAddress
  rw [I.levelArc_cast L.parentLevel_add_depth]
  exact I.levelArc_leftmostDescendant_left a L.depth

@[simp] theorem levelArc_rightmostAddress_right
    (a : LevelAddress n) :
    (I.levelArc (L.rightmostAddress a)).right =
      (I.levelArc a).right := by
  unfold rightmostAddress
  rw [I.levelArc_cast L.parentLevel_add_depth]
  exact I.levelArc_rightmostDescendant_right a L.depth

@[simp] theorem leftmostAddress_leftHair_carrier
    (a : LevelAddress n) :
    (I.levelLeftHair (L.leftmostAddress a)).carrier =
      (I.levelLeftHair a).carrier := by
  unfold leftmostAddress
  rw [I.levelLeftHair_cast_carrier L.parentLevel_add_depth]
  exact I.levelLeftHair_leftmostDescendant_carrier a L.depth

@[simp] theorem rightmostAddress_rightHair_carrier
    (a : LevelAddress n) :
    (I.levelRightHair (L.rightmostAddress a)).carrier =
      (I.levelRightHair a).carrier := by
  unfold rightmostAddress
  rw [I.levelRightHair_cast_carrier L.parentLevel_add_depth]
  exact I.levelRightHair_rightmostDescendant_carrier a L.depth

/-- The left endpoint of the selected deeper descendant is strictly before
the parent synchronized point in the common retained-hair order. -/
theorem leftmost_carrierParameter_lt_parent (a : LevelAddress n) :
    let child : (I.levelLeftHair a).carrier :=
      ⟨L.next.family.forgetObstacle.leftSynchronizedPoint
          (L.leftmostAddress a), by
        rw [← L.leftmostAddress_leftHair_carrier a]
        exact L.next.family.forgetObstacle.leftSynchronizedPoint_mem_leftHair _⟩
    let parent : (I.levelLeftHair a).carrier :=
      ⟨F.leftSynchronizedPoint a,
        F.leftSynchronizedPoint_mem_leftHair a⟩
    (I.levelLeftHair a).carrierParameter child <
      (I.levelLeftHair a).carrierParameter parent := by
  exact L.next.child_left_carrierParameter_lt_parent F hn a
    (L.leftmostAddress a)
    (by simp [L.levelArc_leftmostAddress_left a])
    (L.leftmostAddress_leftHair_carrier a)

/-- The right endpoint of the selected deeper descendant is strictly before
the parent synchronized point in the common retained-hair order. -/
theorem rightmost_carrierParameter_lt_parent (a : LevelAddress n) :
    let child : (I.levelRightHair a).carrier :=
      ⟨L.next.family.forgetObstacle.rightSynchronizedPoint
          (L.rightmostAddress a), by
        rw [← L.rightmostAddress_rightHair_carrier a]
        exact L.next.family.forgetObstacle.rightSynchronizedPoint_mem_rightHair _⟩
    let parent : (I.levelRightHair a).carrier :=
      ⟨F.rightSynchronizedPoint a,
        F.rightSynchronizedPoint_mem_rightHair a⟩
    (I.levelRightHair a).carrierParameter child <
      (I.levelRightHair a).carrierParameter parent := by
  exact L.next.child_right_carrierParameter_lt_parent F hn a
    (L.rightmostAddress a)
    (by simp [L.levelArc_rightmostAddress_right a])
    (L.rightmostAddress_rightHair_carrier a)

/-- The raw trimmed endpoint of the extreme left descendant precedes the
parent synchronized endpoint on their common retained hair. -/
theorem leftmost_trimmed_carrierParameter_lt_parent
    (a : LevelAddress n) :
    let child : (I.levelLeftHair a).carrier :=
      ⟨L.next.family.forgetObstacle.trimmedLeftPoint
          (levelIndexOf L.next.level (L.leftmostAddress a)), by
        rw [← L.leftmostAddress_leftHair_carrier a]
        exact (L.next.family.forgetObstacle.leftHairPoint
          (L.leftmostAddress a)).2⟩
    let parent : (I.levelLeftHair a).carrier :=
      ⟨F.leftSynchronizedPoint a,
        F.leftSynchronizedPoint_mem_leftHair a⟩
    (I.levelLeftHair a).carrierParameter child <
      (I.levelLeftHair a).carrierParameter parent := by
  dsimp only
  apply (I.levelLeftHair a).carrierParameter_lt_of_dist_base_lt
  exact L.next.dist_child_trimmedLeft_lt_parent_left F hn a
    (L.leftmostAddress a)
    (by simp [L.levelArc_leftmostAddress_left a])

/-- The raw trimmed endpoint of the extreme right descendant precedes the
parent synchronized endpoint on their common retained hair. -/
theorem rightmost_trimmed_carrierParameter_lt_parent
    (a : LevelAddress n) :
    let child : (I.levelRightHair a).carrier :=
      ⟨L.next.family.forgetObstacle.trimmedRightPoint
          (levelIndexOf L.next.level (L.rightmostAddress a)), by
        rw [← L.rightmostAddress_rightHair_carrier a]
        exact (L.next.family.forgetObstacle.rightHairPoint
          (L.rightmostAddress a)).2⟩
    let parent : (I.levelRightHair a).carrier :=
      ⟨F.rightSynchronizedPoint a,
        F.rightSynchronizedPoint_mem_rightHair a⟩
    (I.levelRightHair a).carrierParameter child <
      (I.levelRightHair a).carrierParameter parent := by
  dsimp only
  apply (I.levelRightHair a).carrierParameter_lt_of_dist_base_lt
  exact L.next.dist_child_trimmedRight_lt_parent_right F hn a
    (L.rightmostAddress a)
    (by simp [L.levelArc_rightmostAddress_right a])

end Later

end RecursiveInsideCollarStep
end InitialAngularArcs
end JordanCircle

end Schoenflies
