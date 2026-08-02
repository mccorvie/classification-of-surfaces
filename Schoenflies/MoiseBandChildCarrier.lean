import Schoenflies.ExactSynchronizedCrosscutRanges
import Schoenflies.MoiseBandCellSeams

/-!
# The retained child boundary of a recursive Moise band

The non-retracing Moise cells use raw trimmed child crosscuts and direct
segments between consecutive raw endpoints.  Exactness of the synchronized
crosscut ranges shows that all of these retained pieces lie on the next
polygonal collar.  Thus, after the parent and side seams are cancelled, the
only possible boundary of the filled band is the child collar itself.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private noncomputable abbrev childIndex
    (b : LevelAddress L.next.level) :
    Fin (levelAddressCount L.next.level) :=
  levelIndexOf L.next.level b

private abbrev childDisk : PolygonalCircle :=
  L.next.family.forgetObstacle.synchronizedPolygonalCircle
    L.next.one_le_level

/-- Every raw child edge used by a Moise cell lies on the synchronized child
polygon.  The essential input is that synchronization did not loop-erase any
part of the original three-piece crosscut. -/
theorem childSegment_subset_childCarrier
    (a : LevelAddress n)
    (e : L.next.family.forgetObstacle.TrimmedEdgeAddress) :
    segment ℝ
        (MoiseBandSegmentAddress.left L a
          (MoiseBandSegmentAddress.child L e))
        (MoiseBandSegmentAddress.right L a
          (MoiseBandSegmentAddress.child L e)) ⊆
      L.childDisk.carrier := by
  let G := L.next.family.forgetObstacle
  intro x hx
  have hxEdge : x ∈ G.trimmedEdgeSegment e := by
    change x ∈ segment ℝ (G.trimmedEdgeFinish e)
      (G.trimmedEdgeStart e) at hx
    simpa only [LevelAvoidingJoinFamily.trimmedEdgeSegment, segment_symm]
      using hx
  have hxTrim : x ∈ range (G.trimmedPath (L.childIndex e.1)) :=
    G.trimmedEdgeSegment_subset_trimmedPathRange e hxEdge
  have hxSet : x ∈ G.synchronizedCrosscutSet e.1 :=
    Or.inl (Or.inr hxTrim)
  rw [← G.range_synchronizedCrosscutPath_eq_set e.1] at hxSet
  rw [G.carrier_synchronizedPolygonalCircle L.next.one_le_level]
  exact Set.mem_iUnion.mpr ⟨e.1, hxSet⟩

/-- The direct retained-hair junction between consecutive raw child
crosscuts lies on one of their two synchronized extensions, hence on the
child polygon. -/
theorem childJunction_subset_childCarrier
    (a : LevelAddress n) {b c : LevelAddress L.next.level}
    (hbc : I.LevelAdjacent b c) :
    segment ℝ
        (MoiseBandSegmentAddress.left L a
          (MoiseBandSegmentAddress.junction L b c))
        (MoiseBandSegmentAddress.right L a
          (MoiseBandSegmentAddress.junction L b c)) ⊆
      L.childDisk.carrier := by
  let G := L.next.family.forgetObstacle
  have hc : c = nextLevelAddress L.next.level b :=
    (I.levelRightPoint_eq_levelLeftPoint_iff b c).mp hbc
  subst c
  have hsync : G.rightSynchronizedPoint b =
        G.trimmedRightPoint (L.childIndex b) ∨
      G.rightSynchronizedPoint b =
        G.trimmedLeftPoint
          (L.childIndex (nextLevelAddress L.next.level b)) := by
    simpa [LevelAvoidingJoinFamily.rightSynchronizedPoint] using
      G.synchronizedPoint_eq_right_or_left b
        (nextLevelAddress L.next.level b) hbc
  intro x hx
  change x ∈ segment ℝ (G.trimmedRightPoint (L.childIndex b))
    (G.trimmedLeftPoint
      (L.childIndex (nextLevelAddress L.next.level b))) at hx
  rcases hsync with hright | hleft
  · have hxLeft : x ∈ segment ℝ
        (G.leftSynchronizedPoint (nextLevelAddress L.next.level b))
        (G.trimmedLeftPoint
          (L.childIndex (nextLevelAddress L.next.level b))) := by
      rw [← G.rightSynchronizedPoint_next_eq_leftSynchronizedPoint b,
        hright]
      exact hx
    have hxSet : x ∈
        G.synchronizedCrosscutSet (nextLevelAddress L.next.level b) :=
      Or.inl (Or.inl hxLeft)
    rw [← G.range_synchronizedCrosscutPath_eq_set
      (nextLevelAddress L.next.level b)] at hxSet
    rw [G.carrier_synchronizedPolygonalCircle L.next.one_le_level]
    exact Set.mem_iUnion.mpr
      ⟨nextLevelAddress L.next.level b, hxSet⟩
  · have hxRight : x ∈ segment ℝ
        (G.trimmedRightPoint (L.childIndex b))
        (G.rightSynchronizedPoint b) := by
      rw [hleft]
      exact hx
    have hxSet : x ∈ G.synchronizedCrosscutSet b := Or.inr hxRight
    rw [← G.range_synchronizedCrosscutPath_eq_set b] at hxSet
    rw [G.carrier_synchronizedPolygonalCircle L.next.one_le_level]
    exact Set.mem_iUnion.mpr ⟨b, hxSet⟩

/-- The whole non-retracing finer-level route in one Moise cell belongs to
the synchronized child polygon. -/
theorem childMoiseCarrier_subset_childCarrier
    (a : LevelAddress n) :
    L.childMoiseCarrier a ⊆ L.childDisk.carrier := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  rcases Set.mem_iUnion.mp hxj with ⟨hj, hxSegment⟩
  rcases L.child_or_junction_of_mem_childMoiseSegments
      (L.addresses_isChain a) hj with hchild | hjunction
  · obtain ⟨e, rfl⟩ := hchild
    exact L.childSegment_subset_childCarrier a e hxSegment
  · obtain ⟨b, c, hbc, rfl⟩ := hjunction
    exact L.childJunction_subset_childCarrier a hbc hxSegment

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
