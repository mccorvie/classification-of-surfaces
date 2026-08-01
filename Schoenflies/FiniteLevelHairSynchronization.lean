import Schoenflies.FiniteLevelCrosscuts
import Schoenflies.LevelHairSynchronization

/-!
# Synchronizing a pairwise-disjoint finite level on shared hairs

Two neighboring trimmed crosscuts generally stop at different points of
their common retained access hair.  Extend each toward the shallower of the
two points.  One extension is degenerate, and the two extended crosscuts
then meet exactly at the synchronized point.
-/

namespace Schoenflies

open Metric Set Function

namespace JordanCircle
namespace InitialAngularArcs
namespace LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

private noncomputable abbrev index (a : LevelAddress n) :
    Fin (levelAddressCount n) :=
  levelIndexOf n a

/-- The trimmed right endpoint, as a point of the retained right hair. -/
noncomputable def rightHairPoint (a : LevelAddress n) :
    (I.levelRightHair a).carrier :=
  ⟨F.trimmedRightPoint (index a), by
    have h := (F.hairTrimData (index a)).right_mem
    have haddr : levelAddressAt n (index a) = a :=
      levelAddressAt_levelIndexOf n a
    have hcarrier :
        (I.levelRightHair (levelAddressAt n (index a))).carrier =
          (I.levelRightHair a).carrier :=
      congrArg (fun c => (I.levelRightHair c).carrier) haddr
    exact hcarrier ▸ h⟩

/-- The trimmed left endpoint, as a point of the retained left hair. -/
noncomputable def leftHairPoint (a : LevelAddress n) :
    (I.levelLeftHair a).carrier :=
  ⟨F.trimmedLeftPoint (index a), by
    have h := (F.hairTrimData (index a)).left_mem
    have haddr : levelAddressAt n (index a) = a :=
      levelAddressAt_levelIndexOf n a
    have hcarrier :
        (I.levelLeftHair (levelAddressAt n (index a))).carrier =
          (I.levelLeftHair a).carrier :=
      congrArg (fun c => (I.levelLeftHair c).carrier) haddr
    exact hcarrier ▸ h⟩

theorem trimmedRightPoint_inside (a : LevelAddress n) :
    F.trimmedRightPoint (index a) ∈ J.inside :=
  (F.range_trimmedPath_subset_controlled (index a)
    (Path.source_mem_range (F.trimmedPath (index a)))).1

theorem trimmedLeftPoint_inside (a : LevelAddress n) :
    F.trimmedLeftPoint (index a) ∈ J.inside :=
  (F.range_trimmedPath_subset_controlled (index a)
    (Path.target_mem_range (F.trimmedPath (index a)))).1

/-- Transport the left endpoint of the following arc onto the preceding
arc's right hair. -/
noncomputable def sharedLeftHairPoint (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    (I.levelRightHair a).carrier :=
  ⟨F.trimmedLeftPoint (index b), by
    rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq a b hshared]
    exact (F.leftHairPoint b).2⟩

/-- The common endpoint obtained by retaining the shallower of the two
points on a shared hair. -/
noncomputable def synchronizedPoint (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) : Plane :=
  ((I.levelRightHair a).shallowerPoint (F.rightHairPoint a)
    (F.sharedLeftHairPoint a b hshared) :
      (I.levelRightHair a).carrier)

theorem synchronizedPoint_eq_right_or_left (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    F.synchronizedPoint a b hshared = F.trimmedRightPoint (index a) ∨
      F.synchronizedPoint a b hshared = F.trimmedLeftPoint (index b) := by
  have h := (I.levelRightHair a).shallowerPoint_eq_left_or_right
    (F.rightHairPoint a) (F.sharedLeftHairPoint a b hshared)
  exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)

theorem synchronizedPoint_mem_rightHair (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    F.synchronizedPoint a b hshared ∈ (I.levelRightHair a).carrier :=
  ((I.levelRightHair a).shallowerPoint (F.rightHairPoint a)
    (F.sharedLeftHairPoint a b hshared)).2

theorem synchronizedPoint_mem_leftHair (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    F.synchronizedPoint a b hshared ∈ (I.levelLeftHair b).carrier := by
  rw [← I.levelRightHair_carrier_eq_levelLeftHair_of_eq a b hshared]
  exact F.synchronizedPoint_mem_rightHair a b hshared

theorem synchronizedPoint_inside (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    F.synchronizedPoint a b hshared ∈ J.inside := by
  rcases F.synchronizedPoint_eq_right_or_left a b hshared with h | h
  · simpa [h] using F.trimmedRightPoint_inside a
  · simpa [h] using F.trimmedLeftPoint_inside b

theorem synchronizedPoint_parameter_le_right (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    (I.levelRightHair a).carrierParameter
        ⟨F.synchronizedPoint a b hshared,
          F.synchronizedPoint_mem_rightHair a b hshared⟩ ≤
      (I.levelRightHair a).carrierParameter (F.rightHairPoint a) :=
  (I.levelRightHair a).shallowerPoint_parameter_le_left
    (F.rightHairPoint a) (F.sharedLeftHairPoint a b hshared)

theorem synchronizedPoint_parameter_le_left (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    (I.levelRightHair a).carrierParameter
        ⟨F.synchronizedPoint a b hshared,
          F.synchronizedPoint_mem_rightHair a b hshared⟩ ≤
      (I.levelRightHair a).carrierParameter
        (F.sharedLeftHairPoint a b hshared) :=
  (I.levelRightHair a).shallowerPoint_parameter_le_right
    (F.rightHairPoint a) (F.sharedLeftHairPoint a b hshared)

/-- The two synchronization extensions overlap only at their new common
endpoint. -/
theorem synchronizedExtensions_inter (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    segment ℝ (F.synchronizedPoint a b hshared)
          (F.trimmedRightPoint (index a)) ∩
        segment ℝ (F.trimmedLeftPoint (index b))
          (F.synchronizedPoint a b hshared) =
      {F.synchronizedPoint a b hshared} := by
  rcases F.synchronizedPoint_eq_right_or_left a b hshared with h | h
  · rw [h]
    simp
    exact right_mem_segment ℝ _ _
  · rw [h]
    simp
    exact left_mem_segment ℝ _ _

theorem rightExtension_subset_inside (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    segment ℝ (F.synchronizedPoint a b hshared)
        (F.trimmedRightPoint (index a)) ⊆ J.inside :=
  (I.levelRightHair a).segment_subset_inside_of_parameter_le
    (J.curvePoint (I.levelArc a).right).2
    ⟨F.synchronizedPoint a b hshared,
      F.synchronizedPoint_mem_rightHair a b hshared⟩
    (F.rightHairPoint a) (F.synchronizedPoint_inside a b hshared)
    (F.synchronizedPoint_parameter_le_right a b hshared)

theorem leftExtension_subset_inside (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    segment ℝ (F.trimmedLeftPoint (index b))
        (F.synchronizedPoint a b hshared) ⊆ J.inside := by
  rw [segment_symm]
  exact (I.levelRightHair a).segment_subset_inside_of_parameter_le
    (J.curvePoint (I.levelArc a).right).2
    ⟨F.synchronizedPoint a b hshared,
      F.synchronizedPoint_mem_rightHair a b hshared⟩
    (F.sharedLeftHairPoint a b hshared)
    (F.synchronizedPoint_inside a b hshared)
    (F.synchronizedPoint_parameter_le_left a b hshared)

/-- The range of the preceding crosscut after extending its source endpoint
outward on the shared right hair. -/
noncomputable def synchronizedRightRange (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) : Set Plane :=
  segment ℝ (F.synchronizedPoint a b hshared)
      (F.trimmedRightPoint (index a)) ∪
    range (F.trimmedPath (index a))

/-- The range of the following crosscut after extending its target endpoint
outward on the shared left hair. -/
noncomputable def synchronizedLeftRange (a b : LevelAddress n)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) : Set Plane :=
  range (F.trimmedPath (index b)) ∪
    segment ℝ (F.trimmedLeftPoint (index b))
      (F.synchronizedPoint a b hshared)

/-- For distinct neighboring arcs, synchronization changes disjoint ranges
into ranges meeting at exactly their new common endpoint. -/
theorem synchronizedRanges_inter (a b : LevelAddress n) (hab : a ≠ b)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane)) :
    F.synchronizedRightRange a b hshared ∩
        F.synchronizedLeftRange a b hshared =
      {F.synchronizedPoint a b hshared} := by
  apply Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    rcases hxA with hxExtA | hxPathA
    · rcases hxB with hxPathB | hxExtB
      · have hxRightHair : x ∈ (I.levelRightHair a).carrier :=
          (convex_segment
            (J.curvePoint (I.levelArc a).right : Plane)
            (I.levelRightHair a).tip).segment_subset
              (F.synchronizedPoint_mem_rightHair a b hshared)
              (F.rightHairPoint a).2 hxExtA
        have hxLeftHair : x ∈ (I.levelLeftHair b).carrier := by
          rw [← I.levelRightHair_carrier_eq_levelLeftHair_of_eq a b hshared]
          exact hxRightHair
        have hxLeft : x = F.trimmedLeftPoint (index b) := by
          have haddr : levelAddressAt n (index b) = b :=
            levelAddressAt_levelIndexOf n b
          have hxInter : x ∈ range (F.trimmedPath (index b)) ∩
              (I.levelLeftHair (levelAddressAt n (index b))).carrier := by
            rw [haddr]
            exact ⟨hxPathB, hxLeftHair⟩
          have hxSingleton := congrArg (fun S : Set Plane => x ∈ S)
            (F.range_trimmedPath_inter_leftHair (index b)) |>.mp hxInter
          exact mem_singleton_iff.mp hxSingleton
        have hxExtB' : x ∈ segment ℝ (F.trimmedLeftPoint (index b))
            (F.synchronizedPoint a b hshared) := by
          rw [hxLeft]
          exact left_mem_segment ℝ _ _
        have hxInter : x ∈
            segment ℝ (F.synchronizedPoint a b hshared)
                (F.trimmedRightPoint (index a)) ∩
              segment ℝ (F.trimmedLeftPoint (index b))
                (F.synchronizedPoint a b hshared) :=
          ⟨hxExtA, hxExtB'⟩
        rw [F.synchronizedExtensions_inter a b hshared] at hxInter
        exact hxInter
      · have hxInter : x ∈
            segment ℝ (F.synchronizedPoint a b hshared)
                (F.trimmedRightPoint (index a)) ∩
              segment ℝ (F.trimmedLeftPoint (index b))
                (F.synchronizedPoint a b hshared) :=
          ⟨hxExtA, hxExtB⟩
        rw [F.synchronizedExtensions_inter a b hshared] at hxInter
        exact hxInter
    · rcases hxB with hxPathB | hxExtB
      · exact False.elim <| Set.disjoint_left.mp
          (F.pairwise_disjoint_trimmedPath
            (fun hindex => hab (levelIndexOf_injective n hindex)))
          hxPathA hxPathB
      · have hxRightHair : x ∈ (I.levelRightHair a).carrier :=
          (convex_segment
            (J.curvePoint (I.levelArc a).right : Plane)
            (I.levelRightHair a).tip).segment_subset
              (F.sharedLeftHairPoint a b hshared).2
              (F.synchronizedPoint_mem_rightHair a b hshared)
              hxExtB
        have hxRight : x = F.trimmedRightPoint (index a) := by
          have haddr : levelAddressAt n (index a) = a :=
            levelAddressAt_levelIndexOf n a
          have hxInter : x ∈ range (F.trimmedPath (index a)) ∩
              (I.levelRightHair (levelAddressAt n (index a))).carrier := by
            rw [haddr]
            exact ⟨hxPathA, hxRightHair⟩
          have hxSingleton := congrArg (fun S : Set Plane => x ∈ S)
            (F.range_trimmedPath_inter_rightHair (index a)) |>.mp hxInter
          exact mem_singleton_iff.mp hxSingleton
        have hxExtA' : x ∈ segment ℝ (F.synchronizedPoint a b hshared)
            (F.trimmedRightPoint (index a)) := by
          rw [hxRight]
          exact right_mem_segment ℝ _ _
        have hxInter : x ∈
            segment ℝ (F.synchronizedPoint a b hshared)
                (F.trimmedRightPoint (index a)) ∩
              segment ℝ (F.trimmedLeftPoint (index b))
                (F.synchronizedPoint a b hshared) :=
          ⟨hxExtA', hxExtB⟩
        rw [F.synchronizedExtensions_inter a b hshared] at hxInter
        exact hxInter
  · intro x hx
    have hx : x = F.synchronizedPoint a b hshared :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨Or.inl (left_mem_segment ℝ _ _),
      Or.inr (right_mem_segment ℝ _ _)⟩

/-- A crosscut is disjoint from a retained right hair based at neither of
its own endpoints. -/
theorem trimmedPath_disjoint_levelRightHair_of_nonincident
    (a c : LevelAddress n)
    (hLeft :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).left : Plane))
    (hRight :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).right : Plane)) :
    Disjoint (range (F.trimmedPath (index c)))
      (I.levelRightHair a).carrier := by
  have hAvoid := F.range_trimmedPath_disjoint_nonEndpointHairCarrier (index c)
  have haddr : levelAddressAt n (index c) = c :=
    levelAddressAt_levelIndexOf n c
  have hcarrier :
      I.nonEndpointHairCarrier (levelAddressAt n (index c)) =
        I.nonEndpointHairCarrier c :=
    congrArg I.nonEndpointHairCarrier haddr
  have hAvoid' : Disjoint (range (F.trimmedPath (index c)))
      (I.nonEndpointHairCarrier c) := hcarrier ▸ hAvoid
  exact hAvoid'.mono_right
    (I.levelRightHair_carrier_subset_nonEndpointHairCarrier
      a c hLeft hRight)

/-- A synchronized source extension at the junction `a.right = b.left`
remains disjoint from every crosscut `c` not incident to that junction. -/
theorem synchronizedRightRange_disjoint_trimmedPath_of_nonincident
    (a b c : LevelAddress n) (hac : a ≠ c)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane))
    (hLeft :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).left : Plane))
    (hRight :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).right : Plane)) :
    Disjoint (F.synchronizedRightRange a b hshared)
      (range (F.trimmedPath (index c))) := by
  rw [Set.disjoint_left]
  intro x hxSync hxC
  rcases hxSync with hxExtension | hxA
  · have hxHair : x ∈ (I.levelRightHair a).carrier :=
      (convex_segment
        (J.curvePoint (I.levelArc a).right : Plane)
        (I.levelRightHair a).tip).segment_subset
          (F.synchronizedPoint_mem_rightHair a b hshared)
          (F.rightHairPoint a).2 hxExtension
    exact Set.disjoint_left.mp
      (F.trimmedPath_disjoint_levelRightHair_of_nonincident
        a c hLeft hRight) hxC hxHair
  · exact Set.disjoint_left.mp
      (F.pairwise_disjoint_trimmedPath
        (fun hindex => hac (levelIndexOf_injective n hindex))) hxA hxC

/-- The analogous target extension on the following arc is also disjoint
from every crosscut not incident to the shared junction. -/
theorem synchronizedLeftRange_disjoint_trimmedPath_of_nonincident
    (a b c : LevelAddress n) (hbc : b ≠ c)
    (hshared :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc b).left : Plane))
    (hLeft :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).left : Plane))
    (hRight :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).right : Plane)) :
    Disjoint (F.synchronizedLeftRange a b hshared)
      (range (F.trimmedPath (index c))) := by
  rw [Set.disjoint_left]
  intro x hxSync hxC
  rcases hxSync with hxB | hxExtension
  · exact Set.disjoint_left.mp
      (F.pairwise_disjoint_trimmedPath
        (fun hindex => hbc (levelIndexOf_injective n hindex))) hxB hxC
  · have hxHair : x ∈ (I.levelRightHair a).carrier :=
      (convex_segment
        (J.curvePoint (I.levelArc a).right : Plane)
        (I.levelRightHair a).tip).segment_subset
          (F.sharedLeftHairPoint a b hshared).2
          (F.synchronizedPoint_mem_rightHair a b hshared)
          hxExtension
    exact Set.disjoint_left.mp
      (F.trimmedPath_disjoint_levelRightHair_of_nonincident
        a c hLeft hRight) hxC hxHair

end LevelAvoidingJoinFamily
end InitialAngularArcs
end JordanCircle

end Schoenflies
