import Schoenflies.LevelEndpointIncidence
import Schoenflies.FiniteLevelHairSynchronization

/-!
# Synchronized returns at one complete subdivision level

Every elementary level arc receives a polygonal return whose two inner
endpoints have been synchronized with its cyclic neighbors.  The return is
the finite chain consisting of two boundary-side hair segments, two short
synchronization extensions, and the trimmed middle crosscut.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace InitialAngularArcs
namespace LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

private noncomputable abbrev index (a : LevelAddress n) :
    Fin (levelAddressCount n) :=
  levelIndexOf n a

/-- The point at which the return for `a` meets the return for its cyclic
predecessor. -/
noncomputable def leftSynchronizedPoint (a : LevelAddress n) : Plane :=
  F.synchronizedPoint (prevLevelAddress n a) a
    (I.levelAdjacent_prevLevelAddress n a)

/-- The point at which the return for `a` meets the return for its cyclic
successor. -/
noncomputable def rightSynchronizedPoint (a : LevelAddress n) : Plane :=
  F.synchronizedPoint a (nextLevelAddress n a)
    (I.levelAdjacent_nextLevelAddress n a)

theorem leftSynchronizedPoint_mem_leftHair (a : LevelAddress n) :
    F.leftSynchronizedPoint a ∈ (I.levelLeftHair a).carrier :=
  F.synchronizedPoint_mem_leftHair (prevLevelAddress n a) a
    (I.levelAdjacent_prevLevelAddress n a)

theorem rightSynchronizedPoint_mem_rightHair (a : LevelAddress n) :
    F.rightSynchronizedPoint a ∈ (I.levelRightHair a).carrier :=
  F.synchronizedPoint_mem_rightHair a (nextLevelAddress n a)
    (I.levelAdjacent_nextLevelAddress n a)

theorem leftSynchronizedPoint_inside (a : LevelAddress n) :
    F.leftSynchronizedPoint a ∈ J.inside :=
  F.synchronizedPoint_inside (prevLevelAddress n a) a
    (I.levelAdjacent_prevLevelAddress n a)

theorem rightSynchronizedPoint_inside (a : LevelAddress n) :
    F.rightSynchronizedPoint a ∈ J.inside :=
  F.synchronizedPoint_inside a (nextLevelAddress n a)
    (I.levelAdjacent_nextLevelAddress n a)

@[simp] theorem rightSynchronizedPoint_next_eq_leftSynchronizedPoint
    (a : LevelAddress n) :
    F.rightSynchronizedPoint a =
      F.leftSynchronizedPoint (nextLevelAddress n a) := by
  simp [rightSynchronizedPoint, leftSynchronizedPoint]

/-- Neighboring returns use literally the same boundary-side segment of
their common retained hair. -/
theorem rightBaseSegment_eq_leftBaseSegment_next
    (a : LevelAddress n) :
    segment ℝ (F.rightSynchronizedPoint a)
        (J.curvePoint (I.levelArc a).right : Plane) =
      segment ℝ
        (J.curvePoint
          (I.levelArc (nextLevelAddress n a)).left : Plane)
        (F.leftSynchronizedPoint (nextLevelAddress n a)) := by
  have hbase := I.levelAdjacent_nextLevelAddress n a
  rw [F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a, hbase]
  exact segment_symm _ _ _

/-- The boundary-side right segment and the inner right extension meet only
at their synchronized endpoint. -/
theorem rightBaseSegment_inter_rightExtension (a : LevelAddress n) :
    segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
          (F.rightSynchronizedPoint a) ∩
        segment ℝ (F.rightSynchronizedPoint a)
          (F.trimmedRightPoint (index a)) =
      {F.rightSynchronizedPoint a} := by
  rw [inter_comm]
  exact (I.levelRightHair a).segment_inter_baseSegment_eq
    ⟨F.rightSynchronizedPoint a,
      F.rightSynchronizedPoint_mem_rightHair a⟩
    (F.rightHairPoint a)
    (F.synchronizedPoint_parameter_le_right a
      (nextLevelAddress n a)
      (I.levelAdjacent_nextLevelAddress n a))

/-- The analogous two pieces at the left endpoint also meet only at their
synchronized endpoint. -/
theorem leftBaseSegment_inter_leftExtension (a : LevelAddress n) :
    segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
          (F.leftSynchronizedPoint a) ∩
        segment ℝ (F.leftSynchronizedPoint a)
          (F.trimmedLeftPoint (index a)) =
      {F.leftSynchronizedPoint a} := by
  let p := prevLevelAddress n a
  let hshared := I.levelAdjacent_prevLevelAddress n a
  rw [inter_comm]
  have h := (I.levelRightHair p).segment_inter_baseSegment_eq
    ⟨F.leftSynchronizedPoint a, by
      exact F.synchronizedPoint_mem_rightHair p a hshared⟩
    (F.sharedLeftHairPoint p a hshared)
    (F.synchronizedPoint_parameter_le_left p a hshared)
  have hbase :
      (J.curvePoint (I.levelArc p).right : Plane) =
        (J.curvePoint (I.levelArc a).left : Plane) := hshared
  have hpoint : (F.sharedLeftHairPoint p a hshared : Plane) =
      F.trimmedLeftPoint (index a) := rfl
  rw [hpoint] at h
  simpa [leftSynchronizedPoint, p, hshared, hbase] using h

/-- The inner polygonal crosscut from the synchronized left endpoint to the
synchronized right endpoint. -/
noncomputable def synchronizedCrosscutSet (a : LevelAddress n) : Set Plane :=
  segment ℝ (F.leftSynchronizedPoint a)
      (F.trimmedLeftPoint (index a)) ∪
    range (F.trimmedPath (index a)) ∪
    segment ℝ (F.trimmedRightPoint (index a))
      (F.rightSynchronizedPoint a)

theorem leftExtension_subset_levelLeftHair (a : LevelAddress n) :
    segment ℝ (F.leftSynchronizedPoint a)
        (F.trimmedLeftPoint (index a)) ⊆
      (I.levelLeftHair a).carrier := by
  exact (convex_segment
    (J.curvePoint (I.levelArc a).left : Plane)
    (I.levelLeftHair a).tip).segment_subset
      (F.leftSynchronizedPoint_mem_leftHair a)
      (F.leftHairPoint a).2

theorem rightExtension_subset_levelRightHair (a : LevelAddress n) :
    segment ℝ (F.trimmedRightPoint (index a))
        (F.rightSynchronizedPoint a) ⊆
      (I.levelRightHair a).carrier := by
  exact (convex_segment
    (J.curvePoint (I.levelArc a).right : Plane)
    (I.levelRightHair a).tip).segment_subset
      (F.rightHairPoint a).2
      (F.rightSynchronizedPoint_mem_rightHair a)

/-- Address inequalities discharge the geometric nonincidence hypotheses
for a synchronized right range. -/
theorem synchronizedRightRange_disjoint_trimmedPath_of_not_incident
    (a c : LevelAddress n) (hac : a ≠ c)
    (hnext : nextLevelAddress n a ≠ c) :
    Disjoint
      (F.synchronizedRightRange a (nextLevelAddress n a)
        (I.levelAdjacent_nextLevelAddress n a))
      (range (F.trimmedPath (index c))) := by
  exact F.synchronizedRightRange_disjoint_trimmedPath_of_nonincident
    a (nextLevelAddress n a) c hac
    (I.levelAdjacent_nextLevelAddress n a)
    (I.levelRightPoint_ne_levelLeftPoint_of_ne_next a c hnext.symm)
    (I.levelRightPoint_ne_levelRightPoint_of_ne a c hac)

/-- The analogous address-only criterion for a synchronized left range. -/
theorem synchronizedLeftRange_disjoint_trimmedPath_of_not_incident
    (a c : LevelAddress n) (hac : a ≠ c)
    (hprev : prevLevelAddress n a ≠ c) :
    Disjoint
      (F.synchronizedLeftRange (prevLevelAddress n a) a
        (I.levelAdjacent_prevLevelAddress n a))
      (range (F.trimmedPath (index c))) := by
  exact F.synchronizedLeftRange_disjoint_trimmedPath_of_nonincident
    (prevLevelAddress n a) a c hac
    (I.levelAdjacent_prevLevelAddress n a)
    (I.levelRightPoint_ne_levelLeftPoint_of_ne_next
      (prevLevelAddress n a) c (by simpa using hac.symm))
    (I.levelRightPoint_ne_levelRightPoint_of_ne
      (prevLevelAddress n a) c hprev)

/-- A complete synchronized crosscut avoids every trimmed middle path whose
arc is not one of its two cyclic neighbors or itself. -/
theorem synchronizedCrosscutSet_disjoint_trimmedPath_of_not_incident
    (a c : LevelAddress n)
    (hprev : prevLevelAddress n a ≠ c) (hac : a ≠ c)
    (hnext : nextLevelAddress n a ≠ c) :
    Disjoint (F.synchronizedCrosscutSet a)
      (range (F.trimmedPath (index c))) := by
  rw [Set.disjoint_left]
  intro x hxCross hxPath
  rcases hxCross with (hxLeft | hxMiddle) | hxRight
  · have hxSync : x ∈ F.synchronizedLeftRange
        (prevLevelAddress n a) a
        (I.levelAdjacent_prevLevelAddress n a) := by
      right
      simpa [segment_symm, leftSynchronizedPoint] using hxLeft
    exact Set.disjoint_left.mp
      (F.synchronizedLeftRange_disjoint_trimmedPath_of_not_incident
        a c hac hprev) hxSync hxPath
  · have hxSync : x ∈ F.synchronizedLeftRange
        (prevLevelAddress n a) a
        (I.levelAdjacent_prevLevelAddress n a) := Or.inl hxMiddle
    exact Set.disjoint_left.mp
      (F.synchronizedLeftRange_disjoint_trimmedPath_of_not_incident
        a c hac hprev) hxSync hxPath
  · have hxSync : x ∈ F.synchronizedRightRange
        a (nextLevelAddress n a)
        (I.levelAdjacent_nextLevelAddress n a) := by
      left
      simpa [segment_symm, rightSynchronizedPoint] using hxRight
    exact Set.disjoint_left.mp
      (F.synchronizedRightRange_disjoint_trimmedPath_of_not_incident
        a c hac hnext) hxSync hxPath

/-- Synchronized inner crosscuts belonging to nonadjacent level arcs are
disjoint. -/
theorem disjoint_synchronizedCrosscutSet_of_nonadjacent
    (a c : LevelAddress n) (hac : a ≠ c)
    (hca : c ≠ nextLevelAddress n a)
    (hacNext : a ≠ nextLevelAddress n c) :
    Disjoint (F.synchronizedCrosscutSet a)
      (F.synchronizedCrosscutSet c) := by
  have hprevA : prevLevelAddress n a ≠ c := by
    intro h
    apply hacNext
    rw [← h]
    simp
  have hprevC : prevLevelAddress n c ≠ a := by
    intro h
    apply hca
    rw [← h]
    simp
  have hAPathC :=
    F.synchronizedCrosscutSet_disjoint_trimmedPath_of_not_incident
      a c hprevA hac hca.symm
  have hCPathA :=
    F.synchronizedCrosscutSet_disjoint_trimmedPath_of_not_incident
      c a hprevC hac.symm hacNext.symm
  rw [Set.disjoint_left]
  intro x hxA hxC
  rcases hxA with (hxALeft | hxAMiddle) | hxARight
  · rcases hxC with (hxCLeft | hxCMiddle) | hxCRight
    · exact Set.disjoint_left.mp
        (I.disjoint_levelLeftHairs_of_ne a c hac)
        (F.leftExtension_subset_levelLeftHair a hxALeft)
        (F.leftExtension_subset_levelLeftHair c hxCLeft)
    · exact Set.disjoint_left.mp hAPathC
        (Or.inl (Or.inl hxALeft)) hxCMiddle
    · exact Set.disjoint_left.mp
        (I.disjoint_levelRightHair_levelLeftHair_of_ne_next
          c a hacNext).symm
        (F.leftExtension_subset_levelLeftHair a hxALeft)
        (F.rightExtension_subset_levelRightHair c hxCRight)
  · exact Set.disjoint_left.mp hCPathA hxC hxAMiddle
  · rcases hxC with (hxCLeft | hxCMiddle) | hxCRight
    · exact Set.disjoint_left.mp
        (I.disjoint_levelRightHair_levelLeftHair_of_ne_next
          a c hca)
        (F.rightExtension_subset_levelRightHair a hxARight)
        (F.leftExtension_subset_levelLeftHair c hxCLeft)
    · exact Set.disjoint_left.mp hAPathC
        (Or.inr hxARight) hxCMiddle
    · exact Set.disjoint_left.mp
        (I.disjoint_levelRightHairs_of_ne a c hac)
        (F.rightExtension_subset_levelRightHair a hxARight)
        (F.rightExtension_subset_levelRightHair c hxCRight)

theorem trimmedPath_disjoint_levelRightHair_of_not_incident
    (a c : LevelAddress n)
    (hleft : c ≠ nextLevelAddress n a) (hright : a ≠ c) :
    Disjoint (range (F.trimmedPath (index c)))
      (I.levelRightHair a).carrier :=
  F.trimmedPath_disjoint_levelRightHair_of_nonincident a c
    (I.levelRightPoint_ne_levelLeftPoint_of_ne_next a c hleft)
    (I.levelRightPoint_ne_levelRightPoint_of_ne a c hright)

/-- At every level with at least four arcs, neighboring synchronized inner
crosscuts meet exactly at their common synchronized endpoint. -/
theorem synchronizedCrosscutSet_inter_next (hn : 1 ≤ n)
    (a : LevelAddress n) :
    F.synchronizedCrosscutSet a ∩
        F.synchronizedCrosscutSet (nextLevelAddress n a) =
      {F.rightSynchronizedPoint a} := by
  let b := nextLevelAddress n a
  let hshared := I.levelAdjacent_nextLevelAddress n a
  have hab : a ≠ b := by
    simpa [b] using (nextLevelAddress_ne n a).symm
  have hba : b ≠ a := hab.symm
  have hnextB : nextLevelAddress n b ≠ a := by
    simpa [b] using nextLevelAddress_next_ne n hn a
  have haNextB : a ≠ nextLevelAddress n b := hnextB.symm
  have hprevAB : prevLevelAddress n a ≠ b := by
    intro h
    have hnext := congrArg (nextLevelAddress n) h
    have : a = nextLevelAddress n b := by simpa [b] using hnext
    exact haNextB this
  have hcore := F.synchronizedRanges_inter a b hab hshared
  apply Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    rcases hxA with (hxALeft | hxAMiddle) | hxARight
    · rcases hxB with (hxBLeft | hxBMiddle) | hxBRight
      · exact False.elim <| Set.disjoint_left.mp
          (I.disjoint_levelLeftHairs_of_ne a b hab)
          (F.leftExtension_subset_levelLeftHair a hxALeft)
          (F.leftExtension_subset_levelLeftHair b hxBLeft)
      · have hxAHair : x ∈ (I.levelRightHair
            (prevLevelAddress n a)).carrier := by
          rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq
            (prevLevelAddress n a) a
            (I.levelAdjacent_prevLevelAddress n a)]
          exact F.leftExtension_subset_levelLeftHair a hxALeft
        exact False.elim <| Set.disjoint_left.mp
          (F.trimmedPath_disjoint_levelRightHair_of_not_incident
            (prevLevelAddress n a) b (by simpa using hba) hprevAB)
          hxBMiddle hxAHair
      · exact False.elim <| Set.disjoint_left.mp
          (I.disjoint_levelRightHair_levelLeftHair_of_ne_next
            b a haNextB).symm
          (F.leftExtension_subset_levelLeftHair a hxALeft)
          (F.rightExtension_subset_levelRightHair b hxBRight)
    · rcases hxB with (hxBLeft | hxBMiddle) | hxBRight
      · have hxCoreA : x ∈ F.synchronizedRightRange a b hshared :=
          Or.inr hxAMiddle
        have hxCoreB : x ∈ F.synchronizedLeftRange a b hshared := by
          right
          rw [segment_symm] at hxBLeft
          simpa [leftSynchronizedPoint, b, hshared] using hxBLeft
        exact (congrArg (fun S : Set Plane => x ∈ S) hcore).mp
          ⟨hxCoreA, hxCoreB⟩
      · have hxCoreA : x ∈ F.synchronizedRightRange a b hshared :=
          Or.inr hxAMiddle
        have hxCoreB : x ∈ F.synchronizedLeftRange a b hshared :=
          Or.inl hxBMiddle
        exact (congrArg (fun S : Set Plane => x ∈ S) hcore).mp
          ⟨hxCoreA, hxCoreB⟩
      · exact False.elim <| Set.disjoint_left.mp
          (F.trimmedPath_disjoint_levelRightHair_of_not_incident
            b a haNextB hba)
          hxAMiddle (F.rightExtension_subset_levelRightHair b hxBRight)
    · rcases hxB with (hxBLeft | hxBMiddle) | hxBRight
      · have hxCoreA : x ∈ F.synchronizedRightRange a b hshared := by
          left
          simpa [segment_symm, rightSynchronizedPoint, b, hshared]
            using hxARight
        have hxCoreB : x ∈ F.synchronizedLeftRange a b hshared := by
          right
          rw [segment_symm] at hxBLeft
          simpa [leftSynchronizedPoint, b, hshared] using hxBLeft
        exact (congrArg (fun S : Set Plane => x ∈ S) hcore).mp
          ⟨hxCoreA, hxCoreB⟩
      · have hxCoreA : x ∈ F.synchronizedRightRange a b hshared := by
          left
          simpa [segment_symm, rightSynchronizedPoint, b, hshared]
            using hxARight
        have hxCoreB : x ∈ F.synchronizedLeftRange a b hshared :=
          Or.inl hxBMiddle
        exact (congrArg (fun S : Set Plane => x ∈ S) hcore).mp
          ⟨hxCoreA, hxCoreB⟩
      · exact False.elim <| Set.disjoint_left.mp
          (I.disjoint_levelRightHairs_of_ne a b hab)
          (F.rightExtension_subset_levelRightHair a hxARight)
          (F.rightExtension_subset_levelRightHair b hxBRight)
  · intro x hx
    have hxEq : x = F.rightSynchronizedPoint a :=
      mem_singleton_iff.mp hx
    subst x
    constructor
    · exact Or.inr (right_mem_segment ℝ _ _)
    · left
      left
      rw [← F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
      exact left_mem_segment ℝ _ _

theorem synchronizedCrosscutSet_subset_inside (a : LevelAddress n) :
    F.synchronizedCrosscutSet a ⊆ J.inside := by
  rintro x ((hxLeft | hxMiddle) | hxRight)
  · have h := F.leftExtension_subset_inside
      (prevLevelAddress n a) a
      (I.levelAdjacent_prevLevelAddress n a)
    exact h (by
      simpa [segment_symm, leftSynchronizedPoint] using hxLeft)
  · exact (F.range_trimmedPath_subset_controlled (index a) hxMiddle).1
  · exact F.rightExtension_subset_inside a (nextLevelAddress n a)
      (I.levelAdjacent_nextLevelAddress n a)
      (by simpa [segment_symm, rightSynchronizedPoint] using hxRight)

/-- The synchronized inner crosscut is an explicit finite broken-line join. -/
theorem joinedByBrokenLine_synchronizedCrosscutSet (a : LevelAddress n) :
    JoinedByBrokenLine (F.synchronizedCrosscutSet a)
      (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) := by
  let B := F.trimmedLine (index a)
  have hleft : JoinedByBrokenLine (F.synchronizedCrosscutSet a)
      (F.leftSynchronizedPoint a)
      (F.trimmedLeftPoint (index a)) := by
    apply JoinedByBrokenLine.of_segment
    intro x hx
    exact Or.inl (Or.inl hx)
  have hmiddle : JoinedByBrokenLine (F.synchronizedCrosscutSet a)
      (F.trimmedRightPoint (index a))
      (F.trimmedLeftPoint (index a)) := by
    refine ⟨B.data.n, B.data.vertex, B.start_eq, B.finish_eq, ?_⟩
    intro i x hx
    exact Or.inl (Or.inr (B.data.segment_subset i hx))
  have hright : JoinedByBrokenLine (F.synchronizedCrosscutSet a)
      (F.trimmedRightPoint (index a))
      (F.rightSynchronizedPoint a) := by
    apply JoinedByBrokenLine.of_segment
    intro x hx
    exact Or.inr hx
  exact (hleft.trans hmiddle.symm).trans hright

theorem leftSynchronizedPoint_ne_rightSynchronizedPoint
    (a : LevelAddress n) :
    F.leftSynchronizedPoint a ≠ F.rightSynchronizedPoint a := by
  intro h
  have hright : F.leftSynchronizedPoint a ∈
      (I.levelRightHair a).carrier := by
    rw [h]
    exact F.rightSynchronizedPoint_mem_rightHair a
  exact Set.disjoint_left.mp (I.disjoint_levelEndpointHairs a)
    (F.leftSynchronizedPoint_mem_leftHair a) hright

/-- Loop erase one inner crosscut while retaining the synchronized endpoints
and its controlled carrier. -/
noncomputable def synchronizedCrosscutLine (a : LevelAddress n) :
    SimpleBrokenLine (F.synchronizedCrosscutSet a)
      (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) :=
  simpleBrokenLineOfJoined (F.joinedByBrokenLine_synchronizedCrosscutSet a)

/-- The injective PL parameterization of one synchronized inner crosscut. -/
noncomputable def synchronizedCrosscutPath (a : LevelAddress n) :
    Path (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) :=
  (F.synchronizedCrosscutLine a).toPath
    (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)

theorem synchronizedCrosscutPath_injective (a : LevelAddress n) :
    Injective (F.synchronizedCrosscutPath a) :=
  (F.synchronizedCrosscutLine a).toPath_injective
    (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)

theorem range_synchronizedCrosscutPath_subset (a : LevelAddress n) :
    range (F.synchronizedCrosscutPath a) ⊆
      F.synchronizedCrosscutSet a :=
  (F.synchronizedCrosscutLine a).range_toPath_subset
    (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)

theorem range_synchronizedCrosscutPath_inter_next (hn : 1 ≤ n)
    (a : LevelAddress n) :
    range (F.synchronizedCrosscutPath a) ∩
        range (F.synchronizedCrosscutPath (nextLevelAddress n a)) =
      {F.rightSynchronizedPoint a} := by
  apply Subset.antisymm
  · intro x hx
    have hxSets : x ∈ F.synchronizedCrosscutSet a ∩
        F.synchronizedCrosscutSet (nextLevelAddress n a) :=
      ⟨F.range_synchronizedCrosscutPath_subset a hx.1,
        F.range_synchronizedCrosscutPath_subset
          (nextLevelAddress n a) hx.2⟩
    rw [F.synchronizedCrosscutSet_inter_next hn a] at hxSets
    exact hxSets
  · intro x hx
    have hxEq : x = F.rightSynchronizedPoint a :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range (F.synchronizedCrosscutPath a), by
      rw [F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
      exact Path.source_mem_range
        (F.synchronizedCrosscutPath (nextLevelAddress n a))⟩

theorem disjoint_range_synchronizedCrosscutPath_of_nonadjacent
    (a c : LevelAddress n) (hac : a ≠ c)
    (hca : c ≠ nextLevelAddress n a)
    (hacNext : a ≠ nextLevelAddress n c) :
    Disjoint (range (F.synchronizedCrosscutPath a))
      (range (F.synchronizedCrosscutPath c)) :=
  (F.disjoint_synchronizedCrosscutSet_of_nonadjacent
    a c hac hca hacNext).mono
      (F.range_synchronizedCrosscutPath_subset a)
      (F.range_synchronizedCrosscutPath_subset c)

/-- The whole cell-side return, including the two boundary-side retained-hair
segments. -/
noncomputable def synchronizedReturnSet (a : LevelAddress n) : Set Plane :=
  segment ℝ (J.curvePoint (I.levelArc a).left)
      (F.leftSynchronizedPoint a) ∪
    F.synchronizedCrosscutSet a ∪
    segment ℝ (F.rightSynchronizedPoint a)
      (J.curvePoint (I.levelArc a).right)

theorem joinedByBrokenLine_synchronizedReturnSet (a : LevelAddress n) :
    JoinedByBrokenLine (F.synchronizedReturnSet a)
      (J.curvePoint (I.levelArc a).left)
      (J.curvePoint (I.levelArc a).right) := by
  have hleft : JoinedByBrokenLine (F.synchronizedReturnSet a)
      (J.curvePoint (I.levelArc a).left)
      (F.leftSynchronizedPoint a) := by
    apply JoinedByBrokenLine.of_segment
    intro x hx
    exact Or.inl (Or.inl hx)
  have hmiddle : JoinedByBrokenLine (F.synchronizedReturnSet a)
      (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) :=
    (F.joinedByBrokenLine_synchronizedCrosscutSet a).mono (by
      intro x hx
      exact Or.inl (Or.inr hx))
  have hright : JoinedByBrokenLine (F.synchronizedReturnSet a)
      (F.rightSynchronizedPoint a)
      (J.curvePoint (I.levelArc a).right) := by
    apply JoinedByBrokenLine.of_segment
    intro x hx
    exact Or.inr hx
  exact (hleft.trans hmiddle).trans hright

theorem synchronizedReturnSet_subset_insideCrosscutSet
    (a : LevelAddress n) :
    F.synchronizedReturnSet a ⊆
      J.insideCrosscutSet
        (J.curvePoint (I.levelArc a).left)
        (J.curvePoint (I.levelArc a).right) := by
  rintro x ((hxLeft | hxMiddle) | hxRight)
  · have hxHair : x ∈ (I.levelLeftHair a).carrier :=
      (convex_segment
        (J.curvePoint (I.levelArc a).left : Plane)
        (I.levelLeftHair a).tip).segment_subset
          (left_mem_segment ℝ _ _)
          (F.leftSynchronizedPoint_mem_leftHair a) hxLeft
    rcases (I.levelLeftHair a).carrier_subset hxHair with hxInside | hxBase
    · exact Or.inl hxInside
    · exact Or.inr (Or.inl (mem_singleton_iff.mp hxBase))
  · exact Or.inl (F.synchronizedCrosscutSet_subset_inside a hxMiddle)
  · have hxHair : x ∈ (I.levelRightHair a).carrier :=
      (convex_segment
        (J.curvePoint (I.levelArc a).right : Plane)
        (I.levelRightHair a).tip).segment_subset
          (F.rightSynchronizedPoint_mem_rightHair a)
          (left_mem_segment ℝ _ _) hxRight
    rcases (I.levelRightHair a).carrier_subset hxHair with hxInside | hxBase
    · exact Or.inl hxInside
    · exact Or.inr (Or.inr (mem_singleton_iff.mp hxBase))

/-- Loop erase the synchronized finite chain. -/
noncomputable def synchronizedReturnLine (a : LevelAddress n) :
    SimpleBrokenLine (F.synchronizedReturnSet a)
      (J.curvePoint (I.levelArc a).left)
      (J.curvePoint (I.levelArc a).right) :=
  simpleBrokenLineOfJoined (F.joinedByBrokenLine_synchronizedReturnSet a)

/-- Orient the synchronized return from right to left so that it closes the
selected wild boundary arc. -/
noncomputable def synchronizedReturnPath (a : LevelAddress n) :
    Path (J.curvePoint (I.levelArc a).right : Plane)
      (J.curvePoint (I.levelArc a).left : Plane) :=
  (F.synchronizedReturnLine a).toPath (I.levelArc a).endpoint_ne |>.symm

theorem synchronizedReturnPath_injective (a : LevelAddress n) :
    Injective (F.synchronizedReturnPath a) := by
  intro s t hst
  apply unitInterval.symm_bijective.injective
  exact (F.synchronizedReturnLine a).toPath_injective
    (I.levelArc a).endpoint_ne hst

theorem range_synchronizedReturnPath_subset (a : LevelAddress n) :
    range (F.synchronizedReturnPath a) ⊆
      F.synchronizedReturnSet a := by
  rw [synchronizedReturnPath, Path.symm_range]
  exact (F.synchronizedReturnLine a).range_toPath_subset
    (I.levelArc a).endpoint_ne

/-- The synchronized return behind the common `InsideReturnArc` interface. -/
noncomputable def synchronizedInsideReturnArc (a : LevelAddress n) :
    (I.levelArc a).InsideReturnArc where
  permittedSet := F.synchronizedReturnSet a
  path := F.synchronizedReturnPath a
  sourceBrokenLine := F.synchronizedReturnLine a
  path_injective := F.synchronizedReturnPath_injective a
  segmentCarrier_eq_range := by
    rw [(F.synchronizedReturnLine a).segmentCarrier_carrierBrokenLine
        (I.levelArc a).endpoint_ne,
      synchronizedReturnPath, Path.symm_range]
  range_subset_insideCrosscutSet :=
    (F.range_synchronizedReturnPath_subset a).trans
      (F.synchronizedReturnSet_subset_insideCrosscutSet a)

end LevelAvoidingJoinFamily
end InitialAngularArcs
end JordanCircle

end Schoenflies
