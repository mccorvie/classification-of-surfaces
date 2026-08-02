import Schoenflies.PolygonalTwoArcCycle
import Schoenflies.SynchronizedLevelReturns
import ClassificationOfSurfaces.Moise.GraphPolygonalization

/-!
# Exact ranges of synchronized level crosscuts

The synchronized crosscut was originally defined by loop-erasing the join
of a left hair extension, a trimmed embedded crosscut, and a right hair
extension.  The endpoint synchronization can make either extension
degenerate, but the remaining pieces still form one embedded arc.  Hence
loop erasure does not shorten its carrier.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

private noncomputable abbrev index (a : LevelAddress n) :
    Fin (levelAddressCount n) :=
  levelIndexOf n a

/-- The synchronized crosscut before loop erasure, omitting either straight
extension when synchronization makes it constant. -/
noncomputable def exactSynchronizedCrosscutPath (a : LevelAddress n) :
    Path (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) :=
  if hleft : F.leftSynchronizedPoint a =
      F.trimmedLeftPoint (index a) then
    if hright : F.rightSynchronizedPoint a =
        F.trimmedRightPoint (index a) then
      (F.trimmedPath (index a)).symm.cast hleft hright
    else
      ((F.trimmedPath (index a)).symm.trans <|
        Path.segment (F.trimmedRightPoint (index a))
          (F.rightSynchronizedPoint a)).cast hleft rfl
  else if hright : F.rightSynchronizedPoint a =
      F.trimmedRightPoint (index a) then
    ((Path.segment (F.leftSynchronizedPoint a)
      (F.trimmedLeftPoint (index a))).trans
        (F.trimmedPath (index a)).symm).cast rfl hright
  else
    (Path.segment (F.leftSynchronizedPoint a)
        (F.trimmedLeftPoint (index a))).trans
      ((F.trimmedPath (index a)).symm.trans <|
        Path.segment (F.trimmedRightPoint (index a))
          (F.rightSynchronizedPoint a))

theorem range_exactSynchronizedCrosscutPath (a : LevelAddress n) :
    range (F.exactSynchronizedCrosscutPath a) =
      F.synchronizedCrosscutSet a := by
  change range (F.exactSynchronizedCrosscutPath a) =
    segment ℝ (F.leftSynchronizedPoint a)
        (F.trimmedLeftPoint (levelIndexOf n a)) ∪
      range (F.trimmedPath (levelIndexOf n a)) ∪
      segment ℝ (F.trimmedRightPoint (levelIndexOf n a))
        (F.rightSynchronizedPoint a)
  by_cases hleft : F.leftSynchronizedPoint a =
      F.trimmedLeftPoint (index a)
  · by_cases hright : F.rightSynchronizedPoint a =
        F.trimmedRightPoint (index a)
    · rw [exactSynchronizedCrosscutPath, dif_pos hleft, dif_pos hright]
      simp only [Path.cast_coe, Path.symm_range]
      dsimp only [index]
      rw [hleft, hright, segment_same, segment_same]
      apply Set.Subset.antisymm
      · intro x hx
        exact Or.inl (Or.inr hx)
      · rintro x ((hx | hx) | hx)
        · rw [mem_singleton_iff] at hx
          subst x
          exact Path.target_mem_range _
        · exact hx
        · rw [mem_singleton_iff] at hx
          subst x
          exact Path.source_mem_range _
    · rw [exactSynchronizedCrosscutPath, dif_pos hleft, dif_neg hright]
      simp only [Path.cast_coe, Path.trans_range, Path.symm_range,
        Path.range_segment]
      dsimp only [index]
      rw [hleft, segment_same]
      apply Set.Subset.antisymm
      · rintro x (hx | hx)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
      · rintro x ((hx | hx) | hx)
        · rw [mem_singleton_iff] at hx
          subst x
          exact Or.inl (Path.target_mem_range _)
        · exact Or.inl hx
        · exact Or.inr hx
  · by_cases hright : F.rightSynchronizedPoint a =
        F.trimmedRightPoint (index a)
    · rw [exactSynchronizedCrosscutPath, dif_neg hleft, dif_pos hright]
      simp only [Path.cast_coe, Path.trans_range, Path.symm_range,
        Path.range_segment]
      dsimp only [index]
      rw [hright, segment_same]
      apply Set.Subset.antisymm
      · intro x hx
        exact Or.inl hx
      · rintro x (hx | hx)
        · exact hx
        · rw [mem_singleton_iff] at hx
          subst x
          exact Or.inr (Path.source_mem_range _)
    · rw [exactSynchronizedCrosscutPath, dif_neg hleft, dif_neg hright]
      simp only [Path.trans_range, Path.symm_range, Path.range_segment]
      dsimp only [index]
      exact (Set.union_assoc _ _ _).symm

private theorem leftExtension_inter_trimmedPath
    (a : LevelAddress n) :
    segment ℝ (F.leftSynchronizedPoint a)
          (F.trimmedLeftPoint (index a)) ∩
        range (F.trimmedPath (index a)) =
      {F.trimmedLeftPoint (index a)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSegment, hxPath⟩
    have hxHair : x ∈ (I.levelLeftHair a).carrier :=
      F.leftExtension_subset_levelLeftHair a hxSegment
    have hx : x ∈ range (F.trimmedPath (index a)) ∩
        (I.levelLeftHair (levelAddressAt n (index a))).carrier := by
      rw [levelAddressAt_levelIndexOf]
      exact ⟨hxPath, hxHair⟩
    rwa [F.range_trimmedPath_inter_leftHair (index a)] at hx
  · intro x hx
    have hxEq : x = F.trimmedLeftPoint (index a) :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨right_mem_segment ℝ _ _,
      Path.target_mem_range (F.trimmedPath (index a))⟩

private theorem trimmedPath_inter_rightExtension
    (a : LevelAddress n) :
    range (F.trimmedPath (index a)) ∩
        segment ℝ (F.trimmedRightPoint (index a))
          (F.rightSynchronizedPoint a) =
      {F.trimmedRightPoint (index a)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxPath, hxSegment⟩
    have hxHair : x ∈ (I.levelRightHair a).carrier :=
      F.rightExtension_subset_levelRightHair a hxSegment
    have hx : x ∈ range (F.trimmedPath (index a)) ∩
        (I.levelRightHair (levelAddressAt n (index a))).carrier := by
      rw [levelAddressAt_levelIndexOf]
      exact ⟨hxPath, hxHair⟩
    rwa [F.range_trimmedPath_inter_rightHair (index a)] at hx
  · intro x hx
    have hxEq : x = F.trimmedRightPoint (index a) :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.source_mem_range (F.trimmedPath (index a)),
      left_mem_segment ℝ _ _⟩

private theorem disjoint_leftExtension_rightExtension
    (a : LevelAddress n) :
    Disjoint
      (segment ℝ (F.leftSynchronizedPoint a)
        (F.trimmedLeftPoint (index a)))
      (segment ℝ (F.trimmedRightPoint (index a))
        (F.rightSynchronizedPoint a)) := by
  apply (I.disjoint_levelEndpointHairs a).mono
  · exact F.leftExtension_subset_levelLeftHair a
  · exact F.rightExtension_subset_levelRightHair a

theorem exactSynchronizedCrosscutPath_injective
    (a : LevelAddress n) :
    Injective (F.exactSynchronizedCrosscutPath a) := by
  let middle := (F.trimmedPath (index a)).symm
  have hmiddle : Injective middle :=
    (F.trimmedPath_injective (index a)).comp
      unitInterval.symm_bijective.injective
  by_cases hleft : F.leftSynchronizedPoint a =
      F.trimmedLeftPoint (index a)
  · by_cases hright : F.rightSynchronizedPoint a =
        F.trimmedRightPoint (index a)
    · rw [exactSynchronizedCrosscutPath, dif_pos hleft, dif_pos hright]
      simpa only [Path.cast_coe] using hmiddle
    · let last := Path.segment (F.trimmedRightPoint (index a))
          (F.rightSynchronizedPoint a)
      have hlast : Injective last :=
        Path.segment_injective_of_ne (Ne.symm hright)
      have hinter : range middle ∩ range last =
          {F.trimmedRightPoint (index a)} := by
        simpa only [middle, last, Path.symm_range, Path.range_segment] using
          F.trimmedPath_inter_rightExtension a
      rw [exactSynchronizedCrosscutPath, dif_pos hleft, dif_neg hright]
      simpa only [Path.cast_coe] using
        (Path.trans_injective_of_range_inter middle last
          hmiddle hlast hinter)
  · let first := Path.segment (F.leftSynchronizedPoint a)
        (F.trimmedLeftPoint (index a))
    have hfirst : Injective first := Path.segment_injective_of_ne hleft
    have hfirstMiddle : range first ∩ range middle =
        {F.trimmedLeftPoint (index a)} := by
      simpa only [first, middle, Path.symm_range, Path.range_segment] using
        F.leftExtension_inter_trimmedPath a
    by_cases hright : F.rightSynchronizedPoint a =
        F.trimmedRightPoint (index a)
    · rw [exactSynchronizedCrosscutPath, dif_neg hleft, dif_pos hright]
      simpa only [Path.cast_coe] using
        (Path.trans_injective_of_range_inter first middle
          hfirst hmiddle hfirstMiddle)
    · let last := Path.segment (F.trimmedRightPoint (index a))
          (F.rightSynchronizedPoint a)
      have hlast : Injective last :=
        Path.segment_injective_of_ne (Ne.symm hright)
      have hmiddleLast : range middle ∩ range last =
          {F.trimmedRightPoint (index a)} := by
        simpa only [middle, last, Path.symm_range, Path.range_segment] using
          F.trimmedPath_inter_rightExtension a
      have htail : Injective (middle.trans last) :=
        Path.trans_injective_of_range_inter middle last
          hmiddle hlast hmiddleLast
      have hfirstLast : range first ∩ range last = ∅ := by
        exact Set.disjoint_iff_inter_eq_empty.mp <| by
          simpa only [first, last, Path.range_segment] using
            F.disjoint_leftExtension_rightExtension a
      have hfirstTail : range first ∩ range (middle.trans last) =
          {F.trimmedLeftPoint (index a)} := by
        rw [Path.trans_range, inter_union_distrib_left,
          hfirstMiddle, hfirstLast, union_empty]
      rw [exactSynchronizedCrosscutPath, dif_neg hleft, dif_neg hright]
      exact
        (Path.trans_injective_of_range_inter first (middle.trans last)
          hfirst htail hfirstTail)

/-- The existing loop-erased synchronized crosscut has exactly the complete
three-piece carrier from which it was constructed. -/
theorem range_synchronizedCrosscutPath_eq_set (a : LevelAddress n) :
    range (F.synchronizedCrosscutPath a) =
      F.synchronizedCrosscutSet a := by
  let p := F.exactSynchronizedCrosscutPath a
  have hp : Injective p := F.exactSynchronizedCrosscutPath_injective a
  have hset : F.synchronizedCrosscutSet a = range p := by
    exact (F.range_exactSynchronizedCrosscutPath a).symm
  have h := (F.synchronizedCrosscutLine a)
    |>.range_toPath_eq_of_subset_injectivePath
      (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a) p hp
      (by rw [hset])
  exact h.trans hset.symm

end JordanCircle.InitialAngularArcs.LevelAvoidingJoinFamily

end

end Schoenflies
