import Schoenflies.MoiseBandChildCarrier
import Schoenflies.CollarBandSegments
import Schoenflies.MarkedMoiseBandBoundaries

/-!
# Coarse-window localization of finer crosscuts on a Moise cell

A finer-level synchronized crosscut that meets the boundary of a recursive
Moise cell must carry an address from the cell's own transported descendant
block or from one of its two cyclic neighbors.  Consequently the raw outer
and raw inner boundary parametrizations of consecutive shrinking stages
assign every shared polygon point to canonical target arcs whose master
windows are equal or adjacent at the coarser level.  This is the source
half of the marked-sector drift estimate.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

/-- Two synchronized crosscuts sharing a point have equal or cyclically
adjacent addresses. -/
theorem LevelAvoidingJoinFamily.crosscutSet_adjacent_of_mem
    {J : JordanCircle} {I : J.InitialAngularArcs} {n : ℕ} {epsilon : ℝ}
    (F : I.LevelAvoidingJoinFamily n epsilon)
    {b c : LevelAddress n} {x : Plane}
    (hxb : x ∈ F.synchronizedCrosscutSet b)
    (hxc : x ∈ F.synchronizedCrosscutSet c) :
    c = b ∨ c = nextLevelAddress n b ∨ b = nextLevelAddress n c := by
  by_contra hall
  push Not at hall
  obtain ⟨hcb, hcnext, hbnext⟩ := hall
  exact Set.disjoint_left.mp
    (F.disjoint_synchronizedCrosscutSet_of_nonadjacent b c
      (fun h => hcb h.symm) hcnext hbnext) hxb hxc

namespace RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private abbrev G (M : RecursiveInsideCollarStep.Later F hn) :
    I.LevelAvoidingJoinFamily M.next.level
      ((M.next.buffer / 4) / 4) :=
  M.next.family.forgetObstacle

private theorem crosscutSet_subset_childCarrier
    (c : LevelAddress L.next.level) :
    (L.G).synchronizedCrosscutSet c ⊆
      ((L.G).synchronizedPolygonalCircle L.next.one_le_level).carrier := by
  intro x hx
  rw [← (L.G).range_synchronizedCrosscutPath_eq_set c] at hx
  rw [(L.G).carrier_synchronizedPolygonalCircle L.next.one_le_level]
  exact Set.mem_iUnion.mpr ⟨c, hx⟩

/-- **Coarse-window localization.**  A finer synchronized crosscut meeting
the boundary of the Moise cell labelled `a` has its address in the
transported descendant block of `a` or of one of `a`'s cyclic neighbors. -/
theorem crosscut_block_near_of_mem_moiseBandCarrier
    (c : LevelAddress L.next.level) (a : LevelAddress n) {x : Plane}
    (hxc : x ∈ (L.G).synchronizedCrosscutSet c)
    (hcell : x ∈ L.moiseBandCarrier a) :
    c ∈ L.addresses (prevLevelAddress n a) ∨
      c ∈ L.addresses a ∨
      c ∈ L.addresses (nextLevelAddress n a) := by
  rw [L.moiseBandCarrier_eq_parent_left_child_right a] at hcell
  rcases hcell with hxParent | hxLeftSeam | hxChild | hxRightSeam
  · -- the parent side lies on the old polygon, which misses the child one
    exfalso
    have hxParentCarrier : x ∈
        (F.synchronizedPolygonalCircle hn).carrier := by
      rw [L.parentMoiseCarrier_eq_crosscutRange a] at hxParent
      rw [F.carrier_synchronizedPolygonalCircle hn]
      exact Set.mem_iUnion.mpr ⟨a, hxParent⟩
    have hxParentClosed : x ∈
        (F.synchronizedPolygonalCircle hn).closedRegion := by
      rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
      exact Or.inr hxParentCarrier
    exact Set.disjoint_left.mp L.next.carrier_disjoint hxParentClosed
      (L.crosscutSet_subset_childCarrier c hxc)
  · -- the left seam lies on the shared retained left hair of `a`
    have hleftSync : F.leftSynchronizedPoint a ∈
        (I.levelLeftHair a).carrier :=
      F.leftSynchronizedPoint_mem_leftHair a
    have htrim : (L.G).trimmedLeftPoint
        (levelIndexOf L.next.level (L.leftmostAddress a)) ∈
        (I.levelLeftHair a).carrier := by
      rw [← L.leftmostAddress_leftHair_carrier a]
      exact ((L.G).leftHairPoint (L.leftmostAddress a)).2
    have hconv : Convex ℝ (I.levelLeftHair a).carrier := by
      change Convex ℝ (segment ℝ _ _)
      exact convex_segment _ _
    have hxHair : x ∈ (I.levelLeftHair (L.leftmostAddress a)).carrier := by
      rw [L.leftmostAddress_leftHair_carrier a]
      exact hconv.segment_subset hleftSync htrim hxLeftSeam
    rcases (L.G).crosscutSet_incident_of_mem_levelLeftHair c
        (L.leftmostAddress a) hxc hxHair with hlm | hlm
    · exact Or.inr (Or.inl (hlm ▸ L.leftmostAddress_mem_addresses a))
    · left
      have hc : c = prevLevelAddress L.next.level (L.leftmostAddress a) := by
        rw [hlm]
        simp
      rw [hc, L.prevLevelAddress_leftmostAddress a]
      exact L.rightmostAddress_mem_addresses (prevLevelAddress n a)
  · -- the retained child route names a supporting descendant address
    obtain ⟨b, hbMem, hxb⟩ :=
      L.exists_mem_crosscutSet_of_mem_childMoiseCarrier a hxChild
    rcases (L.G).crosscutSet_adjacent_of_mem hxb hxc with hcb | hcb | hcb
    · exact Or.inr (Or.inl (hcb ▸ hbMem))
    · rcases L.nextLevelAddress_mem_addresses_or hbMem with hnextMem | hlast
      · exact Or.inr (Or.inl (hcb ▸ hnextMem))
      · right
        right
        rw [hcb, hlast, L.nextLevelAddress_rightmostAddress a]
        exact L.leftmostAddress_mem_addresses (nextLevelAddress n a)
    · have hc : c = prevLevelAddress L.next.level b := by
        rw [hcb]
        simp
      rcases L.prevLevelAddress_mem_addresses_or hbMem with hprevMem | hfirst
      · exact Or.inr (Or.inl (hc ▸ hprevMem))
      · left
        rw [hc, hfirst, L.prevLevelAddress_leftmostAddress a]
        exact L.rightmostAddress_mem_addresses (prevLevelAddress n a)
  · -- the right seam lies on the shared retained right hair of `a`
    have hrightSync : F.rightSynchronizedPoint a ∈
        (I.levelRightHair a).carrier :=
      F.rightSynchronizedPoint_mem_rightHair a
    have htrim : (L.G).trimmedRightPoint
        (levelIndexOf L.next.level (L.rightmostAddress a)) ∈
        (I.levelRightHair a).carrier := by
      rw [← L.rightmostAddress_rightHair_carrier a]
      exact ((L.G).rightHairPoint (L.rightmostAddress a)).2
    have hconv : Convex ℝ (I.levelRightHair a).carrier := by
      change Convex ℝ (segment ℝ _ _)
      exact convex_segment _ _
    have hshared :
        (J.curvePoint
            (I.levelArc (L.rightmostAddress a)).right : Plane) =
          (J.curvePoint
            (I.levelArc (nextLevelAddress L.next.level
              (L.rightmostAddress a))).left : Plane) := by
      have h := I.levelAdjacent_nextLevelAddress L.next.level
        (L.rightmostAddress a)
      unfold InitialAngularArcs.LevelAdjacent at h
      exact h
    have hxHair : x ∈
        (I.levelLeftHair (nextLevelAddress L.next.level
          (L.rightmostAddress a))).carrier := by
      rw [← I.levelRightHair_carrier_eq_levelLeftHair_of_eq
        (L.rightmostAddress a)
        (nextLevelAddress L.next.level (L.rightmostAddress a)) hshared,
        L.rightmostAddress_rightHair_carrier a]
      exact hconv.segment_subset htrim hrightSync hxRightSeam
    rcases (L.G).crosscutSet_incident_of_mem_levelLeftHair c
        (nextLevelAddress L.next.level (L.rightmostAddress a))
        hxc hxHair with hlm | hlm
    · right
      right
      rw [← hlm, L.nextLevelAddress_rightmostAddress a]
      exact L.leftmostAddress_mem_addresses (nextLevelAddress n a)
    · have hc : c = L.rightmostAddress a := by
        have := congrArg (prevLevelAddress L.next.level) hlm
        simpa using this.symm
      exact Or.inr (Or.inl (hc ▸ L.rightmostAddress_mem_addresses a))

/-- **Adjacent-window agreement of consecutive raw parametrizations.**  At
every point of the shared polygon between two consecutive Moise bands, the
raw outer restriction of the earlier band and the raw inner restriction of
the later band land in scaled master windows that are equal or cyclically
adjacent at the earlier level. -/
theorem rawBoundary_mem_masterArcImage_tripled
    (L₁ : RecursiveInsideCollarStep.Later (L.G) L.next.one_le_level)
    (m : ℕ)
    (houtward₀ : ∀ c : LevelAddress n,
      (F.synchronizedPolygonalCircle hn).closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (houtward₁ : ∀ c : LevelAddress L.next.level,
      ((L.G).synchronizedPolygonalCircle
            L.next.one_le_level).closedRegion ∩
          (L₁.moiseBandPolygonalCircle c).closedRegion =
        range ((L.G).synchronizedCrosscutPath c))
    (x : ((L.G).synchronizedPolygonalCircle L.next.one_le_level).carrier) :
    ∃ a : LevelAddress n,
      (L.markedMoiseRawOuterBoundaryMap m houtward₀ x : Plane) ∈
        I.masterArcImage (m + 1) a ∧
      (L₁.markedMoiseRawInnerBoundaryMap (m + 1) houtward₁ x : Plane) ∈
        I.masterArcImage (m + 1) (prevLevelAddress n a) ∪
          (I.masterArcImage (m + 1) a ∪
            I.masterArcImage (m + 1) (nextLevelAddress n a)) := by
  have hxCells := L.childCircle_carrier_subset_iUnion_moiseBandCarrier x.2
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxCells
  have hxCellCarrier : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).carrier := by
    rw [L.moiseBandPolygonalCircle_carrier]
    exact hxa
  refine ⟨a, ?_, ?_⟩
  · exact I.range_indexedTargetBoundarySplit_first_subset_masterArcImage
      (m + 1) a
      (L.markedMoiseRawOuterBoundaryMap_mem_targetArc m houtward₀ a
        x hxCellCarrier)
  · have hxUnion : (x : Plane) ∈
        ⋃ c : LevelAddress L.next.level,
          range ((L.G).synchronizedCrosscutPath c) := by
      rw [← (L.G).carrier_synchronizedPolygonalCircle L.next.one_le_level]
      exact x.2
    obtain ⟨c, t, ht⟩ := Set.mem_iUnion.mp hxUnion
    have hxEq : x = ⟨(L.G).synchronizedCrosscutPath c t, by
        rw [ht]
        exact x.2⟩ :=
      Subtype.ext ht.symm
    have hvmem : (L₁.markedMoiseRawInnerBoundaryMap (m + 1) houtward₁ x :
        Plane) ∈ range (I.indexedTargetBoundarySplit (m + 1) c).first := by
      rw [hxEq, L₁.markedMoiseRawInnerBoundaryMap_apply_crosscut (m + 1)
        houtward₁ c t]
      exact ⟨t, rfl⟩
    have hxSet : (x : Plane) ∈ (L.G).synchronizedCrosscutSet c := by
      rw [← (L.G).range_synchronizedCrosscutPath_eq_set c]
      exact ⟨t, ht⟩
    have hcmem := I.range_indexedTargetBoundarySplit_first_subset_masterArcImage
      (m + 1) c hvmem
    rcases L.crosscut_block_near_of_mem_moiseBandCarrier c a hxSet hxa
      with hc | hc | hc
    · exact Or.inl (I.masterArcImage_mono (m + 1)
        (L.levelArc_curveArcPlane_subset_of_mem_addresses hc) hcmem)
    · exact Or.inr (Or.inl (I.masterArcImage_mono (m + 1)
        (L.levelArc_curveArcPlane_subset_of_mem_addresses hc) hcmem))
    · exact Or.inr (Or.inr (I.masterArcImage_mono (m + 1)
        (L.levelArc_curveArcPlane_subset_of_mem_addresses hc) hcmem))

end RecursiveInsideCollarStep.Later

end JordanCircle.InitialAngularArcs

end

end Schoenflies
