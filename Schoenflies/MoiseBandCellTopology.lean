import Schoenflies.MoiseBandCellBounds

/-!
# Topological placement of the recursive Moise band cells

The metric estimates alone do not identify the side of each polygonal cell.
Here we first prove that every raw edge and retained-hair junction lies in the
original Jordan inside, and hence so does the complete bounded polygonal
cell.
-/

namespace Schoenflies

open Metric Set Function AffineMap
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InsideAccessHair

variable {J : JordanCircle} {q : Plane}

/-- A segment joining two inside points on the same access hair stays in the
Jordan inside.  The only point of the full hair not known a priori to be
inside is its boundary base, and positivity of the affine hair parameters
rules that point out of the intervening segment. -/
theorem segment_subset_inside_of_endpoints_mem_inside
    (H : J.InsideAccessHair q) (hq : q ∈ J.carrier)
    (x y : H.carrier) (hx : (x : Plane) ∈ J.inside)
    (hy : (y : Plane) ∈ J.inside) :
    segment ℝ (x : Plane) (y : Plane) ⊆ J.inside := by
  intro z hz
  have hzHair : z ∈ H.carrier :=
    (convex_segment q H.tip).segment_subset x.2 y.2 hz
  rcases H.carrier_subset hzHair with hzInside | hzBase
  · exact hzInside
  · have hzEq : z = q := mem_singleton_iff.mp hzBase
    let z' : H.carrier := ⟨z, hzHair⟩
    have hzParam : H.carrierParameter z' = 0 := by
      have hzSubtype : z' = ⟨q, H.base_mem⟩ := by
        apply Subtype.ext
        exact hzEq
      rw [hzSubtype, H.carrierParameter_base]
    have hxPos := H.carrierParameter_pos_of_mem_inside hq x hx
    have hyPos := H.carrierParameter_pos_of_mem_inside hq y hy
    by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
    · have hlower :=
        (H.carrierParameter_bounds_of_mem_segment x y hxy hz).1
      change H.carrierParameter x ≤ H.carrierParameter z' at hlower
      rw [hzParam] at hlower
      linarith
    · have hyx : H.carrierParameter y ≤ H.carrierParameter x :=
        le_of_not_ge hxy
      have hlower :=
        (H.carrierParameter_bounds_of_mem_segment y x hyx
          (by simpa [segment_symm] using hz)).1
      change H.carrierParameter y ≤ H.carrierParameter z' at hlower
      rw [hzParam] at hlower
      linarith

/-- Three points occurring in order on one access hair determine nested
segments.  This elementary order lemma is useful at a junction where two
later raw endpoints are both shallower than the retained parent endpoint. -/
theorem segment_subset_segment_of_parameter_le
    (H : J.InsideAccessHair q) (x y p : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y)
    (hyp : H.carrierParameter y ≤ H.carrierParameter p) :
    segment ℝ (x : Plane) (y : Plane) ⊆
      segment ℝ (x : Plane) (p : Plane) := by
  apply (convex_segment (x : Plane) (p : Plane)).segment_subset
  · exact left_mem_segment ℝ _ _
  · by_cases hxp : H.carrierParameter x = H.carrierParameter p
    · have hxyParam : H.carrierParameter x = H.carrierParameter y :=
        le_antisymm hxy (hyp.trans_eq hxp.symm)
      have hsub : x = y := H.carrierParameter_injective hxyParam
      simpa [hsub] using left_mem_segment ℝ (x : Plane) (p : Plane)
    · have hpos : 0 < H.carrierParameter p - H.carrierParameter x :=
        sub_pos.mpr (lt_of_le_of_ne (hxy.trans hyp) hxp)
      rw [segment_eq_image_lineMap]
      refine ⟨(H.carrierParameter y - H.carrierParameter x) /
          (H.carrierParameter p - H.carrierParameter x), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr hxy) hpos.le
        · exact (div_le_one hpos).mpr (sub_le_sub_right hyp _)
      · rw [← H.lineMap_carrierParameter x,
          ← H.lineMap_carrierParameter y,
          ← H.lineMap_carrierParameter p]
        have hden : H.carrierParameter p - H.carrierParameter x ≠ 0 :=
          ne_of_gt hpos
        have hcoordinate :
            (1 - (H.carrierParameter y - H.carrierParameter x) /
                (H.carrierParameter p - H.carrierParameter x)) *
                H.carrierParameter x +
              ((H.carrierParameter y - H.carrierParameter x) /
                (H.carrierParameter p - H.carrierParameter x)) *
                H.carrierParameter p = H.carrierParameter y := by
          field_simp [hden]
          ring
        rw [show lineMap
              (lineMap q H.tip (H.carrierParameter x))
              (lineMap q H.tip (H.carrierParameter p))
              ((H.carrierParameter y - H.carrierParameter x) /
                (H.carrierParameter p - H.carrierParameter x)) =
            lineMap q H.tip
              ((1 - (H.carrierParameter y - H.carrierParameter x) /
                  (H.carrierParameter p - H.carrierParameter x)) *
                  H.carrierParameter x +
                ((H.carrierParameter y - H.carrierParameter x) /
                  (H.carrierParameter p - H.carrierParameter x)) *
                  H.carrierParameter p) by
            simp only [lineMap_apply_module]
            module]
        rw [hcoordinate]

/-- Tail segments on one access hair are nested in the opposite direction
from the initial segments: if `x`, `y`, and `p` occur in that order, then
the tail from `y` to `p` is contained in the tail from `x` to `p`. -/
theorem tailSegment_subset_of_parameter_le
    (H : J.InsideAccessHair q) (x y p : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y)
    (hyp : H.carrierParameter y ≤ H.carrierParameter p) :
    segment ℝ (y : Plane) (p : Plane) ⊆
      segment ℝ (x : Plane) (p : Plane) := by
  apply (convex_segment (x : Plane) (p : Plane)).segment_subset
  · exact H.segment_subset_segment_of_parameter_le x y p hxy hyp
      (right_mem_segment ℝ _ _)
  · exact right_mem_segment ℝ _ _

/-- Consequently, two tails ending at the same deeper hair point intersect
in the tail whose initial point is deeper. -/
theorem tailSegment_inter_tailSegment_eq_of_parameter_le
    (H : J.InsideAccessHair q) (x y p : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y)
    (hyp : H.carrierParameter y ≤ H.carrierParameter p) :
    segment ℝ (x : Plane) (p : Plane) ∩
        segment ℝ (y : Plane) (p : Plane) =
      segment ℝ (y : Plane) (p : Plane) := by
  exact Set.inter_eq_right.mpr
    (H.tailSegment_subset_of_parameter_le x y p hxy hyp)

/-- If two points are both no deeper than a third point of the same hair,
their joining segment is covered by the two segments to that third point. -/
theorem segment_subset_union_segments_of_parameter_le
    (H : J.InsideAccessHair q) (x y p : H.carrier)
    (hxp : H.carrierParameter x ≤ H.carrierParameter p)
    (hyp : H.carrierParameter y ≤ H.carrierParameter p) :
    segment ℝ (x : Plane) (y : Plane) ⊆
      segment ℝ (x : Plane) (p : Plane) ∪
        segment ℝ (p : Plane) (y : Plane) := by
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · exact (H.segment_subset_segment_of_parameter_le x y p hxy hyp).trans
      Set.subset_union_left
  · have hyx : H.carrierParameter y ≤ H.carrierParameter x :=
      le_of_not_ge hxy
    intro z hz
    apply Or.inr
    rw [segment_symm]
    exact H.segment_subset_segment_of_parameter_le y x p hyx hxp
      (by simpa [segment_symm] using hz)

end InsideAccessHair

namespace InitialAngularArcs

variable {J : JordanCircle}

/-- Every address at a deeper complete level belongs to the descendant
block of some address at the parent level. -/
theorem exists_mem_descendantAddresses (n k : ℕ)
    (b : LevelAddress (n + k)) :
    ∃ a : LevelAddress n, b ∈ descendantAddresses a k := by
  have hb := mem_orderedLevelAddresses (n + k) b
  rw [← flatMap_descendantAddresses_orderedLevelAddresses n k,
    List.mem_flatMap] at hb
  obtain ⟨a, _ha, hba⟩ := hb
  exact ⟨a, hba⟩

namespace RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private noncomputable abbrev childIndex
    (b : LevelAddress L.next.level) :
    Fin (levelAddressCount L.next.level) :=
  levelIndexOf L.next.level b

/-- The transported descendant blocks used by a later step cover its whole
child address level. -/
theorem exists_parentAddress (b : LevelAddress L.next.level) :
    ∃ a : LevelAddress n, b ∈ L.addresses a := by
  let b₀ : LevelAddress (n + L.depth) :=
    _root_.cast (congrArg LevelAddress L.parentLevel_add_depth.symm) b
  obtain ⟨a, hb₀⟩ := exists_mem_descendantAddresses n L.depth b₀
  refine ⟨a, ?_⟩
  rw [addresses, List.mem_map]
  refine ⟨b₀, hb₀, ?_⟩
  dsimp only [b₀]
  simp

/-- The exact non-retracing boundary of every Moise band cell lies in the
inside of the original Jordan curve. -/
theorem moiseBandCarrier_subset_inside (a : LevelAddress n) :
    L.moiseBandCarrier a ⊆ J.inside := by
  let G := L.next.family.forgetObstacle
  rw [moiseBandCarrier]
  intro x hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hj, hxSegment⟩ := Set.mem_iUnion.mp hxj
  rw [moiseBandSegments, List.mem_append] at hj
  rcases hj with hjOpen | hjRight
  · rw [List.mem_append] at hjOpen
    rcases hjOpen with hjParentLeft | hjChild
    · rw [List.mem_append] at hjParentLeft
      rcases hjParentLeft with hjParent | hjLeft
      · obtain ⟨i, rfl⟩ := L.parent_index_of_mem_parentMoiseSegments hjParent
        change x ∈ segment ℝ (F.edgeFinish ⟨a, i⟩)
          (F.edgeStart ⟨a, i⟩) at hxSegment
        apply F.synchronizedCrosscutSet_subset_inside a
        apply F.range_synchronizedCrosscutPath_subset a
        apply F.edgeSegment_subset_crosscutRange ⟨a, i⟩
        simpa [LevelAvoidingJoinFamily.edgeSegment, segment_symm]
          using hxSegment
      · have hjEq : j = MoiseBandSegmentAddress.leftSide L := by
          simpa only [List.mem_singleton] using hjLeft
        subst j
        let H := I.levelLeftHair a
        let parent : H.carrier :=
          ⟨F.leftSynchronizedPoint a,
            F.leftSynchronizedPoint_mem_leftHair a⟩
        let child : H.carrier :=
          ⟨G.trimmedLeftPoint (L.childIndex (L.leftmostAddress a)), by
            rw [← L.leftmostAddress_leftHair_carrier a]
            exact (G.leftHairPoint (L.leftmostAddress a)).2⟩
        exact H.segment_subset_inside_of_endpoints_mem_inside
          (J.curvePoint (I.levelArc a).left).2 parent child
          (F.leftSynchronizedPoint_inside a)
          (G.trimmedLeftPoint_inside (L.leftmostAddress a)) hxSegment
    · rcases L.child_or_junction_with_addresses_of_mem
          (L.addresses_isChain a) hjChild with hraw | hjunction
      · obtain ⟨e, _heMem, rfl⟩ := hraw
        change x ∈ segment ℝ (G.trimmedEdgeFinish e)
          (G.trimmedEdgeStart e) at hxSegment
        exact (G.range_trimmedPath_subset_controlled (L.childIndex e.1)
          (G.trimmedEdgeSegment_subset_trimmedPathRange e
            (by simpa [LevelAvoidingJoinFamily.trimmedEdgeSegment,
              segment_symm] using hxSegment))).1
      · obtain ⟨b, d, _hbMem, _hdMem, hbd, rfl⟩ := hjunction
        let H := I.levelRightHair b
        let left : H.carrier :=
          ⟨G.trimmedRightPoint (L.childIndex b),
            (G.rightHairPoint b).2⟩
        let right : H.carrier :=
          ⟨G.trimmedLeftPoint (L.childIndex d), by
            rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq b d hbd]
            exact (G.leftHairPoint d).2⟩
        exact H.segment_subset_inside_of_endpoints_mem_inside
          (J.curvePoint (I.levelArc b).right).2 left right
          (G.trimmedRightPoint_inside b) (G.trimmedLeftPoint_inside d)
          hxSegment
  · have hjEq : j = MoiseBandSegmentAddress.rightSide L := by
      simpa only [List.mem_singleton] using hjRight
    subst j
    let H := I.levelRightHair a
    let child : H.carrier :=
      ⟨G.trimmedRightPoint (L.childIndex (L.rightmostAddress a)), by
        rw [← L.rightmostAddress_rightHair_carrier a]
        exact (G.rightHairPoint (L.rightmostAddress a)).2⟩
    let parent : H.carrier :=
      ⟨F.rightSynchronizedPoint a,
        F.rightSynchronizedPoint_mem_rightHair a⟩
    exact H.segment_subset_inside_of_endpoints_mem_inside
      (J.curvePoint (I.levelArc a).right).2 child parent
      (G.trimmedRightPoint_inside (L.rightmostAddress a))
      (F.rightSynchronizedPoint_inside a) hxSegment

/-- The complete bounded polygonal region of a Moise band cell is contained
in the original Jordan inside. -/
theorem moiseBandClosedRegion_subset_inside (a : LevelAddress n) :
    (L.moiseBandPolygonalCircle a).closedRegion ⊆ J.inside := by
  let P := L.moiseBandPolygonalCircle a
  have hPcarrier : P.carrier ⊆ J.inside := by
    rw [L.moiseBandPolygonalCircle_carrier a]
    exact L.moiseBandCarrier_subset_inside a
  have hcarrier : P.toJordanCircle.carrier ⊆ J.inside ∪ J.carrier := by
    rw [P.carrier_toJordanCircle]
    exact hPcarrier.trans Set.subset_union_left
  have hinterior : P.interiorRegion ⊆ J.inside := by
    rw [← P.inside_toJordanCircle]
    exact J.inside_subset_inside_of_carrier_subset P.toJordanCircle hcarrier
  rw [P.closedRegion_eq_union]
  exact union_subset hinterior hPcarrier

/-- The old synchronized crosscut assigned to `a` is literally part of the
corresponding Moise cell boundary. -/
theorem parentCrosscutRange_subset_moiseBandCarrier
    (a : LevelAddress n) :
    range (F.synchronizedCrosscutPath a) ⊆ L.moiseBandCarrier a := by
  intro x hx
  have hxCarrier : x ∈
      (F.synchronizedCrosscutCarrierLine a).data.segmentCarrier := by
    rw [F.segmentCarrier_synchronizedCrosscutCarrierLine_eq_range a]
    exact hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCarrier
  rw [moiseBandCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨MoiseBandSegmentAddress.parent L ⟨a, i⟩, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, ?_⟩
  · have hedge : (⟨a, i⟩ : F.LevelEdgeAddress) ∈ F.edgeBlock a := by
      simp [LevelAvoidingJoinFamily.edgeBlock]
    have hparent : MoiseBandSegmentAddress.parent L ⟨a, i⟩ ∈
        L.parentMoiseSegments a := by
      rw [parentMoiseSegments, List.mem_map]
      exact ⟨⟨a, i⟩, by simpa using hedge, rfl⟩
    simp [moiseBandSegments, hparent]
  · change x ∈ segment ℝ (F.edgeFinish ⟨a, i⟩)
      (F.edgeStart ⟨a, i⟩)
    change x ∈ segment ℝ (F.edgeStart ⟨a, i⟩)
      (F.edgeFinish ⟨a, i⟩) at hxi
    simpa [segment_symm] using hxi

/-- Consequently the whole old polygonal collar is covered by the Moise
band boundaries. -/
theorem parentCircle_carrier_subset_iUnion_moiseBandCarrier :
    (F.synchronizedPolygonalCircle hn).carrier ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  rw [F.carrier_synchronizedPolygonalCircle hn]
  intro x hx
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr
    ⟨a, L.parentCrosscutRange_subset_moiseBandCarrier a hxa⟩

/-- Every raw edge of a listed child crosscut occurs in the recursive child
route of the parent band cell. -/
theorem childSegment_mem_childMoiseSegments_of_mem
    {l : List (LevelAddress L.next.level)}
    {b : LevelAddress L.next.level} (hb : b ∈ l)
    (i : Fin
      (L.next.family.forgetObstacle.trimmedCrosscutCarrierLine b).data.n) :
    MoiseBandSegmentAddress.child L ⟨b, i⟩ ∈
      L.childMoiseSegments l := by
  induction l with
  | nil => simp at hb
  | cons d tail ih =>
      cases tail with
      | nil =>
          have hbd : b = d := by simpa using hb
          subst b
          rw [childMoiseSegments, reversedTrimmedBlock, List.mem_map]
          refine ⟨⟨d, i⟩, ?_, rfl⟩
          rw [List.mem_reverse, LevelAvoidingJoinFamily.trimmedEdgeBlock,
            List.mem_ofFn']
          exact ⟨i, rfl⟩
      | cons e tail =>
          rw [childMoiseSegments, List.mem_append]
          rcases List.mem_cons.mp hb with rfl | hbTail
          · left
            rw [List.mem_append]
            left
            rw [reversedTrimmedBlock, List.mem_map]
            refine ⟨⟨b, i⟩, ?_, rfl⟩
            rw [List.mem_reverse, LevelAvoidingJoinFamily.trimmedEdgeBlock,
              List.mem_ofFn']
            exact ⟨i, rfl⟩
          · right
            exact ih hbTail

/-- The original un-loop-erased trimmed path of every listed child is part
of its parent Moise cell boundary. -/
theorem childTrimmedPathRange_subset_moiseBandCarrier
    (a : LevelAddress n) {b : LevelAddress L.next.level}
    (hb : b ∈ L.addresses a) :
    range (L.next.family.forgetObstacle.trimmedPath (L.childIndex b)) ⊆
      L.moiseBandCarrier a := by
  let G := L.next.family.forgetObstacle
  intro x hx
  have hxCarrier : x ∈
      (G.trimmedCrosscutCarrierLine b).data.segmentCarrier := by
    rw [G.segmentCarrier_trimmedCrosscutCarrierLine_eq_range b]
    exact hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCarrier
  rw [moiseBandCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨MoiseBandSegmentAddress.child L ⟨b, i⟩, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, ?_⟩
  · have hchild := L.childSegment_mem_childMoiseSegments_of_mem hb i
    simp [moiseBandSegments, hchild]
  · change x ∈ segment ℝ (G.trimmedEdgeFinish ⟨b, i⟩)
      (G.trimmedEdgeStart ⟨b, i⟩)
    change x ∈ segment ℝ (G.trimmedEdgeStart ⟨b, i⟩)
      (G.trimmedEdgeFinish ⟨b, i⟩) at hxi
    simpa [segment_symm] using hxi

/-- A non-head member of a chained child block has an immediately preceding
member, and the corresponding raw-hair junction is present in the recursive
Moise route. -/
theorem exists_leftNeighbor_junction_mem_childMoiseSegments
    {l : List (LevelAddress L.next.level)} (hl : l ≠ [])
    (hchain : l.IsChain I.LevelAdjacent)
    {b : LevelAddress L.next.level} (hb : b ∈ l)
    (hbHead : b ≠ l.head hl) :
    ∃ c : LevelAddress L.next.level,
      I.LevelAdjacent c b ∧
        MoiseBandSegmentAddress.junction L c b ∈
          L.childMoiseSegments l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons d tail ih =>
      cases tail with
      | nil =>
          have hbd : b = d := by simpa using hb
          exact (hbHead (by simpa [hbd])).elim
      | cons e rest =>
          have hbNeD : b ≠ d := by
            intro hbd
            apply hbHead
            simpa [hbd]
          have hbTail : b ∈ e :: rest := by
            rcases List.mem_cons.mp hb with hbd | hbTail
            · exact (hbNeD hbd).elim
            · exact hbTail
          by_cases hbe : b = e
          · subst b
            refine ⟨d, hchain.rel, ?_⟩
            rw [childMoiseSegments, List.mem_append]
            left
            rw [List.mem_append]
            exact Or.inr (by simp)
          · obtain ⟨c, hce, hj⟩ := ih (by simp) hchain.tail hbTail (by
              simpa using hbe)
            refine ⟨c, hce, ?_⟩
            rw [childMoiseSegments, List.mem_append]
            exact Or.inr hj

/-- The corrected extreme left side is literally part of the Moise cell
boundary. -/
theorem rawLeftSide_subset_moiseBandCarrier (a : LevelAddress n) :
    segment ℝ (F.leftSynchronizedPoint a)
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (L.leftmostAddress a))) ⊆
      L.moiseBandCarrier a := by
  intro x hx
  rw [moiseBandCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨MoiseBandSegmentAddress.leftSide L, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, hx⟩
  simp [moiseBandSegments]

/-- The corrected extreme right side is likewise part of the Moise cell
boundary. -/
theorem rawRightSide_subset_moiseBandCarrier (a : LevelAddress n) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint
          (L.childIndex (L.rightmostAddress a)))
        (F.rightSynchronizedPoint a) ⊆
      L.moiseBandCarrier a := by
  intro x hx
  rw [moiseBandCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨MoiseBandSegmentAddress.rightSide L, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, hx⟩
  simp [moiseBandSegments]

/-- Any junction label in the recursive child route contributes its whole
retained-hair segment to the Moise carrier. -/
theorem junctionSegment_subset_moiseBandCarrier
    (a : LevelAddress n) {b c : LevelAddress L.next.level}
    (hj : MoiseBandSegmentAddress.junction L b c ∈
      L.childMoiseSegments (L.addresses a)) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex c)) ⊆
      L.moiseBandCarrier a := by
  intro x hx
  rw [moiseBandCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨MoiseBandSegmentAddress.junction L b c, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, hx⟩
  simp [moiseBandSegments, hj]

/-- Both raw endpoints of a child crosscut belong to its parent Moise
carrier. -/
theorem childRawEndpoints_mem_moiseBandCarrier
    (a : LevelAddress n) {b : LevelAddress L.next.level}
    (hb : b ∈ L.addresses a) :
    L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex b) ∈
        L.moiseBandCarrier a ∧
      L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b) ∈
        L.moiseBandCarrier a := by
  constructor
  · exact L.childTrimmedPathRange_subset_moiseBandCarrier a hb
      (Path.target_mem_range
        (L.next.family.forgetObstacle.trimmedPath (L.childIndex b)))
  · exact L.childTrimmedPathRange_subset_moiseBandCarrier a hb
      (Path.source_mem_range
        (L.next.family.forgetObstacle.trimmedPath (L.childIndex b)))

/-- Away from the first child of a parent block, the synchronized left
extension is covered by that same parent Moise cell. -/
theorem childLeftExtension_subset_moiseBandCarrier_of_ne_leftmost
    (a : LevelAddress n) {b : LevelAddress L.next.level}
    (hb : b ∈ L.addresses a) (hbLeft : b ≠ L.leftmostAddress a) :
    segment ℝ
        (L.next.family.forgetObstacle.leftSynchronizedPoint b)
        (L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex b)) ⊆
      L.moiseBandCarrier a := by
  let G := L.next.family.forgetObstacle
  have hbHead : b ≠ (L.addresses a).head (L.addresses_nonempty a) := by
    simpa using hbLeft
  obtain ⟨c, hcb, hj⟩ :=
    L.exists_leftNeighbor_junction_mem_childMoiseSegments
      (L.addresses_nonempty a) (L.addresses_isChain a) hb hbHead
  have hnext : nextLevelAddress L.next.level c = b :=
    ((I.levelRightPoint_eq_levelLeftPoint_iff c b).mp hcb).symm
  have hsync : G.leftSynchronizedPoint b =
      G.synchronizedPoint c b hcb := by
    subst b
    simp [LevelAvoidingJoinFamily.leftSynchronizedPoint]
  rcases G.synchronizedPoint_eq_right_or_left c b hcb with
    hright | hleft
  · rw [hsync, hright]
    exact L.junctionSegment_subset_moiseBandCarrier a hj
  · rw [hsync, hleft, segment_same]
    exact singleton_subset_iff.mpr
      (L.childRawEndpoints_mem_moiseBandCarrier a hb).1

/-- The raw junction between the last child of one parent and the first
child of the next parent is covered by the two extreme side segments. -/
theorem extremeChildJunction_subset_union_moiseBandCarrier
    (a : LevelAddress n) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint
          (L.childIndex
            (L.rightmostAddress (prevLevelAddress n a))))
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (L.leftmostAddress a))) ⊆
      L.moiseBandCarrier (prevLevelAddress n a) ∪
        L.moiseBandCarrier a := by
  let G := L.next.family.forgetObstacle
  let p := prevLevelAddress n a
  let b := L.leftmostAddress a
  let c := L.rightmostAddress p
  let H := I.levelRightHair p
  let x : H.carrier :=
    ⟨G.trimmedRightPoint (L.childIndex c), by
      rw [← L.rightmostAddress_rightHair_carrier p]
      exact (G.rightHairPoint c).2⟩
  have hpa : I.LevelAdjacent p a := by
    dsimp only [p]
    exact I.levelAdjacent_prevLevelAddress n a
  let y : H.carrier :=
    ⟨G.trimmedLeftPoint (L.childIndex b), by
      rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq p a hpa]
      rw [← L.leftmostAddress_leftHair_carrier a]
      exact (G.leftHairPoint b).2⟩
  let s : H.carrier :=
    ⟨F.rightSynchronizedPoint p,
      F.rightSynchronizedPoint_mem_rightHair p⟩
  have hxs : H.carrierParameter x < H.carrierParameter s := by
    dsimp only [H, x, s]
    exact L.rightmost_trimmed_carrierParameter_lt_parent p
  have hpnext : nextLevelAddress n p = a := by simp [p]
  have hsyncParent : F.rightSynchronizedPoint p =
      F.leftSynchronizedPoint a := by
    calc
      F.rightSynchronizedPoint p =
          F.leftSynchronizedPoint (nextLevelAddress n p) :=
        F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint p
      _ = F.leftSynchronizedPoint a := by rw [hpnext]
  have hys : H.carrierParameter y < H.carrierParameter s := by
    apply H.carrierParameter_lt_of_dist_base_lt
    change dist (J.curvePoint (I.levelArc p).right : Plane)
        (G.trimmedLeftPoint (L.childIndex b)) <
      dist (J.curvePoint (I.levelArc p).right : Plane)
        (F.rightSynchronizedPoint p)
    rw [hpa, hsyncParent]
    exact L.next.dist_child_trimmedLeft_lt_parent_left F hn a b
      (by simp [b, L.levelArc_leftmostAddress_left a])
  have hbridge := H.segment_subset_union_segments_of_parameter_le
    x y s hxs.le hys.le
  intro z hz
  rcases hbridge hz with hzPrev | hzCurrent
  · exact Or.inl (L.rawRightSide_subset_moiseBandCarrier p hzPrev)
  · apply Or.inr
    apply L.rawLeftSide_subset_moiseBandCarrier a
    change z ∈ segment ℝ (F.rightSynchronizedPoint p)
      (G.trimmedLeftPoint (L.childIndex b)) at hzCurrent
    rw [hsyncParent] at hzCurrent
    simpa only [b] using hzCurrent

/-- At the first child of a parent block, its synchronized left extension
is covered jointly by the preceding parent's right side and the current
parent's left side. -/
theorem leftmostChildLeftExtension_subset_union_moiseBandCarrier
    (a : LevelAddress n) :
    segment ℝ
        (L.next.family.forgetObstacle.leftSynchronizedPoint
          (L.leftmostAddress a))
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (L.leftmostAddress a))) ⊆
      L.moiseBandCarrier (prevLevelAddress n a) ∪
        L.moiseBandCarrier a := by
  let G := L.next.family.forgetObstacle
  let p := prevLevelAddress n a
  let b := L.leftmostAddress a
  let c := L.rightmostAddress p
  have hnext : nextLevelAddress L.next.level c = b := by
    dsimp only [b, c, p]
    rw [L.nextLevelAddress_rightmostAddress]
    simp
  have hsync : G.leftSynchronizedPoint b =
      G.rightSynchronizedPoint c := by
    rw [← hnext]
    exact (G.rightSynchronizedPoint_next_eq_leftSynchronizedPoint c).symm
  have hsyncRaw :
      G.rightSynchronizedPoint c =
          G.trimmedRightPoint (L.childIndex c) ∨
        G.rightSynchronizedPoint c =
          G.trimmedLeftPoint (L.childIndex b) := by
    have h := G.synchronizedPoint_eq_right_or_left c
      (nextLevelAddress L.next.level c)
      (I.levelAdjacent_nextLevelAddress L.next.level c)
    have h' :
        G.rightSynchronizedPoint c =
            G.trimmedRightPoint (L.childIndex c) ∨
          G.rightSynchronizedPoint c =
            G.trimmedLeftPoint
              (L.childIndex (nextLevelAddress L.next.level c)) := by
      simpa [LevelAvoidingJoinFamily.rightSynchronizedPoint] using h
    exact h'.imp id fun hleft => hleft.trans <|
      congrArg (fun d => G.trimmedLeftPoint (L.childIndex d)) hnext
  rcases hsyncRaw with hright | hleft
  · rw [hsync, hright]
    let H := I.levelRightHair p
    let x : H.carrier :=
      ⟨G.trimmedRightPoint (L.childIndex c), by
        rw [← L.rightmostAddress_rightHair_carrier p]
        exact (G.rightHairPoint c).2⟩
    have hpa : I.LevelAdjacent p a := by
      dsimp only [p]
      exact I.levelAdjacent_prevLevelAddress n a
    let y : H.carrier :=
      ⟨G.trimmedLeftPoint (L.childIndex b), by
        rw [I.levelRightHair_carrier_eq_levelLeftHair_of_eq p a hpa]
        rw [← L.leftmostAddress_leftHair_carrier a]
        exact (G.leftHairPoint b).2⟩
    let s : H.carrier :=
      ⟨F.rightSynchronizedPoint p,
        F.rightSynchronizedPoint_mem_rightHair p⟩
    have hxs : H.carrierParameter x < H.carrierParameter s := by
      dsimp only [H, x, s]
      exact L.rightmost_trimmed_carrierParameter_lt_parent p
    have hpnext : nextLevelAddress n p = a := by simp [p]
    have hsyncParent : F.rightSynchronizedPoint p =
        F.leftSynchronizedPoint a := by
      calc
        F.rightSynchronizedPoint p =
            F.leftSynchronizedPoint (nextLevelAddress n p) :=
          F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint p
        _ = F.leftSynchronizedPoint a := by rw [hpnext]
    have hys : H.carrierParameter y < H.carrierParameter s := by
      apply H.carrierParameter_lt_of_dist_base_lt
      change dist (J.curvePoint (I.levelArc p).right : Plane)
          (G.trimmedLeftPoint (L.childIndex b)) <
        dist (J.curvePoint (I.levelArc p).right : Plane)
          (F.rightSynchronizedPoint p)
      rw [hpa, hsyncParent]
      exact L.next.dist_child_trimmedLeft_lt_parent_left F hn a b
        (by simp [b, L.levelArc_leftmostAddress_left a])
    have hbridge := H.segment_subset_union_segments_of_parameter_le
      x y s hxs.le hys.le
    intro z hz
    rcases hbridge hz with hzPrev | hzCurrent
    · exact Or.inl (L.rawRightSide_subset_moiseBandCarrier p hzPrev)
    · apply Or.inr
      apply L.rawLeftSide_subset_moiseBandCarrier a
      change z ∈ segment ℝ (F.rightSynchronizedPoint p)
        (G.trimmedLeftPoint (L.childIndex b)) at hzCurrent
      rw [hsyncParent] at hzCurrent
      simpa only [b] using hzCurrent
  · rw [hsync, hleft, segment_same]
    have hb : b ∈ L.addresses a := by
      have hhead := List.head_mem (L.addresses_nonempty a)
      rw [L.addresses_head a] at hhead
      simpa only [b] using hhead
    exact singleton_subset_iff.mpr <| Or.inr <|
      (L.childRawEndpoints_mem_moiseBandCarrier a hb).1

/-- Every child left synchronization extension is covered by the union of
the Moise band boundaries. -/
theorem childLeftExtension_subset_iUnion_moiseBandCarrier
    (b : LevelAddress L.next.level) :
    segment ℝ
        (L.next.family.forgetObstacle.leftSynchronizedPoint b)
        (L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex b)) ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  obtain ⟨a, hb⟩ := L.exists_parentAddress b
  by_cases hleft : b = L.leftmostAddress a
  · subst b
    intro x hx
    rcases L.leftmostChildLeftExtension_subset_union_moiseBandCarrier a hx with
      hxPrev | hxCurrent
    · exact Set.mem_iUnion.mpr ⟨prevLevelAddress n a, hxPrev⟩
    · exact Set.mem_iUnion.mpr ⟨a, hxCurrent⟩
  · exact (L.childLeftExtension_subset_moiseBandCarrier_of_ne_leftmost
      a hb hleft).trans (Set.subset_iUnion (fun a => L.moiseBandCarrier a) a)

/-- Every raw junction between cyclically successive child crosscuts is
covered by the Moise band boundaries, whether it lies inside one parent
block or between two consecutive blocks. -/
theorem childCyclicJunction_subset_iUnion_moiseBandCarrier
    (b : LevelAddress L.next.level) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (nextLevelAddress L.next.level b))) ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  let d := nextLevelAddress L.next.level b
  obtain ⟨a, hd⟩ := L.exists_parentAddress d
  by_cases hdLeft : d = L.leftmostAddress a
  · let c := L.rightmostAddress (prevLevelAddress n a)
    have hcnext : nextLevelAddress L.next.level c = d := by
      calc
        nextLevelAddress L.next.level c =
            L.leftmostAddress
              (nextLevelAddress n (prevLevelAddress n a)) := by
          exact L.nextLevelAddress_rightmostAddress
            (prevLevelAddress n a)
        _ = L.leftmostAddress a := by simp
        _ = d := hdLeft.symm
    have hbc : b = c :=
      nextLevelAddress_injective L.next.level (by
        change nextLevelAddress L.next.level b =
          nextLevelAddress L.next.level c
        exact (rfl : d = d).trans hcnext.symm)
    intro x hx
    have hx' := hx
    rw [hbc, hcnext, hdLeft] at hx'
    have hxExtreme :=
      L.extremeChildJunction_subset_union_moiseBandCarrier a (by
        simpa only [c] using hx')
    rcases hxExtreme with hxPrev | hxCurrent
    · exact Set.mem_iUnion.mpr ⟨prevLevelAddress n a, hxPrev⟩
    · exact Set.mem_iUnion.mpr ⟨a, hxCurrent⟩
  · have hdHead : d ≠
        (L.addresses a).head (L.addresses_nonempty a) := by
      simpa using hdLeft
    obtain ⟨c, hcd, hj⟩ :=
      L.exists_leftNeighbor_junction_mem_childMoiseSegments
        (L.addresses_nonempty a) (L.addresses_isChain a) hd hdHead
    have hcnext : nextLevelAddress L.next.level c = d :=
      ((I.levelRightPoint_eq_levelLeftPoint_iff c d).mp hcd).symm
    have hcb : c = b :=
      nextLevelAddress_injective L.next.level (by
        change nextLevelAddress L.next.level c =
          nextLevelAddress L.next.level b
        exact hcnext)
    subst c
    exact (L.junctionSegment_subset_moiseBandCarrier a hj).trans
      (Set.subset_iUnion (fun a => L.moiseBandCarrier a) a)

/-- A synchronized right extension is a subsegment of the full raw bridge
to the next child. -/
theorem childRightExtension_subset_childCyclicJunction
    (b : LevelAddress L.next.level) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.rightSynchronizedPoint b) ⊆
      segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (nextLevelAddress L.next.level b))) := by
  let G := L.next.family.forgetObstacle
  have h := G.synchronizedPoint_eq_right_or_left b
    (nextLevelAddress L.next.level b)
    (I.levelAdjacent_nextLevelAddress L.next.level b)
  have h' : G.rightSynchronizedPoint b =
        G.trimmedRightPoint (L.childIndex b) ∨
      G.rightSynchronizedPoint b =
        G.trimmedLeftPoint
          (L.childIndex (nextLevelAddress L.next.level b)) := by
    simpa [LevelAvoidingJoinFamily.rightSynchronizedPoint] using h
  rcases h' with hright | hleft
  · rw [hright, segment_same]
    exact singleton_subset_iff.mpr (left_mem_segment ℝ _ _)
  · rw [hleft]

/-- Hence every child right synchronization extension is globally covered
by the Moise band boundaries. -/
theorem childRightExtension_subset_iUnion_moiseBandCarrier
    (b : LevelAddress L.next.level) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.rightSynchronizedPoint b) ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a :=
  (L.childRightExtension_subset_childCyclicJunction b).trans
    (L.childCyclicJunction_subset_iUnion_moiseBandCarrier b)

/-- Every raw trimmed child path is globally covered by the Moise band
boundaries. -/
theorem childTrimmedPathRange_subset_iUnion_moiseBandCarrier
    (b : LevelAddress L.next.level) :
    range (L.next.family.forgetObstacle.trimmedPath (L.childIndex b)) ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  obtain ⟨a, hb⟩ := L.exists_parentAddress b
  exact (L.childTrimmedPathRange_subset_moiseBandCarrier a hb).trans
    (Set.subset_iUnion (fun a => L.moiseBandCarrier a) a)

/-- The complete synchronized crosscut of every child, including both
hair extensions and its raw middle path, is globally covered. -/
theorem childSynchronizedCrosscutSet_subset_iUnion_moiseBandCarrier
    (b : LevelAddress L.next.level) :
    L.next.family.forgetObstacle.synchronizedCrosscutSet b ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  rintro x ((hxLeft | hxMiddle) | hxRight)
  · exact L.childLeftExtension_subset_iUnion_moiseBandCarrier b hxLeft
  · exact L.childTrimmedPathRange_subset_iUnion_moiseBandCarrier b hxMiddle
  · exact L.childRightExtension_subset_iUnion_moiseBandCarrier b hxRight

/-- Consequently the whole next synchronized polygonal collar is covered by
the finite family of Moise band boundaries. -/
theorem childCircle_carrier_subset_iUnion_moiseBandCarrier :
    (L.next.family.forgetObstacle.synchronizedPolygonalCircle
      L.next.one_le_level).carrier ⊆
      ⋃ a : LevelAddress n, L.moiseBandCarrier a := by
  let G := L.next.family.forgetObstacle
  rw [G.carrier_synchronizedPolygonalCircle L.next.one_le_level]
  intro x hx
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hx
  exact L.childSynchronizedCrosscutSet_subset_iUnion_moiseBandCarrier b
    (G.range_synchronizedCrosscutPath_subset b hxb)

end RecursiveInsideCollarStep.Later
end InitialAngularArcs
end JordanCircle

end

end Schoenflies
