import Schoenflies.AnnularSeparatorPairs
import Schoenflies.JordanThetaRegions
import Schoenflies.LocallyStraightSets

/-!
# The crosscut theorem for a polygonal annulus

For two disjoint straight crosscuts of a polygonal annulus, the two
complementary Jordan separators have closed bounded regions whose union is
the outer polygonal disk.  This is the finite-shell compatibility theorem
used to preserve cyclic order between consecutive polygonal levels.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.AnnularCrosscut.SeparatorPair

variable {P Q : PolygonalCircle} {A B : AnnularCrosscut P Q}
  (S : SeparatorPair A B)

/-- The full polygonal support of the shared bridge.  It differs from the
chosen bridge only by the complementary inner boundary arc. -/
def bridgeSupport (_S : SeparatorPair A B) : Set Plane :=
  range A.path ∪ (P.carrier ∪ range B.path)

/-- The only points at which the bridge support need not be locally a single
straight line: polygon vertices and the four joins to the crosscuts. -/
def exceptionalSet (_S : SeparatorPair A B) : Set Plane :=
  range P.vertex ∪
    {A.innerPoint, B.innerPoint, A.outerPoint, B.outerPoint}

theorem exceptionalSet_finite : S.exceptionalSet.Finite := by
  exact (Set.finite_range P.vertex).union (by simp)

theorem bridgeSupport_eq_commonBridge_union_innerSecond :
    S.bridgeSupport =
      range S.commonBridge ∪ range S.innerSplit.second := by
  rw [bridgeSupport, commonBridge, range_bridgePath]
  rw [← P.carrier_toJordanCircle, ← S.innerSplit.cover]
  ext x
  simp only [mem_union]
  tauto

private theorem not_exceptional_points {p : Plane}
    (hp : p ∉ S.exceptionalSet) :
    p ≠ A.innerPoint ∧ p ≠ B.innerPoint ∧
      p ≠ A.outerPoint ∧ p ≠ B.outerPoint := by
  simp only [exceptionalSet, mem_union, mem_insert_iff,
    mem_singleton_iff, not_or] at hp
  exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

private theorem not_mem_vertexRange {p : Plane}
    (hp : p ∉ S.exceptionalSet) : p ∉ range P.vertex := by
  intro hpVertex
  exact hp (Or.inl hpVertex)

/-- Away from its four joins and the inner polygon vertices, the full bridge
support is locally a straight line. -/
theorem bridgeSupport_exists_local_determinantLine
    (hAB : Disjoint (range A.path) (range B.path))
    (hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint)
    {p : Plane} (hpBridge : p ∈ range S.commonBridge)
    (hpExceptional : p ∉ S.exceptionalSet) :
    ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      ball p r ∩ S.bridgeSupport =
        ball p r ∩ determinantLine p d := by
  obtain ⟨hpAi, hpBi, hpAo, hpBo⟩ :=
    S.not_exceptional_points hpExceptional
  change p ∈ range (bridgePath A B S.innerSplit.first) at hpBridge
  rw [range_bridgePath] at hpBridge
  rcases hpBridge with (hpA | hpInner) | hpB
  · have hpNotP : p ∉ P.carrier := by
      intro hpP
      have hpMeet : p ∈ range A.path ∩ P.carrier := ⟨hpA, hpP⟩
      rw [A.range_inter_inner] at hpMeet
      exact hpAi (Set.mem_singleton_iff.mp hpMeet)
    have hpNotB : p ∉ range B.path := by
      exact Set.disjoint_left.mp hAB hpA
    have hpSegment : p ∈ segment ℝ A.outerPoint A.innerPoint :=
      hAsegment ▸ hpA
    have hpOpen : p ∈ openSegment ℝ A.outerPoint A.innerPoint :=
      mem_openSegment_of_ne_left_right hpAo.symm hpAi.symm hpSegment
    have hlocal : ∃ r : ℝ, 0 < r ∧
        ball p r ∩ range A.path =
          ball p r ∩ determinantLine p (A.innerPoint - A.outerPoint) := by
      rw [hAsegment]
      exact exists_local_determinantLine_segment
        (by
          intro h
          have ht : (0 : unitInterval) = 1 := A.path_injective <| by
            simpa only [Path.source, Path.target] using h
          have := congrArg Subtype.val ht
          norm_num at this)
        hpOpen
    refine ⟨A.innerPoint - A.outerPoint, ?_⟩
    simpa only [bridgeSupport, union_assoc] using
      exists_local_determinantLine_union_of_compact_avoid hlocal
        (P.isCompact_carrier.union (isCompact_range B.path.continuous))
        (by simp only [mem_union, hpNotP, hpNotB, or_self, not_false_eq_true])
  · have hpP : p ∈ P.carrier := S.innerFirst_range_subset hpInner
    have hpNotA : p ∉ range A.path := by
      intro hpA
      have hpMeet : p ∈ range A.path ∩ P.carrier := ⟨hpA, hpP⟩
      rw [A.range_inter_inner] at hpMeet
      exact hpAi (Set.mem_singleton_iff.mp hpMeet)
    have hpNotB : p ∉ range B.path := by
      intro hpB
      have hpMeet : p ∈ range B.path ∩ P.carrier := ⟨hpB, hpP⟩
      rw [B.range_inter_inner] at hpMeet
      exact hpBi (Set.mem_singleton_iff.mp hpMeet)
    obtain ⟨i, hpOpen⟩ :=
      Schoenflies.PolygonalCircle.exists_openEdge_of_mem_carrier_not_vertex P hpP
        (S.not_mem_vertexRange hpExceptional)
    obtain ⟨r, hr, hlocalP⟩ :=
      polygonalCircle_exists_local_determinantLine P hpOpen
    let d : Plane := P.vertex (i + 1) - P.vertex i
    have hlocal : ∃ r : ℝ, 0 < r ∧
        ball p r ∩ P.carrier = ball p r ∩ determinantLine p d :=
      ⟨r, hr, hlocalP⟩
    obtain ⟨r', hr', hlocal'⟩ :=
      exists_local_determinantLine_union_of_compact_avoid hlocal
        ((isCompact_range A.path.continuous).union
          (isCompact_range B.path.continuous))
        (by simp only [mem_union, hpNotA, hpNotB, or_self, not_false_eq_true])
    refine ⟨d, r', hr', ?_⟩
    simpa only [bridgeSupport, union_assoc, union_left_comm, union_comm]
      using hlocal'
  · have hpNotP : p ∉ P.carrier := by
      intro hpP
      have hpMeet : p ∈ range B.path ∩ P.carrier := ⟨hpB, hpP⟩
      rw [B.range_inter_inner] at hpMeet
      exact hpBi (Set.mem_singleton_iff.mp hpMeet)
    have hpNotA : p ∉ range A.path := by
      exact Set.disjoint_left.mp hAB.symm hpB
    have hpSegment : p ∈ segment ℝ B.outerPoint B.innerPoint :=
      hBsegment ▸ hpB
    have hpOpen : p ∈ openSegment ℝ B.outerPoint B.innerPoint :=
      mem_openSegment_of_ne_left_right hpBo.symm hpBi.symm hpSegment
    have hlocal : ∃ r : ℝ, 0 < r ∧
        ball p r ∩ range B.path =
          ball p r ∩ determinantLine p (B.innerPoint - B.outerPoint) := by
      rw [hBsegment]
      exact exists_local_determinantLine_segment
        (by
          intro h
          have ht : (0 : unitInterval) = 1 := B.path_injective <| by
            simpa only [Path.source, Path.target] using h
          have := congrArg Subtype.val ht
          norm_num at this)
        hpOpen
    obtain ⟨r, hr, hlocal'⟩ :=
      exists_local_determinantLine_union_of_compact_avoid hlocal
        ((isCompact_range A.path.continuous).union P.isCompact_carrier)
        (by simp only [mem_union, hpNotA, hpNotP, or_self, not_false_eq_true])
    refine ⟨B.innerPoint - B.outerPoint, r, hr, ?_⟩
    simpa only [bridgeSupport, union_assoc, union_left_comm, union_comm]
      using hlocal'

/-- The compact pieces which distinguish the two separators from the full
bridge support. -/
def omittedPieces : Set Plane :=
  range S.innerSplit.second ∪
    (range S.outerArc₀ ∪ range S.outerArc₁)

theorem omittedPieces_isCompact : IsCompact S.omittedPieces :=
  (isCompact_range S.innerSplit.second.continuous).union <|
    (isCompact_range S.outerArc₀.continuous).union
      (isCompact_range S.outerArc₁.continuous)

theorem commonBridge_not_mem_omittedPieces
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    {p : Plane} (hpBridge : p ∈ range S.commonBridge)
    (hpExceptional : p ∉ S.exceptionalSet) :
    p ∉ S.omittedPieces := by
  obtain ⟨hpAi, hpBi, hpAo, hpBo⟩ :=
    S.not_exceptional_points hpExceptional
  rw [omittedPieces]
  rintro (hpInnerSecond | hpOuter)
  · change p ∈ range (bridgePath A B S.innerSplit.first) at hpBridge
    rw [range_bridgePath] at hpBridge
    rcases hpBridge with (hpA | hpInnerFirst) | hpB
    · have hpP := S.innerSecond_range_subset hpInnerSecond
      have hpMeet : p ∈ range A.path ∩ P.carrier := ⟨hpA, hpP⟩
      rw [A.range_inter_inner] at hpMeet
      exact hpAi (Set.mem_singleton_iff.mp hpMeet)
    · have hpMeet : p ∈
          range S.innerSplit.first ∩ range S.innerSplit.second :=
        ⟨hpInnerFirst, hpInnerSecond⟩
      rw [S.innerSplit.overlap] at hpMeet
      rcases hpMeet with hpA | hpB
      · exact hpAi hpA
      · exact hpBi hpB
    · have hpP := S.innerSecond_range_subset hpInnerSecond
      have hpMeet : p ∈ range B.path ∩ P.carrier := ⟨hpB, hpP⟩
      rw [B.range_inter_inner] at hpMeet
      exact hpBi (Set.mem_singleton_iff.mp hpMeet)
  · rcases hpOuter with hpOuter₀ | hpOuter₁
    · have hpEnds : p ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
        rw [← S.commonBridge_inter_outerArc₀ hPQ]
        exact ⟨hpBridge, hpOuter₀⟩
      rcases hpEnds with hpA | hpB
      · exact hpAo hpA
      · exact hpBo hpB
    · have hpEnds : p ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
        rw [← S.commonBridge_inter_outerArc₁ hPQ]
        exact ⟨hpBridge, hpOuter₁⟩
      rcases hpEnds with hpA | hpB
      · exact hpAo hpA
      · exact hpBo hpB

private theorem restrict_local_equality {X Y : Set Plane} {p : Plane}
    {r R : ℝ} (hrR : r ≤ R)
    (h : ball p R ∩ X = ball p R ∩ Y) :
    ball p r ∩ X = ball p r ∩ Y := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxBall, hxX⟩
    have hx : x ∈ ball p R ∩ X :=
      ⟨ball_subset_ball hrR hxBall, hxX⟩
    rw [h] at hx
    exact ⟨hxBall, hx.2⟩
  · rintro x ⟨hxBall, hxY⟩
    have hx : x ∈ ball p R ∩ Y :=
      ⟨ball_subset_ball hrR hxBall, hxY⟩
    rw [← h] at hx
    exact ⟨hxBall, hx.2⟩

/-- At every nonexceptional point of their common bridge, both complementary
separators agree with the same straight line in the same ball. -/
theorem circles_exists_common_local_determinantLine
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hAB : Disjoint (range A.path) (range B.path))
    (hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint)
    {p : Plane} (hpBridge : p ∈ range S.commonBridge)
    (hpExceptional : p ∉ S.exceptionalSet) :
    ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      ball p r ∩ (S.circle₀ hPQ hAB).carrier =
        ball p r ∩ determinantLine p d ∧
      ball p r ∩ (S.circle₁ hPQ hAB).carrier =
        ball p r ∩ determinantLine p d := by
  obtain ⟨d, rS, hrS, hlocalS⟩ :=
    S.bridgeSupport_exists_local_determinantLine hAB hAsegment hBsegment
      hpBridge hpExceptional
  obtain ⟨rO, hrO, hlocalO⟩ :=
    exists_ball_inter_eq_empty_of_isCompact S.omittedPieces_isCompact
      (S.commonBridge_not_mem_omittedPieces hPQ hpBridge hpExceptional)
  let r : ℝ := min rS rO
  have hr : 0 < r := lt_min hrS hrO
  have hsupport := restrict_local_equality (min_le_left rS rO) hlocalS
  have homitted : ball p r ∩ S.omittedPieces = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ ball p rO ∩ S.omittedPieces :=
        ⟨ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
      rw [hlocalO] at hx'
      exact hx'.elim
    · exact empty_subset _
  have hcircleSupport₀ :
      ball p r ∩ (S.circle₀ hPQ hAB).carrier =
        ball p r ∩ S.bridgeSupport := by
    rw [S.carrier_circle₀ hPQ hAB,
      S.bridgeSupport_eq_commonBridge_union_innerSecond]
    apply Set.Subset.antisymm
    · rintro x ⟨hxBall, hxBridge | hxOuter⟩
      · exact ⟨hxBall, Or.inl hxBridge⟩
      · have hxOmitted : x ∈ S.omittedPieces := by
          rw [omittedPieces]
          exact Or.inr (Or.inl hxOuter)
        have : x ∈ ball p r ∩ S.omittedPieces := ⟨hxBall, hxOmitted⟩
        rw [homitted] at this
        exact this.elim
    · rintro x ⟨hxBall, hxBridge | hxInner⟩
      · exact ⟨hxBall, Or.inl hxBridge⟩
      · have hxOmitted : x ∈ S.omittedPieces := by
          rw [omittedPieces]
          exact Or.inl hxInner
        have : x ∈ ball p r ∩ S.omittedPieces := ⟨hxBall, hxOmitted⟩
        rw [homitted] at this
        exact this.elim
  have hcircleSupport₁ :
      ball p r ∩ (S.circle₁ hPQ hAB).carrier =
        ball p r ∩ S.bridgeSupport := by
    rw [S.carrier_circle₁ hPQ hAB,
      S.bridgeSupport_eq_commonBridge_union_innerSecond]
    apply Set.Subset.antisymm
    · rintro x ⟨hxBall, hxBridge | hxOuter⟩
      · exact ⟨hxBall, Or.inl hxBridge⟩
      · have hxOmitted : x ∈ S.omittedPieces := by
          rw [omittedPieces]
          exact Or.inr (Or.inr hxOuter)
        have : x ∈ ball p r ∩ S.omittedPieces := ⟨hxBall, hxOmitted⟩
        rw [homitted] at this
        exact this.elim
    · rintro x ⟨hxBall, hxBridge | hxInner⟩
      · exact ⟨hxBall, Or.inl hxBridge⟩
      · have hxOmitted : x ∈ S.omittedPieces := by
          rw [omittedPieces]
          exact Or.inl hxInner
        have : x ∈ ball p r ∩ S.omittedPieces := ⟨hxBall, hxOmitted⟩
        rw [homitted] at this
        exact this.elim
  refine ⟨d, r, hr, hcircleSupport₀.trans hsupport,
    hcircleSupport₁.trans hsupport⟩

/-- Polygonal-annulus crosscut theorem: the two complementary separator
regions exactly fill the outer polygonal disk. -/
theorem closure_outerInterior_eq_union_separatorInteriors
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hAB : Disjoint (range A.path) (range B.path))
    (hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint) :
    closure Q.interiorRegion =
      closure (S.circle₀ hPQ hAB).inside ∪
        closure (S.circle₁ hPQ hAB).inside := by
  have hcircle₀ : (S.circle₀ hPQ hAB).carrier ⊆
      Q.toJordanCircle.inside ∪ Q.toJordanCircle.carrier := by
    intro x hx
    have hxClosed := (S.circle₀_carrier_subset_closedShell hPQ hAB hx).1
    rw [Q.closedRegion_eq_union] at hxClosed
    simpa only [Q.inside_toJordanCircle, Q.carrier_toJordanCircle]
      using hxClosed
  have hcircle₁ : (S.circle₁ hPQ hAB).carrier ⊆
      Q.toJordanCircle.inside ∪ Q.toJordanCircle.carrier := by
    intro x hx
    have hxClosed := (S.circle₁_carrier_subset_closedShell hPQ hAB hx).1
    rw [Q.closedRegion_eq_union] at hxClosed
    simpa only [Q.inside_toJordanCircle, Q.carrier_toJordanCircle]
      using hxClosed
  simpa only [Q.inside_toJordanCircle] using
    (JordanThetaRegions.closure_inside_eq_union
      (Q := Q.toJordanCircle)
      (K₀ := S.circle₀ hPQ hAB) (K₁ := S.circle₁ hPQ hAB)
      (B := range S.commonBridge)
      (A₀ := range S.outerArc₀) (A₁ := range S.outerArc₁)
      (F := S.exceptionalSet)
      hcircle₀ hcircle₁
      (by simpa only [Q.carrier_toJordanCircle] using S.outer_carrier_eq_union)
      (S.carrier_circle₀ hPQ hAB) (S.carrier_circle₁ hPQ hAB)
      (S.outerArc₀_sdiff_circle₁_nonempty hPQ hAB)
      (S.outerArc₁_sdiff_circle₀_nonempty hPQ hAB)
      S.exceptionalSet_finite
      (by
        intro p hp
        exact S.circles_exists_common_local_determinantLine hPQ hAB
          hAsegment hBsegment hp.1 hp.2))

end PolygonalCircle.AnnularCrosscut.SeparatorPair

end

end Schoenflies
