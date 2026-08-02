import Schoenflies.LocalStraightCrossing

/-!
# Point-set helpers for locally straight finite graphs

These lemmas isolate the metric shrinking arguments used when a polygonal
arc is accompanied by finitely many compact pieces that miss the point under
consideration.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

/-- A local set equality remains true after shrinking the ball. -/
theorem restrict_local_set_equality {X Y : Set Plane} {p : Plane}
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

/-- A compact set missing a point misses some open ball about that point. -/
theorem exists_ball_inter_eq_empty_of_isCompact {C : Set Plane} {p : Plane}
    (hC : IsCompact C) (hp : p ∉ C) :
    ∃ r : ℝ, 0 < r ∧ ball p r ∩ C = ∅ := by
  have hnhds : Cᶜ ∈ nhds p := hC.isClosed.isOpen_compl.mem_nhds hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r, hr, ?_⟩
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxBall, hxC⟩
  exact hball hxBall hxC

/-- Adding a compact set which misses `p` preserves a locally straight
description after shrinking the ball. -/
theorem exists_local_determinantLine_union_of_compact_avoid
    {X C : Set Plane} {p d : Plane}
    (hX : ∃ r : ℝ, 0 < r ∧
      ball p r ∩ X = ball p r ∩ determinantLine p d)
    (hC : IsCompact C) (hpC : p ∉ C) :
    ∃ r : ℝ, 0 < r ∧
      ball p r ∩ (X ∪ C) = ball p r ∩ determinantLine p d := by
  obtain ⟨rX, hrX, hlocalX⟩ := hX
  obtain ⟨rC, hrC, hlocalC⟩ :=
    exists_ball_inter_eq_empty_of_isCompact hC hpC
  let r : ℝ := min rX rC
  have hr : 0 < r := lt_min hrX hrC
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxBall, hxX | hxC⟩
    · have hx : x ∈ ball p rX ∩ X :=
        ⟨ball_subset_ball (min_le_left _ _) hxBall, hxX⟩
      rw [hlocalX] at hx
      exact ⟨hxBall, hx.2⟩
    · have hx : x ∈ ball p rC ∩ C :=
        ⟨ball_subset_ball (min_le_right _ _) hxBall, hxC⟩
      rw [hlocalC] at hx
      exact hx.elim
  · rintro x ⟨hxBall, hxLine⟩
    have hx : x ∈ ball p rX ∩ determinantLine p d :=
      ⟨ball_subset_ball (min_le_left _ _) hxBall, hxLine⟩
    rw [← hlocalX] at hx
    exact ⟨hxBall, Or.inl hx.2⟩

/-- Removing a compact summand which misses `p` from a locally straight
union preserves the same local straight description after shrinking. -/
theorem exists_local_determinantLine_of_union_compact_avoid
    {X C : Set Plane} {p d : Plane}
    (hUnion : ∃ r : ℝ, 0 < r ∧
      ball p r ∩ (X ∪ C) = ball p r ∩ determinantLine p d)
    (hC : IsCompact C) (hpC : p ∉ C) :
    ∃ r : ℝ, 0 < r ∧
      ball p r ∩ X = ball p r ∩ determinantLine p d := by
  obtain ⟨rU, hrU, hlocalU⟩ := hUnion
  obtain ⟨rC, hrC, hlocalC⟩ :=
    exists_ball_inter_eq_empty_of_isCompact hC hpC
  let r : ℝ := min rU rC
  have hr : 0 < r := lt_min hrU hrC
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxBall, hxX⟩
    have hx : x ∈ ball p rU ∩ (X ∪ C) :=
      ⟨ball_subset_ball (min_le_left _ _) hxBall, Or.inl hxX⟩
    rw [hlocalU] at hx
    exact ⟨hxBall, hx.2⟩
  · rintro x ⟨hxBall, hxLine⟩
    have hx : x ∈ ball p rU ∩ determinantLine p d :=
      ⟨ball_subset_ball (min_le_left _ _) hxBall, hxLine⟩
    rw [← hlocalU] at hx
    rcases hx.2 with hxX | hxC
    · exact ⟨hxBall, hxX⟩
    · have hxAvoid : x ∈ ball p rC ∩ C :=
        ⟨ball_subset_ball (min_le_right _ _) hxBall, hxC⟩
      rw [hlocalC] at hxAvoid
      exact hxAvoid.elim

/-- At a relative-interior point, a nondegenerate segment agrees locally
with its supporting determinant line. -/
theorem exists_local_determinantLine_segment {a b p : Plane}
    (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b) :
    ∃ r : ℝ, 0 < r ∧
      ball p r ∩ segment ℝ a b =
        ball p r ∩ determinantLine p (b - a) := by
  obtain ⟨r, hr, hline⟩ :=
    exists_ball_inter_determinantLine_subset_segment hab hp
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxBall, hxSegment⟩
    refine ⟨hxBall, mem_determinantLine_of_mem_affineSpan_pair ?_ ?_⟩
    · exact mem_affineSpan_pair_of_mem_segment
        (openSegment_subset_segment ℝ _ _ hp)
    · exact mem_affineSpan_pair_of_mem_segment hxSegment
  · intro x hx
    exact ⟨hx.1, hline hx⟩

namespace PolygonalCircle

/-- A point of a polygonal carrier which is not a polygon vertex lies in
the relative interior of one of its edges. -/
theorem exists_openEdge_of_mem_carrier_not_vertex (P : PolygonalCircle)
    {p : Plane} (hp : p ∈ P.carrier) (hpVertex : p ∉ range P.vertex) :
    ∃ i : ZMod P.n,
      p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) := by
  change p ∈ ⋃ i : ZMod P.n, P.edgeSegment i at hp
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
  refine ⟨i, mem_openSegment_of_ne_left_right ?_ ?_ hpi⟩
  · intro h
    apply hpVertex
    exact ⟨i, h⟩
  · intro h
    apply hpVertex
    exact ⟨i + 1, h⟩

end PolygonalCircle

end

end Schoenflies
