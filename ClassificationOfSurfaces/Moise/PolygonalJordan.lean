/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PlaneComplex
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Jordan curve theorem for polygons

Statements of the separation properties of polygonal simple closed curves in the plane, following
Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 2 ("Separation properties of polygons in
R²").  Only the **polygonal** case is stated: this is what the triangulation theorem consumes
(via the combinatorial Schoenflies theorem, Moise Thm. 5.3).  The full Jordan curve theorem
(Moise Ch. 4) is *not* on the triangulation route's critical path.

`PolygonalCircle` is the honest object: cyclically indexed vertices joined by genuine segments,
with adjacent segments meeting exactly at their shared vertex and non-adjacent segments disjoint.
A junk witness cannot satisfy these fields: they force the carrier to be a topological circle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A polygonal simple closed curve in the plane: at least three vertices, cyclically indexed,
with consecutive vertices distinct, adjacent edges meeting exactly in their shared vertex, and
non-adjacent edges disjoint. -/
structure PolygonalCircle where
  /-- The number of vertices (and edges). -/
  n : ℕ
  /-- A polygon has at least three vertices. -/
  three_le : 3 ≤ n
  /-- The cyclically indexed vertices. -/
  vertex : ZMod n → Plane
  /-- Consecutive vertices are distinct, so every edge is a genuine segment. -/
  adjacent_ne : ∀ i, vertex i ≠ vertex (i + 1)
  /-- Adjacent edges meet exactly in their shared vertex. -/
  consecutive_inter : ∀ i,
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex (i + 1)) (vertex (i + 2)) =
      {vertex (i + 1)}
  /-- Non-adjacent edges are disjoint. -/
  nonadjacent_disjoint : ∀ i j, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) = ∅

namespace PolygonalCircle

variable (J : PolygonalCircle)

instance : NeZero J.n :=
  ⟨by have := J.three_le; omega⟩

/-- The edge from vertex `i` to vertex `i + 1`. -/
def edgeSegment (i : ZMod J.n) : Set Plane :=
  segment ℝ (J.vertex i) (J.vertex (i + 1))

/-- The carrier of the polygon: the union of its edges. -/
def carrier : Set Plane :=
  ⋃ i, J.edgeSegment i

theorem vertex_mem_carrier (i : ZMod J.n) : J.vertex i ∈ J.carrier :=
  Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

theorem carrier_nonempty : J.carrier.Nonempty :=
  ⟨J.vertex 0, J.vertex_mem_carrier 0⟩

theorem isCompact_edgeSegment (i : ZMod J.n) : IsCompact (J.edgeSegment i) := by
  rw [edgeSegment, ← convexHull_pair]
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp)

/-- The carrier of a polygon is compact. -/
theorem isCompact_carrier : IsCompact J.carrier :=
  isCompact_iUnion J.isCompact_edgeSegment

theorem isClosed_carrier : IsClosed J.carrier :=
  J.isCompact_carrier.isClosed

/-- **Theorem boundary** (Moise Ch. 2, Thms. 1, 5, 6: the Jordan curve theorem for polygons).

The complement of a polygon has exactly two connected components: a bounded interior and an
unbounded exterior, both open, and the polygon is the frontier of each.

Must-fail check: the statement forces `interior ∪ exterior = carrierᶜ` with both sides connected
and the frontiers equal to the carrier, so it cannot be satisfied by choosing junk open sets. -/
theorem polygonal_jordan :
    ∃ inside outside : Set Plane,
      IsOpen inside ∧ IsOpen outside ∧ Disjoint inside outside ∧
      inside ∪ outside = J.carrierᶜ ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      frontier inside = J.carrier ∧ frontier outside = J.carrier := by
  sorry

/-- The interior region of a polygon (the bounded complementary component). -/
noncomputable def interiorRegion : Set Plane :=
  J.polygonal_jordan.choose

/-- The exterior region of a polygon (the unbounded complementary component). -/
noncomputable def exteriorRegion : Set Plane :=
  J.polygonal_jordan.choose_spec.choose

theorem isOpen_interiorRegion : IsOpen J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.1

theorem isOpen_exteriorRegion : IsOpen J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.1

theorem disjoint_interior_exterior : Disjoint J.interiorRegion J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.1

theorem interior_union_exterior : J.interiorRegion ∪ J.exteriorRegion = J.carrierᶜ :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.1

theorem isConnected_interiorRegion : IsConnected J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.1

theorem isConnected_exteriorRegion : IsConnected J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.1

theorem isBounded_interiorRegion : Bornology.IsBounded J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.1

theorem not_isBounded_exteriorRegion : ¬ Bornology.IsBounded J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.1

theorem frontier_interiorRegion : frontier J.interiorRegion = J.carrier :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1

theorem frontier_exteriorRegion : frontier J.exteriorRegion = J.carrier :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2

/-! ### The crossing index (Moise Ch. 2, proof of Thm. 1, Lemma 2)

The parity of the number of polygon edges crossed by the leftward horizontal ray from a point.
We use the half-open edge convention (an edge is crossed when the point's height lies in the
half-open interval between the endpoint heights): this replaces Moise's "slightly perturbed
line" device, needs no general-position choice of axes, and makes the index everywhere defined.
Horizontal edges are never crossed. -/

/-- The x-coordinate at height `y` of the line through `v` and `w` (meaningful when the heights
of `v` and `w` differ, which the crossing condition guarantees at use sites). -/
noncomputable def crossingX (v w : Plane) (y : ℝ) : ℝ :=
  v 0 + (y - v 1) / (w 1 - v 1) * (w 0 - v 0)

/-- The leftward horizontal ray from `P` crosses edge `i`, with the half-open height
convention. -/
def EdgeCrossed (i : ZMod J.n) (P : Plane) : Prop :=
  ((J.vertex i) 1 ≤ P 1 ∧ P 1 < (J.vertex (i + 1)) 1 ∨
    (J.vertex (i + 1)) 1 ≤ P 1 ∧ P 1 < (J.vertex i) 1) ∧
  crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0

open scoped Classical in
/-- The Moise index of a point: the parity of the number of edges crossed by its leftward
horizontal ray. -/
noncomputable def index (P : Plane) : ℕ :=
  (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P).card % 2

theorem index_lt_two (P : Plane) : J.index P < 2 :=
  Nat.mod_lt _ (by norm_num)

/-- Points of a segment have heights between the endpoint heights. -/
theorem height_le_max_of_mem_segment {v w q : Plane} (hq : q ∈ segment ℝ v w) :
    q 1 ≤ max (v 1) (w 1) := by
  rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
  have h1 : (a • v + b • w) 1 = a * v 1 + b * w 1 := by
    simp
  rw [h1]
  calc a * v 1 + b * w 1 ≤ a * max (v 1) (w 1) + b * max (v 1) (w 1) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max (v 1) (w 1) := by rw [← add_mul, hab, one_mul]

/-- Points of the polygon have heights at most the maximal vertex height. -/
theorem height_le_of_mem_carrier {q : Plane} (hq : q ∈ J.carrier) :
    ∃ i : ZMod J.n, q 1 ≤ (J.vertex i) 1 := by
  rcases Set.mem_iUnion.mp hq with ⟨i, hqi⟩
  rcases le_total ((J.vertex i) 1) ((J.vertex (i + 1)) 1) with h | h
  · exact ⟨i + 1, by simpa [max_eq_right h] using height_le_max_of_mem_segment hqi⟩
  · exact ⟨i, by simpa [max_eq_left h] using height_le_max_of_mem_segment hqi⟩

/-- A point strictly above every vertex has index zero: its leftward ray crosses nothing. -/
theorem index_eq_zero_of_high {P : Plane} (hP : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1) :
    J.index P = 0 := by
  classical
  have hempty : (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i _
    rintro ⟨hy | hy, -⟩
    · exact absurd hy.2 (not_lt.mpr (hP (i + 1)).le)
    · exact absurd hy.2 (not_lt.mpr (hP i).le)
  simp [index, hempty]

/-- A point strictly above every vertex is off the polygon. -/
theorem notMem_carrier_of_high {P : Plane} (hP : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1) :
    P ∉ J.carrier := by
  intro hmem
  rcases J.height_le_of_mem_carrier hmem with ⟨i, hi⟩
  exact absurd hi (not_le.mpr (hP i))

/-- There are points off the polygon with index zero. -/
theorem exists_index_eq_zero : ∃ P : Plane, P ∉ J.carrier ∧ J.index P = 0 := by
  classical
  obtain ⟨ymax, hymax⟩ : ∃ y, ∀ i : ZMod J.n, (J.vertex i) 1 ≤ y := by
    set g : ZMod J.n → ℝ := fun i => (J.vertex i) 1 with hg
    exact ⟨(Finset.univ.image g).max' (by simp),
      fun i => Finset.le_max' _ (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))⟩
  set P : Plane := (WithLp.toLp 2 ![0, ymax + 1] : Plane) with hPdef
  have hP1 : P 1 = ymax + 1 := rfl
  have hhigh : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1 := by
    intro i
    rw [hP1]
    exact lt_of_le_of_lt (hymax i) (by linarith)
  exact ⟨P, J.notMem_carrier_of_high hhigh, J.index_eq_zero_of_high hhigh⟩

/-- **Sub-boundary** (Moise Ch. 2, Thm. 1, Lemma 2, local constancy of the index).

Off the polygon the crossing index is locally constant.  The proof is elementary casework: for
`Q` near `P`, the crossing status of each edge is unchanged unless the ray endpoint passes a
vertex height, and at a vertex height the half-open convention makes the count change by `0` or
`2` (the two edges at that vertex are both gained or both lost when they point to the same side,
and exchanged when they point to opposite sides). -/
theorem index_locallyConstant {P : Plane} (hP : P ∉ J.carrier) :
    ∀ᶠ Q in nhds P, J.index Q = J.index P := by
  sorry

/-- **Sub-boundary** (Moise Ch. 2, Thm. 1, Lemma 2, existence of an inside point).

Some point off the polygon has index one: take a height that is no vertex height but is attained
by the polygon, let `P₁` be the leftmost polygon point at that height, and move slightly right of
`P₁`.  (Moise's construction; requires knowing the polygon is not contained in a single
horizontal line, which follows from the embedding fields.) -/
theorem exists_index_eq_one : ∃ P : Plane, P ∉ J.carrier ∧ J.index P = 1 := by
  sorry

/-- **Moise Ch. 2, Thm. 1, Lemma 2**: the complement of a polygon is disconnected.  Proved from
the index machinery: the index-0 and index-1 loci are relatively open (local constancy), cover
the complement (the index is a parity), and are both nonempty. -/
theorem compl_carrier_not_isPreconnected : ¬ IsPreconnected (J.carrierᶜ : Set Plane) := by
  classical
  intro hconn
  obtain ⟨P₀, hP₀mem, hP₀⟩ := J.exists_index_eq_zero
  obtain ⟨P₁, hP₁mem, hP₁⟩ := J.exists_index_eq_one
  -- the two index loci, fattened to open sets by local constancy
  set U : Set Plane := {Q | Q ∉ J.carrier ∧ J.index Q = 0} with hUdef
  set V : Set Plane := {Q | Q ∉ J.carrier ∧ J.index Q = 1} with hVdef
  have hopen : ∀ k, IsOpen {Q : Plane | Q ∉ J.carrier ∧ J.index Q = k} := by
    intro k
    rw [isOpen_iff_mem_nhds]
    rintro Q ⟨hQmem, hQk⟩
    have hcompl : J.carrierᶜ ∈ nhds Q :=
      J.isClosed_carrier.isOpen_compl.mem_nhds hQmem
    filter_upwards [J.index_locallyConstant hQmem, hcompl] with R hR hRmem
    exact ⟨hRmem, by rw [hR, hQk]⟩
  have hcover : (J.carrierᶜ : Set Plane) ⊆ U ∪ V := by
    intro Q hQ
    have := J.index_lt_two Q
    interval_cases h : J.index Q
    · exact Or.inl ⟨hQ, h⟩
    · exact Or.inr ⟨hQ, h⟩
  have hUne : ((J.carrierᶜ : Set Plane) ∩ U).Nonempty := ⟨P₀, hP₀mem, hP₀mem, hP₀⟩
  have hVne : ((J.carrierᶜ : Set Plane) ∩ V).Nonempty := ⟨P₁, hP₁mem, hP₁mem, hP₁⟩
  obtain ⟨Q, -, ⟨-, hQ0⟩, ⟨-, hQ1⟩⟩ := hconn U V (hopen 0) (hopen 1) hcover hUne hVne
  rw [hQ0] at hQ1
  exact absurd hQ1 (by norm_num)

/-- The closed region bounded by a polygon: the closure of its interior region. -/
noncomputable def closedRegion : Set Plane :=
  closure J.interiorRegion

theorem closedRegion_eq_union : J.closedRegion = J.interiorRegion ∪ J.carrier := by
  rw [closedRegion, closure_eq_self_union_frontier, J.frontier_interiorRegion]

theorem isCompact_closedRegion : IsCompact J.closedRegion :=
  J.isBounded_interiorRegion.isCompact_closure

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
