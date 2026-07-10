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

/-! #### The handshake lemma for the local-constancy casework

Near a point `P` off the polygon, the only edges whose crossing status is not locally constant
are those with exactly one endpoint at the height of `P`, that endpoint lying strictly to the
left of `P`: rising edges switch on and falling edges switch off as the query point's height
crosses `P`'s.  The index is therefore locally constant provided the number of such edges is
even, which is a double-counting argument: every vertex has two incident edges, a horizontal
partner of a left vertex is itself a left vertex (otherwise the horizontal edge would contain
`P`), and so the non-horizontal incident edges of the left vertices pair up. -/

/-- Two plane points with equal coordinates are equal. -/
theorem plane_ext {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- A point at the height of a horizontal segment, with abscissa between the endpoints, lies on
the segment. -/
theorem mem_segment_of_horizontal {a b P : Plane} (ha : a 1 = P 1) (hb : b 1 = P 1)
    (hax : a 0 ≤ P 0) (hxb : P 0 ≤ b 0) : P ∈ segment ℝ a b := by
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · have hPa : P = a := by
      apply plane_ext
      · exact le_antisymm (by rw [hab]; exact hxb) hax
      · exact ha.symm
    rw [hPa]
    exact left_mem_segment ℝ a b
  · set t : ℝ := (P 0 - a 0) / (b 0 - a 0) with ht
    have hden : (0 : ℝ) < b 0 - a 0 := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hden]
      linarith
    have hpt : (1 - t) • a + t • b = P := by
      apply plane_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [ht]
        field_simp
        ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [ha, hb]
        ring
    exact ⟨1 - t, t, by linarith, ht0, by ring, hpt⟩

variable (J : PolygonalCircle)

open Classical in
/-- The vertices at the height of `P`, strictly to its left. -/
noncomputable def leftVertices (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun k => (J.vertex k) 1 = P 1 ∧ (J.vertex k) 0 < P 0

open Classical in
/-- Edges with one endpoint at the height of `P` and left of `P`, the other endpoint strictly
above. -/
noncomputable def upLeftEdges (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun i =>
    ((J.vertex i) 1 = P 1 ∧ (J.vertex i) 0 < P 0 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
    ((J.vertex (i + 1)) 1 = P 1 ∧ (J.vertex (i + 1)) 0 < P 0 ∧ P 1 < (J.vertex i) 1)

open Classical in
/-- Edges with one endpoint at the height of `P` and left of `P`, the other endpoint strictly
below. -/
noncomputable def downLeftEdges (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun i =>
    ((J.vertex i) 1 = P 1 ∧ (J.vertex i) 0 < P 0 ∧ (J.vertex (i + 1)) 1 < P 1) ∨
    ((J.vertex (i + 1)) 1 = P 1 ∧ (J.vertex (i + 1)) 0 < P 0 ∧ (J.vertex i) 1 < P 1)

/-- The horizontal partner of a left vertex is a left vertex: otherwise the horizontal edge
between them would contain `P`. -/
theorem left_of_horizontal_partner {P : Plane} (hP : P ∉ J.carrier) {k : ZMod J.n}
    (hk1 : (J.vertex k) 1 = P 1) (hk0 : (J.vertex k) 0 < P 0)
    {l : ZMod J.n} (hl1 : (J.vertex l) 1 = P 1)
    (hedge : segment ℝ (J.vertex k) (J.vertex l) ⊆ J.carrier ∨
      segment ℝ (J.vertex l) (J.vertex k) ⊆ J.carrier) :
    (J.vertex l) 0 < P 0 := by
  by_contra hge
  rw [not_lt] at hge
  have hmem : P ∈ segment ℝ (J.vertex k) (J.vertex l) :=
    mem_segment_of_horizontal hk1 hl1 hk0.le hge
  rcases hedge with h | h
  · exact hP (h hmem)
  · refine hP (h ?_)
    rw [segment_symm]
    exact hmem

/-- Edge `i` (from vertex `i` to vertex `i + 1`) lies on the carrier. -/
theorem edgeSegment_subset_carrier (i : ZMod J.n) :
    segment ℝ (J.vertex i) (J.vertex (i + 1)) ⊆ J.carrier :=
  fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩

open Classical in
/-- **The handshake lemma**: the flipping edges (up-left plus down-left) are even in number. -/
theorem upLeft_card_add_downLeft_card_even {P : Plane} (hP : P ∉ J.carrier) :
    Even ((J.upLeftEdges P).card + (J.downLeftEdges P).card) := by
  classical
  set h : ℝ := P 1 with hh
  -- edges based at their first endpoint / second endpoint
  set A : Finset (ZMod J.n) := Finset.univ.filter fun i =>
    ((J.vertex i) 1 = h ∧ (J.vertex i) 0 < P 0) ∧ (J.vertex (i + 1)) 1 ≠ h with hA
  set B : Finset (ZMod J.n) := Finset.univ.filter fun i =>
    ((J.vertex (i + 1)) 1 = h ∧ (J.vertex (i + 1)) 0 < P 0) ∧ (J.vertex i) 1 ≠ h with hB
  -- the flipping edges split as A ⊔ B
  have hsplit : (J.upLeftEdges P).card + (J.downLeftEdges P).card = A.card + B.card := by
    have hUD : J.upLeftEdges P ∪ J.downLeftEdges P = A ∪ B := by
      ext i
      simp only [upLeftEdges, downLeftEdges, hA, hB, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨h1, h0, hup⟩ | ⟨h1, h0, hup⟩) | (⟨h1, h0, hdn⟩ | ⟨h1, h0, hdn⟩))
        · exact Or.inl ⟨⟨h1, h0⟩, (ne_of_lt hup).symm⟩
        · exact Or.inr ⟨⟨h1, h0⟩, (ne_of_lt hup).symm⟩
        · exact Or.inl ⟨⟨h1, h0⟩, ne_of_lt hdn⟩
        · exact Or.inr ⟨⟨h1, h0⟩, ne_of_lt hdn⟩
      · rintro (⟨⟨h1, h0⟩, hne⟩ | ⟨⟨h1, h0⟩, hne⟩)
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr (Or.inl ⟨h1, h0, hlt⟩)
          · exact Or.inl (Or.inl ⟨h1, h0, hgt⟩)
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr (Or.inr ⟨h1, h0, hlt⟩)
          · exact Or.inl (Or.inr ⟨h1, h0, hgt⟩)
    have hUDdisj : Disjoint (J.upLeftEdges P) (J.downLeftEdges P) := by
      rw [Finset.disjoint_left]
      intro i hiU hiD
      simp only [upLeftEdges, downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        at hiU hiD
      rcases hiU with ⟨h1, -, hup⟩ | ⟨h1, -, hup⟩ <;>
        rcases hiD with ⟨h1', -, hdn⟩ | ⟨h1', -, hdn⟩ <;> linarith
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
      exact hiB.2 hiA.1.1
    rw [← Finset.card_union_of_disjoint hUDdisj, ← Finset.card_union_of_disjoint hABdisj, hUD]
  -- count A against the left vertices whose outgoing edge is horizontal
  have hAcount : A.card +
      ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h).card =
        (J.leftVertices P).card := by
    have hdisj : Disjoint A ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h) := by
      rw [Finset.disjoint_left]
      intro i hiA hiL
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiL
      exact hiA.2 hiL.2
    have hunion : A ∪ ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h) =
        J.leftVertices P := by
      ext i
      simp only [hA, leftVertices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, hh]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- count B against the left vertices whose incoming edge is horizontal, via the shift bijection
  have hBcount : B.card +
      ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h).card =
        (J.leftVertices P).card := by
    have hBimg : B = ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h).image
        (fun k => k - 1) := by
      ext i
      simp only [hB, leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h0⟩, hne⟩
        exact ⟨i + 1, ⟨⟨h1, h0⟩, by simpa using hne⟩, by ring⟩
      · rintro ⟨k, ⟨⟨h1, h0⟩, hne⟩, rfl⟩
        refine ⟨⟨by simpa using h1, by simpa using h0⟩, by simpa using hne⟩
    have himgcard : B.card =
        ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h).card := by
      rw [hBimg]
      exact Finset.card_image_of_injective _ sub_left_injective
    have hdisj : Disjoint ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h)
        ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h) := by
      rw [Finset.disjoint_left]
      intro i hiA hiL
      simp only [Finset.mem_filter] at hiA hiL
      exact hiA.2 hiL.2
    have hunion : ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h) ∪
        ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h) = J.leftVertices P := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    rw [himgcard, ← Finset.card_union_of_disjoint hdisj, hunion]
  -- horizontal partners stay left, so the two horizontal counts agree via the shift bijection
  have hhoriz : ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h).card =
      ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h).card := by
    apply Finset.card_bij (fun k _ => k + 1)
    · intro k hk
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh] at hk ⊢
      obtain ⟨⟨h1, h0⟩, hpart⟩ := hk
      have hleft : (J.vertex (k + 1)) 0 < P 0 :=
        J.left_of_horizontal_partner hP h1 h0 hpart
          (Or.inl (J.edgeSegment_subset_carrier k))
      exact ⟨⟨hpart, hleft⟩, by simpa using h1⟩
    · intro a _ b _ hab
      exact add_left_injective 1 hab
    · intro k hk
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh] at hk
      obtain ⟨⟨h1, h0⟩, hpart⟩ := hk
      refine ⟨k - 1, ?_, by ring⟩
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh]
      have hseg : segment ℝ (J.vertex (k - 1)) (J.vertex k) ⊆ J.carrier := by
        have hsub := J.edgeSegment_subset_carrier (k - 1)
        rwa [show k - 1 + 1 = k by ring] at hsub
      have hleft : (J.vertex (k - 1)) 0 < P 0 :=
        J.left_of_horizontal_partner hP h1 h0 (l := k - 1) hpart (Or.inr hseg)
      exact ⟨⟨hpart, hleft⟩, by rwa [show k - 1 + 1 = k by ring]⟩
  rw [hsplit, Nat.even_iff]
  omega

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
