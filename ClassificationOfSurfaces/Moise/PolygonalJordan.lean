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
