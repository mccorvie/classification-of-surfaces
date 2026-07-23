/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.ChartInduction
import ClassificationOfSurfaces.Moise.GeometricTriangulation

/-!
# Finite surface triangulations

The legacy triangulation package consumed by the cell-complex conversion, now fed exclusively by
the faithful `GeometricTriangulation` object through the compatibility bridge
(`GeometricTriangulation.toFiniteSurfaceTriangulation`).  Radó's theorem enters as
`moise_triangulation`, proved from the Moise-route boundaries in
`ClassificationOfSurfaces/Moise/` (see `docs/MOISE_ROUTE.md`).

`FiniteSurfaceTriangulation` itself is in the weakness ledger (`docs/KNOWN_WEAK.md`): its
combinatorial data is not linked to its realization, so build new work on
`GeometricTriangulation` instead.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- An oriented use of an edge in a triangle boundary word. -/
inductive OrientedEdge (α : Type*) where
  | pos : α → OrientedEdge α
  | neg : α → OrientedEdge α
deriving DecidableEq, Repr, Fintype

namespace OrientedEdge

/-- The underlying unoriented edge. -/
def edge {α : Type*} : OrientedEdge α → α
  | pos e => e
  | neg e => e

/-- Reverse an oriented edge. -/
def flip {α : Type*} : OrientedEdge α → OrientedEdge α
  | pos e => neg e
  | neg e => pos e

@[simp] theorem flip_flip {α : Type*} (e : OrientedEdge α) : flip (flip e) = e := by
  cases e <;> rfl

end OrientedEdge

/-- Finite combinatorial validity data for the project triangulation object.

This deliberately stays close to what the current PL complex handoff can prove:
edges have two vertices, triangles have three vertices, recorded endpoints lie
on their edge, and every edge appearing in a triangle boundary is a face of that
triangle.  Cyclic ordering and quotient-realization geometry are separate
theorem boundaries. -/
structure FiniteSurfaceTriangulation.Valid
    (Vertex Edge Triangle : Type*) [DecidableEq Vertex]
    (edgeVertices : Edge → Finset Vertex)
    (triangleVertices : Triangle → Finset Vertex)
    (edgeSource edgeTarget : Edge → Vertex)
    (triangleBoundary : Triangle → List (OrientedEdge Edge)) : Prop where
  edge_card : ∀ e : Edge, (edgeVertices e).card = 2
  triangle_card : ∀ t : Triangle, (triangleVertices t).card = 3
  edgeSource_mem : ∀ e : Edge, edgeSource e ∈ edgeVertices e
  edgeTarget_mem : ∀ e : Edge, edgeTarget e ∈ edgeVertices e
  edgeSource_ne_edgeTarget : ∀ e : Edge, edgeSource e ≠ edgeTarget e
  boundary_edge_vertices_subset :
    ∀ t : Triangle, ∀ oe ∈ triangleBoundary t,
      edgeVertices oe.edge ⊆ triangleVertices t

/-- A finite triangulation of a topological surface.

This should eventually be replaced by, or bridged to, the best available mathlib notion of finite
simplicial/CW complex realization.  For now it records the public API needed by the common
triangulation-to-cell-complex bridge: finite incidence data, a topological realization, and a
homeomorphism from that realization to the target surface. -/
structure FiniteSurfaceTriangulation (S : Type*) [TopologicalSpace S] where
  Vertex : Type
  Edge : Type
  Triangle : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  edgeFintype : Fintype Edge
  triangleFintype : Fintype Triangle
  realization : Type
  realizationTop : TopologicalSpace realization
  edgeVertices : Edge → Finset Vertex
  triangleVertices : Triangle → Finset Vertex
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  triangleBoundary : Triangle → List (OrientedEdge Edge)
  edgeIsBoundary : Edge → Prop
  isSurfaceTriangulation :
    FiniteSurfaceTriangulation.Valid Vertex Edge Triangle edgeVertices triangleVertices
      edgeSource edgeTarget triangleBoundary
  homeomorphSurface : Nonempty (realization ≃ₜ S)

attribute [instance] FiniteSurfaceTriangulation.realizationTop
attribute [instance] FiniteSurfaceTriangulation.vertexFintype
attribute [instance] FiniteSurfaceTriangulation.vertexDecidableEq
attribute [instance] FiniteSurfaceTriangulation.edgeFintype
attribute [instance] FiniteSurfaceTriangulation.triangleFintype

namespace FiniteSurfaceTriangulation

/-- Number of vertices in a finite surface triangulation. -/
def numVertices {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Vertex

/-- Number of edges in a finite surface triangulation. -/
def numEdges {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Edge

/-- Number of triangles in a finite surface triangulation. -/
def numTriangles {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) : ℕ :=
  Fintype.card T.Triangle

/-- Source vertex of an oriented edge occurrence in a triangulation. -/
def orientedEdgeSource {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeSource e
  | OrientedEdge.neg e => T.edgeTarget e

/-- Target vertex of an oriented edge occurrence in a triangulation. -/
def orientedEdgeTarget {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    OrientedEdge T.Edge → T.Vertex
  | OrientedEdge.pos e => T.edgeTarget e
  | OrientedEdge.neg e => T.edgeSource e

end FiniteSurfaceTriangulation


namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

/-- The boundary word of a face of a geometric triangulation: its two-element subsets, listed
with the positive orientation. -/
noncomputable def triangleBoundary (t : T.Triangle) : List (OrientedEdge T.Edge) :=
  (t.1.powersetCard 2).toList.attach.map fun e =>
    OrientedEdge.pos
      ⟨e.1,
        T.mem_edges_of_subset_face t.2
          (Finset.mem_powersetCard.mp (Finset.mem_toList.mp e.2)).1
          (Finset.mem_powersetCard.mp (Finset.mem_toList.mp e.2)).2⟩

theorem edge_subset_of_mem_triangleBoundary {t : T.Triangle} {oe : OrientedEdge T.Edge}
    (hoe : oe ∈ T.triangleBoundary t) : oe.edge.1 ⊆ t.1 := by
  unfold triangleBoundary at hoe
  rw [List.mem_map] at hoe
  rcases hoe with ⟨e, _he, rfl⟩
  exact (Finset.mem_powersetCard.mp (Finset.mem_toList.mp e.2)).1

/-- Package a geometric triangulation as the project's `FiniteSurfaceTriangulation` object.

This is the compatibility bridge: downstream consumers (the cell-complex conversion and the
Gallier--Xu route) keep their interface, while the triangulation content now lives in the
faithful geometric object. -/
noncomputable def toFiniteSurfaceTriangulation : FiniteSurfaceTriangulation S where
  Vertex := T.Vertex
  Edge := T.Edge
  Triangle := T.Triangle
  vertexFintype := T.vertexFintype
  vertexDecidableEq := T.vertexDecidableEq
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := T.realization
  realizationTop := inferInstance
  edgeVertices := fun e => e.1
  triangleVertices := fun t => t.1
  edgeSource := T.edgeSource
  edgeTarget := T.edgeTarget
  triangleBoundary := T.triangleBoundary
  edgeIsBoundary := fun e => T.IsBoundaryEdge e
  isSurfaceTriangulation :=
    { edge_card := T.edge_card
      triangle_card := T.triangle_card
      edgeSource_mem := T.edgeSource_mem
      edgeTarget_mem := T.edgeTarget_mem
      edgeSource_ne_edgeTarget := T.edgeSource_ne_edgeTarget
      boundary_edge_vertices_subset := fun _t _oe hoe =>
        T.edge_subset_of_mem_triangleBoundary hoe }
  homeomorphSurface := ⟨T.homeo⟩

/-- The bridge realizes the ambient space. -/
theorem toFiniteSurfaceTriangulation_homeomorphSurface :
    Nonempty (T.toFiniteSurfaceTriangulation.realization ≃ₜ S) :=
  T.toFiniteSurfaceTriangulation.homeomorphSurface

end GeometricTriangulation

/-- Compatibility alias for the initial scaffold name. -/
abbrev FiniteTriangulation (S : Type*) [TopologicalSpace S] :=
  FiniteSurfaceTriangulation S


section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- Radó's theorem (Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 8, Thm. 3; bordered
version): every compact surface in the Eval sense admits a finite geometric triangulation — a
homeomorphism onto the realization of a finite two-dimensional simplicial complex.

Semantic anchors: the conclusion implies `CompactSpace S` and `T2Space S`
(`GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`), and is refuted for
non-compact spaces (`Moise/Countermodels.lean`), so it cannot be discharged by a junk witness.

The proof is the assembled boundary-preserving Radó chart induction
(`Moise.moise_triangulation_of_boundaries`). -/
theorem moise_triangulation : Nonempty (GeometricTriangulation S) :=
  Moise.moise_triangulation_of_boundaries S

/-- Radó's theorem for compact boundaryless Eval surfaces.  This specialization uses emptiness of
the ambient manifold boundary to supply a simpler certificate to the shared crossing-weld
implementation. -/
theorem moise_triangulation_boundaryless
    [BoundarylessManifold (modelWithCornersEuclideanHalfSpace 2) S] :
    Nonempty (GeometricTriangulation S) :=
  Moise.moise_triangulation_boundaryless S

/-- The named finite surface triangulation produced for a compact Eval surface, obtained from the
geometric triangulation boundary `moise_triangulation` through the compatibility bridge. -/
noncomputable def compact_eval_surface_finiteSurfaceTriangulation :
    FiniteSurfaceTriangulation S :=
  (Classical.choice (moise_triangulation S)).toFiniteSurfaceTriangulation

/-- The named compact Eval surface triangulation realizes the ambient surface. -/
theorem compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface :
    Nonempty ((compact_eval_surface_finiteSurfaceTriangulation S).realization ≃ₜ S) :=
  (compact_eval_surface_finiteSurfaceTriangulation S).homeomorphSurface

/-- Moise/PL theorem boundary: compact Eval surfaces admit finite triangulations. -/
theorem compact_eval_surface_finitely_triangulable :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨compact_eval_surface_finiteSurfaceTriangulation S,
    compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface S⟩

end EvalHypotheses


end ClassificationOfSurfaces
end Topology
end LeanEval
