/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.ChartInduction
import ClassificationOfSurfaces.Moise.GeometricTriangulation
import Mathlib.Data.List.Rotate

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

/-- A position in one of the stored oriented triangle boundaries. -/
abbrev BoundaryPosition {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) :=
  Σ t : T.Triangle, Fin (T.triangleBoundary t).length

namespace BoundaryPosition

/-- The oriented edge stored at a triangle-boundary position. -/
def orientedEdge {S : Type*} [TopologicalSpace S] {T : FiniteSurfaceTriangulation S}
    (o : T.BoundaryPosition) : OrientedEdge T.Edge :=
  (T.triangleBoundary o.1).get o.2

/-- The unoriented edge stored at a triangle-boundary position. -/
def edge {S : Type*} [TopologicalSpace S] {T : FiniteSurfaceTriangulation S}
    (o : T.BoundaryPosition) : T.Edge :=
  o.orientedEdge.edge

end BoundaryPosition

/-- Two triangles are adjacent when their stored boundaries share an unoriented edge. -/
def TriangleAdjacent {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) (f g : T.Triangle) : Prop :=
  ∃ df ∈ T.triangleBoundary f, ∃ dg ∈ T.triangleBoundary g, df.edge = dg.edge

/-- Incidence information needed by the legacy triangulation-to-cell-complex bridge.

`edge_valence_le_two` is deliberately stated for boundary positions rather than merely named
edges. This detects repeated uses inside one boundary word as well as uses by different triangles.
The separate `edge_used` field is necessary because the legacy triangulation type can contain
named edges which occur in no triangle boundary. Genuine geometric triangulations will discharge
both fields from their generated two-vertex faces. -/
structure IncidenceCertificate {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) : Prop where
  triangle_nonempty : Nonempty T.Triangle
  boundary_rotated_injective :
    ∀ f g, (T.triangleBoundary f).IsRotated (T.triangleBoundary g) → f = g
  edge_used : ∀ e, ∃ o : T.BoundaryPosition, o.edge = e
  edge_valence_le_two :
    ∀ e (o₀ o₁ o₂ : T.BoundaryPosition),
      o₀.edge = e → o₁.edge = e → o₂.edge = e →
        o₀ = o₁ ∨ o₀ = o₂ ∨ o₁ = o₂
  dual_connected :
    ∀ f g, Relation.ReflTransGen T.TriangleAdjacent f g

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

/-- Each geometric edge occurs at most once in a triangle's canonical boundary list. -/
theorem triangleBoundary_nodup (t : T.Triangle) : (T.triangleBoundary t).Nodup := by
  unfold triangleBoundary
  apply ((t.1.powersetCard 2).nodup_toList.attach).map
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun oe : OrientedEdge T.Edge => oe.edge.1) hab

/-- A geometric edge occurs in a canonical triangle boundary exactly when it is a face of that
triangle. -/
theorem pos_mem_triangleBoundary_iff (t : T.Triangle) (e : T.Edge) :
    OrientedEdge.pos e ∈ T.triangleBoundary t ↔ e.1 ⊆ t.1 := by
  constructor
  · exact fun h => T.edge_subset_of_mem_triangleBoundary h
  · intro he
    unfold triangleBoundary
    rw [List.mem_map]
    have hepow : e.1 ∈ t.1.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨he, T.edge_card e⟩
    have helist : e.1 ∈ (t.1.powersetCard 2).toList :=
      Finset.mem_toList.mpr hepow
    let a : {x // x ∈ (t.1.powersetCard 2).toList} := ⟨e.1, helist⟩
    refine ⟨a, by simp [a], ?_⟩
    apply congrArg OrientedEdge.pos
    apply Subtype.ext
    rfl

/-- Every canonical triangle boundary has its three geometric edges. -/
theorem triangleBoundary_length (t : T.Triangle) :
    (T.triangleBoundary t).length = 3 := by
  simp [triangleBoundary, T.triangle_card t]

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

private theorem eq_pos_of_mem_triangleBoundary
    {t : T.Triangle} {oe : OrientedEdge T.Edge}
    (hoe : oe ∈ T.triangleBoundary t) : ∃ e, oe = OrientedEdge.pos e := by
  unfold triangleBoundary at hoe
  rw [List.mem_map] at hoe
  rcases hoe with ⟨e, _he, rfl⟩
  exact ⟨_, rfl⟩

private theorem boundaryPosition_eq_of_fst_eq_of_edge_eq
    {o p : T.toFiniteSurfaceTriangulation.BoundaryPosition}
    (hface : o.1 = p.1) (hedge : o.edge = p.edge) : o = p := by
  rcases o with ⟨f, i⟩
  rcases p with ⟨g, j⟩
  simp only at hface
  subst g
  have hi := List.get_mem (T.triangleBoundary f) i
  have hj := List.get_mem (T.triangleBoundary f) j
  obtain ⟨ei, hei⟩ := T.eq_pos_of_mem_triangleBoundary hi
  obtain ⟨ej, hej⟩ := T.eq_pos_of_mem_triangleBoundary hj
  change ((T.triangleBoundary f).get i).edge =
    ((T.triangleBoundary f).get j).edge at hedge
  have hget : (T.triangleBoundary f).get i =
      (T.triangleBoundary f).get j := by
    rw [hei, hej]
    rw [hei, hej] at hedge
    simp only [OrientedEdge.edge] at hedge
    simpa using hedge
  have hij : i = j := (T.triangleBoundary_nodup f).injective_get hget
  subst j
  rfl

private theorem powersetCard_eq_of_boundary_rotated
    {f g : T.Triangle}
    (hrot : (T.triangleBoundary f).IsRotated (T.triangleBoundary g)) :
    f.1.powersetCard 2 = g.1.powersetCard 2 := by
  ext e
  constructor
  · intro he
    let E : T.Edge := ⟨e, T.mem_edges_of_subset_face f.2
      (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp he).2⟩
    have hmemf : OrientedEdge.pos E ∈ T.triangleBoundary f :=
      (T.pos_mem_triangleBoundary_iff f E).mpr
        (Finset.mem_powersetCard.mp he).1
    have hmemg : OrientedEdge.pos E ∈ T.triangleBoundary g :=
      hrot.mem_iff.mp hmemf
    exact Finset.mem_powersetCard.mpr ⟨
      T.edge_subset_of_mem_triangleBoundary hmemg,
      (Finset.mem_powersetCard.mp he).2⟩
  · intro he
    let E : T.Edge := ⟨e, T.mem_edges_of_subset_face g.2
      (Finset.mem_powersetCard.mp he).1
      (Finset.mem_powersetCard.mp he).2⟩
    have hmemg : OrientedEdge.pos E ∈ T.triangleBoundary g :=
      (T.pos_mem_triangleBoundary_iff g E).mpr
        (Finset.mem_powersetCard.mp he).1
    have hmemf : OrientedEdge.pos E ∈ T.triangleBoundary f :=
      hrot.mem_iff.mpr hmemg
    exact Finset.mem_powersetCard.mpr ⟨
      T.edge_subset_of_mem_triangleBoundary hmemf,
      (Finset.mem_powersetCard.mp he).2⟩

private theorem faceAdjacent_to_triangleAdjacent
    {f g : TriangleFamily.Face T.faces}
    (hfg : TriangleFamily.FaceAdjacent T.faces f g) :
    T.toFiniteSurfaceTriangulation.TriangleAdjacent f g := by
  rcases hfg with ⟨e, hecard, hef, heg⟩
  let E : T.Edge := ⟨e, T.mem_edges_of_subset_face f.2 hef hecard⟩
  refine ⟨OrientedEdge.pos E,
    (T.pos_mem_triangleBoundary_iff f E).mpr hef,
    OrientedEdge.pos E, ?_, rfl⟩
  exact (T.pos_mem_triangleBoundary_iff g E).mpr heg

/-- A geometric surface-incidence certificate supplies every incidence obligation required by
the legacy finite triangulation bridge. -/
theorem incidenceCertificate_of_surfaceIncidence
    (h : T.SurfaceIncidence) :
    T.toFiniteSurfaceTriangulation.IncidenceCertificate := by
  classical
  refine {
    triangle_nonempty := ?_
    boundary_rotated_injective := ?_
    edge_used := ?_
    edge_valence_le_two := ?_
    dual_connected := ?_ }
  · rcases h.faces_nonempty with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · intro f g hrot
    apply Subtype.ext
    exact Finset.eq_of_powersetCard_eq
      ((T.triangle_card f).trans (T.triangle_card g).symm)
      (by decide) (by simp [T.triangle_card f])
      (T.powersetCard_eq_of_boundary_rotated hrot)
  · intro e
    rcases Finset.mem_biUnion.mp e.2 with ⟨t, ht, hep⟩
    let f : T.toFiniteSurfaceTriangulation.Triangle := ⟨t, ht⟩
    have hmem : OrientedEdge.pos e ∈
        T.toFiniteSurfaceTriangulation.triangleBoundary f := by
      change OrientedEdge.pos e ∈
        T.triangleBoundary (⟨t, ht⟩ : T.Triangle)
      exact (T.pos_mem_triangleBoundary_iff _ _).mpr
        (Finset.mem_powersetCard.mp hep).1
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
    refine ⟨⟨f, i⟩, ?_⟩
    simp only [FiniteSurfaceTriangulation.BoundaryPosition.edge,
      FiniteSurfaceTriangulation.BoundaryPosition.orientedEdge, hi,
      OrientedEdge.edge]
  · intro e o₀ o₁ o₂ ho₀ ho₁ ho₂
    by_contra hdistinct
    simp only [not_or] at hdistinct
    rcases hdistinct with ⟨ho₀₁, ho₀₂, ho₁₂⟩
    have hf₀₁ : o₀.1 ≠ o₁.1 := fun hfaces ↦
      ho₀₁ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₀.trans ho₁.symm))
    have hf₀₂ : o₀.1 ≠ o₂.1 := fun hfaces ↦
      ho₀₂ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₀.trans ho₂.symm))
    have hf₁₂ : o₁.1 ≠ o₂.1 := fun hfaces ↦
      ho₁₂ (T.boundaryPosition_eq_of_fst_eq_of_edge_eq hfaces
        (ho₁.trans ho₂.symm))
    have hs₀ : e.1 ⊆ o₀.1.1 := by
      rw [← ho₀]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₀.1) o₀.2)
    have hs₁ : e.1 ⊆ o₁.1.1 := by
      rw [← ho₁]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₁.1) o₁.2)
    have hs₂ : e.1 ⊆ o₂.1.1 := by
      rw [← ho₂]
      exact T.edge_subset_of_mem_triangleBoundary
        (List.get_mem (T.triangleBoundary o₂.1) o₂.2)
    have hm₀ : o₀.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₀.1.2, hs₀⟩
    have hm₁ : o₁.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₁.1.2, hs₁⟩
    have hm₂ : o₂.1.1 ∈ T.faces.filter fun t ↦ e.1 ⊆ t :=
      Finset.mem_filter.mpr ⟨o₂.1.2, hs₂⟩
    have hv₀₁ : o₀.1.1 ≠ o₁.1.1 := fun hv ↦ hf₀₁ (Subtype.ext hv)
    have hv₀₂ : o₀.1.1 ≠ o₂.1.1 := fun hv ↦ hf₀₂ (Subtype.ext hv)
    have hv₁₂ : o₁.1.1 ≠ o₂.1.1 := fun hv ↦ hf₁₂ (Subtype.ext hv)
    have hthree : 2 < (T.faces.filter fun t ↦ e.1 ⊆ t).card :=
      Finset.two_lt_card_iff.mpr
        ⟨o₀.1.1, o₁.1.1, o₂.1.1, hm₀, hm₁, hm₂,
          hv₀₁, hv₀₂, hv₁₂⟩
    have heEdges : e.1 ∈ TriangleFamily.edges T.faces := by
      exact e.2
    exact (Nat.not_lt_of_ge (h.edge_valence_le_two e.1 heEdges)) hthree
  · intro f g
    exact (h.dual_connected f g).mono fun _ _ ↦
      T.faceAdjacent_to_triangleAdjacent

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
variable [ChartBoundaryInvariant S]

/-- Radó's theorem (Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 8, Thm. 3; bordered
version): every compact surface in the Eval sense admits a finite geometric triangulation — a
homeomorphism onto the realization of a finite two-dimensional simplicial complex.

Semantic anchors: the conclusion implies `CompactSpace S` and `T2Space S`
(`GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`), and is refuted for
non-compact spaces (`Moise/Countermodels.lean`), so it cannot be discharged by a junk witness.

The proof is the assembled Radó chart induction (`Moise.moise_triangulation_of_boundaries`); the
remaining hard content sits on its two named boundaries, `Moise.moise_finite_chart_cover`
(a port of the proven `PL.lean` spine) and `Moise.moise_induction_step` (which will consume the
polygonal Jordan/Schoenflies theorems and PL approximation, Moise Ch. 2-6). -/
theorem moise_triangulation : Nonempty (GeometricTriangulation S) :=
  Moise.moise_triangulation_of_boundaries S

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
