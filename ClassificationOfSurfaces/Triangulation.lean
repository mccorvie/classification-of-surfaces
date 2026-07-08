/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.PL

/-!
# Finite surface triangulations

This file isolates the topological theorem boundary produced by the Moise/PL route: every compact
surface in the eval sense admits a finite triangulation whose realization is homeomorphic to the
original surface.
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

namespace PLComplexInSpace.FiniteSupportData

/-- The chosen source vertex for a supported one-simplex. -/
noncomputable def edgeSourceVertex {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (_F : K.FiniteSupportData) (e : _F.OneSimplex) : K.Complex.Vertex :=
  (K.Complex.simplex_nonempty e.1).choose

theorem edgeSourceVertex_mem {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (e : F.OneSimplex) :
    F.edgeSourceVertex e ∈ K.Complex.vertices e.1 :=
  (K.Complex.simplex_nonempty e.1).choose_spec

/-- The chosen target vertex for a supported one-simplex, distinct from the source because
one-simplexes have two vertices. -/
noncomputable def edgeTargetVertex {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (e : F.OneSimplex) : K.Complex.Vertex :=
  let source := F.edgeSourceVertex e
  have hsource : source ∈ K.Complex.vertices e.1 := F.edgeSourceVertex_mem e
  have hcard : (K.Complex.vertices e.1).card = 2 :=
    EuclideanComplex.vertices_card_eq_two_of_mem_oneSimplexes K.Complex
      (F.oneSimplex_mem_complex_oneSimplexes e)
  have hnonempty : ((K.Complex.vertices e.1).erase source).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcardErase : ((K.Complex.vertices e.1).erase source).card = 0 := by
      simp [hempty]
    rw [Finset.card_erase_of_mem hsource, hcard] at hcardErase
    simp at hcardErase
  hnonempty.choose

theorem edgeTargetVertex_mem {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (e : F.OneSimplex) :
    F.edgeTargetVertex e ∈ K.Complex.vertices e.1 := by
  unfold edgeTargetVertex
  dsimp
  exact Finset.mem_of_mem_erase (Classical.choose_spec
    (show ((K.Complex.vertices e.1).erase (F.edgeSourceVertex e)).Nonempty from by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsource : F.edgeSourceVertex e ∈ K.Complex.vertices e.1 :=
        F.edgeSourceVertex_mem e
      have hcard : (K.Complex.vertices e.1).card = 2 :=
        EuclideanComplex.vertices_card_eq_two_of_mem_oneSimplexes K.Complex
          (F.oneSimplex_mem_complex_oneSimplexes e)
      have hcardErase : ((K.Complex.vertices e.1).erase (F.edgeSourceVertex e)).card = 0 := by
        simp [hempty]
      rw [Finset.card_erase_of_mem hsource, hcard] at hcardErase
      simp at hcardErase))

theorem edgeTargetVertex_ne_source {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (e : F.OneSimplex) :
    F.edgeTargetVertex e ≠ F.edgeSourceVertex e := by
  unfold edgeTargetVertex
  dsimp
  exact Finset.ne_of_mem_erase (Classical.choose_spec
    (show ((K.Complex.vertices e.1).erase (F.edgeSourceVertex e)).Nonempty from by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsource : F.edgeSourceVertex e ∈ K.Complex.vertices e.1 :=
        F.edgeSourceVertex_mem e
      have hcard : (K.Complex.vertices e.1).card = 2 :=
        EuclideanComplex.vertices_card_eq_two_of_mem_oneSimplexes K.Complex
          (F.oneSimplex_mem_complex_oneSimplexes e)
      have hcardErase : ((K.Complex.vertices e.1).erase (F.edgeSourceVertex e)).card = 0 := by
        simp [hempty]
      rw [Finset.card_erase_of_mem hsource, hcard] at hcardErase
      simp at hcardErase))

/-- Boundary word for a supported two-simplex, retaining codimension-one faces that are supported
one-simplexes.  Orientations are still scaffold data, so every retained edge is recorded with the
positive orientation. -/
noncomputable def triangleBoundaryWord {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (σ : F.TwoSimplex) : List (OrientedEdge F.OneSimplex) :=
  (K.Complex.boundarySimplexes σ.1).toList.filterMap fun τ =>
    if hτ : τ ∈ F.oneSimplexes then
      some (OrientedEdge.pos ⟨τ, hτ⟩)
    else
      none

theorem edgeVertices_subset_triangleVertices_of_mem_boundaryWord
    {S : Type*} [TopologicalSpace S] {K : PLComplexInSpace S}
    (F : K.FiniteSupportData) (σ : F.TwoSimplex)
    {oe : OrientedEdge F.OneSimplex} (hoe : oe ∈ F.triangleBoundaryWord σ) :
    K.Complex.vertices oe.edge.1 ⊆ K.Complex.vertices σ.1 := by
  unfold triangleBoundaryWord at hoe
  rw [List.mem_filterMap] at hoe
  rcases hoe with ⟨τ, hτmem, hτ⟩
  by_cases hτF : τ ∈ F.oneSimplexes
  · simp only [hτF, ↓reduceDIte] at hτ
    injection hτ with hτoe
    rw [← hτoe]
    rw [Finset.mem_toList] at hτmem
    rw [EuclideanComplex.boundarySimplexes, Finset.mem_filter] at hτmem
    exact hτmem.2.1
  · simp only [hτF, ↓reduceDIte] at hτ
    cases hτ

end PLComplexInSpace.FiniteSupportData

namespace PLComplexInSpace

/-- Convert a finite embedded PL complex covering the ambient surface into the current project
triangulation object.  The vertex type is the complex vertex type, edges are supported
one-simplexes, and triangles are supported two-simplexes. -/
noncomputable def toFiniteSurfaceTriangulation {S : Type*} [TopologicalSpace S]
    (K : PLComplexInSpace S) (covers : K.support = Set.univ)
    (finiteSupport : K.FiniteSupportData) (boundary : K.BoundarySubcomplexData) :
    FiniteSurfaceTriangulation S := by
  classical
  have hsurj : Function.Surjective K.embed := by
    rw [← Set.range_eq_univ]
    exact covers
  exact
    { Vertex := K.Complex.Vertex
      Edge := finiteSupport.OneSimplex
      Triangle := finiteSupport.TwoSimplex
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      edgeFintype := inferInstance
      triangleFintype := inferInstance
      realization := K.Complex.support
      realizationTop := inferInstance
      edgeVertices := fun e => K.Complex.vertices e.1
      triangleVertices := fun σ => K.Complex.vertices σ.1
      edgeSource := finiteSupport.edgeSourceVertex
      edgeTarget := finiteSupport.edgeTargetVertex
      triangleBoundary := finiteSupport.triangleBoundaryWord
      edgeIsBoundary := fun e => e.1 ∈ boundary.boundary.simplexes
      isSurfaceTriangulation :=
        { edge_card := by
            intro e
            exact K.Complex.vertices_card_eq_two_of_mem_oneSimplexes
              (finiteSupport.oneSimplex_mem_complex_oneSimplexes e)
          triangle_card := by
            intro σ
            exact K.Complex.vertices_card_eq_three_of_mem_twoSimplexes
              (finiteSupport.twoSimplex_mem_complex_twoSimplexes σ)
          edgeSource_mem := finiteSupport.edgeSourceVertex_mem
          edgeTarget_mem := finiteSupport.edgeTargetVertex_mem
          edgeSource_ne_edgeTarget := by
            intro e h
            exact finiteSupport.edgeTargetVertex_ne_source e h.symm
          boundary_edge_vertices_subset := by
            intro σ oe hoe
            exact finiteSupport.edgeVertices_subset_triangleVertices_of_mem_boundaryWord σ hoe }
      homeomorphSurface := ⟨K.isEmbedding.toHomeomorphOfSurjective hsurj⟩ }

end PLComplexInSpace

namespace FinitePLTriangulationData

/-- Convert finite PL triangulation data into the public finite surface triangulation object. -/
noncomputable def toFiniteSurfaceTriangulation {S : Type*} [TopologicalSpace S]
    (D : FinitePLTriangulationData S) : FiniteSurfaceTriangulation S :=
  D.K.toFiniteSurfaceTriangulation D.covers D.finiteSupport D.boundary

/-- The finite surface triangulation converted from finite PL data realizes the ambient space. -/
theorem toFiniteSurfaceTriangulation_homeomorphSurface
    {S : Type*} [TopologicalSpace S] (D : FinitePLTriangulationData S) :
    Nonempty (D.toFiniteSurfaceTriangulation.realization ≃ₜ S) :=
  D.toFiniteSurfaceTriangulation.homeomorphSurface

end FinitePLTriangulationData

/-- A space is triangulable if it has a finite surface triangulation in the project sense. -/
def SurfaceTriangulable (S : Type*) [TopologicalSpace S] : Prop :=
  ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S)

/-- Compatibility alias for the initial scaffold name. -/
abbrev FiniteTriangulation (S : Type*) [TopologicalSpace S] :=
  FiniteSurfaceTriangulation S

/-- Compatibility alias for the initial scaffold predicate. -/
abbrev Triangulable (S : Type*) [TopologicalSpace S] :=
  SurfaceTriangulable S

/-- Conversion theorem boundary from Moise's finite PL complex output to the project's finite
surface-triangulation object.

This is the final combinatorial packaging step after the Rado/Moise construction: extract the
finite vertex, edge, and triangle sets from the finite embedded PL complex, record the boundary
subcomplex, and identify the PL realization with the ambient surface by the covering
homeomorphism. -/
theorem finite_pl_complex_to_finite_surface_triangulation
    (S : Type*) [TopologicalSpace S] (K : PLComplexInSpace S)
    (covers : K.support = Set.univ) (finiteSupport : K.FiniteSupportData)
    (boundary : K.BoundarySubcomplexData) :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  let T : FiniteSurfaceTriangulation S :=
    K.toFiniteSurfaceTriangulation covers finiteSupport boundary
  exact ⟨T, T.homeomorphSurface⟩

section MathlibBorderedSurface

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [Nonempty S] [T2Space S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The named finite surface triangulation produced by the Moise--Rado route for a compact
mathlib bordered surface. -/
noncomputable def mathlib_bordered_surface_finiteSurfaceTriangulation :
    FiniteSurfaceTriangulation S :=
  (mathlib_bordered_surface_finitePLTriangulationData S).toFiniteSurfaceTriangulation

/-- The named mathlib bordered-surface triangulation realizes the ambient surface. -/
theorem mathlib_bordered_surface_finiteSurfaceTriangulation_homeomorphSurface :
    Nonempty ((mathlib_bordered_surface_finiteSurfaceTriangulation S).realization ≃ₜ S) := by
  let D := mathlib_bordered_surface_finitePLTriangulationData S
  exact D.toFiniteSurfaceTriangulation_homeomorphSurface

/-- Mathlib bordered-surface hypotheses produce a finite surface triangulation through the
Moise--Rado finite PL triangulation data package. -/
theorem mathlib_bordered_surface_finitely_triangulable :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨mathlib_bordered_surface_finiteSurfaceTriangulation S,
    mathlib_bordered_surface_finiteSurfaceTriangulation_homeomorphSurface S⟩

end MathlibBorderedSurface

section MathlibBorderedSurfaceContMDiff

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [Nonempty S] [T2Space S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S]

/-- The named finite surface triangulation produced by the positive-regularity Moise--Rado route
for a compact mathlib bordered surface. -/
noncomputable def mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff :
    FiniteSurfaceTriangulation S :=
  (mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff S).toFiniteSurfaceTriangulation

/-- The positive-regularity mathlib bordered-surface triangulation realizes the ambient surface. -/
theorem mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff_homeomorphSurface :
    Nonempty
      ((mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff S).realization ≃ₜ S) := by
  let D := mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff S
  exact D.toFiniteSurfaceTriangulation_homeomorphSurface

/-- Positive-regularity mathlib bordered-surface hypotheses produce a finite surface
triangulation through the Moise--Rado finite PL triangulation data package. -/
theorem mathlib_bordered_surface_finitely_triangulable_of_contMDiff :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff S,
    mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff_homeomorphSurface S⟩

end MathlibBorderedSurfaceContMDiff

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- The named finite surface triangulation produced for a compact Eval surface. -/
noncomputable def compact_eval_surface_finiteSurfaceTriangulation :
    FiniteSurfaceTriangulation S :=
  mathlib_bordered_surface_finiteSurfaceTriangulation S

/-- The named compact Eval surface triangulation realizes the ambient surface. -/
theorem compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface :
    Nonempty ((compact_eval_surface_finiteSurfaceTriangulation S).realization ≃ₜ S) :=
  mathlib_bordered_surface_finiteSurfaceTriangulation_homeomorphSurface S

/-- Moise/PL theorem boundary: compact Eval surfaces admit finite triangulations. -/
theorem compact_eval_surface_finitely_triangulable :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨compact_eval_surface_finiteSurfaceTriangulation S,
    compact_eval_surface_finiteSurfaceTriangulation_homeomorphSurface S⟩

/-- Compatibility theorem for the initial scaffold name. -/
theorem compact_surface_triangulable : Triangulable S :=
  compact_eval_surface_finitely_triangulable S

end EvalHypotheses

section EvalHypothesesContMDiff

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S]

/-- The named finite surface triangulation produced for a compact positive-regularity Eval
surface. -/
noncomputable def compact_eval_surface_finiteSurfaceTriangulation_of_contMDiff :
    FiniteSurfaceTriangulation S :=
  mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff S

/-- The named compact positive-regularity Eval surface triangulation realizes the ambient
surface. -/
theorem compact_eval_surface_finiteSurfaceTriangulation_of_contMDiff_homeomorphSurface :
    Nonempty
      ((compact_eval_surface_finiteSurfaceTriangulation_of_contMDiff S).realization ≃ₜ S) :=
  mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff_homeomorphSurface S

/-- Positive-regularity compact Eval surfaces admit finite triangulations by the proved
Moise--Rado route. -/
theorem compact_eval_surface_finitely_triangulable_of_contMDiff :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  exact ⟨compact_eval_surface_finiteSurfaceTriangulation_of_contMDiff S,
    compact_eval_surface_finiteSurfaceTriangulation_of_contMDiff_homeomorphSurface S⟩

end EvalHypothesesContMDiff

end ClassificationOfSurfaces
end Topology
end LeanEval
