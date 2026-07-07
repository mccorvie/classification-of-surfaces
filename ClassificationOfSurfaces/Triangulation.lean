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

/-- Placeholder for a finite triangulation of a topological surface.

This should eventually be replaced by, or bridged to, the best available mathlib notion of finite
simplicial/CW complex realization. For now it records the public API needed by the common
triangulation-to-cell-complex bridge: a topological realization and a homeomorphism from that
realization to the target surface. -/
structure FiniteSurfaceTriangulation (S : Type*) [TopologicalSpace S] where
  Vertex : Type
  Edge : Type
  Triangle : Type
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  triangleFintype : Fintype Triangle
  realization : Type
  realizationTop : TopologicalSpace realization
  edgeSource : Edge → Vertex
  edgeTarget : Edge → Vertex
  triangleBoundary : Triangle → List (OrientedEdge Edge)
  edgeIsBoundary : Edge → Prop
  isSurfaceTriangulation : Prop
  homeomorphSurface : Nonempty (realization ≃ₜ S)

attribute [instance] FiniteSurfaceTriangulation.realizationTop
attribute [instance] FiniteSurfaceTriangulation.vertexFintype
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
      edgeFintype := inferInstance
      triangleFintype := inferInstance
      realization := K.Complex.support
      realizationTop := inferInstance
      edgeSource := fun e => (K.Complex.simplex_nonempty e.1).choose
      edgeTarget := fun e => (K.Complex.simplex_nonempty e.1).choose
      triangleBoundary := finiteSupport.triangleBoundaryWord
      edgeIsBoundary := fun e => e.1 ∈ boundary.boundary.simplexes
      isSurfaceTriangulation := True
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

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- Moise/PL theorem boundary: compact Eval surfaces admit finite triangulations. -/
theorem compact_eval_surface_finitely_triangulable :
    ∃ T : FiniteSurfaceTriangulation S, Nonempty (T.realization ≃ₜ S) := by
  rcases eval_surface_to_moise_bordered_surface S with ⟨_hM, _⟩
  rcases rado_bordered_surface_triangulation S with ⟨K, hK, finiteSupport, boundary, _⟩
  exact finite_pl_complex_to_finite_surface_triangulation S K hK finiteSupport boundary

/-- Compatibility theorem for the initial scaffold name. -/
theorem compact_surface_triangulable : Triangulable S :=
  compact_eval_surface_finitely_triangulable S

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
