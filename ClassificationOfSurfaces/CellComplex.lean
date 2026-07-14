/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Triangulation

/-!
# Finite surface cell complexes

This file owns the shared combinatorial API between the topological triangulation route and the
Gallier-Xu normal-form route. The definitions are still intentionally light, but the public names
and theorem boundaries match the Moise/PL blueprint.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- A deliberately small API for Gallier-Xu finite surface cell complexes.

The fields expose the main finite types, oriented darts, pairing, vertices, face boundary words,
and realization type expected by downstream APIs. Surface validity and connectivity are not data:
they are the predicates `SurfaceCellComplex.IsSurfaceValid` and `SurfaceCellComplex.IsConnected`,
computed from the incidence data below and assumed as explicit hypotheses by the theorems that
need them. -/
structure SurfaceCellComplex where
  Face : Type
  Dart : Type
  Vertex : Type
  realization : Type
  faceFintype : Fintype Face
  dartFintype : Fintype Dart
  vertexFintype : Fintype Vertex
  realizationTop : TopologicalSpace realization
  inv : Dart ≃ Dart
  source : Dart → Vertex
  target : Dart → Vertex
  boundary : Face → List Dart
  isBoundaryDart : Dart → Prop
  inv_involutive : ∀ d, inv (inv d) = d
  inv_source : ∀ d, source (inv d) = target d
  inv_target : ∀ d, target (inv d) = source d

attribute [instance] SurfaceCellComplex.faceFintype
attribute [instance] SurfaceCellComplex.dartFintype
attribute [instance] SurfaceCellComplex.vertexFintype
attribute [instance] SurfaceCellComplex.realizationTop

namespace SurfaceCellComplex

/-- The number of faces in a finite surface cell complex. -/
def numFaces (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Face

/-- The number of oriented darts in a finite surface cell complex. -/
def numDarts (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Dart

/-- The number of vertices in a finite surface cell complex. -/
def numVertices (K : SurfaceCellComplex) : ℕ :=
  Fintype.card K.Vertex

/-- The length of a face boundary word. -/
def faceBoundaryLength (K : SurfaceCellComplex) (f : K.Face) : ℕ :=
  (K.boundary f).length

open Classical in
/-- Number of occurrences, across all face boundary words, of the unoriented edge underlying the
dart `d`: occurrences of either `d` itself or of its reversal `K.inv d`.

Stated with classical decidability so that it makes sense for an arbitrary complex; on concrete
complexes it is computed through `oneFacePresentation_edgePairOccurrences` and its analogues. -/
noncomputable def edgePairOccurrences (K : SurfaceCellComplex) (d : K.Dart) : ℕ :=
  ∑ f : K.Face, (K.boundary f).countP fun x => decide (x = d ∨ x = K.inv d)

/-- Surface validity computed from the incidence data, after Gallier-Xu Definition 6.1: no dart
is its own reversal, being a boundary dart is orientation-invariant, every interior edge occurs
exactly twice among the face boundary words, and every boundary edge occurs exactly once.

This is deliberately a `Prop`-valued predicate rather than a field of `SurfaceCellComplex`:
theorems that need validity must assume it explicitly, and junk complexes are refutable (see the
vacuity probes in `Examples.lean`). -/
structure IsSurfaceValid (K : SurfaceCellComplex) : Prop where
  inv_ne : ∀ d, K.inv d ≠ d
  isBoundaryDart_inv : ∀ d, K.isBoundaryDart (K.inv d) ↔ K.isBoundaryDart d
  interior_pair : ∀ d, ¬K.isBoundaryDart d → K.edgePairOccurrences d = 2
  boundary_single : ∀ d, K.isBoundaryDart d → K.edgePairOccurrences d = 1

/-- One-step adjacency between vertices: some dart runs from `v` to `w`. -/
def VertexAdj (K : SurfaceCellComplex) (v w : K.Vertex) : Prop :=
  ∃ d, K.source d = v ∧ K.target d = w

/-- Combinatorial connectivity computed from the incidence data: the vertex set is nonempty and
any two vertices are joined by a chain of darts.

Like `IsSurfaceValid`, this is a predicate assumed by theorems as needed, not a data field. -/
structure IsConnected (K : SurfaceCellComplex) : Prop where
  nonempty : Nonempty K.Vertex
  joined : ∀ v w : K.Vertex, Relation.ReflTransGen K.VertexAdj v w

/-- A signed occurrence of a named edge in a polygonal boundary word. -/
inductive SignedDart (α : Type*) where
  | pos : α → SignedDart α
  | neg : α → SignedDart α
deriving DecidableEq, Repr, Fintype

namespace SignedDart

/-- Reverse the orientation of a signed dart. -/
def flip {α : Type*} : SignedDart α → SignedDart α
  | pos a => neg a
  | neg a => pos a

@[simp] theorem flip_flip {α : Type*} (d : SignedDart α) : flip (flip d) = d := by
  cases d <;> rfl

/-- Orientation reversal as an equivalence. -/
def flipEquiv (α : Type*) : SignedDart α ≃ SignedDart α where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

@[simp] theorem flipEquiv_apply {α : Type*} (d : SignedDart α) : flipEquiv α d = flip d :=
  rfl

end SignedDart

/-- A single-face polygonal presentation with all edge names based at one vertex.

This constructor is intentionally simple. It is useful for normal-form examples and for testing the
Gallier-Xu boundary-word API before the full realization/gluing semantics are implemented. -/
def oneFacePresentation (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop := fun _ => False) :
    SurfaceCellComplex where
  Face := PUnit
  Dart := SignedDart Edge
  Vertex := PUnit
  realization := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  realizationTop := inferInstance
  inv := SignedDart.flipEquiv Edge
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun _ => word
  isBoundaryDart := fun
    | SignedDart.pos e => boundaryEdge e
    | SignedDart.neg e => boundaryEdge e
  inv_involutive := SignedDart.flip_flip
  inv_source := by
    intro d
    rfl
  inv_target := by
    intro d
    rfl

/-- A one-face presentation is combinatorially connected: it has a single vertex. -/
theorem oneFacePresentation_isConnected (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop := fun _ => False) :
    (oneFacePresentation Edge word boundaryEdge).IsConnected :=
  ⟨⟨PUnit.unit⟩, fun v w => by cases v; cases w; exact Relation.ReflTransGen.refl⟩

/-- No dart of a one-face presentation is its own reversal. -/
theorem oneFacePresentation_inv_ne (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop) :
    ∀ d, (oneFacePresentation Edge word boundaryEdge).inv d ≠ d := by
  intro d h
  have h' : SignedDart.flip d = d := h
  cases d <;> simp [SignedDart.flip] at h'

/-- Boundary-dart marking of a one-face presentation is orientation-invariant. -/
theorem oneFacePresentation_isBoundaryDart_inv (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop) :
    ∀ d, (oneFacePresentation Edge word boundaryEdge).isBoundaryDart
        ((oneFacePresentation Edge word boundaryEdge).inv d) ↔
      (oneFacePresentation Edge word boundaryEdge).isBoundaryDart d := by
  intro d
  cases d <;> exact Iff.rfl

/-- In a one-face presentation the edge-pair occurrence count is a count in the single boundary
word, computed with the decidable equality of `SignedDart`. -/
theorem oneFacePresentation_edgePairOccurrences (Edge : Type) [Fintype Edge] [DecidableEq Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop) (d : SignedDart Edge) :
    (oneFacePresentation Edge word boundaryEdge).edgePairOccurrences d =
      word.countP fun x => decide (x = d ∨ x = SignedDart.flip d) := by
  simp only [edgePairOccurrences, oneFacePresentation, Finset.univ_unique, Finset.sum_singleton]
  refine List.countP_congr fun x _ => ?_
  simp only [decide_eq_true_eq]
  exact Iff.rfl

/-- Convert an oriented triangulation edge occurrence to a cell-complex signed dart. -/
def signedDartOfOrientedEdge {Edge : Type*} :
    OrientedEdge Edge → SignedDart Edge
  | OrientedEdge.pos e => SignedDart.pos e
  | OrientedEdge.neg e => SignedDart.neg e

/-- Polygonal pre-realization carrier.

This is currently the same carrier as `Realization`; the future quotient model should replace this
with the finite disjoint union of standard polygons. -/
abbrev PreRealization (K : SurfaceCellComplex) : Type := K.realization

/-- Placeholder gluing relation on the polygonal pre-realization. -/
def gluingRel (K : SurfaceCellComplex) : Setoid K.PreRealization :=
  ⊥

/-- Blueprint spelling for the placeholder gluing relation. -/
abbrev GluingRel (K : SurfaceCellComplex) : Setoid K.PreRealization :=
  K.gluingRel

/-- Realization of a surface cell complex as a topological space. -/
abbrev Realization (K : SurfaceCellComplex) : Type := K.realization

instance (K : SurfaceCellComplex) : TopologicalSpace K.Realization :=
  K.realizationTop

/-- Placeholder sphere surface cell complex. -/
def sphere : SurfaceCellComplex where
  Face := PUnit
  Dart := Empty
  Vertex := PUnit
  realization := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  realizationTop := inferInstance
  inv := Equiv.refl Empty
  source := Empty.elim
  target := Empty.elim
  boundary := fun _ => []
  isBoundaryDart := Empty.elim
  inv_involutive := by
    intro d
    cases d
  inv_source := by
    intro d
    cases d
  inv_target := by
    intro d
    cases d

/-- The placeholder sphere complex is surface-valid: it has no darts at all. -/
theorem sphere_isSurfaceValid : sphere.IsSurfaceValid := by
  constructor <;> intro d <;> cases d

/-- The placeholder sphere complex is combinatorially connected: it has a single vertex. -/
theorem sphere_isConnected : sphere.IsConnected := by
  refine ⟨⟨PUnit.unit⟩, fun v w => ?_⟩
  cases v; cases w
  exact Relation.ReflTransGen.refl

/-- Equivalence generated by the allowed Gallier-Xu cut/glue transformations. -/
def Equivalent (K L : SurfaceCellComplex) : Prop :=
  Nonempty (K.Realization ≃ₜ L.Realization)

/-- Quotient congruence for surface-cell realizations.

The implementation is currently hidden behind the placeholder realization. The final proof should
descend `e` through the two quotient relations using mathlib's quotient-topology API. -/
noncomputable def realizationCongr {K L : SurfaceCellComplex}
    (e : K.PreRealization ≃ₜ L.PreRealization)
    (_hrel : ∀ x y, K.gluingRel x y ↔ L.gluingRel (e x) (e y)) :
    K.Realization ≃ₜ L.Realization :=
  e

/-- Relation-only quotient congruence on a fixed pre-space. -/
noncomputable def realizationCongrRight {X : Type*} [TopologicalSpace X]
    {r s : Setoid X} (_h : ∀ x y, r x y ↔ s x y) :
    Quotient r ≃ₜ Quotient s := by
  exact Homeomorph.Quotient.congrRight _h

end SurfaceCellComplex

/-- Compatibility alias for the initial scaffold name. -/
abbrev CellComplex :=
  SurfaceCellComplex

namespace CellComplex

/-- Compatibility spelling for the initial scaffold namespace. -/
abbrev Realization (K : CellComplex) : Type :=
  SurfaceCellComplex.Realization K

/-- Compatibility spelling for the initial scaffold sphere complex. -/
abbrev sphere : CellComplex :=
  SurfaceCellComplex.sphere

/-- Compatibility spelling for the initial scaffold equivalence relation. -/
abbrev Equivalent (K L : CellComplex) : Prop :=
  SurfaceCellComplex.Equivalent K L

end CellComplex

/-- Bridge from a finite triangulation to a finite surface cell complex. -/
def FiniteSurfaceTriangulation.toCellComplex {S : Type*} [TopologicalSpace S]
    (T : FiniteSurfaceTriangulation S) : SurfaceCellComplex where
  Face := T.Triangle
  Dart := SurfaceCellComplex.SignedDart T.Edge
  Vertex := T.Vertex
  realization := T.realization
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  realizationTop := T.realizationTop
  inv := SurfaceCellComplex.SignedDart.flipEquiv T.Edge
  source := fun
    | SurfaceCellComplex.SignedDart.pos e => T.edgeSource e
    | SurfaceCellComplex.SignedDart.neg e => T.edgeTarget e
  target := fun
    | SurfaceCellComplex.SignedDart.pos e => T.edgeTarget e
    | SurfaceCellComplex.SignedDart.neg e => T.edgeSource e
  boundary := fun f => (T.triangleBoundary f).map SurfaceCellComplex.signedDartOfOrientedEdge
  isBoundaryDart := fun
    | SurfaceCellComplex.SignedDart.pos e => T.edgeIsBoundary e
    | SurfaceCellComplex.SignedDart.neg e => T.edgeIsBoundary e
  inv_involutive := SurfaceCellComplex.SignedDart.flip_flip
  inv_source := by
    intro d
    cases d <;> rfl
  inv_target := by
    intro d
    cases d <;> rfl

/-- The realization of the associated cell complex agrees with the triangulation realization. -/
theorem FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    Nonempty (T.realization ≃ₜ T.toCellComplex.Realization) := by
  exact ⟨Homeomorph.refl T.realization⟩

/-- Compatibility spelling for the initial scaffold namespace. -/
abbrev FiniteTriangulation.toCellComplex {S : Type*} [TopologicalSpace S]
    (T : FiniteTriangulation S) : CellComplex :=
  FiniteSurfaceTriangulation.toCellComplex T

/-- A finite triangulation produces a finite surface cell complex realizing the same space. -/
theorem finite_triangulation_to_cell_complex
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    ∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization) := by
  refine ⟨T.toCellComplex, ?_⟩
  rcases T.homeomorphSurface with ⟨hTS⟩
  rcases T.toCellComplex_realization_homeomorphic with ⟨hTR⟩
  exact ⟨hTS.symm.trans hTR⟩

section EvalHypotheses

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
variable [ChartBoundaryInvariant S]

/-- Topological bridge from Eval surfaces to finite surface cell complexes. -/
theorem compact_surface_homeomorphic_to_cell_complex :
    ∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization) := by
  obtain ⟨T, _hT⟩ := compact_eval_surface_finitely_triangulable S
  exact finite_triangulation_to_cell_complex T

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
