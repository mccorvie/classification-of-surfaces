/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Triangulation
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Rotate

/-!
# Finite surface cell complexes

This file owns the shared combinatorial API between the topological triangulation route and the
Gallier-Xu normal-form route. The definitions are still intentionally light, but the public names
and theorem boundaries match the Moise/PL blueprint.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The raw finite incidence data underlying a Gallier-Xu surface cell complex.

Validity and connectedness are derived from this data by `IsSurfaceValid` and `IsConnected`, rather
than stored as unconstrained propositions. The realization is still a placeholder until the
polygon-quotient construction is implemented. -/
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

/-- A position in one of the stored, positively oriented face boundaries. -/
abbrev BoundaryOccurrence (K : SurfaceCellComplex) :=
  Σ f : K.Face, Fin (K.boundary f).length

instance boundaryOccurrenceFintype (K : SurfaceCellComplex) : Fintype K.BoundaryOccurrence :=
  inferInstance

/-- The dart stored at a boundary occurrence. -/
def BoundaryOccurrence.dart {K : SurfaceCellComplex} (o : K.BoundaryOccurrence) : K.Dart :=
  (K.boundary o.1).get o.2

/-- Two darts name the same unoriented edge. -/
def SameEdge (K : SurfaceCellComplex) (d e : K.Dart) : Prop :=
  e = d ∨ e = K.inv d

/-- A boundary position belongs to the unoriented edge named by `d`. -/
def Occurs (K : SurfaceCellComplex) (d : K.Dart) (o : K.BoundaryOccurrence) : Prop :=
  K.SameEdge d o.dart

/-- The unoriented edge named by `d` occurs at exactly one boundary position. -/
def OccursExactlyOnce (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  ∃ o, K.Occurs d o ∧ ∀ o', K.Occurs d o' → o' = o

/-- The unoriented edge named by `d` occurs at exactly two boundary positions. -/
def OccursExactlyTwice (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  ∃ o₁ o₂, o₁ ≠ o₂ ∧ K.Occurs d o₁ ∧ K.Occurs d o₂ ∧
    ∀ o, K.Occurs d o → o = o₁ ∨ o = o₂

/-- Boundary status derived from incidence: the edge orbit of `d` occurs exactly once. -/
def IsBoundaryDart (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  K.OccursExactlyOnce d

/-- Deprecated accessor spelling for the former stored boundary-dart label. -/
@[deprecated IsBoundaryDart (since := "2026-07-15")]
abbrev isBoundaryDart (K : SurfaceCellComplex) (d : K.Dart) : Prop :=
  K.IsBoundaryDart d

/-- Incidence validity for the stored face-boundary system.

There is at least one face, different faces have different cyclic boundary words, inverse darts are
distinct, and every unoriented edge occurs either once (a boundary edge) or twice (an inner edge).
Boundary status and occurrence counts are derived from explicit boundary positions, so repeated
darts such as the projective-plane word `a a` are retained. The stored vertex endpoints are an
enrichment of Gallier--Xu's boundary-word data and are deliberately not part of this predicate. -/
def IsSurfaceValid (K : SurfaceCellComplex) : Prop :=
  Nonempty K.Face ∧
    (∀ f g, (K.boundary f).IsRotated (K.boundary g) → f = g) ∧
    (∀ d, K.inv d ≠ d) ∧
    ∀ d, K.OccursExactlyOnce d ∨ K.OccursExactlyTwice d

/-- Inverting the chosen representative does not change its unoriented edge. -/
@[simp]
theorem sameEdge_inv_left_iff (K : SurfaceCellComplex) (d e : K.Dart) :
    K.SameEdge (K.inv d) e ↔ K.SameEdge d e := by
  simp only [SameEdge, K.inv_involutive]
  exact or_comm

/-- Inverting the chosen representative does not change which boundary positions it occupies. -/
@[simp]
theorem occurs_inv_iff (K : SurfaceCellComplex) (d : K.Dart) (o : K.BoundaryOccurrence) :
    K.Occurs (K.inv d) o ↔ K.Occurs d o :=
  K.sameEdge_inv_left_iff d o.dart

/-- Boundary status is invariant under reversing the representative dart. -/
@[simp]
theorem isBoundaryDart_inv_iff (K : SurfaceCellComplex) (d : K.Dart) :
    K.IsBoundaryDart (K.inv d) ↔ K.IsBoundaryDart d := by
  constructor
  · rintro ⟨o, ho, hunique⟩
    refine ⟨o, (K.occurs_inv_iff d o).mp ho, ?_⟩
    intro o' ho'
    exact hunique o' ((K.occurs_inv_iff d o').mpr ho')
  · rintro ⟨o, ho, hunique⟩
    refine ⟨o, (K.occurs_inv_iff d o).mpr ho, ?_⟩
    intro o' ho'
    exact hunique o' ((K.occurs_inv_iff d o').mp ho')

namespace IsSurfaceValid

/-- Inverse darts in a valid incidence system are distinct. -/
theorem inv_ne {K : SurfaceCellComplex} (h : K.IsSurfaceValid) (d : K.Dart) :
    K.inv d ≠ d :=
  h.2.2.1 d

/-- A non-boundary edge in a valid incidence system occurs exactly twice. -/
theorem occurs_twice_of_not_boundary {K : SurfaceCellComplex} (h : K.IsSurfaceValid)
    {d : K.Dart} (hd : ¬K.IsBoundaryDart d) : K.OccursExactlyTwice d := by
  rcases h.2.2.2 d with hone | htwo
  · exact False.elim (hd hone)
  · exact htwo

end IsSurfaceValid

/-- Two faces are adjacent when their boundaries use the same unoriented edge. -/
def FaceAdjacent (K : SurfaceCellComplex) (f g : K.Face) : Prop :=
  ∃ d ∈ K.boundary f, ∃ e ∈ K.boundary g, K.SameEdge d e

/-- Gallier-Xu connectivity of the face-edge incidence system. -/
def IsConnected (K : SurfaceCellComplex) : Prop :=
  Nonempty K.Face ∧ ∀ f g, Relation.ReflTransGen K.FaceAdjacent f g

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

@[simp]
theorem flipEquiv_apply {α : Type*} (d : SignedDart α) : flipEquiv α d = flip d :=
  rfl

end SignedDart

/-- A single-face polygonal presentation with all edge names based at one vertex.

This constructor is intentionally simple. It is useful for normal-form examples and for testing the
Gallier-Xu boundary-word API before the full realization/gluing semantics are implemented. -/
def oneFacePresentation (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) :
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
  inv_involutive := SignedDart.flip_flip
  inv_source := by
    intro d
    rfl
  inv_target := by
    intro d
    rfl

/-- Every one-face presentation is connected in the face-edge incidence sense. -/
theorem oneFacePresentation_isConnected (Edge : Type) [Fintype Edge]
    (word : List (SignedDart Edge)) :
    (oneFacePresentation Edge word).IsConnected := by
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  intro f g
  cases f
  cases g
  exact Relation.ReflTransGen.refl

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

/-- The sphere presented as two monogons with oppositely oriented copies of one edge.

The stored realization remains a placeholder until the polygonal quotient cutover. The nonempty
boundary presentation is equivalent to Gallier--Xu's empty-word sphere and is directly compatible
with the polygonal occurrence adapter. -/
def sphere : SurfaceCellComplex where
  Face := Bool
  Dart := SignedDart PUnit
  Vertex := PUnit
  realization := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  realizationTop := inferInstance
  inv := SignedDart.flipEquiv PUnit
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun
    | false => [SignedDart.pos PUnit.unit]
    | true => [SignedDart.neg PUnit.unit]
  inv_involutive := SignedDart.flip_flip
  inv_source := by
    intro d
    rfl
  inv_target := by
    intro d
    rfl

/-- The two-monogon presentation of the sphere has valid incidence data. -/
theorem sphere_isSurfaceValid : sphere.IsSurfaceValid := by
  refine ⟨⟨false⟩, ?_, ?_, ?_⟩
  · intro f g hfg
    cases f <;> cases g
    · rfl
    · simp [sphere] at hfg
    · simp [sphere] at hfg
    · rfl
  · intro d
    cases d <;> intro hd <;> cases hd
  · intro d
    right
    let o₀ : sphere.BoundaryOccurrence :=
      ⟨false, ⟨0, by simp [sphere]⟩⟩
    let o₁ : sphere.BoundaryOccurrence :=
      ⟨true, ⟨0, by simp [sphere]⟩⟩
    refine ⟨o₀, o₁, ?_, ?_, ?_, ?_⟩
    · simp [o₀, o₁]
    · cases d with
      | pos e =>
          cases e
          exact Or.inl rfl
      | neg e =>
          cases e
          exact Or.inr rfl
    · cases d with
      | pos e =>
          cases e
          exact Or.inr rfl
      | neg e =>
          cases e
          exact Or.inl rfl
    · rintro ⟨f, i⟩ _hi
      cases f
      · left
        change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
      · right
        change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl

/-- The two faces of the sphere presentation are connected through their common edge. -/
theorem sphere_isConnected : sphere.IsConnected := by
  refine ⟨⟨false⟩, ?_⟩
  intro f g
  cases f <;> cases g
  · exact Relation.ReflTransGen.refl
  · apply Relation.ReflTransGen.single
    refine ⟨SignedDart.pos PUnit.unit, List.mem_cons_self,
      SignedDart.neg PUnit.unit, List.mem_cons_self, Or.inr rfl⟩
  · apply Relation.ReflTransGen.single
    refine ⟨SignedDart.neg PUnit.unit, List.mem_cons_self,
      SignedDart.pos PUnit.unit, List.mem_cons_self, Or.inr rfl⟩
  · exact Relation.ReflTransGen.refl

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

/-- Raw compatibility bridge from the ledgered triangulation record to stored cell-presentation
data.

This conversion does not prove `IsSurfaceValid` or `IsConnected`; in particular, those properties
do not follow from `FiniteSurfaceTriangulation.Valid`.  New geometric work should start from
`GeometricTriangulation`, and downstream cellulation work must separately certify the incidence
predicates. -/
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

/-- A legacy finite-triangulation record produces raw finite cell-presentation data with the same
stored realization.  No incidence validity or face-edge connectivity is asserted. -/
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

/-- An Eval surface is homeomorphic to the stored realization of raw finite cell-presentation
data.  This is only the current compatibility handoff: `K.IsSurfaceValid`, `K.IsConnected`, and
agreement with the polygonal quotient realization remain separate obligations. -/
theorem compact_surface_homeomorphic_to_cell_complex :
    ∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization) := by
  obtain ⟨T, _hT⟩ := compact_eval_surface_finitely_triangulable S
  exact finite_triangulation_to_cell_complex T

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
