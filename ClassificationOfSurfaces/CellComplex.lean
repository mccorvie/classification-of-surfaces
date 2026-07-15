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

/-- The underlying unoriented edge name of a signed dart. -/
def edge {α : Type*} : SignedDart α → α
  | pos a => a
  | neg a => a

/-- Reverse the orientation of a signed dart. -/
def flip {α : Type*} : SignedDart α → SignedDart α
  | pos a => neg a
  | neg a => pos a

@[simp] theorem edge_flip {α : Type*} (d : SignedDart α) : (flip d).edge = d.edge := by
  cases d <;> rfl

@[simp] theorem flip_flip {α : Type*} (d : SignedDart α) : flip (flip d) = d := by
  cases d <;> rfl

/-- Orientation reversal as an equivalence. -/
def flipEquiv (α : Type*) : SignedDart α ≃ SignedDart α where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

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

theorem signedDartOfOrientedEdge_injective {Edge : Type*} :
    Function.Injective
      (signedDartOfOrientedEdge : OrientedEdge Edge → SignedDart Edge) := by
  intro d e h
  cases d <;> cases e <;> simp_all [signedDartOfOrientedEdge]

@[simp]
theorem signedDartOfOrientedEdge_edge {Edge : Type*} (d : OrientedEdge Edge) :
    (signedDartOfOrientedEdge d).edge = d.edge := by
  cases d <;> rfl

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
  inv_involutive := by
    intro d
    cases d
  inv_source := by
    intro d
    cases d
  inv_target := by
    intro d
    cases d

/-- The empty-edge presentation of the sphere has valid incidence data. -/
theorem sphere_isSurfaceValid : sphere.IsSurfaceValid := by
  refine ⟨⟨PUnit.unit⟩, ?_, ?_, ?_⟩
  · intro f g _h
    cases f
    cases g
    rfl
  · intro d
    exact Empty.elim d
  · intro d
    exact Empty.elim d

/-- The one-face sphere presentation is connected. -/
theorem sphere_isConnected : sphere.IsConnected := by
  refine ⟨⟨PUnit.unit⟩, ?_⟩
  intro f g
  cases f
  cases g
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
  inv_involutive := SurfaceCellComplex.SignedDart.flip_flip
  inv_source := by
    intro d
    cases d <;> rfl
  inv_target := by
    intro d
    cases d <;> rfl

@[simp]
theorem FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S)
    (d e : T.toCellComplex.Dart) :
    T.toCellComplex.SameEdge d e ↔ e.edge = d.edge := by
  change e = d ∨ e = SurfaceCellComplex.SignedDart.flip d ↔ e.edge = d.edge
  cases d <;> cases e <;>
    simp only [SurfaceCellComplex.SignedDart.flip,
      SurfaceCellComplex.SignedDart.edge, reduceCtorEq,
      false_or, or_false]
  all_goals
    constructor
    · intro h
      injection h
    · rintro rfl
      rfl

/-- The realization of the associated cell complex agrees with the triangulation realization. -/
theorem FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S) :
    Nonempty (T.realization ≃ₜ T.toCellComplex.Realization) := by
  exact ⟨Homeomorph.refl T.realization⟩

namespace FiniteSurfaceTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- Triangle-boundary positions are canonically the boundary occurrences of the converted cell
complex. -/
def boundaryPositionEquivCellOccurrence (T : FiniteSurfaceTriangulation S) :
    T.BoundaryPosition ≃ T.toCellComplex.BoundaryOccurrence :=
  Equiv.sigmaCongrRight fun _ =>
    (Fin.castOrderIso (by simp [toCellComplex])).toEquiv

@[simp]
theorem boundaryPositionEquivCellOccurrence_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).1 = o.1 :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).2.val = o.2.val :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_symm_apply_fst
    (T : FiniteSurfaceTriangulation S) (o : T.toCellComplex.BoundaryOccurrence) :
    (T.boundaryPositionEquivCellOccurrence.symm o).1 = o.1 :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_symm_apply_val
    (T : FiniteSurfaceTriangulation S) (o : T.toCellComplex.BoundaryOccurrence) :
    (T.boundaryPositionEquivCellOccurrence.symm o).2.val = o.2.val :=
  rfl

@[simp]
theorem boundaryPositionEquivCellOccurrence_dart
    (T : FiniteSurfaceTriangulation S) (o : T.BoundaryPosition) :
    (T.boundaryPositionEquivCellOccurrence o).dart =
      SurfaceCellComplex.signedDartOfOrientedEdge o.orientedEdge := by
  change
    ((T.triangleBoundary o.1).map
      SurfaceCellComplex.signedDartOfOrientedEdge).get
        ⟨o.2.val, by simp⟩ =
      SurfaceCellComplex.signedDartOfOrientedEdge
        ((T.triangleBoundary o.1).get o.2)
  simp

theorem sameEdge_boundaryPositionEquivCellOccurrence_iff
    (T : FiniteSurfaceTriangulation S)
    (d : T.toCellComplex.Dart) (o : T.BoundaryPosition) :
    T.toCellComplex.SameEdge d (T.boundaryPositionEquivCellOccurrence o).dart ↔
      o.edge = d.edge := by
  rw [boundaryPositionEquivCellOccurrence_dart,
    FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff]
  simp [BoundaryPosition.edge]

private theorem occurs_once_or_twice_of_incidenceCertificate
    {T : FiniteSurfaceTriangulation S} (h : T.IncidenceCertificate)
    (d : T.toCellComplex.Dart) :
    T.toCellComplex.OccursExactlyOnce d ∨ T.toCellComplex.OccursExactlyTwice d := by
  let e := d.edge
  obtain ⟨o₀, ho₀⟩ := h.edge_used e
  classical
  by_cases hunique : ∀ o : T.BoundaryPosition, o.edge = e → o = o₀
  · left
    refine ⟨T.boundaryPositionEquivCellOccurrence o₀, ?_, ?_⟩
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₀).mpr ho₀
    · intro occurrence hoccur
      let o := T.boundaryPositionEquivCellOccurrence.symm occurrence
      have hedge : o.edge = e := by
        apply (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o).mp
        simpa only [SurfaceCellComplex.Occurs, o,
          Equiv.apply_symm_apply] using hoccur
      have ho : o = o₀ := hunique o hedge
      calc
        occurrence = T.boundaryPositionEquivCellOccurrence o := by
          simpa only [o] using
            (T.boundaryPositionEquivCellOccurrence.apply_symm_apply occurrence).symm
        _ = T.boundaryPositionEquivCellOccurrence o₀ :=
          congrArg T.boundaryPositionEquivCellOccurrence ho
  · push Not at hunique
    obtain ⟨o₁, ho₁, ho₁_ne⟩ := hunique
    right
    refine ⟨T.boundaryPositionEquivCellOccurrence o₀,
      T.boundaryPositionEquivCellOccurrence o₁, ?_, ?_, ?_, ?_⟩
    · exact T.boundaryPositionEquivCellOccurrence.injective.ne ho₁_ne.symm
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₀).mpr ho₀
    · exact (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₁).mpr ho₁
    · intro occurrence hoccur
      let o₂ := T.boundaryPositionEquivCellOccurrence.symm occurrence
      have ho₂ : o₂.edge = e := by
        apply (T.sameEdge_boundaryPositionEquivCellOccurrence_iff d o₂).mp
        simpa only [SurfaceCellComplex.Occurs, o₂,
          Equiv.apply_symm_apply] using hoccur
      rcases h.edge_valence_le_two e o₀ o₁ o₂ ho₀ ho₁ ho₂ with
        h01 | h02 | h12
      · exact False.elim (ho₁_ne h01.symm)
      · left
        simpa [o₂] using congrArg T.boundaryPositionEquivCellOccurrence h02.symm
      · right
        simpa [o₂] using congrArg T.boundaryPositionEquivCellOccurrence h12.symm

/-- An incidence-certified finite triangulation produces valid cell-complex incidence data. -/
theorem toCellComplex_isSurfaceValid_of_incidenceCertificate
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toCellComplex.IsSurfaceValid := by
  refine ⟨h.triangle_nonempty, ?_, ?_, ?_⟩
  · intro f g hrotated
    apply h.boundary_rotated_injective f g
    obtain ⟨n, hn⟩ := hrotated
    refine ⟨n, ?_⟩
    apply SurfaceCellComplex.signedDartOfOrientedEdge_injective.list_map
    simpa [toCellComplex, List.map_rotate] using hn
  · intro d
    cases d <;> intro hd <;> cases hd
  · exact occurs_once_or_twice_of_incidenceCertificate h

private theorem triangleAdjacent_to_faceAdjacent
    (T : FiniteSurfaceTriangulation S) {f g : T.Triangle}
    (h : T.TriangleAdjacent f g) : T.toCellComplex.FaceAdjacent f g := by
  rcases h with ⟨df, hdf, dg, hdg, hedge⟩
  refine ⟨SurfaceCellComplex.signedDartOfOrientedEdge df, ?_,
    SurfaceCellComplex.signedDartOfOrientedEdge dg, ?_, ?_⟩
  · exact List.mem_map_of_mem hdf
  · exact List.mem_map_of_mem hdg
  · rw [FiniteSurfaceTriangulation.toCellComplex_sameEdge_iff]
    simpa using hedge.symm

/-- Dual connectivity of a certified triangulation gives cell-complex face connectivity. -/
theorem toCellComplex_isConnected_of_incidenceCertificate
    (T : FiniteSurfaceTriangulation S) (h : T.IncidenceCertificate) :
    T.toCellComplex.IsConnected := by
  refine ⟨h.triangle_nonempty, ?_⟩
  intro f g
  exact (h.dual_connected f g).mono fun _ _ ↦ T.triangleAdjacent_to_faceAdjacent

end FiniteSurfaceTriangulation

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

/-- A certified finite triangulation produces a valid, connected cell complex realizing the same
space. -/
theorem finite_triangulation_to_valid_connected_cell_complex
    {S : Type*} [TopologicalSpace S] (T : FiniteSurfaceTriangulation S)
    (h : T.IncidenceCertificate) :
    ∃ K : SurfaceCellComplex,
      Nonempty (S ≃ₜ K.Realization) ∧ K.IsSurfaceValid ∧ K.IsConnected := by
  refine ⟨T.toCellComplex, ?_,
    T.toCellComplex_isSurfaceValid_of_incidenceCertificate h,
    T.toCellComplex_isConnected_of_incidenceCertificate h⟩
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
