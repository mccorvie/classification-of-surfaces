/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Independent
import ClassificationOfSurfaces.Moise.GeometricTriangulation

/-!
# Finite simplicial complexes in the plane

The shared geometric foundation for the Moise route (Moise, *Geometric Topology in Dimensions
2 and 3*, Ch. 0 and Ch. 7 conventions): finite complexes of genuine affine simplexes in the
Euclidean plane.

Unlike the retiring `EuclideanComplex` of `PL.lean` (see `docs/KNOWN_WEAK.md`), the support of a
`PlaneComplex` is *defined* as the union of the convex hulls of its faces, vertex positions are
actual points, faces are affinely independent, and distinct faces meet in the hull of their
shared vertex set.  None of these fields is satisfiable by bookkeeping alone: `face_inter` is a
genuine geometric constraint (it fails, for example, for two triangles that overlap in an open
region).

`IsAffineOn`/`IsPLOn` give the honest piecewise-linear predicates: a map is PL on a complex when
it is affine on every face of some subdivision.  A generic continuous map is *not* PL on any
complex with a 2-face, in contrast to the vacuous `IsPLOnSimplexes` this replaces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The Euclidean plane used throughout the Moise route. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- A finite simplicial complex of affine simplexes in the plane: finitely many vertices at
genuine positions, faces of at most three affinely independent vertices, closed under nonempty
subsets, with any two face carriers meeting exactly in the carrier of their shared vertex set. -/
structure PlaneComplex where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The position of each vertex in the plane. -/
  position : Vertex → Plane
  /-- Distinct vertices sit at distinct points. -/
  position_injective : Function.Injective position
  /-- The faces (simplexes) of the complex, as vertex sets. -/
  simplexes : Finset (Finset Vertex)
  /-- Faces are nonempty. -/
  nonempty_of_mem : ∀ s ∈ simplexes, s.Nonempty
  /-- Faces have at most three vertices: the complex is at most two-dimensional. -/
  card_le_three : ∀ s ∈ simplexes, s.card ≤ 3
  /-- Faces are closed under passing to nonempty subsets. -/
  down_closed : ∀ s ∈ simplexes, ∀ s' ⊆ s, s'.Nonempty → s' ∈ simplexes
  /-- The vertices of each face are affinely independent, so its carrier is a genuine geometric
  simplex of dimension `card - 1`. -/
  affineIndependent : ∀ s ∈ simplexes, AffineIndependent ℝ fun v : s => position v
  /-- Face carriers intersect exactly in the carrier of their shared vertices.  This is the
  face-to-face condition that makes the complex simplicial rather than an arbitrary union. -/
  face_inter : ∀ s ∈ simplexes, ∀ t ∈ simplexes,
    convexHull ℝ (position '' s) ∩ convexHull ℝ (position '' t) =
      convexHull ℝ (position '' ((s ∩ t : Finset Vertex) : Set Vertex))

attribute [instance] PlaneComplex.vertexFintype
attribute [instance] PlaneComplex.vertexDecidableEq

namespace PlaneComplex

variable (K : PlaneComplex)

/-- The carrier of a face: the convex hull of its vertex positions. -/
def cellCarrier (s : Finset K.Vertex) : Set Plane :=
  convexHull ℝ (K.position '' s)

/-- The support of the complex: the union of its face carriers. -/
def support : Set Plane :=
  ⋃ s ∈ K.simplexes, K.cellCarrier s

theorem cellCarrier_subset_support {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    K.cellCarrier s ⊆ K.support :=
  Set.subset_biUnion_of_mem hs

theorem isCompact_cellCarrier (s : Finset K.Vertex) : IsCompact (K.cellCarrier s) :=
  Set.Finite.isCompact_convexHull (𝕜 := ℝ) (s.finite_toSet.image K.position)

/-- The support of a finite plane complex is compact. -/
theorem isCompact_support : IsCompact K.support :=
  K.simplexes.finite_toSet.isCompact_biUnion fun s _ => K.isCompact_cellCarrier s

/-- The two-dimensional faces. -/
def cells : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 3

/-- The edges (one-dimensional faces). -/
def edges : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 2

/-- A complex is purely two-dimensional when every face lies in a two-dimensional one. -/
def IsPure2 : Prop :=
  ∀ s ∈ K.simplexes, ∃ t ∈ K.simplexes, s ⊆ t ∧ t.card = 3

/-- `K'` subdivides `K`: same support, and every face carrier of `K'` lies inside some face
carrier of `K`. -/
def Subdivides (K' K : PlaneComplex) : Prop :=
  K'.support = K.support ∧
    ∀ s' ∈ K'.simplexes, ∃ s ∈ K.simplexes, K'.cellCarrier s' ⊆ K.cellCarrier s

theorem Subdivides.refl (K : PlaneComplex) : K.Subdivides K :=
  ⟨rfl, fun s hs => ⟨s, hs, subset_rfl⟩⟩

end PlaneComplex

/-- `f` agrees with an affine map on `A`. -/
def IsAffineOn (f : Plane → Plane) (A : Set Plane) : Prop :=
  ∃ g : Plane →ᵃ[ℝ] Plane, Set.EqOn f g A

/-- `f` is piecewise linear on the complex `K`: affine on every face of some subdivision.

This is the honest PL predicate: a map that is not affine on any neighborhood of a point interior
to a 2-cell of `K` cannot satisfy it, in contrast to the vacuous `IsPLOnSimplexes` of the
retiring `PL.lean` layer. -/
def IsPLOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  ∃ K' : PlaneComplex, K'.Subdivides K ∧
    ∀ s' ∈ K'.simplexes, IsAffineOn f (K'.cellCarrier s')

/-- `f` is a PL embedding of the support of `K`: piecewise linear and injective on the support. -/
def IsPLEmbeddingOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  IsPLOn K f ∧ Set.InjOn f K.support

/-- **Theorem boundary** (realization compatibility; elementary).

A purely two-dimensional plane complex induces a geometric triangulation of its support: send
each point to its barycentric coordinates in the face containing it.  This connects the ambient
Moise machinery to the project's faithful triangulation object; it is elementary (no surface
topology), and is a good first proof task on this route. -/
theorem PlaneComplex.toGeometricTriangulation (K : PlaneComplex) (hpure : K.IsPure2) :
    Nonempty (GeometricTriangulation K.support) := by
  sorry

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
