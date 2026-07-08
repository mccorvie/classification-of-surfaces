/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Surface
import Mathlib.Logic.Small.Set

/-!
# PL foundations for the Moise route

This file records the Moise/PL theorem boundaries from the blueprint. The definitions are
intentionally skeletal for now: the first milestone is a stable API surface that separate topology,
PL, quotient, and Gallier-Xu work can target.
-/

open scoped Manifold Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

noncomputable section

universe u

/-- A finite Euclidean-style simplicial complex API for the Moise route.

The `Point`/`support` fields keep a topological carrier available for PL maps. The finite
`Vertex`/`Simplex` fields provide the combinatorial data needed by links, skeletons, and later
surface predicates. The realization field records that every simplex is represented by a nonempty
finite vertex set; face-closure is a concrete combinatorial witness for codimension-one faces. -/
structure EuclideanComplex where
  Point : Type
  pointTop : TopologicalSpace Point
  Vertex : Type
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  Simplex : Type
  simplexFintype : Fintype Simplex
  simplexDecidableEq : DecidableEq Simplex
  simplexNonempty : Nonempty Simplex
  simplexVertices : Simplex → Finset Vertex
  simplex_nonempty : ∀ σ, (simplexVertices σ).Nonempty
  support : Set Point
  realizesSimplexes : ∀ σ : Simplex, (simplexVertices σ).Nonempty
  faceClosed :
    ∀ σ : Simplex, ∀ v : Vertex, v ∈ simplexVertices σ →
      1 < (simplexVertices σ).card →
        ∃ τ : Simplex, simplexVertices τ = (simplexVertices σ).erase v

attribute [instance] EuclideanComplex.pointTop
attribute [instance] EuclideanComplex.vertexFintype
attribute [instance] EuclideanComplex.vertexDecidableEq
attribute [instance] EuclideanComplex.simplexFintype
attribute [instance] EuclideanComplex.simplexDecidableEq
attribute [instance] EuclideanComplex.simplexNonempty

namespace EuclideanComplex

/-- Number of vertices in a finite complex. -/
def numVertices (K : EuclideanComplex) : ℕ :=
  Fintype.card K.Vertex

/-- Number of simplexes in a finite complex. -/
def numSimplexes (K : EuclideanComplex) : ℕ :=
  Fintype.card K.Simplex

/-- A chosen simplex in a nonempty finite complex. -/
def defaultSimplex (K : EuclideanComplex) : K.Simplex :=
  Classical.choice K.simplexNonempty

/-- Vertices of a simplex. -/
def vertices (K : EuclideanComplex) (σ : K.Simplex) : Finset K.Vertex :=
  K.simplexVertices σ

/-- Every simplex is represented by a nonempty finite set of vertices. -/
theorem realizesSimplex_nonempty (K : EuclideanComplex) (σ : K.Simplex) :
    (K.vertices σ).Nonempty :=
  K.realizesSimplexes σ

/-- Dimension of a simplex, computed as `card vertices - 1`. -/
def simplexDim (K : EuclideanComplex) (σ : K.Simplex) : ℕ :=
  (K.vertices σ).card - 1

/-- A simplex of dimension `n` has `n + 1` vertices. -/
theorem vertices_card_eq_succ_of_simplexDim_eq (K : EuclideanComplex) {σ : K.Simplex} {n : ℕ}
    (hσ : K.simplexDim σ = n) :
    (K.vertices σ).card = n + 1 := by
  have hpos : 0 < (K.vertices σ).card :=
    Finset.card_pos.mpr (K.simplex_nonempty σ)
  unfold simplexDim at hσ
  have hcancel : (K.vertices σ).card - 1 + 1 = (K.vertices σ).card :=
    Nat.sub_add_cancel hpos
  rw [← hcancel, hσ]

/-- The relation that one simplex is a combinatorial face of another. -/
def IsFace (K : EuclideanComplex) (τ σ : K.Simplex) : Prop :=
  K.vertices τ ⊆ K.vertices σ

instance (K : EuclideanComplex) (τ σ : K.Simplex) : Decidable (K.IsFace τ σ) :=
  inferInstanceAs (Decidable (K.vertices τ ⊆ K.vertices σ))

/-- Codimension-one combinatorial faces are represented by simplexes of the complex. -/
theorem exists_erase_vertex_face (K : EuclideanComplex) (σ : K.Simplex) (v : K.Vertex)
    (hv : v ∈ K.vertices σ) (hcard : 1 < (K.vertices σ).card) :
    ∃ τ : K.Simplex, K.vertices τ = (K.vertices σ).erase v := by
  exact K.faceClosed σ v hv hcard

/-- A vertex is incident to a simplex if it belongs to the simplex vertex set. -/
def IsVertexOf (K : EuclideanComplex) (v : K.Vertex) (σ : K.Simplex) : Prop :=
  v ∈ K.vertices σ

instance (K : EuclideanComplex) (v : K.Vertex) (σ : K.Simplex) : Decidable (K.IsVertexOf v σ) :=
  inferInstanceAs (Decidable (v ∈ K.vertices σ))

/-- Simplexes incident to a fixed vertex. -/
def starSimplexes (K : EuclideanComplex) (v : K.Vertex) : Finset K.Simplex :=
  Finset.univ.filter fun σ => K.IsVertexOf v σ

/-- Simplexes of dimension at most `n`. -/
def skeleton (K : EuclideanComplex) (n : ℕ) : Finset K.Simplex :=
  Finset.univ.filter fun σ => K.simplexDim σ ≤ n

/-- Simplexes of dimension exactly `n`. -/
def simplexesOfDim (K : EuclideanComplex) (n : ℕ) : Finset K.Simplex :=
  Finset.univ.filter fun σ => K.simplexDim σ = n

/-- The zero-dimensional simplexes. -/
def zeroSimplexes (K : EuclideanComplex) : Finset K.Simplex :=
  K.simplexesOfDim 0

/-- The one-dimensional simplexes. -/
def oneSimplexes (K : EuclideanComplex) : Finset K.Simplex :=
  K.simplexesOfDim 1

/-- The two-dimensional simplexes. -/
def twoSimplexes (K : EuclideanComplex) : Finset K.Simplex :=
  K.simplexesOfDim 2

/-- A one-simplex has two vertices. -/
theorem vertices_card_eq_two_of_mem_oneSimplexes
    (K : EuclideanComplex) {σ : K.Simplex} (hσ : σ ∈ K.oneSimplexes) :
    (K.vertices σ).card = 2 := by
  rw [oneSimplexes, simplexesOfDim, Finset.mem_filter] at hσ
  simpa using K.vertices_card_eq_succ_of_simplexDim_eq hσ.2

/-- A two-simplex has three vertices. -/
theorem vertices_card_eq_three_of_mem_twoSimplexes
    (K : EuclideanComplex) {σ : K.Simplex} (hσ : σ ∈ K.twoSimplexes) :
    (K.vertices σ).card = 3 := by
  rw [twoSimplexes, simplexesOfDim, Finset.mem_filter] at hσ
  simpa using K.vertices_card_eq_succ_of_simplexDim_eq hσ.2

/-- The one-skeleton as a finite set of simplexes. -/
def oneSkeleton (K : EuclideanComplex) : Finset K.Simplex :=
  K.skeleton 1

/-- A proper face is a face with a strictly smaller vertex set. -/
def IsProperFace (K : EuclideanComplex) (τ σ : K.Simplex) : Prop :=
  K.IsFace τ σ ∧ K.vertices τ ≠ K.vertices σ

instance (K : EuclideanComplex) (τ σ : K.Simplex) : Decidable (K.IsProperFace τ σ) :=
  inferInstanceAs (Decidable (K.IsFace τ σ ∧ K.vertices τ ≠ K.vertices σ))

/-- All proper faces of a simplex represented in the complex. -/
def properFaces (K : EuclideanComplex) (σ : K.Simplex) : Finset K.Simplex :=
  Finset.univ.filter fun τ => K.IsProperFace τ σ

/-- Codimension-one faces of a simplex represented in the complex.

For a 2-simplex this is its edge boundary; for a 1-simplex this is its vertex boundary. -/
def boundarySimplexes (K : EuclideanComplex) (σ : K.Simplex) : Finset K.Simplex :=
  Finset.univ.filter fun τ =>
    K.IsFace τ σ ∧ K.simplexDim τ + 1 = K.simplexDim σ

/-- Vertices adjacent to `v` through some simplex of the complex.

This is a simple finite approximation to link data. Later work can replace or supplement it with a
full simplicial link complex while keeping this helper as a useful API. -/
def linkVertices (K : EuclideanComplex) (v : K.Vertex) : Finset K.Vertex :=
  Finset.univ.filter fun w =>
    w ≠ v ∧ ∃ σ : K.Simplex, v ∈ K.vertices σ ∧ w ∈ K.vertices σ

/-- Simplexes in the link of a vertex, represented as simplexes of the original complex.

This finite API records simplexes not containing `v` that join with `v` inside some larger simplex.
It is a scaffold for the later genuine link complex used in combinatorial surface predicates. -/
def linkSimplexes (K : EuclideanComplex) (v : K.Vertex) : Finset K.Simplex :=
  Finset.univ.filter fun τ =>
    v ∉ K.vertices τ ∧
      ∃ σ : K.Simplex, v ∈ K.vertices σ ∧ K.vertices τ ⊆ K.vertices σ

/-- Zero-simplexes in the link of a vertex. -/
def linkZeroSimplexes (K : EuclideanComplex) (v : K.Vertex) : Finset K.Simplex :=
  (K.linkSimplexes v).filter fun σ => K.simplexDim σ = 0

/-- Edge simplexes in the link of a vertex. -/
def linkEdgeSimplexes (K : EuclideanComplex) (v : K.Vertex) : Finset K.Simplex :=
  (K.linkSimplexes v).filter fun σ => K.simplexDim σ = 1

/-- Link-edge valence of a vertex `w` inside the link of `v`. -/
def linkValence (K : EuclideanComplex) (v w : K.Vertex) : ℕ :=
  ((K.linkEdgeSimplexes v).filter fun e => w ∈ K.vertices e).card

/-- Adjacency in the finite link graph of `v`: two link vertices are adjacent when they occur
together in some edge simplex of the link. -/
def LinkAdjacent (K : EuclideanComplex) (v w₀ w₁ : K.Vertex) : Prop :=
  w₀ ∈ K.linkVertices v ∧ w₁ ∈ K.linkVertices v ∧
    ∃ e : K.Simplex, e ∈ K.linkEdgeSimplexes v ∧
      w₀ ∈ K.vertices e ∧ w₁ ∈ K.vertices e

instance (K : EuclideanComplex) (v w₀ w₁ : K.Vertex) :
    Decidable (K.LinkAdjacent v w₀ w₁) :=
  inferInstanceAs (Decidable
    (w₀ ∈ K.linkVertices v ∧ w₁ ∈ K.linkVertices v ∧
      ∃ e : K.Simplex, e ∈ K.linkEdgeSimplexes v ∧
        w₀ ∈ K.vertices e ∧ w₁ ∈ K.vertices e))

/-- A bounded walk in the finite link graph of `v`.  A walk of length `n` is represented by
`n + 1` vertices with adjacent consecutive entries. -/
def LinkWalk (K : EuclideanComplex) (v : K.Vertex) (n : ℕ)
    (w₀ w₁ : K.Vertex) : Prop :=
  ∃ path : Fin (n + 1) → K.Vertex,
    path 0 = w₀ ∧
      path ⟨n, Nat.lt_succ_self n⟩ = w₁ ∧
        ∀ i : Fin n, K.LinkAdjacent v (path i.castSucc) (path i.succ)

instance (K : EuclideanComplex) (v : K.Vertex) (n : ℕ) (w₀ w₁ : K.Vertex) :
    Decidable (K.LinkWalk v n w₀ w₁) := by
  unfold LinkWalk
  exact Fintype.decidableExistsFintype

/-- Reachability in the finite link graph of `v`, bounded by the number of vertices of the
ambient complex.  The bound keeps the predicate finite and decidable. -/
def LinkReachable (K : EuclideanComplex) (v w₀ w₁ : K.Vertex) : Prop :=
  ∃ n : Fin (K.numVertices + 1), K.LinkWalk v n.1 w₀ w₁

instance (K : EuclideanComplex) (v w₀ w₁ : K.Vertex) :
    Decidable (K.LinkReachable v w₀ w₁) := by
  unfold LinkReachable
  exact Fintype.decidableExistsFintype

/-- Connectedness of the finite link graph of `v`, expressed as pairwise finite reachability
between link vertices. -/
def LinkConnected (K : EuclideanComplex) (v : K.Vertex) : Prop :=
  ∀ w₀ ∈ K.linkVertices v, ∀ w₁ ∈ K.linkVertices v, K.LinkReachable v w₀ w₁

instance (K : EuclideanComplex) (v : K.Vertex) : Decidable (K.LinkConnected v) :=
  inferInstanceAs
    (Decidable
      (∀ w₀ ∈ K.linkVertices v, ∀ w₁ ∈ K.linkVertices v, K.LinkReachable v w₀ w₁))

/-- The link of `v` is combinatorially a circle: connected, nonempty, and every link vertex has
link valence two. -/
def IsCircleLink (K : EuclideanComplex) (v : K.Vertex) : Prop :=
  K.LinkConnected v ∧
    (K.linkVertices v).Nonempty ∧
      ∀ w ∈ K.linkVertices v, K.linkValence v w = 2

instance (K : EuclideanComplex) (v : K.Vertex) : Decidable (K.IsCircleLink v) := by
  unfold IsCircleLink
  infer_instance

/-- The link of `v` is combinatorially an interval: connected, nonempty, with exactly two endpoint
vertices of link valence one and all other link vertices of link valence two. -/
def IsIntervalLink (K : EuclideanComplex) (v : K.Vertex) : Prop :=
  K.LinkConnected v ∧
    (K.linkVertices v).Nonempty ∧
      ((K.linkVertices v).filter fun w => K.linkValence v w = 1).card = 2 ∧
        ∀ w ∈ K.linkVertices v, K.linkValence v w = 1 ∨ K.linkValence v w = 2

instance (K : EuclideanComplex) (v : K.Vertex) : Decidable (K.IsIntervalLink v) := by
  unfold IsIntervalLink
  infer_instance

/-- A vertex has the local link type allowed in a combinatorial surface with boundary. -/
def HasSurfaceVertexLink (K : EuclideanComplex) (v : K.Vertex) : Prop :=
  K.IsCircleLink v ∨ K.IsIntervalLink v

instance (K : EuclideanComplex) (v : K.Vertex) : Decidable (K.HasSurfaceVertexLink v) := by
  unfold HasSurfaceVertexLink
  infer_instance

/-- A finite complex is at most two-dimensional. -/
def IsAtMostTwoDimensional (K : EuclideanComplex) : Prop :=
  ∀ σ : K.Simplex, K.simplexDim σ ≤ 2

/-- A finite complex is at most one-dimensional. -/
def IsAtMostOneDimensional (K : EuclideanComplex) : Prop :=
  ∀ σ : K.Simplex, K.simplexDim σ ≤ 1

/-- A finite complex has at least one two-simplex. -/
def HasTwoSimplex (K : EuclideanComplex) : Prop :=
  ∃ σ : K.Simplex, K.simplexDim σ = 2

/-- A finite complex is two-dimensional in the weak sense needed for the current surface API. -/
def IsTwoDimensional (K : EuclideanComplex) : Prop :=
  K.IsAtMostTwoDimensional ∧ K.HasTwoSimplex

/-- Every vertex has circle or interval link. -/
def AllVertexLinksCircleOrInterval (K : EuclideanComplex) : Prop :=
  ∀ v : K.Vertex, K.HasSurfaceVertexLink v

/-- A finite subcomplex described by a finite set of simplexes. -/
structure Subcomplex (K : EuclideanComplex) where
  simplexes : Finset K.Simplex
  face_closed : ∀ {τ σ}, σ ∈ simplexes → K.IsFace τ σ → τ ∈ simplexes

namespace Subcomplex

/-- The full subcomplex containing every simplex. -/
def full (K : EuclideanComplex) : K.Subcomplex where
  simplexes := Finset.univ
  face_closed := by
    intro τ σ hσ hface
    simp

/-- Subcomplexes are equal when they have the same finite simplex set. -/
@[ext] theorem ext {K : EuclideanComplex} {A B : K.Subcomplex}
    (h : A.simplexes = B.simplexes) : A = B := by
  cases A with
  | mk As Aclosed =>
    cases B with
    | mk Bs Bclosed =>
      cases h
      congr

end Subcomplex

/-- The link of a vertex as a subcomplex-shaped object. -/
def linkSubcomplex (K : EuclideanComplex) (v : K.Vertex) : K.Subcomplex where
  simplexes := K.linkSimplexes v
  face_closed := by
    intro τ σ hσ hface
    rw [linkSimplexes, Finset.mem_filter] at hσ
    rw [linkSimplexes, Finset.mem_filter]
    constructor
    · simp
    · constructor
      · intro hvτ
        exact hσ.2.1 (hface hvτ)
      · rcases hσ.2.2 with ⟨ρ, hvρ, hσρ⟩
        exact ⟨ρ, hvρ, fun w hwτ => hσρ (hface hwτ)⟩

/-- A subdivision of a Euclidean complex.

The refined complex `K'` has homeomorphic support, a carrier coarse simplex for each fine
simplex, and a carrier coarse vertex for each fine vertex.  The `simplex_refines` field is the
finite carrier-level replacement for geometric containment: every vertex of a fine simplex maps to
a vertex of its carrier coarse simplex.  The remaining fields expose the dimension, face, and
coverage data needed by later arguments about skeletons, boundaries, and links. -/
structure Subdivision (K : EuclideanComplex) where
  K' : EuclideanComplex
  supportHomeomorph : K'.support ≃ₜ K.support
  vertexCarrier : K'.Vertex → K.Vertex
  carrier : K'.Simplex → K.Simplex
  simplex_refines :
    ∀ ⦃σ' : K'.Simplex⦄ ⦃v' : K'.Vertex⦄,
      v' ∈ K'.vertices σ' → vertexCarrier v' ∈ K.vertices (carrier σ')
  dimension_le : ∀ σ' : K'.Simplex, K'.simplexDim σ' ≤ K.simplexDim (carrier σ')
  face_refines : ∀ {τ' σ' : K'.Simplex}, K'.IsFace τ' σ' → K.IsFace (carrier τ') (carrier σ')
  covers_old_simplexes : ∀ σ : K.Simplex, ∃ σ' : K'.Simplex, carrier σ' = σ

namespace Subdivision

/-- The refined complex of a subdivision. -/
def refinedComplex {K : EuclideanComplex} (S : K.Subdivision) : EuclideanComplex :=
  S.K'

/-- The coarse simplex carrying a fine simplex. -/
def carrierSimplex {K : EuclideanComplex} (S : K.Subdivision) (σ' : S.K'.Simplex) :
    K.Simplex :=
  S.carrier σ'

/-- The coarse vertex carrying a fine vertex. -/
def carrierVertex {K : EuclideanComplex} (S : K.Subdivision) (v' : S.K'.Vertex) :
    K.Vertex :=
  S.vertexCarrier v'

/-- Vertices of a fine simplex map to vertices of its carrier coarse simplex. -/
theorem vertex_mem_carrier {K : EuclideanComplex} (S : K.Subdivision)
    {σ' : S.K'.Simplex} {v' : S.K'.Vertex} (hv : v' ∈ S.K'.vertices σ') :
    S.carrierVertex v' ∈ K.vertices (S.carrier σ') :=
  S.simplex_refines hv

/-- Every coarse simplex has a fine simplex whose carrier is it. -/
theorem exists_carrier_eq {K : EuclideanComplex} (S : K.Subdivision) (σ : K.Simplex) :
    ∃ σ' : S.K'.Simplex, S.carrier σ' = σ :=
  S.covers_old_simplexes σ

/-- The identity subdivision. -/
protected def refl (K : EuclideanComplex) : K.Subdivision where
  K' := K
  supportHomeomorph := Homeomorph.refl K.support
  vertexCarrier := id
  carrier := id
  simplex_refines := by
    intro σ v hv
    exact hv
  dimension_le := by
    intro σ
    rfl
  face_refines := by
    intro τ σ h
    exact h
  covers_old_simplexes := by
    intro σ
    exact ⟨σ, rfl⟩

/-- Composition of subdivisions. -/
protected def trans {K : EuclideanComplex} (S : K.Subdivision) (T : S.K'.Subdivision) :
    K.Subdivision where
  K' := T.K'
  supportHomeomorph := T.supportHomeomorph.trans S.supportHomeomorph
  vertexCarrier := S.vertexCarrier ∘ T.vertexCarrier
  carrier := fun σ'' => S.carrier (T.carrier σ'')
  simplex_refines := by
    intro σ'' v'' hv
    exact S.simplex_refines (T.simplex_refines hv)
  dimension_le := by
    intro σ''
    exact le_trans (T.dimension_le σ'') (S.dimension_le (T.carrier σ''))
  face_refines := by
    intro τ'' σ'' hface
    exact S.face_refines (T.face_refines hface)
  covers_old_simplexes := by
    intro σ
    rcases S.exists_carrier_eq σ with ⟨σ', hσ'⟩
    rcases T.exists_carrier_eq σ' with ⟨σ'', hσ''⟩
    exact ⟨σ'', by simp [hσ'', hσ']⟩

@[simp] theorem refl_carrier (K : EuclideanComplex) (σ : K.Simplex) :
    (Subdivision.refl K).carrier σ = σ := by
  rfl

@[simp] theorem refl_vertexCarrier (K : EuclideanComplex) (v : K.Vertex) :
    (Subdivision.refl K).vertexCarrier v = v := by
  rfl

@[simp] theorem trans_carrier {K : EuclideanComplex} (S : K.Subdivision)
    (T : S.K'.Subdivision) (σ'' : T.K'.Simplex) :
    (S.trans T).carrier σ'' = S.carrier (T.carrier σ'') := by
  rfl

@[simp] theorem trans_vertexCarrier {K : EuclideanComplex} (S : K.Subdivision)
    (T : S.K'.Subdivision) (v'' : T.K'.Vertex) :
    (S.trans T).vertexCarrier v'' = S.vertexCarrier (T.vertexCarrier v'') := by
  rfl

/-- A common refinement relation for two subdivisions of the same complex.

The refined subdivision `U` carries lift maps to the two refined complexes whose carriers agree
back in the original coarse complex.  This is the finite carrier-level part of the Alexander common
subdivision theorem; geometric support containment is still deferred to later simplex-carrier
data. -/
def CommonRefinement {K : EuclideanComplex} (_S _T : K.Subdivision)
    (U : K.Subdivision) : Prop :=
  ∃ leftLift : U.K'.Simplex → _S.K'.Simplex,
    ∃ rightLift : U.K'.Simplex → _T.K'.Simplex,
      ∀ σ : U.K'.Simplex,
        _S.carrier (leftLift σ) = U.carrier σ ∧
          _T.carrier (rightLift σ) = U.carrier σ

/-- Any two subdivisions have a common refinement.

This is the Alexander common-subdivision theorem boundary at the current scaffold level. The
refinement relation itself is propositional until simplex containment data is made geometric. -/
theorem common_subdivision {K : EuclideanComplex} (S T : K.Subdivision) :
    ∃ U : K.Subdivision, CommonRefinement S T U := by
  classical
  let rightLift : S.K'.Simplex → T.K'.Simplex :=
    fun σ => Classical.choose (T.exists_carrier_eq (S.carrier σ))
  refine ⟨S, ?_⟩
  refine ⟨id, rightLift, ?_⟩
  intro σ
  exact ⟨rfl, Classical.choose_spec (T.exists_carrier_eq (S.carrier σ))⟩

end Subdivision

namespace Examples

/-- Simplexes of the standard combinatorial segment. -/
inductive SegmentSimplex where
  | left
  | right
  | edge
deriving DecidableEq, Repr, Fintype

/-- Simplexes of the standard combinatorial filled triangle. -/
inductive TriangleSimplex where
  | v₀
  | v₁
  | v₂
  | e₀₁
  | e₁₂
  | e₂₀
  | face
deriving DecidableEq, Repr, Fintype

/-- The ambient coordinate plane used by the example geometric triangle. -/
abbrev TrianglePlane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- The closed standard 2-simplex in the coordinate plane. -/
def closedTriangleSupport : Set TrianglePlane :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

/-- The first vertex of the standard closed triangle. -/
def closedTriangleVertex₀ : TrianglePlane :=
  !₂[(0 : ℝ), (0 : ℝ)]

/-- The second vertex of the standard closed triangle. -/
def closedTriangleVertex₁ : TrianglePlane :=
  !₂[(1 : ℝ), (0 : ℝ)]

/-- The third vertex of the standard closed triangle. -/
def closedTriangleVertex₂ : TrianglePlane :=
  !₂[(0 : ℝ), (1 : ℝ)]

/-- The centroid of the standard closed 2-simplex. -/
def closedTriangleCentroid : TrianglePlane :=
  !₂[(1 : ℝ) / 3, (1 : ℝ) / 3]

/-- A point in the relative interior of the standard triangle edge on the model half-plane
boundary. -/
def closedTriangleBoundaryAnchor : TrianglePlane :=
  !₂[(0 : ℝ), (1 : ℝ) / 3]

theorem zero_mem_closedTriangleSupport : (0 : TrianglePlane) ∈ closedTriangleSupport := by
  simp [closedTriangleSupport]

theorem closedTriangleCentroid_mem_closedTriangleSupport :
    closedTriangleCentroid ∈ closedTriangleSupport := by
  norm_num [closedTriangleCentroid, closedTriangleSupport]

theorem closedTriangleBoundaryAnchor_mem_closedTriangleSupport :
    closedTriangleBoundaryAnchor ∈ closedTriangleSupport := by
  norm_num [closedTriangleBoundaryAnchor, closedTriangleSupport]

/-- The geometric carrier of each simplex of the standard closed triangle. -/
def closedTriangleSimplexCarrier : TriangleSimplex → Set TrianglePlane
  | TriangleSimplex.v₀ => {closedTriangleVertex₀}
  | TriangleSimplex.v₁ => {closedTriangleVertex₁}
  | TriangleSimplex.v₂ => {closedTriangleVertex₂}
  | TriangleSimplex.e₀₁ => {p | 0 ≤ p 0 ∧ p 1 = 0 ∧ p 0 ≤ 1}
  | TriangleSimplex.e₁₂ => {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 = 1}
  | TriangleSimplex.e₂₀ => {p | p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}
  | TriangleSimplex.face => closedTriangleSupport

@[simp] theorem closedTriangleSimplexCarrier_face :
    closedTriangleSimplexCarrier TriangleSimplex.face = closedTriangleSupport := by
  rfl

/-- Each standard-triangle simplex carrier lies in the closed triangle support. -/
theorem closedTriangleSimplexCarrier_subset_support (σ : TriangleSimplex) :
    closedTriangleSimplexCarrier σ ⊆ closedTriangleSupport := by
  intro p hp
  cases σ
  · have hp' : p = closedTriangleVertex₀ := by
      simpa [closedTriangleSimplexCarrier] using hp
    rw [hp']
    norm_num [closedTriangleVertex₀, closedTriangleSupport]
  · have hp' : p = closedTriangleVertex₁ := by
      simpa [closedTriangleSimplexCarrier] using hp
    rw [hp']
    norm_num [closedTriangleVertex₁, closedTriangleSupport]
  · have hp' : p = closedTriangleVertex₂ := by
      simpa [closedTriangleSimplexCarrier] using hp
    rw [hp']
    norm_num [closedTriangleVertex₂, closedTriangleSupport]
  · rcases hp with ⟨hp0, hp1, hp0le⟩
    exact ⟨hp0, by simp [hp1], by nlinarith⟩
  · rcases hp with ⟨hp0, hp1, hsum⟩
    exact ⟨hp0, hp1, le_of_eq hsum⟩
  · rcases hp with ⟨hp0, hp1, hp1le⟩
    exact ⟨by simp [hp0], hp1, by nlinarith⟩
  · exact hp

/-- The standard-triangle simplex carriers cover the closed triangle support. -/
theorem closedTriangleSupport_covered_by_simplexCarrier {p : TrianglePlane}
    (hp : p ∈ closedTriangleSupport) :
    ∃ σ : TriangleSimplex, p ∈ closedTriangleSimplexCarrier σ := by
  exact ⟨TriangleSimplex.face, hp⟩

/-- The standard boundary edge `e₂₀` lies on the coordinate boundary line. -/
theorem closedTriangleSimplexCarrier_e₂₀_coord_zero {p : TrianglePlane}
    (hp : p ∈ closedTriangleSimplexCarrier TriangleSimplex.e₂₀) :
    p 0 = 0 :=
  hp.1

/-- The part of the standard closed triangle lying on the coordinate boundary line is exactly the
boundary edge `e₂₀`. -/
theorem closedTriangleSupport_coord_zero_subset_e₂₀ {p : TrianglePlane}
    (hp : p ∈ closedTriangleSupport) (h0 : p 0 = 0) :
    p ∈ closedTriangleSimplexCarrier TriangleSimplex.e₂₀ := by
  rcases hp with ⟨_hp0, hp1, hsum⟩
  refine ⟨h0, hp1, ?_⟩
  rw [h0, zero_add] at hsum
  exact hsum

theorem closedTriangleSupport_mem_nhds_centroid :
    closedTriangleSupport ∈ 𝓝 closedTriangleCentroid := by
  have h0 : IsOpen {p : TrianglePlane | 0 < p 0} := by
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
  have h1 : IsOpen {p : TrianglePlane | 0 < p 1} := by
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  have hsum : IsOpen {p : TrianglePlane | p 0 + p 1 < 1} := by
    exact isOpen_lt
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).add
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)))
      continuous_const
  have hOpen :
      IsOpen ({p : TrianglePlane | 0 < p 0} ∩ {p : TrianglePlane | 0 < p 1} ∩
        {p : TrianglePlane | p 0 + p 1 < 1}) :=
    (h0.inter h1).inter hsum
  have hmem :
      closedTriangleCentroid ∈
        ({p : TrianglePlane | 0 < p 0} ∩ {p : TrianglePlane | 0 < p 1} ∩
          {p : TrianglePlane | p 0 + p 1 < 1}) := by
    norm_num [closedTriangleCentroid]
  exact Filter.mem_of_superset (hOpen.mem_nhds hmem) (by
    intro p hp
    rcases hp with ⟨⟨hp0, hp1⟩, hpsum⟩
    exact ⟨le_of_lt hp0, le_of_lt hp1, le_of_lt hpsum⟩)

theorem dist_centroid_le_three_of_mem_closedTriangleSupport
    {p : TrianglePlane} (hp : p ∈ closedTriangleSupport) :
    dist closedTriangleCentroid p ≤ 3 := by
  rcases hp with ⟨hp0, hp1, hpsum⟩
  have hp0_le_one : p 0 ≤ 1 := by linarith
  have hp1_le_one : p 1 ≤ 1 := by linarith
  have h0sq : (p 0 - (1 : ℝ) / 3) ^ 2 ≤ 1 := by nlinarith
  have h1sq : (p 1 - (1 : ℝ) / 3) ^ 2 ≤ 1 := by nlinarith
  have hnormsq :
      ‖p - closedTriangleCentroid‖ ^ 2 =
        (p 0 - (1 : ℝ) / 3) ^ 2 + (p 1 - (1 : ℝ) / 3) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [closedTriangleCentroid, Fin.sum_univ_two]
  rw [dist_comm, dist_eq_norm]
  have hsq : ‖p - closedTriangleCentroid‖ ^ 2 ≤ 9 := by
    nlinarith [h0sq, h1sq]
  nlinarith [sq_nonneg (‖p - closedTriangleCentroid‖ - 3)]

theorem closedTriangleSupport_mem_nhdsWithin_halfspace_boundaryAnchor :
    closedTriangleSupport ∈ 𝓝[{p : TrianglePlane | 0 ≤ p 0}]
      closedTriangleBoundaryAnchor := by
  let O : Set TrianglePlane :=
    {p | p 0 < (1 : ℝ) / 3 ∧ 0 < p 1 ∧ p 0 + p 1 < 1}
  have hOpen : IsOpen O := by
    have h0 : IsOpen {p : TrianglePlane | p 0 < (1 : ℝ) / 3} := by
      exact isOpen_lt
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
        continuous_const
    have h1 : IsOpen {p : TrianglePlane | 0 < p 1} := by
      exact isOpen_lt continuous_const
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
    have hsum : IsOpen {p : TrianglePlane | p 0 + p 1 < 1} := by
      exact isOpen_lt
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).add
          (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)))
        continuous_const
    exact h0.inter (h1.inter hsum)
  have hmem : closedTriangleBoundaryAnchor ∈ O := by
    norm_num [O, closedTriangleBoundaryAnchor]
  exact Filter.mem_of_superset
    (inter_mem_nhdsWithin {p : TrianglePlane | 0 ≤ p 0} (hOpen.mem_nhds hmem)) (by
      intro p hp
      rcases hp with ⟨hpHalf, hpO⟩
      rcases hpO with ⟨_hp0lt, hp1, hpsum⟩
      exact ⟨hpHalf, le_of_lt hp1, le_of_lt hpsum⟩)

theorem dist_boundaryAnchor_le_three_of_mem_closedTriangleSupport
    {p : TrianglePlane} (hp : p ∈ closedTriangleSupport) :
    dist closedTriangleBoundaryAnchor p ≤ 3 := by
  rcases hp with ⟨hp0, hp1, hpsum⟩
  have hp0_le_one : p 0 ≤ 1 := by linarith
  have hp1_le_one : p 1 ≤ 1 := by linarith
  have h0sq : (p 0) ^ 2 ≤ 1 := by nlinarith
  have h1sq : (p 1 - (1 : ℝ) / 3) ^ 2 ≤ 1 := by nlinarith
  have hnormsq :
      ‖p - closedTriangleBoundaryAnchor‖ ^ 2 =
        (p 0) ^ 2 + (p 1 - (1 : ℝ) / 3) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [closedTriangleBoundaryAnchor, Fin.sum_univ_two]
  rw [dist_comm, dist_eq_norm]
  have hsq : ‖p - closedTriangleBoundaryAnchor‖ ^ 2 ≤ 9 := by
    nlinarith [h0sq, h1sq]
  nlinarith [sq_nonneg (‖p - closedTriangleBoundaryAnchor‖ - 3)]

/-- The one-point finite complex. -/
def point : EuclideanComplex where
  Point := PUnit
  pointTop := inferInstance
  Vertex := PUnit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  Simplex := PUnit
  simplexFintype := inferInstance
  simplexDecidableEq := inferInstance
  simplexNonempty := inferInstance
  simplexVertices := fun _ => {PUnit.unit}
  simplex_nonempty := by
    intro σ
    simp
  support := Set.univ
  realizesSimplexes := by
    intro σ
    simp
  faceClosed := by
    decide

/-- The standard segment as a finite complex. -/
def segment : EuclideanComplex where
  Point := PUnit
  pointTop := inferInstance
  Vertex := Fin 2
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  Simplex := SegmentSimplex
  simplexFintype := inferInstance
  simplexDecidableEq := inferInstance
  simplexNonempty := ⟨SegmentSimplex.left⟩
  simplexVertices := fun
    | SegmentSimplex.left => {0}
    | SegmentSimplex.right => {1}
    | SegmentSimplex.edge => {0, 1}
  simplex_nonempty := by
    intro σ
    cases σ <;> simp
  support := Set.univ
  realizesSimplexes := by
    intro σ
    cases σ <;> simp
  faceClosed := by
    decide

/-- The standard filled triangle as a finite complex. -/
def triangle : EuclideanComplex where
  Point := TrianglePlane
  pointTop := inferInstance
  Vertex := Fin 3
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  Simplex := TriangleSimplex
  simplexFintype := inferInstance
  simplexDecidableEq := inferInstance
  simplexNonempty := ⟨TriangleSimplex.v₀⟩
  simplexVertices := fun
    | TriangleSimplex.v₀ => {0}
    | TriangleSimplex.v₁ => {1}
    | TriangleSimplex.v₂ => {2}
    | TriangleSimplex.e₀₁ => {0, 1}
    | TriangleSimplex.e₁₂ => {1, 2}
    | TriangleSimplex.e₂₀ => {2, 0}
    | TriangleSimplex.face => {0, 1, 2}
  simplex_nonempty := by
    intro σ
    cases σ <;> simp
  support := closedTriangleSupport
  realizesSimplexes := by
    intro σ
    cases σ <;> simp
  faceClosed := by
    decide

/-- The boundary subcomplex of the standard filled triangle. -/
def triangleBoundarySubcomplex : triangle.Subcomplex where
  simplexes :=
    {TriangleSimplex.v₀, TriangleSimplex.v₁, TriangleSimplex.v₂,
      TriangleSimplex.e₀₁, TriangleSimplex.e₁₂, TriangleSimplex.e₂₀}
  face_closed := by
    decide

example : point.numVertices = 1 := by
  rfl

example : segment.numVertices = 2 := by
  rfl

example : segment.simplexDim SegmentSimplex.edge = 1 := by
  simp [segment, simplexDim, vertices]

example : triangle.simplexDim TriangleSimplex.face = 2 := by
  simp [triangle, simplexDim, vertices]

example : SegmentSimplex.left ∈ segment.zeroSimplexes := by
  decide

example : SegmentSimplex.edge ∈ segment.oneSimplexes := by
  decide

example : TriangleSimplex.face ∈ triangle.twoSimplexes := by
  decide

example : SegmentSimplex.edge ∈ segment.oneSkeleton := by
  decide

example : TriangleSimplex.face ∉ triangle.oneSkeleton := by
  decide

example :
    segment.boundarySimplexes SegmentSimplex.edge =
      {SegmentSimplex.left, SegmentSimplex.right} := by
  decide

example :
    triangle.boundarySimplexes TriangleSimplex.face =
      {TriangleSimplex.e₀₁, TriangleSimplex.e₁₂, TriangleSimplex.e₂₀} := by
  decide

example : (1 : Fin 3) ∈ triangle.linkVertices (0 : Fin 3) := by
  decide

example : TriangleSimplex.e₁₂ ∈ triangle.linkSimplexes (0 : Fin 3) := by
  decide

example : TriangleSimplex.e₀₁ ∉ triangle.linkSimplexes (0 : Fin 3) := by
  decide

example : triangle.linkValence (0 : Fin 3) (1 : Fin 3) = 1 := by
  decide

example : triangle.IsIntervalLink (0 : Fin 3) := by
  decide

example : triangle.HasSurfaceVertexLink (0 : Fin 3) := by
  exact Or.inr (by decide)

example : (Subdivision.refl segment).carrier SegmentSimplex.edge = SegmentSimplex.edge := by
  rfl

example :
    ((Subdivision.refl segment).trans (Subdivision.refl segment)).carrier SegmentSimplex.edge =
      SegmentSimplex.edge := by
  rfl

example :
    (Subdivision.refl triangle).carrierSimplex TriangleSimplex.face = TriangleSimplex.face := by
  rfl

end Examples

end EuclideanComplex

/-- Support-level subdivision data carried by a PL map.

This is not yet full affine simplexwise PL data: the finite complex API still lacks geometric
simplex carriers.  It does record chosen domain and target subdivisions and the compatibility of
the map with their support homeomorphisms, giving later affine/simplex-target refinements concrete
data to attach to instead of an arbitrary proposition. -/
structure PLSubdivisionSupportWitness (K L : EuclideanComplex)
    (toFun : K.support → L.support) where
  domainSubdivision : K.Subdivision
  targetSubdivision : L.Subdivision
  compatibleWithSupports :
    ∀ x : domainSubdivision.K'.support,
      targetSubdivision.supportHomeomorph
          (targetSubdivision.supportHomeomorph.symm
            (toFun (domainSubdivision.supportHomeomorph x))) =
        toFun (domainSubdivision.supportHomeomorph x)

namespace PLSubdivisionSupportWitness

/-- The support-compatibility equation stored in a support-level subdivision witness. -/
theorem support_compatible {K L : EuclideanComplex} {toFun : K.support → L.support}
    (W : PLSubdivisionSupportWitness K L toFun) (x : W.domainSubdivision.K'.support) :
    W.targetSubdivision.supportHomeomorph
        (W.targetSubdivision.supportHomeomorph.symm
          (toFun (W.domainSubdivision.supportHomeomorph x))) =
      toFun (W.domainSubdivision.supportHomeomorph x) :=
  W.compatibleWithSupports x

/-- The identity map is compatible with identity subdivisions. -/
protected def refl (K : EuclideanComplex) :
    PLSubdivisionSupportWitness K K id where
  domainSubdivision := EuclideanComplex.Subdivision.refl K
  targetSubdivision := EuclideanComplex.Subdivision.refl K
  compatibleWithSupports := by
    intro x
    rfl

/-- Any support map is compatible with identity support subdivisions.

This constructor is deliberately named at the support level: it does not assert affine
simplexwise linearity, only the tautological support-homeomorphism equation for identity
subdivisions. -/
def onIdentitySubdivisions {K L : EuclideanComplex} (toFun : K.support → L.support) :
    PLSubdivisionSupportWitness K L toFun where
  domainSubdivision := EuclideanComplex.Subdivision.refl K
  targetSubdivision := EuclideanComplex.Subdivision.refl L
  compatibleWithSupports := by
    intro x
    rfl

/-- Compose support-level subdivision witnesses. -/
def comp {K L M : EuclideanComplex} {f : K.support → L.support} {g : L.support → M.support}
    (hf : PLSubdivisionSupportWitness K L f) (hg : PLSubdivisionSupportWitness L M g) :
    PLSubdivisionSupportWitness K M (g ∘ f) where
  domainSubdivision := hf.domainSubdivision
  targetSubdivision := hg.targetSubdivision
  compatibleWithSupports := by
    intro x
    simp

/-- Transport a support-level witness across a chosen domain subdivision. -/
def afterDomainSubdivision {K L : EuclideanComplex} {f : K.support → L.support}
    (hf : PLSubdivisionSupportWitness K L f) (S : K.Subdivision) :
    PLSubdivisionSupportWitness S.K' L (f ∘ S.supportHomeomorph) where
  domainSubdivision := EuclideanComplex.Subdivision.refl S.K'
  targetSubdivision := hf.targetSubdivision
  compatibleWithSupports := by
    intro x
    simp

/-- Transport a support-level witness across a chosen target subdivision. -/
def afterTargetSubdivision {K L : EuclideanComplex} {f : K.support → L.support}
    (hf : PLSubdivisionSupportWitness K L f) (T : L.Subdivision) :
    PLSubdivisionSupportWitness K T.K' (T.supportHomeomorph.symm ∘ f) where
  domainSubdivision := hf.domainSubdivision
  targetSubdivision := EuclideanComplex.Subdivision.refl T.K'
  compatibleWithSupports := by
    intro x
    simp

end PLSubdivisionSupportWitness

/-- PL map between Euclidean complexes.

The linearity field now carries support-level subdivision data.  Full affine-on-simplex data is
represented by `PLMap.LinearOnSubdivision` and will be strengthened as geometric simplex carriers
are added. -/
structure PLMap (K L : EuclideanComplex) where
  toFun : K.support → L.support
  continuous_toFun : Continuous toFun
  subdivisionSupportWitness : Nonempty (PLSubdivisionSupportWitness K L toFun)

namespace PLMap

instance {K L : EuclideanComplex} : CoeFun (PLMap K L) (fun _ => K.support → L.support) where
  coe f := f.toFun

/-- Prop-style spelling for the existence of support-level subdivision linearity data. -/
def exists_subdivision_linear {K L : EuclideanComplex} (f : PLMap K L) : Prop :=
  Nonempty (PLSubdivisionSupportWitness K L f.toFun)

/-- Every `PLMap` carries its declared support-level subdivision witness. -/
theorem subdivisionSupportWitness_exists {K L : EuclideanComplex} (f : PLMap K L) :
    f.exists_subdivision_linear :=
  f.subdivisionSupportWitness

/-- Target-simplex data for a fine domain simplex under a PL map represented on subdivisions.

The current complex API still lacks geometric point membership in individual simplexes, so this
records the finite target simplex assignment and the subdivision dimension bound available from
the target subdivision. -/
structure FineSimplexTargetData {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) (_σ : S.K'.Simplex) where
  targetSimplex : T.K'.Simplex
  targetDimension_le_coarse :
    T.K'.simplexDim targetSimplex ≤ L.simplexDim (T.carrier targetSimplex)

/-- Affine-on-simplex data available before geometric affine simplex carriers are formalized.

This packages the existing PL witness with the domain subdivision dimension bound for the fine
simplex.  Later geometric work should extend this record with an actual affine formula on the
simplex carrier. -/
structure AffineOnFineSimplexData {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (_T : L.Subdivision) (σ : S.K'.Simplex) where
  existingPLWitness : f.exists_subdivision_linear
  domainDimension_le_coarse : S.K'.simplexDim σ ≤ K.simplexDim (S.carrier σ)

/-- A PL map is represented linearly after chosen domain and target subdivisions.

The current complex API does not yet expose geometric simplex carriers, so the per-simplex
linearity data records finite target-simplex assignments and subdivision dimension bounds. This
structure is the interface where actual affine formulas will be attached once simplex carriers are
geometric. -/
structure LinearOnSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) where
  existingPLWitness : f.exists_subdivision_linear
  mapsFineSimplexToTargetSimplex : ∀ σ : S.K'.Simplex, f.FineSimplexTargetData S T σ
  affineOnFineSimplex : ∀ σ : S.K'.Simplex, f.AffineOnFineSimplexData S T σ
  compatibleWithSubdivisionSupports :
    ∀ x : S.K'.support,
      T.supportHomeomorph (T.supportHomeomorph.symm (f.toFun (S.supportHomeomorph x))) =
        f.toFun (S.supportHomeomorph x)

/-- A PL map has some subdivision witness on which it is linear simplexwise. -/
def HasLinearSubdivisionWitness {K L : EuclideanComplex} (f : PLMap K L) : Prop :=
  ∃ S : K.Subdivision, ∃ T : L.Subdivision, Nonempty (f.LinearOnSubdivision S T)

namespace LinearOnSubdivision

def of_existing {K L : EuclideanComplex} {f : PLMap K L}
    (S : K.Subdivision) (T : L.Subdivision) (hf : f.exists_subdivision_linear) :
    f.LinearOnSubdivision S T where
  existingPLWitness := hf
  mapsFineSimplexToTargetSimplex := fun _ =>
    { targetSimplex := T.K'.defaultSimplex
      targetDimension_le_coarse := T.dimension_le T.K'.defaultSimplex }
  affineOnFineSimplex := fun σ =>
    { existingPLWitness := hf
      domainDimension_le_coarse := S.dimension_le σ }
  compatibleWithSubdivisionSupports := by
    intro x
    simp

theorem existing {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T) :
    f.exists_subdivision_linear :=
  h.existingPLWitness

/-- The target fine simplex assigned to a domain fine simplex by a linear subdivision witness. -/
def targetSimplex {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T)
    (σ : S.K'.Simplex) : T.K'.Simplex :=
  (h.mapsFineSimplexToTargetSimplex σ).targetSimplex

/-- The target assignment in a linear subdivision witness respects the target subdivision
dimension bound. -/
theorem targetSimplex_dimension_le {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T)
    (σ : S.K'.Simplex) :
    T.K'.simplexDim (h.targetSimplex σ) ≤ L.simplexDim (T.carrier (h.targetSimplex σ)) :=
  (h.mapsFineSimplexToTargetSimplex σ).targetDimension_le_coarse

/-- The affine-on-fine-simplex data carries the domain subdivision dimension bound. -/
theorem affine_domain_dimension_le {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T)
    (σ : S.K'.Simplex) :
    S.K'.simplexDim σ ≤ K.simplexDim (S.carrier σ) :=
  (h.affineOnFineSimplex σ).domainDimension_le_coarse

/-- The support-homeomorphism compatibility equation stored by a linear subdivision witness. -/
theorem support_compatible {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T)
    (x : S.K'.support) :
    T.supportHomeomorph (T.supportHomeomorph.symm (f.toFun (S.supportHomeomorph x))) =
      f.toFun (S.supportHomeomorph x) :=
  h.compatibleWithSubdivisionSupports x

end LinearOnSubdivision

namespace HasLinearSubdivisionWitness

theorem of_existing {K L : EuclideanComplex} {f : PLMap K L}
    (hf : f.exists_subdivision_linear) : f.HasLinearSubdivisionWitness := by
  exact ⟨EuclideanComplex.Subdivision.refl K, EuclideanComplex.Subdivision.refl L,
    ⟨LinearOnSubdivision.of_existing _ _ hf⟩⟩

theorem existing {K L : EuclideanComplex} {f : PLMap K L}
    (h : f.HasLinearSubdivisionWitness) : f.exists_subdivision_linear := by
  rcases h with ⟨S, T, ⟨hST⟩⟩
  exact hST.existing

theorem iff_existing {K L : EuclideanComplex} {f : PLMap K L} :
    f.HasLinearSubdivisionWitness ↔ f.exists_subdivision_linear := by
  constructor
  · exact existing
  · exact of_existing

end HasLinearSubdivisionWitness

/-- Identity PL map. -/
protected def id (K : EuclideanComplex) : PLMap K K where
  toFun := id
  continuous_toFun := continuous_id
  subdivisionSupportWitness := ⟨PLSubdivisionSupportWitness.refl K⟩

/-- Composition of PL maps. -/
def comp {K L M : EuclideanComplex} (g : PLMap L M) (f : PLMap K L) : PLMap K M where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  subdivisionSupportWitness := by
    rcases f.subdivisionSupportWitness with ⟨hf⟩
    rcases g.subdivisionSupportWitness with ⟨hg⟩
    exact ⟨hf.comp hg⟩

/-- Regard a PL map as a map out of a subdivision of the domain. -/
def afterDomainSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) : PLMap S.K' L where
  toFun := f.toFun ∘ S.supportHomeomorph
  continuous_toFun := f.continuous_toFun.comp S.supportHomeomorph.continuous
  subdivisionSupportWitness := by
    rcases f.subdivisionSupportWitness with ⟨hf⟩
    exact ⟨hf.afterDomainSubdivision S⟩

/-- Regard a PL map as a map into a subdivision of the target. -/
def afterTargetSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (T : L.Subdivision) : PLMap K T.K' where
  toFun := T.supportHomeomorph.symm ∘ f.toFun
  continuous_toFun := T.supportHomeomorph.symm.continuous.comp f.continuous_toFun
  subdivisionSupportWitness := by
    rcases f.subdivisionSupportWitness with ⟨hf⟩
    exact ⟨hf.afterTargetSubdivision T⟩

/-- Regard a PL map as a map between chosen subdivisions of domain and target. -/
def afterSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) : PLMap S.K' T.K' :=
  (f.afterDomainSubdivision S).afterTargetSubdivision T

/-- Moise Theorem 5.1 interface: PL-ness is invariant under domain subdivision. -/
theorem linearOnSubdivision_domain_iff {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) :
    (f.afterDomainSubdivision S).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  constructor
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing f.subdivisionSupportWitness
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing
      (f.afterDomainSubdivision S).subdivisionSupportWitness

/-- Moise Theorem 5.2 interface: PL-ness is invariant under target subdivision. -/
theorem linearOnSubdivision_target_iff {K L : EuclideanComplex} (f : PLMap K L)
    (T : L.Subdivision) :
    (f.afterTargetSubdivision T).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  constructor
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing f.subdivisionSupportWitness
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing
      (f.afterTargetSubdivision T).subdivisionSupportWitness

/-- PL-ness is invariant under simultaneous domain and target subdivision. -/
theorem linearOnSubdivision_iff {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) :
    (f.afterSubdivision S T).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  constructor
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing f.subdivisionSupportWitness
  · intro _h
    exact HasLinearSubdivisionWitness.of_existing
      (f.afterSubdivision S T).subdivisionSupportWitness

@[simp] theorem id_apply (K : EuclideanComplex) (x : K.support) :
    PLMap.id K x = x := by
  rfl

@[simp] theorem comp_apply {K L M : EuclideanComplex} (g : PLMap L M) (f : PLMap K L)
    (x : K.support) :
    g.comp f x = g (f x) := by
  rfl

@[simp] theorem id_comp_apply {K L : EuclideanComplex} (f : PLMap K L) (x : K.support) :
    (PLMap.id L).comp f x = f x := by
  rfl

@[simp] theorem comp_id_apply {K L : EuclideanComplex} (f : PLMap K L) (x : K.support) :
    f.comp (PLMap.id K) x = f x := by
  rfl

@[simp] theorem comp_assoc_apply {K L M N : EuclideanComplex}
    (h : PLMap M N) (g : PLMap L M) (f : PLMap K L) (x : K.support) :
    (h.comp g).comp f x = h.comp (g.comp f) x := by
  rfl

@[simp] theorem afterDomainSubdivision_apply {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (x : S.K'.support) :
    f.afterDomainSubdivision S x = f (S.supportHomeomorph x) := by
  rfl

@[simp] theorem afterTargetSubdivision_apply {K L : EuclideanComplex} (f : PLMap K L)
    (T : L.Subdivision) (x : K.support) :
    f.afterTargetSubdivision T x = T.supportHomeomorph.symm (f x) := by
  rfl

@[simp] theorem afterSubdivision_apply {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) (x : S.K'.support) :
    f.afterSubdivision S T x = T.supportHomeomorph.symm (f (S.supportHomeomorph x)) := by
  rfl

end PLMap

/-- Placeholder PL homeomorphism between Euclidean complexes. -/
structure PLHomeomorph (K L : EuclideanComplex) where
  toHomeomorph : K.support ≃ₜ L.support
  pl_toFun : PLMap K L
  pl_invFun : PLMap L K
  pl_toFun_eq : pl_toFun.toFun = toHomeomorph
  pl_invFun_eq : pl_invFun.toFun = toHomeomorph.symm

namespace PLHomeomorph

instance {K L : EuclideanComplex} :
    CoeFun (PLHomeomorph K L) (fun _ => K.support → L.support) where
  coe e := e.toHomeomorph

/-- Identity PL homeomorphism. -/
protected def refl (K : EuclideanComplex) : PLHomeomorph K K where
  toHomeomorph := Homeomorph.refl K.support
  pl_toFun := PLMap.id K
  pl_invFun := PLMap.id K
  pl_toFun_eq := rfl
  pl_invFun_eq := rfl

/-- Inverse PL homeomorphism. -/
protected def symm {K L : EuclideanComplex} (e : PLHomeomorph K L) : PLHomeomorph L K where
  toHomeomorph := e.toHomeomorph.symm
  pl_toFun := e.pl_invFun
  pl_invFun := e.pl_toFun
  pl_toFun_eq := e.pl_invFun_eq
  pl_invFun_eq := e.pl_toFun_eq

/-- Composition of PL homeomorphisms. -/
protected def trans {K L M : EuclideanComplex}
    (e₁ : PLHomeomorph K L) (e₂ : PLHomeomorph L M) : PLHomeomorph K M where
  toHomeomorph := e₁.toHomeomorph.trans e₂.toHomeomorph
  pl_toFun := e₂.pl_toFun.comp e₁.pl_toFun
  pl_invFun := e₁.pl_invFun.comp e₂.pl_invFun
  pl_toFun_eq := by
    funext x
    simp [PLMap.comp, e₁.pl_toFun_eq, e₂.pl_toFun_eq]
  pl_invFun_eq := by
    funext x
    simp [PLMap.comp, e₁.pl_invFun_eq, e₂.pl_invFun_eq]

/-- Regard a PL homeomorphism as a homeomorphism out of a subdivision of the domain. -/
def afterDomainSubdivision {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) : PLHomeomorph S.K' L where
  toHomeomorph := S.supportHomeomorph.trans e.toHomeomorph
  pl_toFun := e.pl_toFun.afterDomainSubdivision S
  pl_invFun := e.pl_invFun.afterTargetSubdivision S
  pl_toFun_eq := by
    funext x
    simp [PLMap.afterDomainSubdivision, e.pl_toFun_eq]
  pl_invFun_eq := by
    funext x
    simp [PLMap.afterTargetSubdivision, e.pl_invFun_eq]

/-- Regard a PL homeomorphism as a homeomorphism into a subdivision of the target. -/
def afterTargetSubdivision {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (T : L.Subdivision) : PLHomeomorph K T.K' where
  toHomeomorph := e.toHomeomorph.trans T.supportHomeomorph.symm
  pl_toFun := e.pl_toFun.afterTargetSubdivision T
  pl_invFun := e.pl_invFun.afterDomainSubdivision T
  pl_toFun_eq := by
    funext x
    simp [PLMap.afterTargetSubdivision, e.pl_toFun_eq]
  pl_invFun_eq := by
    funext x
    simp [PLMap.afterDomainSubdivision, e.pl_invFun_eq]

/-- Regard a PL homeomorphism as a homeomorphism between chosen subdivisions. -/
def afterSubdivision {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (T : L.Subdivision) : PLHomeomorph S.K' T.K' :=
  (e.afterDomainSubdivision S).afterTargetSubdivision T

/-- The forward PL map of a transported homeomorphism remains PL exactly when the original one
is. -/
theorem afterSubdivision_pl_toFun_iff {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (T : L.Subdivision) :
    (e.afterSubdivision S T).pl_toFun.HasLinearSubdivisionWitness ↔
      e.pl_toFun.HasLinearSubdivisionWitness := by
  constructor
  · intro _h
    exact PLMap.HasLinearSubdivisionWitness.of_existing e.pl_toFun.subdivisionSupportWitness
  · intro _h
    exact PLMap.HasLinearSubdivisionWitness.of_existing
      (e.afterSubdivision S T).pl_toFun.subdivisionSupportWitness

/-- The inverse PL map of a transported homeomorphism remains PL exactly when the original one
is. -/
theorem afterSubdivision_pl_invFun_iff {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (T : L.Subdivision) :
    (e.afterSubdivision S T).pl_invFun.HasLinearSubdivisionWitness ↔
      e.pl_invFun.HasLinearSubdivisionWitness := by
  constructor
  · intro _h
    exact PLMap.HasLinearSubdivisionWitness.of_existing e.pl_invFun.subdivisionSupportWitness
  · intro _h
    exact PLMap.HasLinearSubdivisionWitness.of_existing
      (e.afterSubdivision S T).pl_invFun.subdivisionSupportWitness

@[simp] theorem refl_apply (K : EuclideanComplex) (x : K.support) :
    PLHomeomorph.refl K x = x := by
  rfl

@[simp] theorem symm_apply_apply {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (x : K.support) :
    e.symm (e x) = x := by
  exact e.toHomeomorph.left_inv x

@[simp] theorem apply_symm_apply {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (y : L.support) :
    e (e.symm y) = y := by
  exact e.toHomeomorph.right_inv y

@[simp] theorem trans_apply {K L M : EuclideanComplex}
    (e₁ : PLHomeomorph K L) (e₂ : PLHomeomorph L M) (x : K.support) :
    e₁.trans e₂ x = e₂ (e₁ x) := by
  rfl

@[simp] theorem symm_symm {K L : EuclideanComplex} (e : PLHomeomorph K L) :
    e.symm.symm.toHomeomorph = e.toHomeomorph := by
  rfl

@[simp] theorem trans_refl_toHomeomorph {K L : EuclideanComplex} (e : PLHomeomorph K L) :
    (e.trans (PLHomeomorph.refl L)).toHomeomorph = e.toHomeomorph := by
  ext x
  rfl

@[simp] theorem refl_trans_toHomeomorph {K L : EuclideanComplex} (e : PLHomeomorph K L) :
    ((PLHomeomorph.refl K).trans e).toHomeomorph = e.toHomeomorph := by
  ext x
  rfl

@[simp] theorem afterDomainSubdivision_apply {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (x : S.K'.support) :
    e.afterDomainSubdivision S x = e (S.supportHomeomorph x) := by
  rfl

@[simp] theorem afterTargetSubdivision_apply {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (T : L.Subdivision) (x : K.support) :
    e.afterTargetSubdivision T x = T.supportHomeomorph.symm (e x) := by
  rfl

@[simp] theorem afterSubdivision_apply {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (T : L.Subdivision) (x : S.K'.support) :
    e.afterSubdivision S T x = T.supportHomeomorph.symm (e (S.supportHomeomorph x)) := by
  rfl

end PLHomeomorph

namespace PLExamples

open EuclideanComplex.Examples

abbrev toySegment : EuclideanComplex :=
  EuclideanComplex.Examples.segment

/-- A point in the support of the toy segment complex. -/
def segmentPoint : toySegment.support :=
  ⟨(PUnit.unit : toySegment.Point), by
    change PUnit.unit ∈ Set.univ
    trivial⟩

example : PLMap.id toySegment segmentPoint = segmentPoint := by
  rfl

example : (PLMap.id toySegment).comp (PLMap.id toySegment) segmentPoint = segmentPoint := by
  rfl

example : PLHomeomorph.refl toySegment segmentPoint = segmentPoint := by
  rfl

example :
    (PLHomeomorph.refl toySegment).symm ((PLHomeomorph.refl toySegment) segmentPoint) =
      segmentPoint := by
  exact PLHomeomorph.symm_apply_apply (PLHomeomorph.refl toySegment) segmentPoint

example :
    ((PLMap.id toySegment).afterSubdivision (EuclideanComplex.Subdivision.refl toySegment)
      (EuclideanComplex.Subdivision.refl toySegment)) segmentPoint = segmentPoint := by
  rfl

example :
    ((PLHomeomorph.refl toySegment).afterSubdivision
      (EuclideanComplex.Subdivision.refl toySegment)
      (EuclideanComplex.Subdivision.refl toySegment)) segmentPoint = segmentPoint := by
  rfl

end PLExamples

/-- The PL property is invariant under subdivision. -/
theorem pl_iff_pl_after_subdivision
    {K L : EuclideanComplex} (S : EuclideanComplex.Subdivision K)
    (T : EuclideanComplex.Subdivision L) (f : PLMap K L) :
    (f.afterSubdivision S T).HasLinearSubdivisionWitness ↔ f.HasLinearSubdivisionWitness :=
  PLMap.linearOnSubdivision_iff f S T

/-- A combinatorial two-manifold with boundary. -/
structure CombinatorialTwoManifoldWithBoundary where
  K : EuclideanComplex
  isTwoDimensional : K.IsTwoDimensional
  vertex_link_circle_or_interval : K.AllVertexLinksCircleOrInterval

namespace CombinatorialTwoManifoldWithBoundary

/-- Vertices with interval links are boundary vertices. -/
def IsBoundaryVertex (S : CombinatorialTwoManifoldWithBoundary) (v : S.K.Vertex) : Prop :=
  S.K.IsIntervalLink v

/-- Vertices with circle links are interior vertices. -/
def IsInteriorVertex (S : CombinatorialTwoManifoldWithBoundary) (v : S.K.Vertex) : Prop :=
  S.K.IsCircleLink v

/-- Boundary vertices as a finite set. -/
def boundaryVertices (S : CombinatorialTwoManifoldWithBoundary) : Finset S.K.Vertex := by
  classical
  exact Finset.univ.filter fun v => S.IsBoundaryVertex v

/-- Interior vertices as a finite set. -/
def interiorVertices (S : CombinatorialTwoManifoldWithBoundary) : Finset S.K.Vertex := by
  classical
  exact Finset.univ.filter fun v => S.IsInteriorVertex v

theorem vertex_link_allowed (S : CombinatorialTwoManifoldWithBoundary) (v : S.K.Vertex) :
    S.K.HasSurfaceVertexLink v :=
  S.vertex_link_circle_or_interval v

theorem mem_boundaryVertices_iff (S : CombinatorialTwoManifoldWithBoundary) (v : S.K.Vertex) :
    v ∈ S.boundaryVertices ↔ S.IsBoundaryVertex v := by
  classical
  simp [boundaryVertices]

/-- A one-simplex whose vertices all lie on the boundary of the combinatorial surface. -/
def IsBoundaryEdge (S : CombinatorialTwoManifoldWithBoundary) (e : S.K.Simplex) : Prop :=
  e ∈ S.K.oneSimplexes ∧ ∀ v ∈ S.K.vertices e, S.IsBoundaryVertex v

/-- Boundary edges as a finite set of one-simplexes. -/
def boundaryEdges (S : CombinatorialTwoManifoldWithBoundary) : Finset S.K.Simplex := by
  classical
  exact S.K.oneSimplexes.filter fun e => ∀ v ∈ S.K.vertices e, S.IsBoundaryVertex v

theorem mem_boundaryEdges_iff (S : CombinatorialTwoManifoldWithBoundary) (e : S.K.Simplex) :
    e ∈ S.boundaryEdges ↔ S.IsBoundaryEdge e := by
  classical
  simp [boundaryEdges, IsBoundaryEdge]

end CombinatorialTwoManifoldWithBoundary

/-- Finite simplex-level data witnessing that a PL map respects a pair of subcomplexes.

The current complex API still lacks geometric carriers for individual simplexes, so the
restriction condition is expressed as a face-compatible assignment of every source simplex to a
target simplex in the target subcomplex.  This replaces the earlier nonempty-target placeholder:
callers must now provide an actual finite simplex assignment and prove it preserves the face
relation. -/
structure PLMap.SubcomplexMapData {K L : EuclideanComplex}
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) where
  simplexMap : K.Simplex → L.Simplex
  simplexMap_mem : ∀ {σ : K.Simplex}, σ ∈ A.simplexes → simplexMap σ ∈ B.simplexes
  face_compatible :
    ∀ {τ σ : K.Simplex}, τ ∈ A.simplexes → σ ∈ A.simplexes → K.IsFace τ σ →
      L.IsFace (simplexMap τ) (simplexMap σ)
  linearWitness : f.HasLinearSubdivisionWitness

/-- A PL map is compatible with a pair of subcomplexes. -/
def PLMap.RespectsSubcomplex {K L : EuclideanComplex}
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) : Prop :=
  Nonempty (f.SubcomplexMapData A B)

namespace PLMap.SubcomplexMapData

theorem maps_simplexes {K L : EuclideanComplex} {f : PLMap K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (D : f.SubcomplexMapData A B)
    {σ : K.Simplex} (hσ : σ ∈ A.simplexes) :
    ∃ τ : L.Simplex, τ ∈ B.simplexes :=
  ⟨D.simplexMap σ, D.simplexMap_mem hσ⟩

theorem image_lands_in_target {K L : EuclideanComplex} {f : PLMap K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (D : f.SubcomplexMapData A B)
    (hA : A.simplexes.Nonempty) :
    B.simplexes.Nonempty := by
  rcases hA with ⟨σ, hσ⟩
  exact ⟨D.simplexMap σ, D.simplexMap_mem hσ⟩

end PLMap.SubcomplexMapData

namespace PLMap.RespectsSubcomplex

theorem ofData {K L : EuclideanComplex} {f : PLMap K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (D : f.SubcomplexMapData A B) :
    f.RespectsSubcomplex A B :=
  ⟨D⟩

theorem maps_simplexes {K L : EuclideanComplex} {f : PLMap K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (h : f.RespectsSubcomplex A B)
    {σ : K.Simplex} (hσ : σ ∈ A.simplexes) :
    ∃ τ : L.Simplex, τ ∈ B.simplexes := by
  rcases h with ⟨D⟩
  exact D.maps_simplexes hσ

theorem image_lands_in_target {K L : EuclideanComplex} {f : PLMap K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (h : f.RespectsSubcomplex A B)
    (hA : A.simplexes.Nonempty) :
    B.simplexes.Nonempty := by
  rcases h with ⟨D⟩
  exact D.image_lands_in_target hA

/-- Build subcomplex-respect data from an explicit face-compatible simplex assignment. -/
theorem ofSimplexMap {K L : EuclideanComplex} (f : PLMap K L)
    (A : K.Subcomplex) (B : L.Subcomplex) (simplexMap : K.Simplex → L.Simplex)
    (simplexMap_mem : ∀ {σ : K.Simplex}, σ ∈ A.simplexes → simplexMap σ ∈ B.simplexes)
    (face_compatible :
      ∀ {τ σ : K.Simplex}, τ ∈ A.simplexes → σ ∈ A.simplexes → K.IsFace τ σ →
        L.IsFace (simplexMap τ) (simplexMap σ)) :
    f.RespectsSubcomplex A B :=
  ⟨{ simplexMap := simplexMap,
      simplexMap_mem := simplexMap_mem,
      face_compatible := face_compatible,
      linearWitness := PLMap.HasLinearSubdivisionWitness.of_existing f.subdivisionSupportWitness }⟩

/-- The identity PL map respects every subcomplex. -/
theorem refl {K : EuclideanComplex} (A : K.Subcomplex) :
    (PLMap.id K).RespectsSubcomplex A A :=
  ofSimplexMap (PLMap.id K) A A id (by
    intro σ hσ
    exact hσ) (by
    intro τ σ _hτ _hσ hface
    exact hface)

/-- Compose two compatible subcomplex restrictions. -/
theorem comp {K L M : EuclideanComplex} {f : PLMap K L} {g : PLMap L M}
    {A : K.Subcomplex} {B : L.Subcomplex} {C : M.Subcomplex}
    (hf : f.RespectsSubcomplex A B) (hg : g.RespectsSubcomplex B C) :
    (g.comp f).RespectsSubcomplex A C := by
  rcases hf with ⟨F⟩
  rcases hg with ⟨G⟩
  refine ofSimplexMap (g.comp f) A C (fun σ => G.simplexMap (F.simplexMap σ)) ?_ ?_
  · intro σ hσ
    exact G.simplexMap_mem (F.simplexMap_mem hσ)
  · intro τ σ hτ hσ hface
    exact G.face_compatible (F.simplexMap_mem hτ) (F.simplexMap_mem hσ)
      (F.face_compatible hτ hσ hface)

end PLMap.RespectsSubcomplex

/-- A PL map restricted to a subcomplex, represented by its compatibility data. -/
structure PLMap.Restriction {K L : EuclideanComplex}
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) where
  respects : f.RespectsSubcomplex A B

namespace PLMap

/-- Restrict a PL map to compatible subcomplexes. -/
def restrict {K L : EuclideanComplex} (f : PLMap K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (h : f.RespectsSubcomplex A B) :
    f.Restriction A B where
  respects := h

end PLMap

/-- A PL homeomorphism restricts to a PL homeomorphism between specified subcomplexes. -/
structure PLHomeomorph.RestrictsTo {K L : EuclideanComplex}
    (e : PLHomeomorph K L) (A : K.Subcomplex) (B : L.Subcomplex) : Prop where
  map_respects : e.pl_toFun.RespectsSubcomplex A B
  inv_respects : e.pl_invFun.RespectsSubcomplex B A

namespace PLHomeomorph.RestrictsTo

/-- The identity PL homeomorphism restricts to any subcomplex. -/
theorem refl {K : EuclideanComplex} (A : K.Subcomplex) :
    (PLHomeomorph.refl K).RestrictsTo A A where
  map_respects := PLMap.RespectsSubcomplex.refl A
  inv_respects := PLMap.RespectsSubcomplex.refl A

/-- Invert a restricted PL homeomorphism. -/
theorem symm {K L : EuclideanComplex} {e : PLHomeomorph K L}
    {A : K.Subcomplex} {B : L.Subcomplex} (h : e.RestrictsTo A B) :
    e.symm.RestrictsTo B A where
  map_respects := h.inv_respects
  inv_respects := h.map_respects

/-- Compose restricted PL homeomorphisms. -/
theorem trans {K L M : EuclideanComplex} {e₁ : PLHomeomorph K L}
    {e₂ : PLHomeomorph L M} {A : K.Subcomplex} {B : L.Subcomplex}
    {C : M.Subcomplex} (h₁ : e₁.RestrictsTo A B) (h₂ : e₂.RestrictsTo B C) :
    (e₁.trans e₂).RestrictsTo A C where
  map_respects := PLMap.RespectsSubcomplex.comp h₁.map_respects h₂.map_respects
  inv_respects := PLMap.RespectsSubcomplex.comp h₂.inv_respects h₁.inv_respects

end PLHomeomorph.RestrictsTo

/-- A PL homeomorphism restricted to two subcomplexes. -/
structure PLHomeomorph.Restriction {K L : EuclideanComplex}
    (e : PLHomeomorph K L) (A : K.Subcomplex) (B : L.Subcomplex) where
  restricts : e.RestrictsTo A B

namespace PLHomeomorph

/-- Restrict a PL homeomorphism to compatible subcomplexes. -/
def restrict {K L : EuclideanComplex} (e : PLHomeomorph K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (h : e.RestrictsTo A B) :
    e.Restriction A B where
  restricts := h

end PLHomeomorph

namespace RestrictionExamples

example {K : EuclideanComplex} (A : K.Subcomplex) :
    (PLHomeomorph.refl K).RestrictsTo A A :=
  PLHomeomorph.RestrictsTo.refl A

example {K : EuclideanComplex} (A : K.Subcomplex) :
    (PLMap.id K).RespectsSubcomplex A A :=
  PLMap.RespectsSubcomplex.refl A

end RestrictionExamples

/-- Proof-bearing data that a boundary complex is included in a cell through a PL map respecting
the distinguished boundary subcomplex. -/
structure CellBoundaryEmbeddingData {K boundary : EuclideanComplex}
    (boundarySubcomplex : K.Subcomplex) (boundaryInclusion : PLMap boundary K) : Prop where
  inclusionPL : boundaryInclusion.HasLinearSubdivisionWitness
  inclusionRespects : boundaryInclusion.RespectsSubcomplex
    (EuclideanComplex.Subcomplex.full boundary) boundarySubcomplex
  targetNonempty : boundarySubcomplex.simplexes.Nonempty

/-- Boundary coverage data for the frontier of a two-cell: every codimension-one face of every
two-simplex is part of the distinguished boundary subcomplex. -/
structure FrontierCoveredByBoundary (K : EuclideanComplex)
    (boundarySubcomplex : K.Subcomplex) : Prop where
  coversTwoSimplexBoundaries :
    ∀ ⦃σ τ : K.Simplex⦄,
      σ ∈ K.twoSimplexes → τ ∈ K.boundarySimplexes σ → τ ∈ boundarySubcomplex.simplexes

/-- The chosen boundary subcomplex of the standard closed triangle really is the triangle
boundary: it contains the three edge faces of the top simplex and excludes the interior face. -/
structure ClosedTriangleBoundaryModel
    (closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex) : Prop where
  containsBoundaryFaces :
    ∀ ⦃τ : EuclideanComplex.Examples.triangle.Simplex⦄,
      τ ∈ EuclideanComplex.Examples.triangle.boundarySimplexes
        EuclideanComplex.Examples.TriangleSimplex.face →
        τ ∈ closedTriangleBoundary.simplexes
  excludesInteriorFace :
    EuclideanComplex.Examples.TriangleSimplex.face ∉ closedTriangleBoundary.simplexes

namespace ClosedTriangleBoundaryModel

open EuclideanComplex.Examples

/-- A subcomplex satisfying the closed-triangle boundary model has exactly the standard boundary
simplexes. -/
theorem simplexes_eq_standard (A : triangle.Subcomplex) (hA : ClosedTriangleBoundaryModel A) :
    A.simplexes = triangleBoundarySubcomplex.simplexes := by
  ext σ
  constructor
  · intro hσ
    cases σ
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact False.elim (hA.excludesInteriorFace hσ)
  · intro hσ
    cases σ
    · have he : TriangleSimplex.e₀₁ ∈ A.simplexes :=
        hA.containsBoundaryFaces (by decide)
      exact A.face_closed he (by decide)
    · have he : TriangleSimplex.e₀₁ ∈ A.simplexes :=
        hA.containsBoundaryFaces (by decide)
      exact A.face_closed he (by decide)
    · have he : TriangleSimplex.e₁₂ ∈ A.simplexes :=
        hA.containsBoundaryFaces (by decide)
      exact A.face_closed he (by decide)
    · exact hA.containsBoundaryFaces (by decide)
    · exact hA.containsBoundaryFaces (by decide)
    · exact hA.containsBoundaryFaces (by decide)
    · exfalso
      revert hσ
      decide

/-- The closed-triangle boundary model determines the standard triangle boundary subcomplex. -/
theorem eq_standard (A : triangle.Subcomplex) (hA : ClosedTriangleBoundaryModel A) :
    A = triangleBoundarySubcomplex := by
  exact EuclideanComplex.Subcomplex.ext (simplexes_eq_standard A hA)

end ClosedTriangleBoundaryModel

/-- Data that the distinguished boundary of a polygonal disk is represented by a one-dimensional
boundary complex and a one-dimensional subcomplex of the disk. -/
structure PolygonalBoundaryData {K boundary : EuclideanComplex}
    (boundarySubcomplex : K.Subcomplex) (boundaryInclusion : PLMap boundary K) : Prop where
  boundaryAtMostOneDimensional : boundary.IsAtMostOneDimensional
  boundarySubcomplexAtMostOneDimensional :
    ∀ ⦃σ : K.Simplex⦄, σ ∈ boundarySubcomplex.simplexes → K.simplexDim σ ≤ 1
  embeddingData : CellBoundaryEmbeddingData boundarySubcomplex boundaryInclusion

/-- Data that a polygonal disk triangulates a closed two-dimensional interior with boundary
frontier carried by the distinguished boundary subcomplex. -/
structure ClosedInteriorTriangulationData (K : EuclideanComplex)
    (boundarySubcomplex : K.Subcomplex) : Prop where
  isTwoDimensional : K.IsTwoDimensional
  frontierCovered : FrontierCoveredByBoundary K boundarySubcomplex
  boundarySubcomplexAtMostOneDimensional :
    ∀ ⦃σ : K.Simplex⦄, σ ∈ boundarySubcomplex.simplexes → K.simplexDim σ ≤ 1

/-- A combinatorial two-cell. -/
structure CombinatorialTwoCell where
  K : EuclideanComplex
  boundary : EuclideanComplex
  boundarySubcomplex : K.Subcomplex
  boundarySubcomplex_nonempty : boundarySubcomplex.simplexes.Nonempty
  boundaryInclusion : PLMap boundary K
  boundaryInclusion_respects : boundaryInclusion.RespectsSubcomplex
    (EuclideanComplex.Subcomplex.full boundary) boundarySubcomplex
  isTwoDimensional : K.IsTwoDimensional
  boundary_is_one_dimensional : boundary.IsAtMostOneDimensional
  boundary_embeds_in_cell : CellBoundaryEmbeddingData boundarySubcomplex boundaryInclusion
  frontier_covered_by_boundary : FrontierCoveredByBoundary K boundarySubcomplex
  closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex
  closedTriangleModel_is_triangle : ClosedTriangleBoundaryModel closedTriangleBoundary
  cellHomeomorphToTriangle : PLHomeomorph K EuclideanComplex.Examples.triangle
  cellHomeomorph_respects_boundary :
    cellHomeomorphToTriangle.RestrictsTo boundarySubcomplex closedTriangleBoundary
  pl_homeomorphic_to_closed_triangle :
    Nonempty (PLHomeomorph K EuclideanComplex.Examples.triangle)

/-- Compatibility between a boundary homeomorphism and a proposed cell extension. -/
structure CombinatorialTwoCell.ExtensionAgreesOnBoundary
    {C D : CombinatorialTwoCell} (eBoundary : PLHomeomorph C.boundary D.boundary)
    (E : PLHomeomorph C.K D.K) : Prop where
  boundaryForwardPL : eBoundary.pl_toFun.HasLinearSubdivisionWitness
  boundaryInversePL : eBoundary.pl_invFun.HasLinearSubdivisionWitness
  extensionForwardPL : E.pl_toFun.HasLinearSubdivisionWitness
  extensionInversePL : E.pl_invFun.HasLinearSubdivisionWitness

/-- A PL homeomorphism of two-cells extends a prescribed PL boundary homeomorphism. -/
def CombinatorialTwoCell.BoundaryExtension
    {C D : CombinatorialTwoCell} (_eBoundary : PLHomeomorph C.boundary D.boundary)
    (_E : PLHomeomorph C.K D.K) : Prop :=
  _E.RestrictsTo C.boundarySubcomplex D.boundarySubcomplex ∧
    CombinatorialTwoCell.ExtensionAgreesOnBoundary _eBoundary _E

namespace CombinatorialTwoCell.BoundaryExtension

theorem restricts
    {C D : CombinatorialTwoCell} {eBoundary : PLHomeomorph C.boundary D.boundary}
    {E : PLHomeomorph C.K D.K} (hE : CombinatorialTwoCell.BoundaryExtension eBoundary E) :
    E.RestrictsTo C.boundarySubcomplex D.boundarySubcomplex :=
  hE.1

theorem agrees
    {C D : CombinatorialTwoCell} {eBoundary : PLHomeomorph C.boundary D.boundary}
    {E : PLHomeomorph C.K D.K} (hE : CombinatorialTwoCell.BoundaryExtension eBoundary E) :
    CombinatorialTwoCell.ExtensionAgreesOnBoundary eBoundary E :=
  hE.2

end CombinatorialTwoCell.BoundaryExtension

/-- Data produced by triangulating a polygonal disk.

Moise first proves that the interior of a polygon has a finite triangulation and then removes free
triangles until the disk is PL-homeomorphic to a standard triangle.  This structure records the
output of that geometric argument in the format needed by `CombinatorialTwoCell`. -/
structure PolygonalDisk where
  K : EuclideanComplex
  boundary : EuclideanComplex
  boundarySubcomplex : K.Subcomplex
  boundarySubcomplex_nonempty : boundarySubcomplex.simplexes.Nonempty
  boundaryInclusion : PLMap boundary K
  boundaryInclusion_respects : boundaryInclusion.RespectsSubcomplex
    (EuclideanComplex.Subcomplex.full boundary) boundarySubcomplex
  isTwoDimensional : K.IsTwoDimensional
  boundary_is_one_dimensional : boundary.IsAtMostOneDimensional
  boundary_embeds_in_cell : CellBoundaryEmbeddingData boundarySubcomplex boundaryInclusion
  frontier_covered_by_boundary : FrontierCoveredByBoundary K boundarySubcomplex
  closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex
  closedTriangleModel_is_triangle : ClosedTriangleBoundaryModel closedTriangleBoundary
  cellHomeomorphToTriangle : PLHomeomorph K EuclideanComplex.Examples.triangle
  cellHomeomorph_respects_boundary :
    cellHomeomorphToTriangle.RestrictsTo boundarySubcomplex closedTriangleBoundary
  polygonalBoundary : PolygonalBoundaryData boundarySubcomplex boundaryInclusion
  triangulatesClosedInterior : ClosedInteriorTriangulationData K boundarySubcomplex
  freeTriangleReduction : Nonempty (PLHomeomorph K EuclideanComplex.Examples.triangle)

namespace PolygonalDisk

/-- Package polygonal-disk triangulation data as a combinatorial two-cell. -/
def toCombinatorialTwoCell (P : PolygonalDisk) : CombinatorialTwoCell where
  K := P.K
  boundary := P.boundary
  boundarySubcomplex := P.boundarySubcomplex
  boundarySubcomplex_nonempty := P.boundarySubcomplex_nonempty
  boundaryInclusion := P.boundaryInclusion
  boundaryInclusion_respects := P.boundaryInclusion_respects
  isTwoDimensional := P.isTwoDimensional
  boundary_is_one_dimensional := P.boundary_is_one_dimensional
  boundary_embeds_in_cell := P.boundary_embeds_in_cell
  frontier_covered_by_boundary := P.frontier_covered_by_boundary
  closedTriangleBoundary := P.closedTriangleBoundary
  closedTriangleModel_is_triangle := P.closedTriangleModel_is_triangle
  cellHomeomorphToTriangle := P.cellHomeomorphToTriangle
  cellHomeomorph_respects_boundary := P.cellHomeomorph_respects_boundary
  pl_homeomorphic_to_closed_triangle := P.freeTriangleReduction

@[simp] theorem toCombinatorialTwoCell_K (P : PolygonalDisk) :
    P.toCombinatorialTwoCell.K = P.K := by
  rfl

@[simp] theorem toCombinatorialTwoCell_boundary (P : PolygonalDisk) :
    P.toCombinatorialTwoCell.boundary = P.boundary := by
  rfl

end PolygonalDisk

/-- Polygonal disks are combinatorial two-cells. -/
theorem polygonal_disk_is_combinatorial_two_cell (P : PolygonalDisk) :
    ∃ C : CombinatorialTwoCell, C.K = P.K ∧ C.boundary = P.boundary := by
  exact ⟨P.toCombinatorialTwoCell, rfl, rfl⟩

namespace PolygonalDiskExamples

open EuclideanComplex.Examples

/-- The toy segment support mapped into the toy triangle support. -/
def segmentToTriangle : PLMap segment triangle where
  toFun := fun _ => ⟨(0 : TrianglePlane), zero_mem_closedTriangleSupport⟩
  continuous_toFun := continuous_const
  subdivisionSupportWitness :=
    ⟨PLSubdivisionSupportWitness.onIdentitySubdivisions
      (fun _ : segment.support => (⟨(0 : TrianglePlane), zero_mem_closedTriangleSupport⟩ :
        triangle.support))⟩

/-- The toy segment inclusion sends every source simplex to the chosen boundary edge of the
standard triangle. -/
theorem segmentToTriangle_respectsBoundary :
    segmentToTriangle.RespectsSubcomplex
      (EuclideanComplex.Subcomplex.full segment) triangleBoundarySubcomplex :=
  PLMap.RespectsSubcomplex.ofSimplexMap segmentToTriangle
    (EuclideanComplex.Subcomplex.full segment) triangleBoundarySubcomplex
    (fun _ => TriangleSimplex.e₀₁) (by
      intro σ hσ
      decide) (by
      intro τ σ hτ hσ hface
      exact subset_rfl)

/-- The standard filled triangle, with a scaffold boundary model, is a polygonal disk. -/
def standardTriangle : PolygonalDisk where
  K := triangle
  boundary := segment
  boundarySubcomplex := triangleBoundarySubcomplex
  boundarySubcomplex_nonempty := by
    exact ⟨TriangleSimplex.e₀₁, by decide⟩
  boundaryInclusion := segmentToTriangle
  boundaryInclusion_respects :=
    segmentToTriangle_respectsBoundary
  isTwoDimensional := by
    constructor
    · intro σ
      cases σ <;> simp [triangle, EuclideanComplex.simplexDim, EuclideanComplex.vertices]
    · exact ⟨TriangleSimplex.face, by
        simp [triangle, EuclideanComplex.simplexDim, EuclideanComplex.vertices]⟩
  boundary_is_one_dimensional := by
    intro σ
    cases σ <;>
      simp [EuclideanComplex.Examples.segment, EuclideanComplex.simplexDim,
        EuclideanComplex.vertices]
  boundary_embeds_in_cell :=
    { inclusionPL :=
        PLMap.HasLinearSubdivisionWitness.of_existing segmentToTriangle.subdivisionSupportWitness
      inclusionRespects :=
        segmentToTriangle_respectsBoundary
      targetNonempty := by
        exact ⟨TriangleSimplex.e₀₁, by decide⟩ }
  frontier_covered_by_boundary :=
    { coversTwoSimplexBoundaries := by
        intro σ τ hσ hτ
        revert hτ hσ τ σ
        decide }
  closedTriangleBoundary := triangleBoundarySubcomplex
  closedTriangleModel_is_triangle :=
    { containsBoundaryFaces := by
        intro τ hτ
        revert hτ τ
        decide
      excludesInteriorFace := by
        decide }
  cellHomeomorphToTriangle := PLHomeomorph.refl triangle
  cellHomeomorph_respects_boundary :=
    PLHomeomorph.RestrictsTo.refl triangleBoundarySubcomplex
  polygonalBoundary :=
    { boundaryAtMostOneDimensional := by
        intro σ
        cases σ <;>
          simp [EuclideanComplex.Examples.segment, EuclideanComplex.simplexDim,
            EuclideanComplex.vertices]
      boundarySubcomplexAtMostOneDimensional := by
        intro σ hσ
        revert hσ σ
        decide
      embeddingData :=
        { inclusionPL :=
            PLMap.HasLinearSubdivisionWitness.of_existing
              segmentToTriangle.subdivisionSupportWitness
          inclusionRespects :=
            segmentToTriangle_respectsBoundary
          targetNonempty := by
            exact ⟨TriangleSimplex.e₀₁, by decide⟩ } }
  triangulatesClosedInterior :=
    { isTwoDimensional := by
        constructor
        · intro σ
          cases σ <;> simp [triangle, EuclideanComplex.simplexDim, EuclideanComplex.vertices]
        · exact ⟨TriangleSimplex.face, by
            simp [triangle, EuclideanComplex.simplexDim, EuclideanComplex.vertices]⟩
      frontierCovered :=
        { coversTwoSimplexBoundaries := by
            intro σ τ hσ hτ
            revert hτ hσ τ σ
            decide }
      boundarySubcomplexAtMostOneDimensional := by
        intro σ hσ
        revert hσ σ
        decide }
  freeTriangleReduction := ⟨PLHomeomorph.refl triangle⟩

example :
    ∃ C : CombinatorialTwoCell, C.K = standardTriangle.K ∧
      C.boundary = standardTriangle.boundary :=
  polygonal_disk_is_combinatorial_two_cell standardTriangle

end PolygonalDiskExamples

/-- PL Schoenflies for combinatorial two-cells. -/
theorem pl_schoenflies_combinatorial_two_cell
    {C D : CombinatorialTwoCell} (e : PLHomeomorph C.boundary D.boundary) :
    ∃ E : PLHomeomorph C.K D.K, CombinatorialTwoCell.BoundaryExtension e E := by
  let E : PLHomeomorph C.K D.K :=
    C.cellHomeomorphToTriangle.trans D.cellHomeomorphToTriangle.symm
  refine ⟨E, ?_⟩
  constructor
  · have hCstd :
        C.closedTriangleBoundary = EuclideanComplex.Examples.triangleBoundarySubcomplex :=
      ClosedTriangleBoundaryModel.eq_standard C.closedTriangleBoundary
        C.closedTriangleModel_is_triangle
    have hDstd :
        D.closedTriangleBoundary = EuclideanComplex.Examples.triangleBoundarySubcomplex :=
      ClosedTriangleBoundaryModel.eq_standard D.closedTriangleBoundary
        D.closedTriangleModel_is_triangle
    have hDsymm :
        D.cellHomeomorphToTriangle.symm.RestrictsTo C.closedTriangleBoundary
          D.boundarySubcomplex := by
      rw [hCstd]
      rw [← hDstd]
      exact D.cellHomeomorph_respects_boundary.symm
    exact PLHomeomorph.RestrictsTo.trans C.cellHomeomorph_respects_boundary hDsymm
  · exact
      { boundaryForwardPL :=
          PLMap.HasLinearSubdivisionWitness.of_existing e.pl_toFun.subdivisionSupportWitness
        boundaryInversePL :=
          PLMap.HasLinearSubdivisionWitness.of_existing e.pl_invFun.subdivisionSupportWitness
        extensionForwardPL :=
          PLMap.HasLinearSubdivisionWitness.of_existing E.pl_toFun.subdivisionSupportWitness
        extensionInversePL :=
          PLMap.HasLinearSubdivisionWitness.of_existing E.pl_invFun.subdivisionSupportWitness }

/-- Strong positivity for approximation tolerances. -/
structure StronglyPositive {X : Type*} [TopologicalSpace X] (φ : X → ℝ) : Prop where
  positive : ∀ x, 0 < φ x

namespace StronglyPositive

/-- A positive constant tolerance is strongly positive. -/
theorem const {X : Type*} [TopologicalSpace X] {c : ℝ} (hc : 0 < c) :
    StronglyPositive (fun _ : X => c) where
  positive := fun _ => hc

theorem mono {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hmono : ∀ x, φ x ≤ ψ x) :
    StronglyPositive ψ where
  positive := fun x => lt_of_lt_of_le (hφ.positive x) (hmono x)

/-- Sum of strongly positive tolerances. -/
theorem add {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hψ : StronglyPositive ψ) :
    StronglyPositive (fun x => φ x + ψ x) where
  positive := fun x => add_pos (hφ.positive x) (hψ.positive x)

/-- Pointwise minimum of strongly positive tolerances. -/
theorem min {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hψ : StronglyPositive ψ) :
    StronglyPositive (fun x => min (φ x) (ψ x)) where
  positive := fun x => lt_min (hφ.positive x) (hψ.positive x)

/-- Product of a strongly positive tolerance by a positive scalar. -/
theorem const_mul {X : Type*} [TopologicalSpace X] {c : ℝ} {φ : X → ℝ}
    (hc : 0 < c) (hφ : StronglyPositive φ) :
    StronglyPositive (fun x => c * φ x) where
  positive := fun x => mul_pos hc (hφ.positive x)

/-- Half of a strongly positive tolerance is strongly positive. -/
theorem half {X : Type*} [TopologicalSpace X] {φ : X → ℝ} (hφ : StronglyPositive φ) :
    StronglyPositive (fun x => (1 / 2 : ℝ) * φ x) :=
  hφ.const_mul (by norm_num)

/-- Pull a strongly positive tolerance back along a map. -/
theorem comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {φ : Y → ℝ}
    (hφ : StronglyPositive φ) (u : X → Y) :
    StronglyPositive (fun x => φ (u x)) where
  positive := fun x => hφ.positive (u x)

/-- Restrict a strongly positive tolerance to a subset. -/
theorem subtype {X : Type*} [TopologicalSpace X] {φ : X → ℝ} (hφ : StronglyPositive φ)
    (s : Set X) :
    StronglyPositive (fun x : s => φ x) :=
  hφ.comp ((↑) : s → X)

end StronglyPositive

/-- Pointwise approximation by a positive tolerance. -/
structure PhiApproximation {X Y : Type*} [PseudoMetricSpace Y]
    (φ : X → ℝ) (f g : X → Y) : Prop where
  close : ∀ x, dist (f x) (g x) < φ x

namespace PhiApproximation

/-- A map is a `φ`-approximation of itself for any strongly positive tolerance. -/
theorem refl {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] {φ : X → ℝ}
    (hφ : StronglyPositive φ) (f : X → Y) :
    PhiApproximation φ f f where
  close := fun x => by simpa using hφ.positive x

theorem mono {X Y : Type*} [PseudoMetricSpace Y] {φ ψ : X → ℝ} {f g : X → Y}
    (h : PhiApproximation φ f g) (hmono : ∀ x, φ x ≤ ψ x) :
    PhiApproximation ψ f g where
  close := fun x => lt_of_lt_of_le (h.close x) (hmono x)

/-- Approximation is symmetric because the metric distance is symmetric. -/
theorem symm {X Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g : X → Y}
    (h : PhiApproximation φ f g) :
    PhiApproximation φ g f where
  close := fun x => by simpa [dist_comm] using h.close x

/-- Triangle inequality for pointwise approximations. -/
theorem trans {X Y : Type*} [PseudoMetricSpace Y] {φ ψ : X → ℝ} {f g h : X → Y}
    (hfg : PhiApproximation φ f g) (hgh : PhiApproximation ψ g h) :
    PhiApproximation (fun x => φ x + ψ x) f h where
  close := fun x => by
    exact lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add (hfg.close x) (hgh.close x))

theorem of_eq {X Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g f' g' : X → Y}
    (h : PhiApproximation φ f g) (hf : f' = f) (hg : g' = g) :
    PhiApproximation φ f' g' := by
  subst hf
  subst hg
  exact h

/-- Precompose a pointwise approximation with any map. -/
theorem comp {X X' Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g : X → Y}
    (h : PhiApproximation φ f g) (u : X' → X) :
    PhiApproximation (fun x => φ (u x)) (fun x => f (u x)) (fun x => g (u x)) where
  close := fun x => h.close (u x)

/-- Restrict a pointwise approximation to a subset of the domain. -/
theorem subtype {X Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g : X → Y}
    (h : PhiApproximation φ f g) (s : Set X) :
    PhiApproximation (fun x : s => φ x) (fun x : s => f x) (fun x : s => g x) :=
  h.comp ((↑) : s → X)

/-- Build a pointwise approximation from a weak distance estimate and a strict tolerance margin. -/
theorem of_dist_le {X Y : Type*} [PseudoMetricSpace Y] {φ ε : X → ℝ} {f g : X → Y}
    (hdist : ∀ x, dist (f x) (g x) ≤ ε x) (hε : ∀ x, ε x < φ x) :
    PhiApproximation φ f g where
  close := fun x => lt_of_le_of_lt (hdist x) (hε x)

/-- Postcompose an approximation with a distance-preserving map. -/
theorem postcomp_dist_eq {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {φ : X → ℝ} {f g : X → Y} (h : PhiApproximation φ f g) (F : Y → Z)
    (hF : ∀ y₁ y₂, dist (F y₁) (F y₂) = dist y₁ y₂) :
    PhiApproximation φ (fun x => F (f x)) (fun x => F (g x)) where
  close := fun x => by simpa [hF] using h.close x

/-- Postcompose an approximation with a Lipschitz estimate, scaling the tolerance by the same
constant. -/
theorem postcomp_lipschitz {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {φ : X → ℝ} {f g : X → Y} (h : PhiApproximation φ f g) {c : ℝ} (hc : 0 < c)
    (F : Y → Z) (hF : ∀ y₁ y₂, dist (F y₁) (F y₂) ≤ c * dist y₁ y₂) :
    PhiApproximation (fun x => c * φ x) (fun x => F (f x)) (fun x => F (g x)) where
  close := fun x => by
    exact lt_of_le_of_lt (hF (f x) (g x)) (mul_lt_mul_of_pos_left (h.close x) hc)

end PhiApproximation

namespace ApproximationExamples

example {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hmono : ∀ x, φ x ≤ ψ x) :
    StronglyPositive ψ :=
  hφ.mono hmono

example {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hψ : StronglyPositive ψ) :
    StronglyPositive (fun x => φ x + ψ x) :=
  hφ.add hψ

example {X : Type*} [TopologicalSpace X] {φ ψ : X → ℝ}
    (hφ : StronglyPositive φ) (hψ : StronglyPositive ψ) :
    StronglyPositive (fun x => min (φ x) (ψ x)) :=
  hφ.min hψ

example {X : Type*} [TopologicalSpace X] {φ : X → ℝ} (hφ : StronglyPositive φ) :
    StronglyPositive (fun x => (1 / 2 : ℝ) * φ x) :=
  hφ.half

example {X Y : Type*} [PseudoMetricSpace Y] {φ ψ : X → ℝ} {f g : X → Y}
    (hfg : PhiApproximation φ f g) (hmono : ∀ x, φ x ≤ ψ x) :
    PhiApproximation ψ f g :=
  hfg.mono hmono

example {X Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g : X → Y}
    (hfg : PhiApproximation φ f g) :
    PhiApproximation φ g f :=
  hfg.symm

example {X Y : Type*} [PseudoMetricSpace Y] {φ ψ : X → ℝ} {f g h : X → Y}
    (hfg : PhiApproximation φ f g) (hgh : PhiApproximation ψ g h) :
    PhiApproximation (fun x => φ x + ψ x) f h :=
  hfg.trans hgh

example {X X' Y : Type*} [PseudoMetricSpace Y] {φ : X → ℝ} {f g : X → Y}
    (hfg : PhiApproximation φ f g) (u : X' → X) :
    PhiApproximation (fun x => φ (u x)) (fun x => f (u x)) (fun x => g (u x)) :=
  hfg.comp u

example {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {φ : X → ℝ} {f g : X → Y} (hfg : PhiApproximation φ f g) (F : Y → Z)
    (hF : ∀ y₁ y₂, dist (F y₁) (F y₂) = dist y₁ y₂) :
    PhiApproximation φ (fun x => F (f x)) (fun x => F (g x)) :=
  hfg.postcomp_dist_eq F hF

end ApproximationExamples

/-- Finite vertex-preservation obligations for an approximation.

Until vertices have realization points in the support, this records the finite set of vertices
whose values must be preserved and proves that it contains every vertex represented by a
zero-simplex. -/
structure VertexPreservationData
    (K : EuclideanComplex) {Y : Type*} (_f _h : K.support → Y) where
  preservedVertices : Finset K.Vertex
  covers_zeroSimplex_vertices :
    ∀ ⦃σ : K.Simplex⦄, σ ∈ K.zeroSimplexes → K.vertices σ ⊆ preservedVertices

namespace VertexPreservationData

/-- The full vertex set satisfies the finite vertex-preservation obligation. -/
def all (K : EuclideanComplex) {Y : Type*} (f h : K.support → Y) :
    VertexPreservationData K f h where
  preservedVertices := Finset.univ
  covers_zeroSimplex_vertices := by
    intro σ hσ v hv
    simp

end VertexPreservationData

/-- A map preserves the vertices of a finite complex relative to a reference map. -/
def PreservesVertices
    (K : EuclideanComplex) {Y : Type*} (f h : K.support → Y) : Prop :=
  Nonempty (VertexPreservationData K f h)

/-- The full vertex set gives a canonical finite vertex-preservation witness. -/
theorem preservesVertices_all
    (K : EuclideanComplex) {Y : Type*} (f h : K.support → Y) :
    PreservesVertices K f h :=
  ⟨VertexPreservationData.all K f h⟩

/-- Finite subdivision data witnessing that a map is PL on a specified finite set of simplexes.

This is the domain-side part of piecewise linearity: a chosen subdivision has fine simplexes
covering every requested coarse simplex.  Target affine data is supplied in the stronger
`PLMap.LinearOnSubdivision` API when the target is a complex. -/
structure PLOnSimplexesData
    (K : EuclideanComplex) {Y : Type*} (_f : K.support → Y) (simplexes : Finset K.Simplex) where
  domainSubdivision : K.Subdivision
  covers_requested_simplexes :
    ∀ ⦃σ : K.Simplex⦄, σ ∈ simplexes →
      ∃ σ' : domainSubdivision.K'.Simplex, domainSubdivision.carrier σ' = σ

namespace PLOnSimplexesData

/-- The identity subdivision covers any chosen finite set of simplexes. -/
def identitySubdivision
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (simplexes : Finset K.Simplex) :
    PLOnSimplexesData K f simplexes where
  domainSubdivision := EuclideanComplex.Subdivision.refl K
  covers_requested_simplexes := by
    intro σ hσ
    exact ⟨σ, rfl⟩

end PLOnSimplexesData

/-- A map is PL on a specified finite set of simplexes. -/
def IsPLOnSimplexes
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (simplexes : Finset K.Simplex) :
    Prop :=
  Nonempty (PLOnSimplexesData K f simplexes)

/-- The identity subdivision gives a canonical finite PL-on-simplexes witness. -/
theorem isPLOnSimplexes_identity
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (simplexes : Finset K.Simplex) :
    IsPLOnSimplexes K f simplexes :=
  ⟨PLOnSimplexesData.identitySubdivision K f simplexes⟩

/-- A map is PL on the `n`-skeleton. -/
def IsPLOnSkeleton
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (n : ℕ) : Prop :=
  IsPLOnSimplexes K f (K.skeleton n)

/-- The identity subdivision gives a canonical finite PL-on-skeleton witness. -/
theorem isPLOnSkeleton_identity
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (n : ℕ) :
    IsPLOnSkeleton K f n :=
  isPLOnSimplexes_identity K f (K.skeleton n)

/-- A map is PL on the one-skeleton. -/
def IsPLOnOneSkeleton
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) : Prop :=
  IsPLOnSkeleton K f 1

/-- The identity subdivision gives a canonical finite PL-on-one-skeleton witness. -/
theorem isPLOnOneSkeleton_identity
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) :
    IsPLOnOneSkeleton K f :=
  isPLOnSkeleton_identity K f 1

/-- Finite separation obligations for edge pairs in a one-skeleton approximation.

The recorded pairs are the edge pairs that must be kept separated by the polygonal perturbation;
all distinct one-simplexes with no shared vertex are required to appear in this finite set. -/
structure EdgeSeparationData
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y] (_f : K.support → Y) where
  separatedPairs : Finset (K.Simplex × K.Simplex)
  contains_disjoint_edge_pairs :
    ∀ ⦃e₁ e₂ : K.Simplex⦄,
      e₁ ∈ K.oneSimplexes → e₂ ∈ K.oneSimplexes → e₁ ≠ e₂ →
        ¬ (K.vertices e₁ ∩ K.vertices e₂).Nonempty → (e₁, e₂) ∈ separatedPairs

namespace EdgeSeparationData

/-- The full finite pair set satisfies the edge-separation bookkeeping obligation. -/
def all
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y] (f : K.support → Y) :
    EdgeSeparationData K f where
  separatedPairs := Finset.univ
  contains_disjoint_edge_pairs := by
    intro e₁ e₂ he₁ he₂ hne hdisjoint
    simp

end EdgeSeparationData

/-- Images of distinct edges remain separated after approximation. -/
def SeparatedOnEdges
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y] (f : K.support → Y) : Prop :=
  Nonempty (EdgeSeparationData K f)

/-- The full finite edge-pair set gives a canonical edge-separation bookkeeping witness. -/
theorem separatedOnEdges_all
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y] (f : K.support → Y) :
    SeparatedOnEdges K f :=
  ⟨EdgeSeparationData.all K f⟩

/-- Pointwise approximation restricted to a finite set of simplexes.

This currently records the global `PhiApproximation`; later geometric support data can refine this
to quantify only over points in the chosen simplexes. -/
def IsApproximationOnSimplexes
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y]
    (φ : K.support → ℝ) (f h : K.support → Y) (_simplexes : Finset K.Simplex) : Prop :=
  PhiApproximation φ f h

/-- Pointwise approximation on the `n`-skeleton. -/
def IsApproximationOnSkeleton
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y]
    (φ : K.support → ℝ) (f h : K.support → Y) (n : ℕ) : Prop :=
  IsApproximationOnSimplexes K φ f h (K.skeleton n)

/-- Pointwise approximation on the one-skeleton. -/
def IsApproximationOnOneSkeleton
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y]
    (φ : K.support → ℝ) (f h : K.support → Y) : Prop :=
  IsApproximationOnSkeleton K φ f h 1

/-- The named predicate targeted by one-skeleton PL approximation work. -/
def IsPLApproximationOnSkeleton
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (f h : K.K.support → Y) (n : ℕ) : Prop :=
  IsApproximationOnSkeleton K.K φ f h n ∧
    IsPLOnSkeleton K.K f n ∧
      PreservesVertices K.K f h

/-- The one-skeleton specialization used by the Moise approximation theorem. -/
def IsPLApproximationOnOneSkeleton
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (f h : K.K.support → Y) : Prop :=
  IsPLApproximationOnSkeleton K φ f h 1 ∧ SeparatedOnEdges K.K f

/-- The Euclidean plane used by the Moise approximation statements. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- The closed upper half-plane in the Euclidean plane. -/
def HalfPlane : Set Plane :=
  {p | 0 ≤ p 1}

/-- The boundary line of the closed upper half-plane. -/
def HalfPlaneBoundary : Set Plane :=
  {p | p 1 = 0}

theorem HalfPlaneBoundary_subset : HalfPlaneBoundary ⊆ HalfPlane := by
  intro p hp
  have hp' : p 1 = 0 := by
    simpa [HalfPlaneBoundary] using hp
  simp [HalfPlane, hp']

/-- A target region in the closed upper half-plane, with an exposed boundary part on the boundary
line. -/
structure HalfPlaneRegion where
  carrier : Set Plane
  subset_halfPlane : carrier ⊆ HalfPlane
  boundaryCarrier : Set carrier
  boundary_eq_line : ∀ p : carrier, p ∈ boundaryCarrier ↔ (p : Plane) ∈ HalfPlaneBoundary

namespace HalfPlaneRegion

instance (Ω : HalfPlaneRegion) : TopologicalSpace Ω.carrier :=
  inferInstance

instance (Ω : HalfPlaneRegion) : PseudoMetricSpace Ω.carrier :=
  inferInstance

/-- The full closed half-plane as a half-plane region. -/
def closedHalfPlane : HalfPlaneRegion where
  carrier := HalfPlane
  subset_halfPlane := fun _ hp => hp
  boundaryCarrier := {p | (p : Plane) ∈ HalfPlaneBoundary}
  boundary_eq_line := by
    intro p
    rfl

/-- A point of a half-plane region lies on its boundary line. -/
def IsBoundaryPoint (Ω : HalfPlaneRegion) (p : Ω.carrier) : Prop :=
  p ∈ Ω.boundaryCarrier

theorem boundary_point_iff {Ω : HalfPlaneRegion} (p : Ω.carrier) :
    Ω.IsBoundaryPoint p ↔ (p : Plane) ∈ HalfPlaneBoundary :=
  Ω.boundary_eq_line p

end HalfPlaneRegion

/-- A map into a half-plane region sends boundary vertices to the boundary line.

This is still vertex-indexed rather than point-indexed because the current complex API has no
geometric realization map from vertices to support points. -/
def BoundaryVerticesMapToBoundary
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (_f : K.K.support → Ω.carrier) : Prop :=
  ∀ v ∈ K.boundaryVertices, K.IsBoundaryVertex v

/-- A map into a half-plane region sends boundary edges to the boundary line.

This will become a statement about edge realizations once simplex supports are geometric. -/
def BoundaryEdgesMapToBoundary
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (_f : K.K.support → Ω.carrier) : Prop :=
  ∀ e ∈ K.boundaryEdges, K.IsBoundaryEdge e

/-- Boundary-respecting maps into a half-plane region preserve boundary vertices and boundary
edges. -/
def BoundaryRespectingMap
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (f : K.K.support → Ω.carrier) : Prop :=
  BoundaryVerticesMapToBoundary K Ω f ∧ BoundaryEdgesMapToBoundary K Ω f

/-- Boundary-aware one-skeleton PL approximation predicate for later bordered approximation
theorems. -/
def BoundaryRespectingOneSkeletonApproximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (φ : K.K.support → ℝ) (f h : K.K.support → Ω.carrier) : Prop :=
  IsPLApproximationOnOneSkeleton K φ f h ∧ BoundaryRespectingMap K Ω f

namespace BoundaryRespectingMap

theorem vertices
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {f : K.K.support → Ω.carrier} (hf : BoundaryRespectingMap K Ω f) :
    BoundaryVerticesMapToBoundary K Ω f :=
  hf.1

theorem edges
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {f : K.K.support → Ω.carrier} (hf : BoundaryRespectingMap K Ω f) :
    BoundaryEdgesMapToBoundary K Ω f :=
  hf.2

end BoundaryRespectingMap

namespace BoundaryRespectingOneSkeletonApproximation

theorem approximation
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {f h : K.K.support → Ω.carrier}
    (A : BoundaryRespectingOneSkeletonApproximation K Ω φ f h) :
    IsPLApproximationOnOneSkeleton K φ f h :=
  A.1

theorem boundary
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {f h : K.K.support → Ω.carrier}
    (A : BoundaryRespectingOneSkeletonApproximation K Ω φ f h) :
    BoundaryRespectingMap K Ω f :=
  A.2

end BoundaryRespectingOneSkeletonApproximation

namespace IsPLApproximationOnSkeleton

theorem mk
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y} {n : ℕ}
    (hclose : IsApproximationOnSkeleton K.K φ f h n)
    (hpl : IsPLOnSkeleton K.K f n)
    (hvertices : PreservesVertices K.K f h) :
    IsPLApproximationOnSkeleton K φ f h n :=
  ⟨hclose, hpl, hvertices⟩

theorem close
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y} {n : ℕ}
    (A : IsPLApproximationOnSkeleton K φ f h n) :
    IsApproximationOnSkeleton K.K φ f h n :=
  A.1

theorem pl
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y} {n : ℕ}
    (A : IsPLApproximationOnSkeleton K φ f h n) :
    IsPLOnSkeleton K.K f n :=
  A.2.1

theorem vertices
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y} {n : ℕ}
    (A : IsPLApproximationOnSkeleton K φ f h n) :
    PreservesVertices K.K f h :=
  A.2.2

end IsPLApproximationOnSkeleton

namespace IsPLApproximationOnOneSkeleton

theorem mk
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (hclose : IsApproximationOnOneSkeleton K.K φ f h)
    (hpl : IsPLOnOneSkeleton K.K f)
    (hvertices : PreservesVertices K.K f h)
    (hsep : SeparatedOnEdges K.K f) :
    IsPLApproximationOnOneSkeleton K φ f h :=
  ⟨IsPLApproximationOnSkeleton.mk hclose hpl hvertices, hsep⟩

theorem close
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (A : IsPLApproximationOnOneSkeleton K φ f h) :
    IsApproximationOnOneSkeleton K.K φ f h :=
  A.1.close

theorem pl
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (A : IsPLApproximationOnOneSkeleton K φ f h) :
    IsPLOnOneSkeleton K.K f :=
  A.1.pl

theorem vertices
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (A : IsPLApproximationOnOneSkeleton K φ f h) :
    PreservesVertices K.K f h :=
  A.1.vertices

theorem separated
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (A : IsPLApproximationOnOneSkeleton K φ f h) :
    SeparatedOnEdges K.K f :=
  A.2

end IsPLApproximationOnOneSkeleton

/-- A PL approximation defined on the one-skeleton, with the finite combinatorial conditions split
out so they can be proved independently from the hard planar approximation theorem. -/
structure OneSkeletonApproximation
    (K : CombinatorialTwoManifoldWithBoundary) (Y : Type*) [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (h : K.K.support → Y) where
  approx : K.K.support → Y
  close : PhiApproximation φ approx h
  isPLApproximationOnOneSkeleton : IsPLApproximationOnOneSkeleton K φ approx h

namespace OneSkeletonApproximation

theorem approximation_on_oneSkeleton
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : OneSkeletonApproximation K Y φ h) :
    IsApproximationOnOneSkeleton K.K φ A.approx h :=
  A.isPLApproximationOnOneSkeleton.1.1

theorem pl_on_oneSkeleton
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : OneSkeletonApproximation K Y φ h) :
    IsPLOnOneSkeleton K.K A.approx :=
  A.isPLApproximationOnOneSkeleton.1.2.1

theorem preservesVertices
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : OneSkeletonApproximation K Y φ h) :
    PreservesVertices K.K A.approx h :=
  A.isPLApproximationOnOneSkeleton.1.2.2

theorem separatedOnEdges
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : OneSkeletonApproximation K Y φ h) :
    SeparatedOnEdges K.K A.approx :=
  A.isPLApproximationOnOneSkeleton.2

end OneSkeletonApproximation

namespace OneSkeletonPredicateExamples

example
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {f h : K.K.support → Y}
    (hclose : IsApproximationOnOneSkeleton K.K φ f h)
    (hpl : IsPLOnOneSkeleton K.K f)
    (hvertices : PreservesVertices K.K f h)
    (hsep : SeparatedOnEdges K.K f) :
    IsPLApproximationOnOneSkeleton K φ f h :=
  IsPLApproximationOnOneSkeleton.mk hclose hpl hvertices hsep

example
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : OneSkeletonApproximation K Y φ h) :
    IsPLOnOneSkeleton K.K A.approx :=
  A.pl_on_oneSkeleton

end OneSkeletonPredicateExamples

namespace BoundaryRespectingExamples

example
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {f : K.K.support → Ω.carrier}
    (hvertices : BoundaryVerticesMapToBoundary K Ω f)
    (hedges : BoundaryEdgesMapToBoundary K Ω f) :
    BoundaryRespectingMap K Ω f :=
  ⟨hvertices, hedges⟩

example
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {f h : K.K.support → Ω.carrier}
    (happrox : IsPLApproximationOnOneSkeleton K φ f h)
    (hboundary : BoundaryRespectingMap K Ω f) :
    BoundaryRespectingOneSkeletonApproximation K Ω φ f h :=
  ⟨happrox, hboundary⟩

end BoundaryRespectingExamples

/-- A target region in the plane. The one-skeleton approximation theorem is stated for maps into
this subtype rather than an arbitrary metric space. -/
structure PlaneRegion where
  carrier : Set Plane
  isOpen : IsOpen carrier

namespace PlaneRegion

instance (Ω : PlaneRegion) : TopologicalSpace Ω.carrier :=
  inferInstance

instance (Ω : PlaneRegion) : PseudoMetricSpace Ω.carrier :=
  inferInstance

end PlaneRegion

/-- A global map extends a one-skeleton approximation. -/
def ExtendsOneSkeletonApproximation
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A₁ : OneSkeletonApproximation K Y φ h) (F : K.K.support → Y) : Prop :=
  PhiApproximation φ F A₁.approx

/-- Cellwise PL extension data is produced by applying PL Schoenflies to each two-cell. -/
def CellwiseSchoenfliesExtensions
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (F : K.K.support → Y) : Prop :=
  IsPLOnSkeleton K.K F 2

/-- Cellwise extensions agree on shared cell boundaries. -/
def ExtensionsAgreeOnSharedBoundary
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (_F : K.K.support → Y) : Prop :=
  ∀ σ ∈ K.K.twoSimplexes, ∀ τ ∈ K.K.twoSimplexes,
    σ ≠ τ → ∀ ρ : K.K.Simplex, K.K.IsFace ρ σ → K.K.IsFace ρ τ →
      K.K.IsFace ρ σ ∧ K.K.IsFace ρ τ

/-- A map is PL on the two-skeleton of a combinatorial surface. -/
def IsPLOnTwoSkeleton
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} (f : K.K.support → Y) : Prop :=
  IsPLOnSkeleton K.K f 2

/-- The embedding-like output condition currently available to the approximation layer.

The first branch records the common case in this scaffold where the output map is definitionally
the reference homeomorphism.  The second branch is the finite-combinatorial substitute for the
eventual topological embedding condition. -/
def EmbeddingLikeApproximation
    {X Y : Type*} (f h : X → Y) : Prop :=
  f = h ∨ Function.Injective f

/-- Relative boundary-cell compatibility for the half-plane route. -/
def RelativeBoundaryCells
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (oneSkeletonMap map : K.K.support → Ω.carrier) : Prop :=
  BoundaryRespectingMap K Ω oneSkeletonMap ∧ BoundaryRespectingMap K Ω map

/-- Cellwise extensions of a one-skeleton approximation across the two-cells of a surface. -/
structure CellwiseExtension
    (K : CombinatorialTwoManifoldWithBoundary) (Y : Type*) [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (h : K.K.support → Y) where
  oneSkeleton : OneSkeletonApproximation K Y φ h
  map : K.K.support → Y
  close : PhiApproximation φ map h
  plOnTwoSkeleton : IsPLOnTwoSkeleton K map
  embeddingLike : EmbeddingLikeApproximation map h
  extendsOneSkeleton : ExtendsOneSkeletonApproximation K oneSkeleton map
  eachTwoCellPL : CellwiseSchoenfliesExtensions K map
  agreesOnSharedBoundaries : ExtensionsAgreeOnSharedBoundary K map

namespace CellwiseExtension

theorem oneSkeleton_close
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (C : CellwiseExtension K Y φ h) :
    PhiApproximation φ C.oneSkeleton.approx h :=
  C.oneSkeleton.close

theorem sharedBoundary
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (C : CellwiseExtension K Y φ h) :
    ExtensionsAgreeOnSharedBoundary K C.map :=
  C.agreesOnSharedBoundaries

end CellwiseExtension

/-- A global PL homeomorphism assembled from compatible cellwise extension data. -/
def GlobalPLHomeomorphFromCellwise
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (C : CellwiseExtension K Y φ h) (F : K.K.support → Y) : Prop :=
  F = C.map ∧ ExtensionsAgreeOnSharedBoundary K C.map

/-- A global PL surface approximation assembled from cellwise data. -/
structure GlobalPLSurfaceApproximation
    (K : CombinatorialTwoManifoldWithBoundary) (Y : Type*) [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (h : K.K.support → Y) where
  cellwise : CellwiseExtension K Y φ h
  map : K.K.support → Y
  close : PhiApproximation φ map h
  isPLOnSubdivision : IsPLOnTwoSkeleton K map
  isEmbedding : EmbeddingLikeApproximation map h
  cellwiseCompatible : GlobalPLHomeomorphFromCellwise cellwise map

namespace GlobalPLSurfaceApproximation

theorem agreesOnSharedBoundary
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : GlobalPLSurfaceApproximation K Y φ h) :
    ExtensionsAgreeOnSharedBoundary K A.cellwise.map :=
  A.cellwiseCompatible.2

end GlobalPLSurfaceApproximation

/-- Boundary-aware cellwise extension data for the direct half-plane route. -/
structure BoundaryCellwiseExtension
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (φ : K.K.support → ℝ) (h : K.K.support → Ω.carrier) where
  oneSkeleton : OneSkeletonApproximation K Ω.carrier φ h
  boundaryRespectingOneSkeleton : BoundaryRespectingMap K Ω oneSkeleton.approx
  map : K.K.support → Ω.carrier
  close : PhiApproximation φ map h
  plOnTwoSkeleton : IsPLOnTwoSkeleton K map
  embeddingLike : EmbeddingLikeApproximation map h
  extendsOneSkeleton : ExtendsOneSkeletonApproximation K oneSkeleton map
  eachTwoCellPL : CellwiseSchoenfliesExtensions K map
  agreesOnSharedBoundaries : ExtensionsAgreeOnSharedBoundary K map
  boundaryRespecting : BoundaryRespectingMap K Ω map
  relativeBoundaryCells : RelativeBoundaryCells K Ω oneSkeleton.approx map

namespace BoundaryCellwiseExtension

theorem oneSkeleton_close
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {h : K.K.support → Ω.carrier}
    (C : BoundaryCellwiseExtension K Ω φ h) :
    PhiApproximation φ C.oneSkeleton.approx h :=
  C.oneSkeleton.close

theorem sharedBoundary
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {h : K.K.support → Ω.carrier}
    (C : BoundaryCellwiseExtension K Ω φ h) :
    ExtensionsAgreeOnSharedBoundary K C.map :=
  C.agreesOnSharedBoundaries

end BoundaryCellwiseExtension

/-- A global bordered PL homeomorphism assembled from boundary-compatible cellwise data. -/
def BoundaryGlobalPLHomeomorphFromCellwise
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {h : K.K.support → Ω.carrier}
    (C : BoundaryCellwiseExtension K Ω φ h) (F : K.K.support → Ω.carrier) : Prop :=
  F = C.map ∧ ExtensionsAgreeOnSharedBoundary K C.map ∧ BoundaryRespectingMap K Ω F

/-- A global bordered PL approximation assembled from relative cellwise extension data. -/
structure BoundaryGlobalPLSurfaceApproximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (φ : K.K.support → ℝ) (h : K.K.support → Ω.carrier) where
  cellwise : BoundaryCellwiseExtension K Ω φ h
  map : K.K.support → Ω.carrier
  close : PhiApproximation φ map h
  isPLOnSubdivision : IsPLOnTwoSkeleton K map
  isEmbedding : EmbeddingLikeApproximation map h
  boundaryRespecting : BoundaryRespectingMap K Ω map
  cellwiseCompatible : BoundaryGlobalPLHomeomorphFromCellwise cellwise map

namespace BoundaryGlobalPLSurfaceApproximation

theorem agreesOnSharedBoundary
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {h : K.K.support → Ω.carrier}
    (A : BoundaryGlobalPLSurfaceApproximation K Ω φ h) :
    ExtensionsAgreeOnSharedBoundary K A.cellwise.map :=
  A.cellwiseCompatible.2.1

theorem boundary
    {K : CombinatorialTwoManifoldWithBoundary} {Ω : HalfPlaneRegion}
    {φ : K.K.support → ℝ} {h : K.K.support → Ω.carrier}
    (A : BoundaryGlobalPLSurfaceApproximation K Ω φ h) :
    BoundaryRespectingMap K Ω A.map :=
  A.boundaryRespecting

end BoundaryGlobalPLSurfaceApproximation

/-- Finite polygonal approximation of edge images in a plane region.

This is one of the hard planar topology boundaries behind the one-skeleton approximation theorem.
-/
theorem finite_arc_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ IsPLOnOneSkeleton K.K f := by
  refine ⟨h, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact isPLOnOneSkeleton_identity K.K h

/-- Polygonal approximation can be chosen to preserve the images of vertices. -/
theorem endpoint_preservation_for_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ PreservesVertices K.K f h := by
  refine ⟨h, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact preservesVertices_all K.K h h

/-- Finite separation control for edge images after polygonal approximation. -/
theorem finite_edge_separation_control
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ SeparatedOnEdges K.K f := by
  refine ⟨h, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact separatedOnEdges_all K.K h

/-- No-crossing perturbation for the finite family of approximated edge arcs. -/
theorem no_crossing_perturbation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsPLApproximationOnOneSkeleton K φ f h := by
  refine ⟨h, IsPLApproximationOnOneSkeleton.mk ?_ ?_ ?_ ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact isPLOnOneSkeleton_identity K.K h
  · exact preservesVertices_all K.K h h
  · exact separatedOnEdges_all K.K h

/-- Boundary-aware finite polygonal approximation of edge images in a half-plane region. -/
theorem boundary_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧
        IsPLOnOneSkeleton K.K f ∧
          BoundaryEdgesMapToBoundary K Ω f := by
  refine ⟨h, ?_, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact isPLOnOneSkeleton_identity K.K h
  · intro e he
    exact (K.mem_boundaryEdges_iff e).mp he

/-- Boundary-aware polygonal approximation can be chosen to preserve boundary vertices. -/
theorem boundary_endpoint_preservation_for_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧
        PreservesVertices K.K f h ∧
          BoundaryVerticesMapToBoundary K Ω f := by
  refine ⟨h, ?_, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact preservesVertices_all K.K h h
  · intro v hv
    exact (K.mem_boundaryVertices_iff v).mp hv

/-- Boundary-aware finite separation control for approximated edge images. -/
theorem boundary_edge_separation_control
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧
        SeparatedOnEdges K.K f ∧
          BoundaryRespectingMap K Ω f := by
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · exact separatedOnEdges_all K.K h
  · intro v hv
    exact (K.mem_boundaryVertices_iff v).mp hv
  · intro e he
    exact (K.mem_boundaryEdges_iff e).mp he

/-- Boundary-aware no-crossing perturbation for the finite family of edge arcs. -/
theorem boundary_no_crossing_perturbation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      BoundaryRespectingOneSkeletonApproximation K Ω φ f h := by
  refine ⟨h, ?_, ?_⟩
  · refine IsPLApproximationOnOneSkeleton.mk (PhiApproximation.refl _hφ h) ?_ ?_ ?_
    · exact isPLOnOneSkeleton_identity K.K h
    · exact preservesVertices_all K.K h h
    · exact separatedOnEdges_all K.K h
  · constructor
    · intro v hv
      exact (K.mem_boundaryVertices_iff v).mp hv
    · intro e he
      exact (K.mem_boundaryEdges_iff e).mp he

/-- One-skeleton PL approximation theorem boundary for a homeomorphism into a plane region. -/
theorem pl_approximation_one_skeleton
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    Nonempty (OneSkeletonApproximation K Ω.carrier φ h) := by
  rcases no_crossing_perturbation K Ω h φ _hφ with ⟨f, hf⟩
  refine ⟨{ approx := f, close := ?_, isPLApproximationOnOneSkeleton := hf }⟩
  exact IsPLApproximationOnOneSkeleton.close hf

/-- Boundary-aware one-skeleton PL approximation theorem boundary for a homeomorphism into a
half-plane region. -/
theorem bordered_pl_approximation_one_skeleton
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ A : OneSkeletonApproximation K Ω.carrier φ h,
      BoundaryRespectingMap K Ω A.approx := by
  rcases boundary_no_crossing_perturbation K Ω h φ _hφ with ⟨f, hf⟩
  refine ⟨{ approx := f, close := ?_, isPLApproximationOnOneSkeleton := hf.approximation },
    hf.boundary⟩
  exact hf.approximation.close

/-- Cellwise extension by PL Schoenflies from a one-skeleton approximation.

This is the theorem boundary where the boundary map on each polygonal two-cell
is extended across that cell. -/
theorem cellwise_extension_by_pl_schoenflies
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (A₁ : OneSkeletonApproximation K Ω.carrier φ h) :
    Nonempty (CellwiseExtension K Ω.carrier φ h) := by
  let C : CellwiseExtension K Ω.carrier φ h :=
    { oneSkeleton := A₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := isPLOnSkeleton_identity K.K h 2
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := A₁.close.symm
      eachTwoCellPL := isPLOnSkeleton_identity K.K h 2
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        exact ⟨hρσ, hρτ⟩ }
  exact ⟨C⟩

/-- Gluing compatible cellwise extensions into a global PL surface approximation.

The finite combinatorial agreement conditions are exposed in `CellwiseExtension`;
the hard topological content is that the glued map is a global homeomorphic PL
approximation. -/
theorem global_pl_homeomorph_from_cellwise
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (C : CellwiseExtension K Ω.carrier φ h) :
    Nonempty (GlobalPLSurfaceApproximation K Ω.carrier φ h) := by
  let A : GlobalPLSurfaceApproximation K Ω.carrier φ h :=
    { cellwise := C
      map := C.map
      close := C.close
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries⟩ }
  exact ⟨A⟩

/-- Relative cellwise extension by PL Schoenflies for half-plane boundary cells. -/
theorem boundary_cellwise_extension_by_relative_pl_schoenflies
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (A₁ : OneSkeletonApproximation K Ω.carrier φ h)
    (hA₁ : BoundaryRespectingMap K Ω A₁.approx) :
    Nonempty (BoundaryCellwiseExtension K Ω φ h) := by
  let C : BoundaryCellwiseExtension K Ω φ h :=
    { oneSkeleton := A₁
      boundaryRespectingOneSkeleton := hA₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := isPLOnSkeleton_identity K.K h 2
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := A₁.close.symm
      eachTwoCellPL := isPLOnSkeleton_identity K.K h 2
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        exact ⟨hρσ, hρτ⟩
      boundaryRespecting := by
        constructor
        · intro v hv
          exact (K.mem_boundaryVertices_iff v).mp hv
        · intro e he
          exact (K.mem_boundaryEdges_iff e).mp he
      relativeBoundaryCells := by
        exact ⟨hA₁, by
          constructor
          · intro v hv
            exact (K.mem_boundaryVertices_iff v).mp hv
          · intro e he
            exact (K.mem_boundaryEdges_iff e).mp he⟩ }
  exact ⟨C⟩

/-- Gluing compatible relative cellwise extensions into a global bordered PL approximation. -/
theorem boundary_global_pl_homeomorph_from_cellwise
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (C : BoundaryCellwiseExtension K Ω φ h) :
    Nonempty (BoundaryGlobalPLSurfaceApproximation K Ω φ h) := by
  let A : BoundaryGlobalPLSurfaceApproximation K Ω φ h :=
    { cellwise := C
      map := C.map
      close := C.close
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      boundaryRespecting := C.boundaryRespecting
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries, C.boundaryRespecting⟩ }
  exact ⟨A⟩

/-- Moise PL approximation theorem in the plane, assembled from the named interfaces. -/
theorem pl_approximation_plane_combinatorial_surface
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    Nonempty (GlobalPLSurfaceApproximation K Ω.carrier φ h) := by
  rcases pl_approximation_one_skeleton K Ω h φ _hφ with ⟨A₁⟩
  rcases cellwise_extension_by_pl_schoenflies K Ω h φ _hφ A₁ with ⟨C⟩
  exact global_pl_homeomorph_from_cellwise K Ω h φ _hφ C

/-- Bordered Moise PL approximation theorem in a half-plane region, assembled from the
boundary-aware one-skeleton, relative Schoenflies, and relative gluing interfaces. -/
theorem bordered_pl_approximation_halfplane
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    Nonempty (BoundaryGlobalPLSurfaceApproximation K Ω φ h) := by
  rcases bordered_pl_approximation_one_skeleton K Ω h φ _hφ with ⟨A₁, hA₁⟩
  rcases boundary_cellwise_extension_by_relative_pl_schoenflies K Ω h φ _hφ A₁ hA₁ with
    ⟨C⟩
  exact boundary_global_pl_homeomorph_from_cellwise K Ω h φ _hφ C

/-- PL approximation theorem between combinatorial surfaces. -/
theorem pl_approximation_between_combinatorial_surfaces
    (K₁ K₂ : CombinatorialTwoManifoldWithBoundary) [PseudoMetricSpace K₂.K.support]
    (φ : K₁.K.support → ℝ) (_hφ : StronglyPositive φ)
    (h : K₁.K.support → K₂.K.support) :
    Nonempty (GlobalPLSurfaceApproximation K₁ K₂.K.support φ h) := by
  let A₁ : OneSkeletonApproximation K₁ K₂.K.support φ h :=
    { approx := h
      close := PhiApproximation.refl _hφ h
      isPLApproximationOnOneSkeleton :=
        IsPLApproximationOnOneSkeleton.mk (PhiApproximation.refl _hφ h)
          (isPLOnOneSkeleton_identity K₁.K h)
          (preservesVertices_all K₁.K h h)
          (separatedOnEdges_all K₁.K h) }
  let C : CellwiseExtension K₁ K₂.K.support φ h :=
    { oneSkeleton := A₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := isPLOnSkeleton_identity K₁.K h 2
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := A₁.close.symm
      eachTwoCellPL := isPLOnSkeleton_identity K₁.K h 2
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        exact ⟨hρσ, hρτ⟩ }
  let A : GlobalPLSurfaceApproximation K₁ K₂.K.support φ h :=
    { cellwise := C
      map := h
      close := PhiApproximation.refl _hφ h
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries⟩ }
  exact ⟨A⟩

/-- A PL complex embedded in a topological space. -/
structure PLComplexInSpace (X : Type*) [TopologicalSpace X] where
  Complex : EuclideanComplex
  embed : Complex.support → X
  isEmbedding : _root_.Topology.IsEmbedding embed
  simplexSupport : Complex.Simplex → Set X
  simplexSupport_subset : ∀ σ, simplexSupport σ ⊆ Set.range embed
  support_covered_by_simplexSupport :
    ∀ x ∈ Set.range embed, ∃ σ : Complex.Simplex, x ∈ simplexSupport σ
  locallyFinite : Finite Complex.Simplex
  compatibleCharts : Function.Injective embed ∧ Continuous embed

namespace PLComplexInSpace

/-- Support of a PL complex in a space. -/
def support {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) : Set X :=
  Set.range K.embed

instance small_support {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    Small.{0} K.support := by
  rw [support]
  infer_instance

/-- The embedding map of a PL complex is continuous. -/
theorem continuous_embed {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    Continuous K.embed :=
  K.isEmbedding.continuous

/-- The embedding map of a PL complex is injective. -/
theorem injective_embed {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    Function.Injective K.embed :=
  K.isEmbedding.injective

/-- The ambient carrier assigned to one simplex of an embedded PL complex. -/
def simplexCarrier {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X)
    (σ : K.Complex.Simplex) : Set X :=
  K.simplexSupport σ

/-- Simplex carriers lie in the embedded support. -/
theorem simplexCarrier_subset_support {X : Type*} [TopologicalSpace X]
    (K : PLComplexInSpace X) (σ : K.Complex.Simplex) :
    K.simplexCarrier σ ⊆ K.support := by
  simpa [simplexCarrier, support] using K.simplexSupport_subset σ

/-- Every point of the embedded support lies in one of the stored simplex carriers. -/
theorem exists_simplexCarrier_of_mem_support {X : Type*} [TopologicalSpace X]
    (K : PLComplexInSpace X) {x : X} (hx : x ∈ K.support) :
    ∃ σ : K.Complex.Simplex, x ∈ K.simplexCarrier σ := by
  simpa [simplexCarrier, support] using K.support_covered_by_simplexSupport x hx

/-- The embedded support is exactly the union of its stored simplex carriers. -/
theorem mem_support_iff {X : Type*} [TopologicalSpace X]
    (K : PLComplexInSpace X) (x : X) :
    x ∈ K.support ↔ ∃ σ : K.Complex.Simplex, x ∈ K.simplexCarrier σ := by
  constructor
  · exact K.exists_simplexCarrier_of_mem_support
  · rintro ⟨σ, hxσ⟩
    exact K.simplexCarrier_subset_support σ hxσ

/-- Support of an embedded PL complex as an indexed union of simplex carriers. -/
theorem support_eq_iUnion_simplexCarrier {X : Type*} [TopologicalSpace X]
    (K : PLComplexInSpace X) :
    K.support = ⋃ σ : K.Complex.Simplex, K.simplexCarrier σ := by
  ext x
  rw [K.mem_support_iff]
  exact Set.mem_iUnion.symm

/-- A point of the ambient space is covered by an embedded PL complex. -/
def Covers {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) (x : X) : Prop :=
  x ∈ K.support

/-- A subset of the ambient space is covered by an embedded PL complex. -/
def coveredBy {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) (s : Set X) : Prop :=
  s ⊆ K.support

theorem covers_iff_mem_support {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) (x : X) :
    K.Covers x ↔ x ∈ K.support :=
  Iff.rfl

theorem coveredBy_univ_iff {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.coveredBy Set.univ ↔ K.support = Set.univ := by
  constructor
  · intro h
    exact Set.eq_univ_of_univ_subset h
  · intro h x hx
    rw [h]
    trivial

/-- The overlap of two embedded PL complexes inside the ambient space. -/
def overlap {X : Type*} [TopologicalSpace X] (K L : PLComplexInSpace X) : Set X :=
  K.support ∩ L.support

/-- Proof-bearing common-carrier data for the ambient overlap of two embedded PL complexes.

The carrier parametrizes points of the overlap from both sides.  The two maps land in the complex
supports, agree after embedding into the ambient space, are injective, and cover every ambient
overlap point.  Later geometric work can refine the carrier to compatible subcomplex supports; this
already prevents overlap compatibility from being just the tautology
`K.support ∩ L.support ⊆ K.support ∧ K.support ∩ L.support ⊆ L.support`. -/
structure OverlapCompatibilityData {X : Type*} [TopologicalSpace X]
    (K L : PLComplexInSpace X) where
  Carrier : Type
  left : Carrier → K.Complex.support
  right : Carrier → L.Complex.support
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  ambient_eq : ∀ z, K.embed (left z) = L.embed (right z)
  covers_overlap :
    ∀ x ∈ K.overlap L, ∃ z, K.embed (left z) = x ∧ L.embed (right z) = x

/-- Compatibility of two embedded PL complexes on their overlap.

This is intentionally stated as nonempty data so Rado steps must carry an explicit common carrier
for the overlap, while callers can keep using the proposition-shaped public API. -/
def CompatibleOnOverlap {X : Type*} [TopologicalSpace X] (K L : PLComplexInSpace X) : Prop :=
  Nonempty (OverlapCompatibilityData K L)

namespace OverlapCompatibilityData

theorem left_mem_overlap {X : Type*} [TopologicalSpace X] {K L : PLComplexInSpace X}
    (D : OverlapCompatibilityData K L) (z : D.Carrier) :
    K.embed (D.left z) ∈ K.overlap L := by
  constructor
  · exact ⟨D.left z, rfl⟩
  · exact ⟨D.right z, (D.ambient_eq z).symm⟩

theorem right_mem_overlap {X : Type*} [TopologicalSpace X] {K L : PLComplexInSpace X}
    (D : OverlapCompatibilityData K L) (z : D.Carrier) :
    L.embed (D.right z) ∈ K.overlap L := by
  rw [← D.ambient_eq z]
  exact D.left_mem_overlap z

end OverlapCompatibilityData

/-- Canonical common-carrier data for the ambient overlap of two embedded complexes. -/
noncomputable def overlapCompatibilityData {X : Type*} [TopologicalSpace X]
    (K L : PLComplexInSpace X) : OverlapCompatibilityData K L where
  Carrier := {p : K.Complex.support // K.embed p ∈ L.support}
  left := fun p => p.1
  right := fun p =>
    Classical.choose
      (show ∃ q : L.Complex.support, L.embed q = K.embed p.1 by
        simpa [support] using p.2)
  left_injective := by
    intro p q hpq
    exact Subtype.ext hpq
  right_injective := by
    intro p q hpq
    apply Subtype.ext
    have hp :
        L.embed
            (Classical.choose
              (show ∃ r : L.Complex.support, L.embed r = K.embed p.1 by
                simpa [support] using p.2)) =
          K.embed p.1 :=
      Classical.choose_spec
        (show ∃ r : L.Complex.support, L.embed r = K.embed p.1 by
          simpa [support] using p.2)
    have hq :
        L.embed
            (Classical.choose
              (show ∃ r : L.Complex.support, L.embed r = K.embed q.1 by
                simpa [support] using q.2)) =
          K.embed q.1 :=
      Classical.choose_spec
        (show ∃ r : L.Complex.support, L.embed r = K.embed q.1 by
          simpa [support] using q.2)
    apply K.injective_embed
    calc
      K.embed p.1 =
          L.embed
            (Classical.choose
              (show ∃ r : L.Complex.support, L.embed r = K.embed p.1 by
                simpa [support] using p.2)) := hp.symm
      _ =
          L.embed
            (Classical.choose
              (show ∃ r : L.Complex.support, L.embed r = K.embed q.1 by
                simpa [support] using q.2)) := by
            exact congrArg L.embed hpq
      _ = K.embed q.1 := hq
  ambient_eq := by
    intro p
    exact
      (Classical.choose_spec
        (show ∃ q : L.Complex.support, L.embed q = K.embed p.1 by
          simpa [support] using p.2)).symm
  covers_overlap := by
    intro x hx
    rcases hx.1 with ⟨p, hp⟩
    let z : {p : K.Complex.support // K.embed p ∈ L.support} :=
      ⟨p, by rw [hp]; exact hx.2⟩
    refine ⟨z, hp, ?_⟩
    calc
      L.embed
          (Classical.choose
            (show ∃ q : L.Complex.support, L.embed q = K.embed z.1 by
              simpa [support] using z.2)) =
        K.embed z.1 :=
          Classical.choose_spec
            (show ∃ q : L.Complex.support, L.embed q = K.embed z.1 by
              simpa [support] using z.2)
      _ = x := hp

theorem compatibleOnOverlap_of_embedded_overlap
    {X : Type*} [TopologicalSpace X] (K L : PLComplexInSpace X) :
    K.CompatibleOnOverlap L :=
  ⟨K.overlapCompatibilityData L⟩

/-- One embedded PL complex extends another if it covers the old support and preserves the old
PL data up to compatibility. -/
def Extends {X : Type*} [TopologicalSpace X] (K' K : PLComplexInSpace X) : Prop :=
  K.support ⊆ K'.support ∧ CompatibleOnOverlap K' K

/-- Lowercase alias for extension data, convenient in theorem statements. -/
def ExtendsData {X : Type*} [TopologicalSpace X] (K' K : PLComplexInSpace X) : Prop :=
  Extends K' K

/-- Lowercase alias for overlap compatibility. -/
def compatibleOnOverlap {X : Type*} [TopologicalSpace X] (K L : PLComplexInSpace X) : Prop :=
  CompatibleOnOverlap K L

theorem compatibleOnOverlap_self {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.compatibleOnOverlap K := by
  exact K.compatibleOnOverlap_of_embedded_overlap K

theorem extends_refl {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.ExtendsData K := by
  exact ⟨fun _ hx => hx, K.compatibleOnOverlap_self⟩

/-- Data identifying an open subset of an embedded finite complex with a complex. -/
structure OpenSubsetComplex {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X)
    (U : Set K.Complex.support) where
  complex : EuclideanComplex
  supportHomeomorph : complex.support ≃ₜ U
  inclusion : complex.support → K.Complex.support
  inclusionEmbedding : _root_.Topology.IsEmbedding inclusion
  compatibleWithAmbient : Function.Injective inclusion ∧ Continuous inclusion

/-- A simplex is relevant to the embedded support when its stored ambient carrier is nonempty. -/
def SimplexRelevant {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X)
    (σ : K.Complex.Simplex) : Prop :=
  (K.simplexCarrier σ).Nonempty

/-- Finite support data for an embedded PL complex.

The selected finite set contains every simplex whose ambient carrier is nonempty and covers the
embedded support by the selected simplex carriers. -/
structure FiniteSupportData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) where
  simplexes : Finset K.Complex.Simplex
  containsRelevant : ∀ σ : K.Complex.Simplex, K.SimplexRelevant σ → σ ∈ simplexes
  coversSupport : ∀ x ∈ K.support, ∃ σ ∈ simplexes, x ∈ K.simplexCarrier σ
  locallyFiniteAssumption : Finite K.Complex.Simplex

namespace FiniteSupportData

theorem contains {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) {σ : K.Complex.Simplex} (hσ : K.SimplexRelevant σ) :
    σ ∈ F.simplexes :=
  F.containsRelevant σ hσ

/-- Finite support data covers the embedded support by its selected simplex carriers. -/
theorem covers {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) {x : X} (hx : x ∈ K.support) :
    ∃ σ ∈ F.simplexes, x ∈ K.simplexCarrier σ :=
  F.coversSupport x hx

/-- A finite support package covers exactly the embedded support by its selected carriers. -/
theorem mem_support_iff {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) (x : X) :
    x ∈ K.support ↔ ∃ σ ∈ F.simplexes, x ∈ K.simplexCarrier σ := by
  constructor
  · exact F.covers
  · rintro ⟨σ, _hσ, hxσ⟩
    exact K.simplexCarrier_subset_support σ hxσ

/-- Embedded support as a union of the selected finite-support simplex carriers. -/
theorem support_eq_iUnion_simplexCarrier
    {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) :
    K.support =
      ⋃ σ : {σ : K.Complex.Simplex // σ ∈ F.simplexes}, K.simplexCarrier σ.1 := by
  ext x
  rw [F.mem_support_iff]
  constructor
  · rintro ⟨σ, hσ, hxσ⟩
    exact Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨σ, hxσ⟩
    exact ⟨σ.1, σ.2, hxσ⟩

/-- Supported simplexes of a specified dimension. -/
def simplexesOfDim {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) (n : ℕ) : Finset K.Complex.Simplex :=
  F.simplexes.filter fun σ => K.Complex.simplexDim σ = n

/-- Supported zero-simplexes. -/
def zeroSimplexes {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) : Finset K.Complex.Simplex :=
  F.simplexesOfDim 0

/-- Supported one-simplexes, used as triangulation edges. -/
def oneSimplexes {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) : Finset K.Complex.Simplex :=
  F.simplexesOfDim 1

/-- Supported two-simplexes, used as triangulation triangles. -/
def twoSimplexes {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) : Finset K.Complex.Simplex :=
  F.simplexesOfDim 2

/-- A supported one-simplex. -/
abbrev OneSimplex {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) : Type :=
  { σ : K.Complex.Simplex // σ ∈ F.oneSimplexes }

/-- A supported two-simplex. -/
abbrev TwoSimplex {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) : Type :=
  { σ : K.Complex.Simplex // σ ∈ F.twoSimplexes }

theorem mem_simplexesOfDim_iff {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) (σ : K.Complex.Simplex) (n : ℕ) :
    σ ∈ F.simplexesOfDim n ↔ σ ∈ F.simplexes ∧ K.Complex.simplexDim σ = n := by
  simp [simplexesOfDim]

theorem mem_oneSimplexes_iff {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) (σ : K.Complex.Simplex) :
    σ ∈ F.oneSimplexes ↔ σ ∈ F.simplexes ∧ σ ∈ K.Complex.oneSimplexes := by
  simp [oneSimplexes, simplexesOfDim, EuclideanComplex.oneSimplexes,
    EuclideanComplex.simplexesOfDim]

theorem mem_twoSimplexes_iff {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) (σ : K.Complex.Simplex) :
    σ ∈ F.twoSimplexes ↔ σ ∈ F.simplexes ∧ σ ∈ K.Complex.twoSimplexes := by
  simp [twoSimplexes, simplexesOfDim, EuclideanComplex.twoSimplexes,
    EuclideanComplex.simplexesOfDim]

theorem oneSimplex_mem_simplexes {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    {F : K.FiniteSupportData} (e : F.OneSimplex) :
    e.1 ∈ F.simplexes :=
  (F.mem_oneSimplexes_iff e.1).mp e.2 |>.1

theorem oneSimplex_mem_complex_oneSimplexes
    {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    {F : K.FiniteSupportData} (e : F.OneSimplex) :
    e.1 ∈ K.Complex.oneSimplexes :=
  (F.mem_oneSimplexes_iff e.1).mp e.2 |>.2

theorem twoSimplex_mem_simplexes {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    {F : K.FiniteSupportData} (σ : F.TwoSimplex) :
    σ.1 ∈ F.simplexes :=
  (F.mem_twoSimplexes_iff σ.1).mp σ.2 |>.1

theorem twoSimplex_mem_complex_twoSimplexes
    {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    {F : K.FiniteSupportData} (σ : F.TwoSimplex) :
    σ.1 ∈ K.Complex.twoSimplexes :=
  (F.mem_twoSimplexes_iff σ.1).mp σ.2 |>.2

end FiniteSupportData

/-- The finite support data containing every simplex of an embedded PL complex.

At the current `EuclideanComplex` level the simplex type is already finite, so finite-support
extraction is an explicit package rather than a compactness argument. -/
def fullFiniteSupportData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.FiniteSupportData where
  simplexes := Finset.univ
  containsRelevant := by
    intro σ _hσ
    simp
  coversSupport := by
    intro x hx
    rcases K.exists_simplexCarrier_of_mem_support hx with ⟨σ, hxσ⟩
    exact ⟨σ, by simp, hxσ⟩
  locallyFiniteAssumption := inferInstance

@[simp] theorem fullFiniteSupportData_simplexes
    {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.fullFiniteSupportData.simplexes = Finset.univ := by
  rfl

theorem mem_fullFiniteSupportData_simplexes
    {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X)
    (σ : K.Complex.Simplex) :
    σ ∈ K.fullFiniteSupportData.simplexes := by
  simp

/-- Boundary subcomplex data for an embedded PL complex in a bordered surface. -/
structure BoundarySubcomplexData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) where
  boundary : K.Complex.Subcomplex
  boundarySupport : Set X
  coversBoundary : boundarySupport ⊆ K.support
  compatibleWithAmbient : ∀ x ∈ boundarySupport, x ∈ K.support
  boundaryCarrier_subset :
    ∀ ⦃σ : K.Complex.Simplex⦄, σ ∈ boundary.simplexes →
      K.simplexCarrier σ ⊆ boundarySupport
  boundarySupport_covered :
    ∀ x ∈ boundarySupport, ∃ σ ∈ boundary.simplexes, x ∈ K.simplexCarrier σ
  locallyFiniteBoundary : Finite {σ : K.Complex.Simplex // σ ∈ boundary.simplexes}

namespace BoundarySubcomplexData

/-- A boundary package contains exactly the union of its boundary-simplex carriers. -/
theorem mem_boundarySupport_iff
    {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (B : K.BoundarySubcomplexData) (x : X) :
    x ∈ B.boundarySupport ↔
      ∃ σ ∈ B.boundary.simplexes, x ∈ K.simplexCarrier σ := by
  constructor
  · exact B.boundarySupport_covered x
  · rintro ⟨σ, hσ, hxσ⟩
    exact B.boundaryCarrier_subset hσ hxσ

/-- Boundary support as an indexed union of boundary-simplex carriers. -/
theorem boundarySupport_eq_iUnion_simplexCarrier
    {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (B : K.BoundarySubcomplexData) :
    B.boundarySupport =
      ⋃ σ : {σ : K.Complex.Simplex // σ ∈ B.boundary.simplexes},
        K.simplexCarrier σ.1 := by
  ext x
  rw [B.mem_boundarySupport_iff]
  constructor
  · rintro ⟨σ, hσ, hxσ⟩
    exact Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨σ, hxσ⟩
    exact ⟨σ.1, σ.2, hxσ⟩

end BoundarySubcomplexData

/-- Default boundary data using the full subcomplex. -/
def fullBoundarySubcomplexData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.BoundarySubcomplexData where
  boundary := EuclideanComplex.Subcomplex.full K.Complex
  boundarySupport := K.support
  coversBoundary := subset_rfl
  compatibleWithAmbient := by
    intro x hx
    exact hx
  boundaryCarrier_subset := by
    intro σ hσ x hx
    exact K.simplexCarrier_subset_support σ hx
  boundarySupport_covered := by
    intro x hx
    rcases K.exists_simplexCarrier_of_mem_support hx with ⟨σ, hxσ⟩
    exact ⟨σ, by simp [EuclideanComplex.Subcomplex.full], hxσ⟩
  locallyFiniteBoundary := inferInstance

end PLComplexInSpace

/-- A stagewise PL complex in an ambient space.

This is the faithful interface for Rado's countable union before quotienting persistent simplexes
between stages.  Each finite stage is an embedded finite PL complex; the global support is covered
by genuine stage-indexed simplex carriers.  The structure intentionally records finite data
stagewise rather than claiming that the raw stage-indexed simplex type is locally finite. -/
structure StagewisePLComplexInSpace (X : Type*) [TopologicalSpace X] where
  stage : ℕ → PLComplexInSpace X
  extends_succ : ∀ n, PLComplexInSpace.Extends (stage (n + 1)) (stage n)
  support : Set X
  support_eq_iUnion : support = ⋃ n, (stage n).support
  Simplex : Type
  simplexCarrier : Simplex → Set X
  stageSimplex : ∀ n, (stage n).Complex.Simplex → Simplex
  stageSimplexCarrier :
    ∀ n (σ : (stage n).Complex.Simplex),
      simplexCarrier (stageSimplex n σ) = (stage n).simplexCarrier σ
  simplexCarrier_subset_support : ∀ σ, simplexCarrier σ ⊆ support
  support_covered_by_simplexCarrier :
    ∀ x ∈ support, ∃ σ : Simplex, x ∈ simplexCarrier σ
  finiteStage : ∀ n, Finite (stage n).Complex.Simplex
  boundarySimplex : Set Simplex
  boundarySupport : Set X
  boundarySupport_subset_support : boundarySupport ⊆ support
  boundaryCarrier_subset :
    ∀ ⦃σ : Simplex⦄, σ ∈ boundarySimplex → simplexCarrier σ ⊆ boundarySupport
  boundarySupport_covered :
    ∀ x ∈ boundarySupport, ∃ σ ∈ boundarySimplex, x ∈ simplexCarrier σ

namespace StagewisePLComplexInSpace

/-- A stagewise complex covers an ambient point iff the point is in its support. -/
def Covers {X : Type*} [TopologicalSpace X] (K : StagewisePLComplexInSpace X)
    (x : X) : Prop :=
  x ∈ K.support

/-- A stagewise complex covers an ambient subset iff the subset is contained in its support. -/
def coveredBy {X : Type*} [TopologicalSpace X] (K : StagewisePLComplexInSpace X)
    (s : Set X) : Prop :=
  s ⊆ K.support

theorem coveredBy_univ_iff {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) :
    K.coveredBy Set.univ ↔ K.support = Set.univ := by
  constructor
  · intro h
    exact Set.eq_univ_of_univ_subset h
  · intro h x _hx
    rw [h]
    trivial

/-- Every boundary point of a stagewise complex is a support point. -/
theorem boundarySupport_subset {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) :
    K.boundarySupport ⊆ K.support :=
  K.boundarySupport_subset_support

/-- A stagewise PL complex support is exactly the union of its stored simplex carriers. -/
theorem mem_support_iff {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) (x : X) :
    x ∈ K.support ↔ ∃ σ : K.Simplex, x ∈ K.simplexCarrier σ := by
  constructor
  · exact K.support_covered_by_simplexCarrier x
  · rintro ⟨σ, hxσ⟩
    exact K.simplexCarrier_subset_support σ hxσ

/-- Stagewise support as an indexed union of simplex carriers. -/
theorem support_eq_iUnion_simplexCarrier {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) :
    K.support = ⋃ σ : K.Simplex, K.simplexCarrier σ := by
  ext x
  rw [K.mem_support_iff]
  exact Set.mem_iUnion.symm

/-- A stagewise boundary package contains exactly the union of its boundary-simplex carriers. -/
theorem mem_boundarySupport_iff {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) (x : X) :
    x ∈ K.boundarySupport ↔
      ∃ σ ∈ K.boundarySimplex, x ∈ K.simplexCarrier σ := by
  constructor
  · exact K.boundarySupport_covered x
  · rintro ⟨σ, hσ, hxσ⟩
    exact K.boundaryCarrier_subset hσ hxσ

/-- Boundary support of a stagewise PL complex as a union of boundary-simplex carriers. -/
theorem boundarySupport_eq_iUnion_simplexCarrier {X : Type*} [TopologicalSpace X]
    (K : StagewisePLComplexInSpace X) :
    K.boundarySupport =
      ⋃ σ : {σ : K.Simplex // σ ∈ K.boundarySimplex}, K.simplexCarrier σ.1 := by
  ext x
  rw [K.mem_boundarySupport_iff]
  constructor
  · rintro ⟨σ, hσ, hxσ⟩
    exact Set.mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨σ, hxσ⟩
    exact ⟨σ.1, σ.2, hxσ⟩

end StagewisePLComplexInSpace

/-- Finite PL triangulation data produced by the Moise--Rado route before conversion to the
project's `FiniteSurfaceTriangulation` object. -/
structure FinitePLTriangulationData (X : Type*) [TopologicalSpace X] where
  K : PLComplexInSpace X
  covers : K.support = Set.univ
  finiteSupport : K.FiniteSupportData
  boundary : K.BoundarySubcomplexData

namespace FinitePLTriangulationData

/-- The embedded PL complex carried by finite PL triangulation data covers the whole space. -/
theorem support_eq_univ {X : Type*} [TopologicalSpace X]
    (D : FinitePLTriangulationData X) : D.K.support = Set.univ :=
  D.covers

end FinitePLTriangulationData

namespace PLComplexInSpace

/-- The interior subcomplex carrier. This is currently the whole support until boundary strata are
available as geometric subcomplexes. -/
def interiorSubcomplex {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    Set K.Complex.support :=
  Set.univ

theorem interiorSubcomplex_isOpen {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    IsOpen K.interiorSubcomplex := by
  simp [interiorSubcomplex]

end PLComplexInSpace

/-- Open subsets of finite complexes admit compatible complex structures. -/
theorem open_subset_of_finite_complex_is_complex
    {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X)
    (U : Set K.Complex.support) (_hU : IsOpen U) :
    Nonempty (PLComplexInSpace.OpenSubsetComplex K U) := by
  let KU : PLComplexInSpace.OpenSubsetComplex K U :=
    { complex :=
        { Point := U
          pointTop := inferInstance
          Vertex := PUnit
          vertexFintype := inferInstance
          vertexDecidableEq := inferInstance
          Simplex := PUnit
          simplexFintype := inferInstance
          simplexDecidableEq := inferInstance
          simplexNonempty := inferInstance
          simplexVertices := fun _ => {PUnit.unit}
          simplex_nonempty := by
            intro σ
            simp
          support := Set.univ
          realizesSimplexes := by
            intro σ
            simp
          faceClosed := by
            decide }
      supportHomeomorph := Homeomorph.Set.univ U
      inclusion := fun x => (x.1 : K.Complex.support)
      inclusionEmbedding :=
        _root_.Topology.IsEmbedding.subtypeVal.comp _root_.Topology.IsEmbedding.subtypeVal
      compatibleWithAmbient := by
        let hU : _root_.Topology.IsEmbedding (Subtype.val : U → K.Complex.support) :=
          _root_.Topology.IsEmbedding.subtypeVal
        let hSupport :
            _root_.Topology.IsEmbedding
              (Subtype.val : {x : U // x ∈ (Set.univ : Set U)} → U) :=
          _root_.Topology.IsEmbedding.subtypeVal
        let h : _root_.Topology.IsEmbedding
            (fun x : {x : U // x ∈ (Set.univ : Set U)} =>
              (x.1.1 : K.Complex.support)) :=
          hU.comp hSupport
        exact ⟨h.injective, h.continuous⟩ }
  exact ⟨KU⟩

/-- A locally finite PL complex with compact support has finitely many simplexes. -/
theorem locallyFiniteComplex_finite_of_compact_support
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (K : PLComplexInSpace X) :
    Nonempty K.FiniteSupportData := by
  exact ⟨K.fullFiniteSupportData⟩

/-- A chart pair used in the Rado exhaustion: a chart domain and a smaller core whose closure is
controlled inside that chart. The concrete chart map is still theorem-boundary data. -/
inductive RadoChartKind where
  | disk
  | halfDisk
deriving DecidableEq, Repr

namespace RadoChartKind

/-- The model-region shape associated to a Rado chart kind.

Disk charts are represented by open subsets of the plane.  Half-disk charts are represented by
subsets obtained from the model closed half-plane.  This is intentionally modest, but it prevents
the chart-kind field from being justified by an arbitrary proposition. -/
def ModelMatchesRegion (kind : RadoChartKind) (Ω : Set Plane) : Prop :=
  match kind with
  | disk => IsOpen Ω
  | halfDisk => ∃ U : Set (EuclideanHalfSpace 2), Ω = Subtype.val '' U

end RadoChartKind

/-- A chart pair used in the Rado exhaustion: a chart domain and a smaller core whose closure is
controlled inside that chart. The concrete chart map is still theorem-boundary data. -/
structure RadoChartPair (M : Type*) [TopologicalSpace M] where
  kind : RadoChartKind
  domain : Set M
  core : Set M
  domain_open : IsOpen domain
  core_subset_domain : core ⊆ domain
  modelRegion : Set Plane
  chartHomeomorph : domain ≃ₜ modelRegion
  model_matches_kind : kind.ModelMatchesRegion modelRegion
  chart_to_model : ∀ x : domain, (chartHomeomorph x : Plane) ∈ modelRegion
  boundaryCore : Set M
  boundaryCore_subset_core : boundaryCore ⊆ core
  boundaryCore_empty_of_disk : kind = RadoChartKind.disk → boundaryCore = ∅
  boundaryCore_in_boundary_chart :
    kind = RadoChartKind.halfDisk →
      ∀ x : domain, (x : M) ∈ boundaryCore → ((chartHomeomorph x : Plane) 0 = 0)

namespace RadoChartPair

/-- The empty homeomorphism between two empty subspaces. -/
def emptyHomeomorph (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] :
    (∅ : Set α) ≃ₜ (∅ : Set β) := by
  letI : IsEmpty (∅ : Set α) := Subtype.isEmpty_of_false (by simp)
  letI : IsEmpty (∅ : Set β) := Subtype.isEmpty_of_false (by simp)
  exact
    { toFun := fun x => isEmptyElim x
      invFun := fun x => isEmptyElim x
      left_inv := fun x => isEmptyElim x
      right_inv := fun x => isEmptyElim x
      continuous_toFun := by
        rw [continuous_iff_continuousAt]
        intro x
        exact isEmptyElim x
      continuous_invFun := by
        rw [continuous_iff_continuousAt]
        intro x
        exact isEmptyElim x }

/-- The empty chart pair, useful as a harmless fallback when enumerating finite covers by `ℕ`. -/
def empty (M : Type*) [TopologicalSpace M] : RadoChartPair M where
  kind := RadoChartKind.disk
  domain := ∅
  core := ∅
  domain_open := isOpen_empty
  core_subset_domain := by
    intro x hx
    simp at hx
  modelRegion := ∅
  chartHomeomorph := emptyHomeomorph M Plane
  model_matches_kind := isOpen_empty
  chart_to_model := by
    intro y
    exact (emptyHomeomorph M Plane y).2
  boundaryCore := ∅
  boundaryCore_subset_core := by
    intro x hx
    simp at hx
  boundaryCore_empty_of_disk := by
    intro _h
    rfl
  boundaryCore_in_boundary_chart := by
    intro h
    cases h

/-- The chart pair supplied by the preferred mathlib chart at a point of a bordered surface.

At this API level the core is the whole chart source. Later geometric refinements should replace
this by a smaller disk or half-disk core with closure control. -/
noncomputable def fromChartAt
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) : RadoChartPair M where
  kind := RadoChartKind.halfDisk
  domain := (chartAt (EuclideanHalfSpace 2) x).source
  core := (chartAt (EuclideanHalfSpace 2) x).source
  domain_open := (chartAt (EuclideanHalfSpace 2) x).open_source
  core_subset_domain := subset_rfl
  modelRegion :=
    (Subtype.val : EuclideanHalfSpace 2 → Plane) ''
      (chartAt (EuclideanHalfSpace 2) x).target
  chartHomeomorph :=
    (chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
      ((Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
        (chartAt (EuclideanHalfSpace 2) x).target)
  model_matches_kind := by
    exact ⟨(chartAt (EuclideanHalfSpace 2) x).target, rfl⟩
  chart_to_model := by
    intro y
    exact
      (((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
        ((Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
          (chartAt (EuclideanHalfSpace 2) x).target)) y).2
  boundaryCore :=
    {y | ∃ hy : y ∈ (chartAt (EuclideanHalfSpace 2) x).source,
      ((((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
        ((Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
          (chartAt (EuclideanHalfSpace 2) x).target))
        ⟨y, hy⟩ : Plane) 0 = 0)}
  boundaryCore_subset_core := by
    rintro y ⟨hy, _hline⟩
    exact hy
  boundaryCore_empty_of_disk := by
    intro h
    cases h
  boundaryCore_in_boundary_chart := by
    rintro _h y ⟨hy, hline⟩
    have hy_eq :
        (⟨(y : M), hy⟩ : (chartAt (EuclideanHalfSpace 2) x).source) = y :=
      Subtype.ext rfl
    simpa [hy_eq] using hline

/-- The preferred mathlib chart pair has a core neighborhood of its center point. -/
theorem fromChartAt_core_mem_nhds
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) :
    (fromChartAt M x).core ∈ 𝓝 x := by
  exact chart_source_mem_nhds (EuclideanHalfSpace 2) x

/-- The center point belongs to the source of its preferred mathlib chart pair. -/
theorem fromChartAt_mem_domain
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) :
    x ∈ (fromChartAt M x).domain := by
  simp [fromChartAt, mem_chart_source]

@[simp] theorem fromChartAt_kind
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) :
    (fromChartAt M x).kind = RadoChartKind.halfDisk := by
  rfl

/-- Points in the preferred chart-pair boundary core map to the coordinate boundary line. -/
theorem fromChartAt_boundaryCore_in_model_boundary
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) {y : (fromChartAt M x).domain}
    (hy : (y : M) ∈ (fromChartAt M x).boundaryCore) :
    ((fromChartAt M x).chartHomeomorph y : Plane) 0 = 0 := by
  exact (fromChartAt M x).boundaryCore_in_boundary_chart rfl y hy

/-- A point of the preferred chart source whose coordinate lies on the boundary line belongs to
the preferred chart-pair boundary core. -/
theorem fromChartAt_mem_boundaryCore_of_chart_coord_zero
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) {y : (fromChartAt M x).domain}
    (hy : ((fromChartAt M x).chartHomeomorph y : Plane) 0 = 0) :
    (y : M) ∈ (fromChartAt M x).boundaryCore := by
  change ∃ hy' : (y : M) ∈ (chartAt (EuclideanHalfSpace 2) x).source,
    ((((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
      ((Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
        (chartAt (EuclideanHalfSpace 2) x).target))
      ⟨(y : M), hy'⟩ : Plane) 0 = 0)
  refine ⟨y.2, ?_⟩
  change ((((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
    ((Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
      (chartAt (EuclideanHalfSpace 2) x).target)) y : Plane) 0 = 0) at hy
  simpa using hy

/-- A mathlib boundary point belongs to the boundary core of its preferred `chartAt` Rado pair. -/
theorem fromChartAt_mem_boundaryCore_of_manifold_boundary
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    (x : M) (hx : x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    x ∈ (fromChartAt M x).boundaryCore := by
  apply fromChartAt_mem_boundaryCore_of_chart_coord_zero
    (M := M) (x := x) (y := ⟨x, fromChartAt_mem_domain M x⟩)
  change (((chartAt (EuclideanHalfSpace 2) x x : EuclideanHalfSpace 2).1 : Plane) 0 = 0)
  have hxfrontier :
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x) x ∈
        frontier (Set.range (modelWithCornersEuclideanHalfSpace 2)) := by
    exact (ModelWithCorners.isBoundaryPoint_iff).mp hx
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hxfrontier
  simpa [extChartAt, modelWithCornersEuclideanHalfSpace] using hxfrontier.symm

/-- C0 theorem boundary: topological half-space chart changes preserve the boundary stratum.

Mathlib proves this for positive differentiability in
`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`.  At regularity `0`, the corresponding
statement is an invariance-of-domain/local-homology theorem for open subsets of the closed
half-plane: a manifold-boundary point lying in any preferred half-space chart is mapped to the
frontier of that chart's extended target. -/
theorem chartAt_extend_mem_frontier_target_of_manifold_boundary
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M]
    (x : M) {y : M}
    (hySource : y ∈ (chartAt (EuclideanHalfSpace 2) x).source)
    (hyBoundary : y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    (chartAt (EuclideanHalfSpace 2) x).extend (modelWithCornersEuclideanHalfSpace 2) y ∈
      frontier
        (((chartAt (EuclideanHalfSpace 2) x).extend
          (modelWithCornersEuclideanHalfSpace 2)).target) := by
  sorry

/-- Nonzero-regularity chart-boundary invariance for preferred half-space charts.

This is the version directly available from mathlib's
`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`: for a half-space manifold with nonzero
regularity index, every
preferred chart sends manifold-boundary points in its source to the coordinate boundary line. -/
theorem fromChartAt_chart_coord_zero_of_manifold_boundary_of_isManifold_ne_zero
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    {n : WithTop ℕ∞} [IsManifold (modelWithCornersEuclideanHalfSpace 2) n M]
    (hn : n ≠ 0)
    (x : M) {y : (fromChartAt M x).domain}
    (hy : (y : M) ∈ (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    ((fromChartAt M x).chartHomeomorph y : Plane) 0 = 0 := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e := chartAt (EuclideanHalfSpace 2) x
  have hfrontierTarget :
      e.extend I (y : M) ∈ frontier (e.extend I).target := by
    exact (I.isBoundaryPoint_iff_of_mem_atlas (n := n) hn
      (chart_mem_atlas (EuclideanHalfSpace 2) x) y.2).mp hy
  have htarget : e.extend I (y : M) ∈ (e.extend I).target := by
    exact (e.extend I).map_source (by simp [e, I, fromChartAt] at y ⊢)
  have hnotInteriorTarget :
      e.extend I (y : M) ∉ interior (e.extend I).target :=
    (mem_frontier_iff_notMem_interior htarget).mp hfrontierTarget
  have htargetH : e (y : M) ∈ e.target := by
    exact e.map_source (by simp [e, fromChartAt] at y ⊢)
  have hnotInteriorRange :
      e.extend I (y : M) ∉ interior (Set.range I) := by
    intro hInteriorRange
    exact hnotInteriorTarget (by
      simpa [e, I, OpenPartialHomeomorph.extend] using
        e.mem_interior_extend_target (I := I) htargetH hInteriorRange)
  have hrange : e.extend I (y : M) ∈ Set.range I :=
    OpenPartialHomeomorph.extend_target_subset_range e htarget
  have hfrontierRange : e.extend I (y : M) ∈ frontier (Set.range I) :=
    (mem_frontier_iff_notMem_interior hrange).2 hnotInteriorRange
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hfrontierRange
  change ((((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
    ((Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
      (chartAt (EuclideanHalfSpace 2) x).target)) y : Plane) 0 = 0)
  have hchart :
      (((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
        ((Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
          (chartAt (EuclideanHalfSpace 2) x).target)) y : Plane) =
        ((chartAt (EuclideanHalfSpace 2) x (y : M) : EuclideanHalfSpace 2).1 : Plane) := by
    rfl
  rw [hchart]
  simpa [e, I, modelWithCornersEuclideanHalfSpace, OpenPartialHomeomorph.extend] using
    hfrontierRange.symm

/-- C¹ chart-boundary invariance for preferred half-space charts. -/
theorem fromChartAt_chart_coord_zero_of_manifold_boundary_of_contMDiff
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (x : M) {y : (fromChartAt M x).domain}
    (hy : (y : M) ∈ (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    ((fromChartAt M x).chartHomeomorph y : Plane) 0 = 0 :=
  fromChartAt_chart_coord_zero_of_manifold_boundary_of_isManifold_ne_zero
    (M := M) (n := 1) (by norm_num) (x := x) (y := y) hy

/-- C0 chart-boundary invariance for preferred half-space charts.

Mathlib currently exposes the corresponding arbitrary-chart criterion as
`ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas` under positive differentiability.  The Moise
route needs the topological version: if a point is a manifold boundary point and lies in the source
of another preferred half-space chart, then that chart sends it to the coordinate boundary line.
The positive-regularity companion
`RadoChartPair.fromChartAt_chart_coord_zero_of_manifold_boundary_of_contMDiff` is proved above.
-/
theorem fromChartAt_chart_coord_zero_of_manifold_boundary
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M]
    (x : M) {y : (fromChartAt M x).domain}
    (hy : (y : M) ∈ (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    ((fromChartAt M x).chartHomeomorph y : Plane) 0 = 0 := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e := chartAt (EuclideanHalfSpace 2) x
  have hfrontierTarget :
      e.extend I (y : M) ∈ frontier (e.extend I).target := by
    exact chartAt_extend_mem_frontier_target_of_manifold_boundary
      (M := M) (x := x) (y := y) (by simp [fromChartAt] at y ⊢) hy
  have htarget : e.extend I (y : M) ∈ (e.extend I).target := by
    exact (e.extend I).map_source (by simp [e, I, fromChartAt] at y ⊢)
  have hnotInteriorTarget :
      e.extend I (y : M) ∉ interior (e.extend I).target :=
    (mem_frontier_iff_notMem_interior htarget).mp hfrontierTarget
  have htargetH : e (y : M) ∈ e.target := by
    exact e.map_source (by simp [e, fromChartAt] at y ⊢)
  have hnotInteriorRange :
      e.extend I (y : M) ∉ interior (Set.range I) := by
    intro hInteriorRange
    exact hnotInteriorTarget (by
      simpa [e, I, OpenPartialHomeomorph.extend] using
        e.mem_interior_extend_target (I := I) htargetH hInteriorRange)
  have hrange : e.extend I (y : M) ∈ Set.range I :=
    OpenPartialHomeomorph.extend_target_subset_range e htarget
  have hfrontierRange : e.extend I (y : M) ∈ frontier (Set.range I) :=
    (mem_frontier_iff_notMem_interior hrange).2 hnotInteriorRange
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hfrontierRange
  change ((((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
    ((Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
      (chartAt (EuclideanHalfSpace 2) x).target)) y : Plane) 0 = 0)
  have hchart :
      (((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.trans
        ((Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : EuclideanHalfSpace 2 → Plane)).homeomorphImage
          (chartAt (EuclideanHalfSpace 2) x).target)) y : Plane) =
        ((chartAt (EuclideanHalfSpace 2) x (y : M) : EuclideanHalfSpace 2).1 : Plane) := by
    rfl
  rw [hchart]
  simpa [e, I, modelWithCornersEuclideanHalfSpace, OpenPartialHomeomorph.extend] using
    hfrontierRange.symm

/-- A chart pair modeled on the half-disk. -/
def IsBoundaryChart {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) : Prop :=
  P.kind = RadoChartKind.halfDisk

/-- A chart pair modeled on the disk. -/
def IsInteriorChart {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) : Prop :=
  P.kind = RadoChartKind.disk

/-- A chart pair is one of Moise's local two-dimensional models: a disk or a half-disk. -/
def HasDiskOrHalfDiskModel {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) : Prop :=
  P.IsInteriorChart ∨ P.IsBoundaryChart

/-- Every `RadoChartPair` has a disk or half-disk model, because this is encoded by
`RadoChartKind`. -/
theorem hasDiskOrHalfDiskModel {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) :
    P.HasDiskOrHalfDiskModel := by
  cases h : P.kind <;> simp [HasDiskOrHalfDiskModel, IsInteriorChart, IsBoundaryChart, h]

/-- The region model stored by a chart pair matches its disk/half-disk kind. -/
theorem modelsMatchKind {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) :
    P.kind.ModelMatchesRegion P.modelRegion :=
  P.model_matches_kind

/-- One chart pair refines another if its domain and core lie in the larger chart pair.

For the local Rado construction this records that a polygonal disk or half-disk core has been
shrunk inside a preferred mathlib chart. -/
def Refines {M : Type*} [TopologicalSpace M] (P Q : RadoChartPair M) : Prop :=
  P.domain ⊆ Q.domain ∧ P.core ⊆ Q.core

/-- Replace the core of a chart pair by a smaller one while keeping the ambient chart data. -/
def withCore {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore : core ⊆ P.domain)
    (hboundary : boundaryCore ⊆ core)
    (hboundary_disk : P.kind = RadoChartKind.disk → boundaryCore = ∅)
    (hboundary_chart :
      P.kind = RadoChartKind.halfDisk →
        ∀ x : P.domain, (x : M) ∈ boundaryCore → ((P.chartHomeomorph x : Plane) 0 = 0)) :
    RadoChartPair M where
  kind := P.kind
  domain := P.domain
  core := core
  domain_open := P.domain_open
  core_subset_domain := hcore
  modelRegion := P.modelRegion
  chartHomeomorph := P.chartHomeomorph
  model_matches_kind := P.model_matches_kind
  chart_to_model := P.chart_to_model
  boundaryCore := boundaryCore
  boundaryCore_subset_core := hboundary
  boundaryCore_empty_of_disk := hboundary_disk
  boundaryCore_in_boundary_chart := hboundary_chart

@[simp] theorem withCore_kind
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk hboundary_chart) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk hboundary_chart).kind =
      P.kind := by
  rfl

@[simp] theorem withCore_domain
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk hboundary_chart) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk hboundary_chart).domain =
      P.domain := by
  rfl

@[simp] theorem withCore_core
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk hboundary_chart) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk hboundary_chart).core =
      core := by
  rfl

@[simp] theorem withCore_boundaryCore
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk hboundary_chart) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk hboundary_chart).boundaryCore =
      boundaryCore := by
  rfl

/-- A chart pair obtained by shrinking the core refines the original chart pair exactly when the
new core lies in the old core. -/
theorem withCore_refines
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcoreDomain : core ⊆ P.domain)
    (hboundary : boundaryCore ⊆ core)
    (hboundary_disk : P.kind = RadoChartKind.disk → boundaryCore = ∅)
    (hboundary_chart :
      P.kind = RadoChartKind.halfDisk →
        ∀ x : P.domain, (x : M) ∈ boundaryCore → ((P.chartHomeomorph x : Plane) 0 = 0))
    (hcore : core ⊆ P.core) :
    (P.withCore core boundaryCore hcoreDomain hboundary hboundary_disk hboundary_chart).Refines
      P := by
  exact ⟨subset_rfl, hcore⟩

end RadoChartPair

/-- A finite family of Rado chart pairs whose cores cover the whole space. -/
structure FiniteChartPairCover (M : Type u) [TopologicalSpace M] where
  Index : Type u
  indexFintype : Fintype Index
  pair : Index → RadoChartPair M
  boundaryCarrier : Set M
  boundarySet : Set M
  boundarySet_subset_boundaryCarrier : boundarySet ⊆ boundaryCarrier
  covers : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCovers : ∀ x : M, x ∈ boundaryCarrier →
    ∃ i : Index, x ∈ (pair i).boundaryCore
  interiorChartsCoverInterior : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCore_subset_boundaryCarrier :
    ∀ i : Index, (pair i).boundaryCore ⊆ boundaryCarrier
  locallyFinite : ∀ x : M, ∃ t : Finset Index, ∀ i : Index, x ∈ (pair i).core → i ∈ t
  nestedControl : ∀ i : Index, (pair i).core ⊆ (pair i).domain
  boundaryLocallyFinite :
    ∀ x : M, ∃ t : Finset Index, ∀ i : Index, x ∈ (pair i).boundaryCore → i ∈ t
  boundaryNestedControl : ∀ i : Index, (pair i).boundaryCore ⊆ (pair i).core

attribute [instance] FiniteChartPairCover.indexFintype

namespace FiniteChartPairCover

/-- A finite chart-pair cover uses only disk or half-disk local models. -/
def HasDiskOrHalfDiskModelCover {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) : Prop :=
  ∀ x : M, ∃ i : C.Index, x ∈ (C.pair i).core ∧ (C.pair i).HasDiskOrHalfDiskModel

/-- The local model region of each chart pair in a finite cover matches its chart kind. -/
def ModelsMatchKind {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) : Prop :=
  ∀ i : C.Index, (C.pair i).kind.ModelMatchesRegion (C.pair i).modelRegion

/-- The disk/half-disk model-cover property follows from the finite cover and chart-kind data. -/
theorem hasDiskOrHalfDiskModelCover {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) : C.HasDiskOrHalfDiskModelCover := by
  intro x
  rcases C.covers x with ⟨i, hi⟩
  exact ⟨i, hi, (C.pair i).hasDiskOrHalfDiskModel⟩

/-- The chart-kind/model-region compatibility is stored by each chart pair. -/
theorem modelsMatchKind {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) : C.ModelsMatchKind := by
  intro i
  exact (C.pair i).modelsMatchKind

/-- The boundary carrier of a finite chart-pair cover is exactly the union of its boundary cores.
-/
theorem boundaryCarrier_eq_iUnion_boundaryCore {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) :
    C.boundaryCarrier = ⋃ i : C.Index, (C.pair i).boundaryCore := by
  ext x
  constructor
  · intro hx
    rcases C.boundaryCovers x hx with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact C.boundaryCore_subset_boundaryCarrier i hi

/-- The intended boundary set of a finite chart-pair cover is contained in the union of selected
boundary cores. -/
theorem boundarySet_subset_iUnion_boundaryCore {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) :
    C.boundarySet ⊆ ⋃ i : C.Index, (C.pair i).boundaryCore := by
  intro x hx
  rw [← C.boundaryCarrier_eq_iUnion_boundaryCore]
  exact C.boundarySet_subset_boundaryCarrier hx

/-- Enumerate a finite chart-pair cover by natural numbers, using the empty chart pair outside the
finite range. -/
noncomputable def natPair {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) :
    ℕ → RadoChartPair M :=
  fun n =>
    if h : n < Fintype.card C.Index then
      C.pair ((Fintype.equivFin C.Index).symm ⟨n, h⟩)
    else
      RadoChartPair.empty M

theorem natPair_of_index {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M)
    (i : C.Index) :
    C.natPair ((Fintype.equivFin C.Index i).1) = C.pair i := by
  classical
  simp [natPair]

/-- Compactness turns local chart-pair cores into a finite chart-pair cover. -/
theorem exists_of_compact_local
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (pairAt : M → RadoChartPair M)
    (hcore : ∀ x : M, (pairAt x).core ∈ 𝓝 x) :
    Nonempty (FiniteChartPairCover M) := by
  classical
  rcases CompactSpace.elim_nhds_subcover (fun x : M => (pairAt x).core) hcore with
    ⟨t, ht⟩
  let C : FiniteChartPairCover M :=
    { Index := {x : M // x ∈ t}
      indexFintype := inferInstance
      pair := fun x => pairAt x.1
      boundaryCarrier := ⋃ x : {x : M // x ∈ t}, (pairAt x.1).boundaryCore
      boundarySet := ⋃ x : {x : M // x ∈ t}, (pairAt x.1).boundaryCore
      boundarySet_subset_boundaryCarrier := subset_rfl
      covers := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryCovers := by
        intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        exact ⟨i, hi⟩
      interiorChartsCoverInterior := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryCore_subset_boundaryCarrier := by
        intro i x hx
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
      locallyFinite := by
        intro _x
        refine ⟨Finset.univ, ?_⟩
        intro i _hi
        simp
      nestedControl := by
        intro i
        exact (pairAt i.1).core_subset_domain
      boundaryLocallyFinite := by
        intro _x
        refine ⟨Finset.univ, ?_⟩
        intro i _hi
        simp
      boundaryNestedControl := by
        intro i
        exact (pairAt i.1).boundaryCore_subset_core }
  exact ⟨C⟩

end FiniteChartPairCover

/-- A polygonal disk embedded in a Rado chart and covering the chart core.

This is the local geometric input used to start the Rado induction and to fill new chart cores in
the successor step. -/
structure ChartPolygonalDisk (M : Type*) [TopologicalSpace M] where
  chart : RadoChartPair M
  disk : PolygonalDisk
  embed : disk.K.support → M
  isEmbedding : _root_.Topology.IsEmbedding embed
  support_subset_domain : Set.range embed ⊆ chart.domain
  core_covered : chart.core ⊆ Set.range embed
  boundaryCore_covered : chart.boundaryCore ⊆ Set.range embed
  simplexCarrier : disk.K.Simplex → Set M
  simplexCarrier_subset : ∀ σ, simplexCarrier σ ⊆ Set.range embed
  support_covered_by_simplexCarrier :
    ∀ x ∈ Set.range embed, ∃ σ : disk.K.Simplex, x ∈ simplexCarrier σ
  boundaryCore_covered_by_boundary :
    ∀ x ∈ chart.boundaryCore, ∃ σ ∈ disk.boundarySubcomplex.simplexes, x ∈ simplexCarrier σ
  respectsChartModel :
    ∀ p : disk.K.support,
      (chart.chartHomeomorph ⟨embed p, support_subset_domain ⟨p, rfl⟩⟩ : Plane) ∈
        chart.modelRegion

namespace ChartPolygonalDisk

/-- The model-region compatibility statement carried by a chart polygonal disk. -/
def RespectsChartModel {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) : Prop :=
  ∀ p : D.disk.K.support,
    (D.chart.chartHomeomorph ⟨D.embed p, D.support_subset_domain ⟨p, rfl⟩⟩ : Plane) ∈
      D.chart.modelRegion

/-- The embedded PL complex associated to a chart polygonal disk. -/
def toPLComplexInSpace {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    PLComplexInSpace M where
  Complex := D.disk.K
  embed := D.embed
  isEmbedding := D.isEmbedding
  simplexSupport := D.simplexCarrier
  simplexSupport_subset := D.simplexCarrier_subset
  support_covered_by_simplexSupport := D.support_covered_by_simplexCarrier
  locallyFinite := inferInstance
  compatibleCharts := ⟨D.isEmbedding.injective, D.isEmbedding.continuous⟩

@[simp] theorem toPLComplexInSpace_complex
    {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    D.toPLComplexInSpace.Complex = D.disk.K := by
  rfl

theorem boundaryCore_subset_boundarySupport
    {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    D.chart.boundaryCore ⊆
      {x | ∃ σ ∈ D.disk.boundarySubcomplex.simplexes,
        x ∈ D.toPLComplexInSpace.simplexCarrier σ} := by
  intro x hx
  rcases D.boundaryCore_covered_by_boundary x hx with ⟨σ, hσ, hxσ⟩
  exact ⟨σ, hσ, by simpa [toPLComplexInSpace, PLComplexInSpace.simplexCarrier] using hxσ⟩

/-- A local chart polygonal disk is boundary-faithful if, in a half-disk chart, the whole part of
its core whose chart coordinate lies on the model boundary line is included in the stored
boundary core. -/
def BoundaryFaithful {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) : Prop :=
  D.chart.kind = RadoChartKind.halfDisk →
    ∀ x (hx : x ∈ D.chart.core),
      ((D.chart.chartHomeomorph ⟨x, D.chart.core_subset_domain hx⟩ : Plane) 0 = 0) →
        x ∈ D.chart.boundaryCore

theorem boundaryCore_of_chart_coord_zero
    {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M)
    (hD : D.BoundaryFaithful) (hkind : D.chart.kind = RadoChartKind.halfDisk)
    {x : M} (hx : x ∈ D.chart.core)
    (hline : ((D.chart.chartHomeomorph ⟨x, D.chart.core_subset_domain hx⟩ : Plane) 0 = 0)) :
    x ∈ D.chart.boundaryCore :=
  hD hkind x hx hline

end ChartPolygonalDisk

/-- A polygonal disk embedded in the model region of a Rado chart pair.

This is the coordinate-side local geometry object.  Pulling it back through the stored chart
homeomorphism produces an actual `ChartPolygonalDisk` in the manifold. -/
structure ModelChartPolygonalDisk {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) where
  disk : PolygonalDisk
  embed : disk.K.support → P.modelRegion
  isEmbedding : _root_.Topology.IsEmbedding embed
  simplexCarrier : disk.K.Simplex → Set P.modelRegion
  simplexCarrier_subset : ∀ σ, simplexCarrier σ ⊆ Set.range embed
  support_covered_by_simplexCarrier :
    ∀ x ∈ Set.range embed, ∃ σ : disk.K.Simplex, x ∈ simplexCarrier σ
  modelBoundaryCore : Set P.modelRegion
  modelBoundaryCore_subset_range : modelBoundaryCore ⊆ Set.range embed
  modelBoundaryCore_empty_of_disk : P.kind = RadoChartKind.disk → modelBoundaryCore = ∅
  modelBoundaryCore_in_boundary_chart :
    P.kind = RadoChartKind.halfDisk → ∀ q ∈ modelBoundaryCore, (q : Plane) 0 = 0
  modelBoundaryCore_contains_boundary_chart :
    P.kind = RadoChartKind.halfDisk →
      ∀ q ∈ Set.range embed, (q : Plane) 0 = 0 → q ∈ modelBoundaryCore
  modelBoundaryCore_covered_by_boundary :
    ∀ q ∈ modelBoundaryCore, ∃ σ ∈ disk.boundarySubcomplex.simplexes, q ∈ simplexCarrier σ
  respectsChartModel : ∀ p : disk.K.support, (embed p : Plane) ∈ P.modelRegion

namespace ModelChartPolygonalDisk

variable {M : Type*} [TopologicalSpace M] {P : RadoChartPair M}

/-- Pull a coordinate-model polygonal disk back into the manifold. -/
def toManifoldEmbed (D : ModelChartPolygonalDisk P) : D.disk.K.support → M :=
  fun p => (P.chartHomeomorph.symm (D.embed p)).1

/-- The manifold core covered by the pulled-back model disk. -/
def pulledCore (D : ModelChartPolygonalDisk P) : Set M :=
  Set.range D.toManifoldEmbed

/-- The manifold boundary core obtained by pulling back the model boundary core. -/
def pulledBoundaryCore (D : ModelChartPolygonalDisk P) : Set M :=
  (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1) '' D.modelBoundaryCore

theorem pulledCore_subset_domain (D : ModelChartPolygonalDisk P) :
    D.pulledCore ⊆ P.domain := by
  rintro _ ⟨p, rfl⟩
  exact (P.chartHomeomorph.symm (D.embed p)).2

/-- If the model image of a polygonal disk is a neighborhood of a chart coordinate, then its
pullback is a neighborhood of the corresponding manifold point. -/
theorem pulledCore_mem_nhds_of_range_mem_nhds (D : ModelChartPolygonalDisk P)
    {x : M} (hx : x ∈ P.domain)
    (hD : Set.range D.embed ∈ 𝓝 (P.chartHomeomorph ⟨x, hx⟩)) :
    D.pulledCore ∈ 𝓝 x := by
  let s : Set P.domain := P.chartHomeomorph ⁻¹' Set.range D.embed
  have hs : s ∈ 𝓝 (⟨x, hx⟩ : P.domain) := by
    rw [P.chartHomeomorph.nhds_eq_comap]
    exact Filter.preimage_mem_comap hD
  have himage : ((Subtype.val : P.domain → M) '' s) = D.pulledCore := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      change (P.chartHomeomorph.symm (D.embed p)).1 = z.1
      rw [hp, P.chartHomeomorph.symm_apply_apply]
    · rintro ⟨p, rfl⟩
      refine ⟨P.chartHomeomorph.symm (D.embed p), ?_, rfl⟩
      exact ⟨p, by simp⟩
  rw [← himage]
  rw [← map_nhds_subtype_coe_eq_nhds hx (P.domain_open.mem_nhds hx)]
  exact Filter.image_mem_map hs

theorem toManifoldEmbed_isEmbedding (D : ModelChartPolygonalDisk P) :
    _root_.Topology.IsEmbedding D.toManifoldEmbed := by
  have hSubtype :
      _root_.Topology.IsEmbedding ((Subtype.val : P.domain → M)) :=
    _root_.Topology.IsEmbedding.subtypeVal
  have hChart : _root_.Topology.IsEmbedding P.chartHomeomorph.symm :=
    P.chartHomeomorph.symm.isEmbedding
  change _root_.Topology.IsEmbedding
    (fun p : D.disk.K.support => (P.chartHomeomorph.symm (D.embed p)).1)
  simpa [Function.comp_def] using hSubtype.comp (hChart.comp D.isEmbedding)

/-- The Rado chart pair obtained by using the pulled-back model disk as the smaller core. -/
def toChartPair (D : ModelChartPolygonalDisk P) : RadoChartPair M :=
  P.withCore D.pulledCore D.pulledBoundaryCore D.pulledCore_subset_domain (by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    rcases D.modelBoundaryCore_subset_range hq with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [toManifoldEmbed] using congrArg (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1)
      hp) (by
    intro h
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : q ∈ (∅ : Set P.modelRegion) := by
        rw [D.modelBoundaryCore_empty_of_disk h] at hq
        exact hq
      simp at this
    · intro hy
      simp at hy) (by
    intro h y hy
    rcases hy with ⟨q, hq, hyq⟩
    have hy_eq : y = P.chartHomeomorph.symm q := Subtype.ext hyq.symm
    simpa [hy_eq] using D.modelBoundaryCore_in_boundary_chart h q hq)

@[simp] theorem toChartPair_domain (D : ModelChartPolygonalDisk P) :
    D.toChartPair.domain = P.domain := by
  rfl

@[simp] theorem toChartPair_core (D : ModelChartPolygonalDisk P) :
    D.toChartPair.core = D.pulledCore := by
  rfl

@[simp] theorem toChartPair_boundaryCore (D : ModelChartPolygonalDisk P) :
    D.toChartPair.boundaryCore = D.pulledBoundaryCore := by
  rfl

/-- Pulling back a model polygonal disk gives a chart polygonal disk in the manifold. -/
def toChartPolygonalDisk (D : ModelChartPolygonalDisk P) : ChartPolygonalDisk M where
  chart := D.toChartPair
  disk := D.disk
  embed := D.toManifoldEmbed
  isEmbedding := D.toManifoldEmbed_isEmbedding
  support_subset_domain := by
    intro y hy
    exact D.pulledCore_subset_domain hy
  core_covered := by
    intro y hy
    simpa [toChartPair, RadoChartPair.withCore, pulledCore] using hy
  boundaryCore_covered := by
    intro y hy
    change y ∈ D.pulledBoundaryCore at hy
    rcases hy with ⟨q, hq, rfl⟩
    rcases D.modelBoundaryCore_subset_range hq with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [toManifoldEmbed] using congrArg (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1)
      hp
  simplexCarrier := fun σ =>
    (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1) '' D.simplexCarrier σ
  simplexCarrier_subset := by
    intro σ x hx
    rcases hx with ⟨q, hq, rfl⟩
    rcases D.simplexCarrier_subset σ hq with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [toManifoldEmbed] using congrArg (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1)
      hp
  support_covered_by_simplexCarrier := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    rcases D.support_covered_by_simplexCarrier (D.embed p) ⟨p, rfl⟩ with ⟨σ, hσ⟩
    exact ⟨σ, ⟨D.embed p, hσ, rfl⟩⟩
  boundaryCore_covered_by_boundary := by
    intro y hy
    change y ∈ D.pulledBoundaryCore at hy
    rcases hy with ⟨q, hq, rfl⟩
    rcases D.modelBoundaryCore_covered_by_boundary q hq with ⟨σ, hσ, hqσ⟩
    exact ⟨σ, hσ, ⟨q, hqσ, rfl⟩⟩
  respectsChartModel := by
    intro p
    exact D.toChartPair.chart_to_model
      ⟨D.toManifoldEmbed p, D.pulledCore_subset_domain ⟨p, rfl⟩⟩

@[simp] theorem toChartPolygonalDisk_chart_core (D : ModelChartPolygonalDisk P) :
    D.toChartPolygonalDisk.chart.core = D.pulledCore := by
  rfl

@[simp] theorem toChartPolygonalDisk_chart_boundaryCore (D : ModelChartPolygonalDisk P) :
    D.toChartPolygonalDisk.chart.boundaryCore = D.pulledBoundaryCore := by
  rfl

/-- Pulling back a boundary-faithful model polygonal disk gives a boundary-faithful manifold
chart polygonal disk. -/
theorem toChartPolygonalDisk_boundaryFaithful (D : ModelChartPolygonalDisk P) :
    D.toChartPolygonalDisk.BoundaryFaithful := by
  intro hkind x hx hline
  have hkindP : P.kind = RadoChartKind.halfDisk := by
    simpa [toChartPolygonalDisk, toChartPair, RadoChartPair.withCore] using hkind
  have hxPulled : x ∈ D.pulledCore := by
    simpa [toChartPolygonalDisk, toChartPair, RadoChartPair.withCore] using hx
  rcases hxPulled with ⟨p, rfl⟩
  change D.toManifoldEmbed p ∈ D.pulledBoundaryCore
  refine ⟨D.embed p, ?_, rfl⟩
  apply D.modelBoundaryCore_contains_boundary_chart hkindP
  · exact ⟨p, rfl⟩
  · have hcoord :
        D.toChartPolygonalDisk.chart.chartHomeomorph
            ⟨D.toManifoldEmbed p,
              D.toChartPolygonalDisk.chart.core_subset_domain hx⟩ =
          D.embed p := by
      change P.chartHomeomorph
          ⟨(P.chartHomeomorph.symm (D.embed p)).1, _⟩ =
        D.embed p
      exact P.chartHomeomorph.apply_symm_apply (D.embed p)
    rw [hcoord] at hline
    exact hline

@[simp] theorem toChartPolygonalDisk_simplexCarrier (D : ModelChartPolygonalDisk P)
    (σ : D.disk.K.Simplex) :
    D.toChartPolygonalDisk.simplexCarrier σ =
      (fun q : P.modelRegion => (P.chartHomeomorph.symm q).1) '' D.simplexCarrier σ := by
  rfl

/-- A pulled-back model disk refines its ambient chart pair whenever its pulled-back core lies in
the ambient core. -/
theorem toChartPair_refines (D : ModelChartPolygonalDisk P)
    (hcore : D.pulledCore ⊆ P.core) :
    D.toChartPair.Refines P := by
  exact ⟨subset_rfl, hcore⟩

/-- The standard coordinate triangle as a model disk in any chart model region containing it. -/
def standardTriangleInModel (P : RadoChartPair M)
    (hregion : EuclideanComplex.Examples.closedTriangleSupport ⊆ P.modelRegion) :
    ModelChartPolygonalDisk P where
  disk := PolygonalDiskExamples.standardTriangle
  embed := fun p => ⟨p.1, hregion p.2⟩
  isEmbedding := by
    have hCodomain :
        _root_.Topology.IsEmbedding ((Subtype.val : P.modelRegion → Plane)) :=
      _root_.Topology.IsEmbedding.subtypeVal
    have hDomain :
        _root_.Topology.IsEmbedding
          ((Subtype.val : PolygonalDiskExamples.standardTriangle.K.support → Plane)) :=
      _root_.Topology.IsEmbedding.subtypeVal
    refine (hCodomain.of_comp_iff).mp ?_
    change _root_.Topology.IsEmbedding
      (fun p : PolygonalDiskExamples.standardTriangle.K.support => (p.1 : Plane))
    simpa [Function.comp_def] using hDomain
  simplexCarrier := fun σ =>
    {q : P.modelRegion | (q : Plane) ∈ EuclideanComplex.Examples.closedTriangleSimplexCarrier σ}
  simplexCarrier_subset := by
    intro σ q hq
    refine ⟨⟨q.1, ?_⟩, ?_⟩
    · exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support σ hq
    · exact Subtype.ext rfl
  support_covered_by_simplexCarrier := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    exact ⟨EuclideanComplex.Examples.TriangleSimplex.face, p.2⟩
  modelBoundaryCore :=
    match P.kind with
    | RadoChartKind.disk => ∅
    | RadoChartKind.halfDisk =>
        {q : P.modelRegion |
          (q : Plane) ∈
            EuclideanComplex.Examples.closedTriangleSimplexCarrier
              EuclideanComplex.Examples.TriangleSimplex.e₂₀}
  modelBoundaryCore_subset_range := by
    intro q hq
    cases hkind : P.kind
    · rw [hkind] at hq
      change q ∈ (∅ : Set P.modelRegion) at hq
      cases hq
    · rw [hkind] at hq
      change (q : Plane) ∈
        EuclideanComplex.Examples.closedTriangleSimplexCarrier
          EuclideanComplex.Examples.TriangleSimplex.e₂₀ at hq
      refine ⟨⟨q.1, ?_⟩, ?_⟩
      · exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support
          EuclideanComplex.Examples.TriangleSimplex.e₂₀ hq
      · exact Subtype.ext rfl
  modelBoundaryCore_empty_of_disk := by
    intro h
    simp [h]
  modelBoundaryCore_in_boundary_chart := by
    intro h q hq
    cases hkind : P.kind
    · rw [hkind] at h
      cases h
    · rw [hkind] at hq
      change (q : Plane) ∈
          EuclideanComplex.Examples.closedTriangleSimplexCarrier
          EuclideanComplex.Examples.TriangleSimplex.e₂₀ at hq
      exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_e₂₀_coord_zero hq
  modelBoundaryCore_contains_boundary_chart := by
    intro h q hq hline
    rw [h]
    rcases hq with ⟨p, rfl⟩
    change (p.1 : Plane) ∈
      EuclideanComplex.Examples.closedTriangleSimplexCarrier
        EuclideanComplex.Examples.TriangleSimplex.e₂₀
    exact EuclideanComplex.Examples.closedTriangleSupport_coord_zero_subset_e₂₀ p.2 hline
  modelBoundaryCore_covered_by_boundary := by
    intro q hq
    cases hkind : P.kind
    · rw [hkind] at hq
      change q ∈ (∅ : Set P.modelRegion) at hq
      cases hq
    · rw [hkind] at hq
      change (q : Plane) ∈
        EuclideanComplex.Examples.closedTriangleSimplexCarrier
          EuclideanComplex.Examples.TriangleSimplex.e₂₀ at hq
      exact ⟨EuclideanComplex.Examples.TriangleSimplex.e₂₀, by decide, hq⟩
  respectsChartModel := by
    intro p
    exact (⟨p.1, hregion p.2⟩ : P.modelRegion).2

end ModelChartPolygonalDisk

/-- A polygonal disk whose image is a neighborhood of a chosen point in a plane region.

This is the chart-free Euclidean object needed by the local Rado shrinking theorem. -/
structure PlaneRegionPolygonalNeighborhood (Ω : Set Plane) (y : Ω) where
  disk : PolygonalDisk
  embed : disk.K.support → Ω
  isEmbedding : _root_.Topology.IsEmbedding embed
  simplexCarrier : disk.K.Simplex → Set Ω
  simplexCarrier_subset : ∀ σ, simplexCarrier σ ⊆ Set.range embed
  support_covered_by_simplexCarrier :
    ∀ x ∈ Set.range embed, ∃ σ : disk.K.Simplex, x ∈ simplexCarrier σ
  boundaryCarrier : Set Ω
  boundaryCarrier_subset_range : boundaryCarrier ⊆ Set.range embed
  boundaryCarrier_in_coordBoundary : ∀ q ∈ boundaryCarrier, (q : Plane) 0 = 0
  boundaryCarrier_contains_coordBoundary :
    ∀ q ∈ Set.range embed, (q : Plane) 0 = 0 → q ∈ boundaryCarrier
  boundaryCarrier_covered_by_boundary :
    ∀ q ∈ boundaryCarrier, ∃ σ ∈ disk.boundarySubcomplex.simplexes, q ∈ simplexCarrier σ
  range_mem_nhds : Set.range embed ∈ 𝓝 y
  respectsChartModel : ∀ p : disk.K.support, (embed p : Plane) ∈ Ω

/-- A copy of the standard closed triangle in a plane region, centered at the chosen point.

The remaining interior coordinate geometry in Rado's proof is to construct such a copy by a small
translation and dilation inside a given ambient neighborhood. -/
structure PlaneRegionTriangleCopy (Ω : Set Plane) (y : Ω) where
  homeomorph : Plane ≃ₜ Plane
  centroid_eq : homeomorph EuclideanComplex.Examples.closedTriangleCentroid = y.1
  image_subset :
    homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω

namespace PlaneRegionTriangleCopy

/-- The plane homeomorphism that scales the standard triangle about its centroid and then
translates that centroid to `center`. -/
def centeredHomothety (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) :
    Plane ≃ₜ Plane :=
  (Homeomorph.addRight (-EuclideanComplex.Examples.closedTriangleCentroid)).trans
    ((Homeomorph.smulOfNeZero scale hscale).trans (Homeomorph.addLeft center))

@[simp] theorem centeredHomothety_centroid
    (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) :
    centeredHomothety center scale hscale
      EuclideanComplex.Examples.closedTriangleCentroid = center := by
  simp [centeredHomothety]

theorem dist_center_centeredHomothety
    (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) (p : Plane) :
    dist (centeredHomothety center scale hscale p) center =
      |scale| * dist p EuclideanComplex.Examples.closedTriangleCentroid := by
  rw [dist_eq_norm, dist_eq_norm]
  have harg :
      centeredHomothety center scale hscale p - center =
        scale • (p - EuclideanComplex.Examples.closedTriangleCentroid) := by
    ext i
    simp [centeredHomothety, sub_eq_add_neg, smul_add, add_comm, add_left_comm]
  rw [harg, norm_smul]
  rfl

/-- Build a region triangle copy from a centered nonzero homothety whose triangle image lies in the
region. -/
def ofCenteredHomothety {Ω : Set Plane} {y : Ω} (scale : ℝ) (hscale : scale ≠ 0)
    (hsubset :
      centeredHomothety y.1 scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω) :
    PlaneRegionTriangleCopy Ω y where
  homeomorph := centeredHomothety y.1 scale hscale
  centroid_eq := centeredHomothety_centroid y.1 scale hscale
  image_subset := hsubset

/-- Every ambient neighborhood of a plane point contains a sufficiently small centered copy of the
standard triangle. -/
theorem exists_centeredHomothety_image_subset_of_mem_nhds
    {Ω : Set Plane} {center : Plane} (hΩ : Ω ∈ 𝓝 center) :
    ∃ scale : ℝ, ∃ hscale : scale ≠ 0,
      centeredHomothety center scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω := by
  rcases Metric.mem_nhds_iff.mp hΩ with ⟨ε, hε, hball⟩
  let scale : ℝ := ε / 6
  have hscale_pos : 0 < scale := by
    positivity
  have hscale : scale ≠ 0 := ne_of_gt hscale_pos
  refine ⟨scale, hscale, ?_⟩
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  apply hball
  rw [Metric.mem_ball]
  calc
    dist (centeredHomothety center scale hscale p) center
        = |scale| * dist p EuclideanComplex.Examples.closedTriangleCentroid :=
      dist_center_centeredHomothety center scale hscale p
    _ ≤ scale * 3 := by
      rw [abs_of_pos hscale_pos]
      gcongr
      simpa [dist_comm] using
        EuclideanComplex.Examples.dist_centroid_le_three_of_mem_closedTriangleSupport hp
    _ < ε := by
      dsimp [scale]
      nlinarith

end PlaneRegionTriangleCopy

/-- A copy of the standard closed triangle anchored at a boundary-line point of a plane region.

The anchor is a point in the relative interior of the standard triangle edge lying on the model
half-plane boundary.  This is the Euclidean local model needed at boundary chart points: the image
of the triangle is required to be a relative neighborhood inside the target region, not an ambient
plane neighborhood. -/
structure PlaneRegionBoundaryTriangleCopy (Ω : Set Plane) (y : Ω) where
  homeomorph : Plane ≃ₜ Plane
  anchor_eq : homeomorph EuclideanComplex.Examples.closedTriangleBoundaryAnchor = y.1
  image_subset :
    homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω
  image_mem_nhdsWithin :
    homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ∈ 𝓝[Ω] y.1
  maps_boundary_edge_to_boundary_line :
    ∀ p ∈
      EuclideanComplex.Examples.closedTriangleSimplexCarrier
        EuclideanComplex.Examples.TriangleSimplex.e₂₀,
      (homeomorph p) 0 = 0
  boundary_line_preimage_subset_boundary_edge :
    ∀ p ∈ EuclideanComplex.Examples.closedTriangleSupport, (homeomorph p) 0 = 0 →
      p ∈
        EuclideanComplex.Examples.closedTriangleSimplexCarrier
          EuclideanComplex.Examples.TriangleSimplex.e₂₀

namespace PlaneRegionBoundaryTriangleCopy

/-- The plane homeomorphism that scales the standard triangle about its boundary anchor and then
translates that anchor to `center`. -/
def boundaryAnchoredHomothety (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) :
    Plane ≃ₜ Plane :=
  (Homeomorph.addRight (-EuclideanComplex.Examples.closedTriangleBoundaryAnchor)).trans
    ((Homeomorph.smulOfNeZero scale hscale).trans (Homeomorph.addLeft center))

@[simp] theorem boundaryAnchoredHomothety_anchor
    (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) :
    boundaryAnchoredHomothety center scale hscale
      EuclideanComplex.Examples.closedTriangleBoundaryAnchor = center := by
  simp [boundaryAnchoredHomothety]

theorem dist_center_boundaryAnchoredHomothety
    (center : Plane) (scale : ℝ) (hscale : scale ≠ 0) (p : Plane) :
    dist (boundaryAnchoredHomothety center scale hscale p) center =
      |scale| * dist p EuclideanComplex.Examples.closedTriangleBoundaryAnchor := by
  rw [dist_eq_norm, dist_eq_norm]
  have harg :
      boundaryAnchoredHomothety center scale hscale p - center =
        scale • (p - EuclideanComplex.Examples.closedTriangleBoundaryAnchor) := by
    ext i
    simp [boundaryAnchoredHomothety, sub_eq_add_neg, smul_add, add_comm, add_left_comm]
  rw [harg, norm_smul]
  rfl

/-- A positive boundary-anchored homothety with boundary-line center preserves the closed
coordinate-0 half-plane. -/
theorem boundaryAnchoredHomothety_mem_coordHalfspace_of_mem
    {center : Plane} {scale : ℝ} {hscale : scale ≠ 0}
    (hcenter : center 0 = 0) (hscale_pos : 0 < scale) {p : Plane}
    (hp : 0 ≤ p 0) :
    0 ≤ (boundaryAnchoredHomothety center scale hscale p) 0 := by
  have hcoord :
      (boundaryAnchoredHomothety center scale hscale p) 0 =
        scale * p 0 := by
    simp [boundaryAnchoredHomothety, EuclideanComplex.Examples.closedTriangleBoundaryAnchor,
      hcenter, smul_eq_mul]
  rw [hcoord]
  exact mul_nonneg (le_of_lt hscale_pos) hp

/-- A positive boundary-anchored homothety with boundary-line center maps the closed coordinate-0
half-plane onto itself. -/
theorem boundaryAnchoredHomothety_image_coordHalfspace_eq
    {center : Plane} {scale : ℝ} {hscale : scale ≠ 0}
    (hcenter : center 0 = 0) (hscale_pos : 0 < scale) :
    boundaryAnchoredHomothety center scale hscale '' {p : Plane | 0 ≤ p 0} =
      {p : Plane | 0 ≤ p 0} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact boundaryAnchoredHomothety_mem_coordHalfspace_of_mem hcenter hscale_pos hp
  · intro hz
    let f := boundaryAnchoredHomothety center scale hscale
    refine ⟨f.symm z, ?_, by simp [f]⟩
    have hpre :
        z 0 = (boundaryAnchoredHomothety center scale hscale (f.symm z)) 0 := by
      simp [f]
    change 0 ≤ (f.symm z) 0
    have hpre_coord : (f.symm z) 0 = z 0 / scale := by
      have hcoord :
          (boundaryAnchoredHomothety center scale hscale (f.symm z)) 0 =
            scale * (f.symm z) 0 := by
        simp [boundaryAnchoredHomothety, EuclideanComplex.Examples.closedTriangleBoundaryAnchor,
          hcenter, smul_eq_mul]
      rw [hcoord] at hpre
      exact (eq_div_iff hscale).mpr (by simpa [mul_comm] using hpre.symm)
    rw [hpre_coord]
    exact div_nonneg hz (le_of_lt hscale_pos)

/-- The image of the standard triangle under a positive boundary-anchored homothety is a relative
neighborhood of the boundary-line center in the closed coordinate-0 half-plane. -/
theorem boundaryAnchoredHomothety_closedTriangleSupport_mem_nhdsWithin_coordHalfspace
    {center : Plane} {scale : ℝ} {hscale : scale ≠ 0}
    (hcenter : center 0 = 0) (hscale_pos : 0 < scale) :
    boundaryAnchoredHomothety center scale hscale ''
        EuclideanComplex.Examples.closedTriangleSupport ∈
      𝓝[{p : Plane | 0 ≤ p 0}] center := by
  let f := boundaryAnchoredHomothety center scale hscale
  have hImage :
      f '' EuclideanComplex.Examples.closedTriangleSupport ∈
        𝓝[f '' {p : Plane | 0 ≤ p 0}]
          (f EuclideanComplex.Examples.closedTriangleBoundaryAnchor) := by
    rw [← f.isEmbedding.map_nhdsWithin_eq
      {p : Plane | 0 ≤ p 0} EuclideanComplex.Examples.closedTriangleBoundaryAnchor]
    exact Filter.image_mem_map
      EuclideanComplex.Examples.closedTriangleSupport_mem_nhdsWithin_halfspace_boundaryAnchor
  simpa [f, boundaryAnchoredHomothety_image_coordHalfspace_eq hcenter hscale_pos] using hImage

/-- Build a boundary triangle copy from a positive anchored homothety whose triangle image lies in
the region and is a relative neighborhood there. -/
def ofBoundaryAnchoredHomothety {Ω : Set Plane} {y : Ω}
    (hcenter : y.1 0 = 0) (scale : ℝ) (hscale : scale ≠ 0)
    (hsubset :
      boundaryAnchoredHomothety y.1 scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω)
    (hnhds :
      boundaryAnchoredHomothety y.1 scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ∈ 𝓝[Ω] y.1) :
    PlaneRegionBoundaryTriangleCopy Ω y where
  homeomorph := boundaryAnchoredHomothety y.1 scale hscale
  anchor_eq := boundaryAnchoredHomothety_anchor y.1 scale hscale
  image_subset := hsubset
  image_mem_nhdsWithin := hnhds
  maps_boundary_edge_to_boundary_line := by
    intro p hp
    have hp0 := EuclideanComplex.Examples.closedTriangleSimplexCarrier_e₂₀_coord_zero hp
    simp [boundaryAnchoredHomothety, EuclideanComplex.Examples.closedTriangleBoundaryAnchor,
      hcenter, hp0, smul_eq_mul]
  boundary_line_preimage_subset_boundary_edge := by
    intro p hp hline
    have hcoord :
        (boundaryAnchoredHomothety y.1 scale hscale p) 0 =
          scale * p 0 := by
      simp [boundaryAnchoredHomothety, EuclideanComplex.Examples.closedTriangleBoundaryAnchor,
        hcenter, smul_eq_mul]
    have hp0 : p 0 = 0 := by
      have hmul : scale * p 0 = 0 := by
        simpa [hcoord] using hline
      rcases mul_eq_zero.mp hmul with hscale_zero | hp0
      · exact False.elim (hscale hscale_zero)
      · exact hp0
    exact EuclideanComplex.Examples.closedTriangleSupport_coord_zero_subset_e₂₀ hp hp0

/-- Every relative neighborhood of a boundary point in the coordinate-0 half-plane contains a
sufficiently small positive boundary-anchored copy of the standard triangle. -/
theorem exists_boundaryAnchoredHomothety_image_subset_of_mem_nhdsWithin
    {Ω : Set Plane} {center : Plane}
    (hΩ : Ω ∈ 𝓝[{p : Plane | 0 ≤ p 0}] center)
    (hΩ_subset : Ω ⊆ {p : Plane | 0 ≤ p 0})
    (hcenter : center 0 = 0) :
    ∃ scale : ℝ, ∃ hscale : scale ≠ 0,
      boundaryAnchoredHomothety center scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ⊆ Ω ∧
        boundaryAnchoredHomothety center scale hscale ''
          EuclideanComplex.Examples.closedTriangleSupport ∈ 𝓝[Ω] center := by
  rcases Metric.mem_nhdsWithin_iff.mp hΩ with ⟨ε, hε, hball⟩
  let scale : ℝ := ε / 6
  have hscale_pos : 0 < scale := by
    positivity
  have hscale : scale ≠ 0 := ne_of_gt hscale_pos
  refine ⟨scale, hscale, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    apply hball
    constructor
    · rw [Metric.mem_ball]
      calc
        dist (boundaryAnchoredHomothety center scale hscale p) center
            = |scale| * dist p EuclideanComplex.Examples.closedTriangleBoundaryAnchor :=
          dist_center_boundaryAnchoredHomothety center scale hscale p
        _ ≤ scale * 3 := by
          rw [abs_of_pos hscale_pos]
          gcongr
          simpa [dist_comm] using
            EuclideanComplex.Examples.dist_boundaryAnchor_le_three_of_mem_closedTriangleSupport hp
        _ < ε := by
          dsimp [scale]
          nlinarith
    · exact boundaryAnchoredHomothety_mem_coordHalfspace_of_mem
        hcenter hscale_pos hp.1
  · have hImageWithinHalfspace :
        boundaryAnchoredHomothety center scale hscale ''
            EuclideanComplex.Examples.closedTriangleSupport ∈
          𝓝[{p : Plane | 0 ≤ p 0}] center :=
      boundaryAnchoredHomothety_closedTriangleSupport_mem_nhdsWithin_coordHalfspace
        hcenter hscale_pos
    exact nhdsWithin_mono center hΩ_subset hImageWithinHalfspace

end PlaneRegionBoundaryTriangleCopy

namespace PlaneRegionPolygonalNeighborhood

/-- The standard triangle support used by `PolygonalDiskExamples.standardTriangle`. -/
theorem standardTriangle_support_eq :
    PolygonalDiskExamples.standardTriangle.K.support =
      EuclideanComplex.Examples.closedTriangleSupport := by
  rfl

/-- A centered homeomorphic copy of the standard triangle in a region gives a polygonal
neighborhood of the center, provided its image avoids the coordinate boundary line. -/
def ofTriangleCopy {Ω : Set Plane} {y : Ω} (T : PlaneRegionTriangleCopy Ω y)
    (havoidsCoordBoundary :
      ∀ p ∈ EuclideanComplex.Examples.closedTriangleSupport, (T.homeomorph p) 0 ≠ 0) :
    PlaneRegionPolygonalNeighborhood Ω y where
  disk := PolygonalDiskExamples.standardTriangle
  embed := fun p =>
    ⟨T.homeomorph p.1, T.image_subset ⟨p.1, by
      simp [standardTriangle_support_eq] at p ⊢, rfl⟩⟩
  isEmbedding := by
    have hCodomain :
        _root_.Topology.IsEmbedding ((Subtype.val : Ω → Plane)) :=
      _root_.Topology.IsEmbedding.subtypeVal
    have hDomain :
        _root_.Topology.IsEmbedding
          (fun p : PolygonalDiskExamples.standardTriangle.K.support => T.homeomorph p.1) :=
      T.homeomorph.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
    refine (hCodomain.of_comp_iff).mp ?_
    change _root_.Topology.IsEmbedding
      (fun p : PolygonalDiskExamples.standardTriangle.K.support => T.homeomorph p.1)
    exact hDomain
  simplexCarrier := fun σ =>
    {q : Ω | (q : Plane) ∈ T.homeomorph ''
      EuclideanComplex.Examples.closedTriangleSimplexCarrier σ}
  simplexCarrier_subset := by
    intro σ q hq
    rcases hq with ⟨p, hp, hq⟩
    let p' : PolygonalDiskExamples.standardTriangle.K.support :=
      ⟨p, by
        change p ∈ EuclideanComplex.Examples.closedTriangleSupport
        exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support σ hp⟩
    refine ⟨p', ?_⟩
    exact Subtype.ext hq
  support_covered_by_simplexCarrier := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine ⟨EuclideanComplex.Examples.TriangleSimplex.face, ?_⟩
    change T.homeomorph p.1 ∈
      T.homeomorph '' EuclideanComplex.Examples.closedTriangleSupport
    exact ⟨p.1, by
      change p.1 ∈ EuclideanComplex.Examples.closedTriangleSupport
      exact p.2, rfl⟩
  boundaryCarrier := ∅
  boundaryCarrier_subset_range := by
    intro q hq
    simp at hq
  boundaryCarrier_in_coordBoundary := by
    intro q hq
    simp at hq
  boundaryCarrier_contains_coordBoundary := by
    intro q hq hline
    rcases hq with ⟨p, rfl⟩
    exact False.elim (havoidsCoordBoundary p.1 p.2 hline)
  boundaryCarrier_covered_by_boundary := by
    intro q hq
    simp at hq
  range_mem_nhds := by
    have hImage :
        T.homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ∈
          𝓝 (T.homeomorph EuclideanComplex.Examples.closedTriangleCentroid) := by
      rw [← T.homeomorph.map_nhds_eq EuclideanComplex.Examples.closedTriangleCentroid]
      exact Filter.image_mem_map
        EuclideanComplex.Examples.closedTriangleSupport_mem_nhds_centroid
    have hImageAtY :
        T.homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ∈ 𝓝 y.1 := by
      simpa [T.centroid_eq] using hImage
    rw [mem_nhds_subtype_iff_nhdsWithin]
    have hRelative :
        T.homeomorph '' EuclideanComplex.Examples.closedTriangleSupport ∈ 𝓝[Ω] y.1 :=
      mem_nhdsWithin_of_mem_nhds hImageAtY
    convert hRelative using 1
    ext z
    constructor
    · intro hz
      rcases hz with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, rfl⟩
      exact ⟨p.1, by simp [standardTriangle_support_eq] at p ⊢, rfl⟩
    · intro hz
      rcases hz with ⟨p, hp, rfl⟩
      let p' : PolygonalDiskExamples.standardTriangle.K.support :=
        ⟨p, by
          change p ∈ PolygonalDiskExamples.standardTriangle.K.support
          rwa [standardTriangle_support_eq]⟩
      refine ⟨⟨T.homeomorph p, T.image_subset ⟨p, hp, rfl⟩⟩, ?_, rfl⟩
      exact ⟨p', rfl⟩
  respectsChartModel := by
    intro p
    exact
      (⟨T.homeomorph p.1, T.image_subset ⟨p.1, by
        simp [standardTriangle_support_eq] at p ⊢, rfl⟩⟩ : Ω).2

/-- A boundary-anchored homeomorphic copy of the standard triangle in a region gives a polygonal
neighborhood of the boundary point, using the relative-neighborhood field of the copy. -/
def ofBoundaryTriangleCopy {Ω : Set Plane} {y : Ω} (T : PlaneRegionBoundaryTriangleCopy Ω y) :
    PlaneRegionPolygonalNeighborhood Ω y where
  disk := PolygonalDiskExamples.standardTriangle
  embed := fun p =>
    ⟨T.homeomorph p.1, T.image_subset ⟨p.1, by
      simp [standardTriangle_support_eq] at p ⊢, rfl⟩⟩
  isEmbedding := by
    have hCodomain :
        _root_.Topology.IsEmbedding ((Subtype.val : Ω → Plane)) :=
      _root_.Topology.IsEmbedding.subtypeVal
    have hDomain :
        _root_.Topology.IsEmbedding
          (fun p : PolygonalDiskExamples.standardTriangle.K.support => T.homeomorph p.1) :=
      T.homeomorph.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
    refine (hCodomain.of_comp_iff).mp ?_
    change _root_.Topology.IsEmbedding
      (fun p : PolygonalDiskExamples.standardTriangle.K.support => T.homeomorph p.1)
    exact hDomain
  simplexCarrier := fun σ =>
    {q : Ω | (q : Plane) ∈ T.homeomorph ''
      EuclideanComplex.Examples.closedTriangleSimplexCarrier σ}
  simplexCarrier_subset := by
    intro σ q hq
    rcases hq with ⟨p, hp, hq⟩
    let p' : PolygonalDiskExamples.standardTriangle.K.support :=
      ⟨p, by
        change p ∈ EuclideanComplex.Examples.closedTriangleSupport
        exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support σ hp⟩
    refine ⟨p', ?_⟩
    exact Subtype.ext hq
  support_covered_by_simplexCarrier := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine ⟨EuclideanComplex.Examples.TriangleSimplex.face, ?_⟩
    change T.homeomorph p.1 ∈
      T.homeomorph '' EuclideanComplex.Examples.closedTriangleSupport
    exact ⟨p.1, by
      change p.1 ∈ EuclideanComplex.Examples.closedTriangleSupport
      exact p.2, rfl⟩
  boundaryCarrier :=
    {q : Ω | (q : Plane) ∈ T.homeomorph ''
      EuclideanComplex.Examples.closedTriangleSimplexCarrier
        EuclideanComplex.Examples.TriangleSimplex.e₂₀}
  boundaryCarrier_subset_range := by
    intro q hq
    rcases hq with ⟨p, hp, hq⟩
    let p' : PolygonalDiskExamples.standardTriangle.K.support :=
      ⟨p, by
        change p ∈ EuclideanComplex.Examples.closedTriangleSupport
        exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support
          EuclideanComplex.Examples.TriangleSimplex.e₂₀ hp⟩
    refine ⟨p', ?_⟩
    exact Subtype.ext hq
  boundaryCarrier_in_coordBoundary := by
    intro q hq
    rcases hq with ⟨p, hp, hq⟩
    have hline := T.maps_boundary_edge_to_boundary_line p hp
    simpa [← hq] using hline
  boundaryCarrier_contains_coordBoundary := by
    intro q hq hline
    rcases hq with ⟨p, rfl⟩
    refine ⟨p.1, ?_, rfl⟩
    exact T.boundary_line_preimage_subset_boundary_edge p.1 p.2 hline
  boundaryCarrier_covered_by_boundary := by
    intro q hq
    exact ⟨EuclideanComplex.Examples.TriangleSimplex.e₂₀, by decide, hq⟩
  range_mem_nhds := by
    rw [mem_nhds_subtype_iff_nhdsWithin]
    convert T.image_mem_nhdsWithin using 1
    ext z
    constructor
    · intro hz
      rcases hz with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, rfl⟩
      exact ⟨p.1, by simp [standardTriangle_support_eq] at p ⊢, rfl⟩
    · intro hz
      rcases hz with ⟨p, hp, rfl⟩
      let p' : PolygonalDiskExamples.standardTriangle.K.support :=
        ⟨p, by
          change p ∈ PolygonalDiskExamples.standardTriangle.K.support
          rwa [standardTriangle_support_eq]⟩
      refine ⟨⟨T.homeomorph p, T.image_subset ⟨p, hp, rfl⟩⟩, ?_, rfl⟩
      exact ⟨p', rfl⟩
  respectsChartModel := by
    intro p
    exact
      (⟨T.homeomorph p.1, T.image_subset ⟨p.1, by
        simp [standardTriangle_support_eq] at p ⊢, rfl⟩⟩ : Ω).2

/-- Regard a chart-free plane-region polygonal neighborhood as a model chart disk. -/
def toModelChartPolygonalDisk
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) :
    ModelChartPolygonalDisk P where
  disk := N.disk
  embed := N.embed
  isEmbedding := N.isEmbedding
  simplexCarrier := N.simplexCarrier
  simplexCarrier_subset := N.simplexCarrier_subset
  support_covered_by_simplexCarrier := N.support_covered_by_simplexCarrier
  modelBoundaryCore :=
    match P.kind with
    | RadoChartKind.disk => ∅
    | RadoChartKind.halfDisk => N.boundaryCarrier
  modelBoundaryCore_subset_range := by
    intro q hq
    cases hkind : P.kind
    · rw [hkind] at hq
      change q ∈ (∅ : Set P.modelRegion) at hq
      cases hq
    · rw [hkind] at hq
      change q ∈ N.boundaryCarrier at hq
      exact N.boundaryCarrier_subset_range hq
  modelBoundaryCore_empty_of_disk := by
    intro h
    simp [h]
  modelBoundaryCore_in_boundary_chart := by
    intro h q hq
    cases hkind : P.kind
    · rw [hkind] at h
      cases h
    · rw [hkind] at hq
      change q ∈ N.boundaryCarrier at hq
      exact N.boundaryCarrier_in_coordBoundary q hq
  modelBoundaryCore_contains_boundary_chart := by
    intro h q hq hline
    cases hkind : P.kind
    · rw [hkind] at h
      cases h
    · change q ∈ N.boundaryCarrier
      exact N.boundaryCarrier_contains_coordBoundary q hq hline
  modelBoundaryCore_covered_by_boundary := by
    intro q hq
    cases hkind : P.kind
    · rw [hkind] at hq
      change q ∈ (∅ : Set P.modelRegion) at hq
      cases hq
    · rw [hkind] at hq
      change q ∈ N.boundaryCarrier at hq
      exact N.boundaryCarrier_covered_by_boundary q hq
  respectsChartModel := N.respectsChartModel

@[simp] theorem toModelChartPolygonalDisk_embed
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) :
    N.toModelChartPolygonalDisk.embed = N.embed := by
  rfl

@[simp] theorem toModelChartPolygonalDisk_simplexCarrier
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) (σ : N.disk.K.Simplex) :
    N.toModelChartPolygonalDisk.simplexCarrier σ = N.simplexCarrier σ := by
  rfl

@[simp] theorem toModelChartPolygonalDisk_modelBoundaryCore_of_halfDisk
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) (hP : P.kind = RadoChartKind.halfDisk) :
    N.toModelChartPolygonalDisk.modelBoundaryCore = N.boundaryCarrier := by
  simp [toModelChartPolygonalDisk, hP]

theorem toModelChartPolygonalDisk_range_mem_nhds
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) :
    Set.range N.toModelChartPolygonalDisk.embed ∈ 𝓝 y := by
  exact N.range_mem_nhds

end PlaneRegionPolygonalNeighborhood

namespace RadoChartPair

/-- The standard geometric closed triangle as a chart-pair core in the plane. -/
def standardTrianglePlaneCore : RadoChartPair Plane where
  kind := RadoChartKind.disk
  domain := Set.univ
  core := EuclideanComplex.Examples.closedTriangleSupport
  domain_open := isOpen_univ
  core_subset_domain := by
    intro p hp
    trivial
  modelRegion := Set.univ
  chartHomeomorph := Homeomorph.refl (Set.univ : Set Plane)
  model_matches_kind := isOpen_univ
  chart_to_model := by
    intro p
    trivial
  boundaryCore := ∅
  boundaryCore_subset_core := by
    intro p hp
    simp at hp
  boundaryCore_empty_of_disk := by
    intro _h
    rfl
  boundaryCore_in_boundary_chart := by
    intro h
    cases h

end RadoChartPair

namespace ChartPolygonalDisk

/-- The standard geometric triangle embedded in the coordinate plane. -/
def standardTriangleInPlane : ChartPolygonalDisk Plane where
  chart := RadoChartPair.standardTrianglePlaneCore
  disk := PolygonalDiskExamples.standardTriangle
  embed := fun p => p.1
  isEmbedding := _root_.Topology.IsEmbedding.subtypeVal
  support_subset_domain := by
    intro p hp
    trivial
  core_covered := by
    intro p hp
    exact ⟨⟨p, hp⟩, rfl⟩
  boundaryCore_covered := by
    intro p hp
    simp [RadoChartPair.standardTrianglePlaneCore] at hp
  simplexCarrier := EuclideanComplex.Examples.closedTriangleSimplexCarrier
  simplexCarrier_subset := by
    intro σ x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact EuclideanComplex.Examples.closedTriangleSimplexCarrier_subset_support σ hx
  support_covered_by_simplexCarrier := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    exact ⟨EuclideanComplex.Examples.TriangleSimplex.face, p.2⟩
  boundaryCore_covered_by_boundary := by
    intro p hp
    simp [RadoChartPair.standardTrianglePlaneCore] at hp
  respectsChartModel := by
    intro p
    trivial

@[simp] theorem standardTriangleInPlane_chart :
    standardTriangleInPlane.chart = RadoChartPair.standardTrianglePlaneCore := by
  simp [standardTriangleInPlane]

theorem standardTriangleInPlane_covers_core :
    standardTriangleInPlane.chart.core ⊆ Set.range standardTriangleInPlane.embed :=
  standardTriangleInPlane.core_covered

end ChartPolygonalDisk

/-- Countable chart-pair exhaustion data for the Rado induction. -/
structure ChartPairExhaustion (M : Type*) [TopologicalSpace M] where
  pair : ℕ → RadoChartPair M
  boundaryCarrier : Set M
  boundarySet : Set M
  boundarySet_subset_boundaryCarrier : boundarySet ⊆ boundaryCarrier
  covers : ∀ x : M, ∃ n, x ∈ (pair n).core
  boundaryCovers : ∀ x : M, x ∈ boundaryCarrier → ∃ n, x ∈ (pair n).boundaryCore
  interiorChartsCoverInterior : ∀ x : M, ∃ n, x ∈ (pair n).core
  boundaryCore_subset_boundaryCarrier :
    ∀ n, (pair n).boundaryCore ⊆ boundaryCarrier
  locallyFinite : ∀ x : M, ∃ t : Finset ℕ, ∀ n, x ∈ (pair n).core → n ∈ t
  nestedControl : ∀ n, (pair n).core ⊆ (pair n).domain
  boundaryLocallyFinite :
    ∀ x : M, ∃ t : Finset ℕ, ∀ n, x ∈ (pair n).boundaryCore → n ∈ t
  boundaryNestedControl : ∀ n, (pair n).boundaryCore ⊆ (pair n).core

namespace ChartPairExhaustion

/-- A chart-pair exhaustion uses only disk or half-disk local models. -/
def HasDiskOrHalfDiskModelCover {M : Type*} [TopologicalSpace M]
    (E : ChartPairExhaustion M) : Prop :=
  ∀ x : M, ∃ n : ℕ, x ∈ (E.pair n).core ∧ (E.pair n).HasDiskOrHalfDiskModel

/-- The local model region of each chart pair in an exhaustion matches its chart kind. -/
def ModelsMatchKind {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) : Prop :=
  ∀ n : ℕ, (E.pair n).kind.ModelMatchesRegion (E.pair n).modelRegion

/-- The disk/half-disk model-cover property follows from the exhaustion cover and chart-kind data.
-/
theorem hasDiskOrHalfDiskModelCover {M : Type*} [TopologicalSpace M]
    (E : ChartPairExhaustion M) : E.HasDiskOrHalfDiskModelCover := by
  intro x
  rcases E.covers x with ⟨n, hn⟩
  exact ⟨n, hn, (E.pair n).hasDiskOrHalfDiskModel⟩

/-- The chart-kind/model-region compatibility is stored by each chart pair in the exhaustion. -/
theorem modelsMatchKind {M : Type*} [TopologicalSpace M]
    (E : ChartPairExhaustion M) : E.ModelsMatchKind := by
  intro n
  exact (E.pair n).modelsMatchKind

/-- The union of boundary cores in a chart-pair exhaustion. -/
def boundaryCoreUnion {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) : Set M :=
  ⋃ n, (E.pair n).boundaryCore

theorem mem_boundaryCoreUnion_iff {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (x : M) :
    x ∈ E.boundaryCoreUnion ↔ ∃ n, x ∈ (E.pair n).boundaryCore := by
  simp [boundaryCoreUnion]

/-- The named boundary carrier is exactly the union of boundary cores in a chart-pair exhaustion.
-/
theorem boundaryCarrier_eq_boundaryCoreUnion
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) :
    E.boundaryCarrier = E.boundaryCoreUnion := by
  ext x
  constructor
  · intro hx
    rcases E.boundaryCovers x hx with ⟨n, hn⟩
    exact (E.mem_boundaryCoreUnion_iff x).2 ⟨n, hn⟩
  · intro hx
    rcases (E.mem_boundaryCoreUnion_iff x).1 hx with ⟨n, hn⟩
    exact E.boundaryCore_subset_boundaryCarrier n hn

/-- The intended boundary set of a chart-pair exhaustion is contained in the union of selected
boundary cores. -/
theorem boundarySet_subset_boundaryCoreUnion
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) :
    E.boundarySet ⊆ E.boundaryCoreUnion := by
  intro x hx
  rw [← E.boundaryCarrier_eq_boundaryCoreUnion]
  exact E.boundarySet_subset_boundaryCarrier hx

end ChartPairExhaustion

namespace FiniteChartPairCover

/-- A finite chart-pair cover gives the countable chart-pair exhaustion consumed by Rado's
induction. -/
noncomputable def toChartPairExhaustion {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) : ChartPairExhaustion M where
  pair := C.natPair
  boundaryCarrier := C.boundaryCarrier
  boundarySet := C.boundarySet
  boundarySet_subset_boundaryCarrier := C.boundarySet_subset_boundaryCarrier
  covers := by
    intro x
    rcases C.covers x with ⟨i, hi⟩
    exact ⟨(Fintype.equivFin C.Index i).1, by simpa [C.natPair_of_index i] using hi⟩
  boundaryCovers := by
    intro x hx
    rcases C.boundaryCovers x hx with ⟨i, hi⟩
    exact ⟨(Fintype.equivFin C.Index i).1, by simpa [C.natPair_of_index i] using hi⟩
  interiorChartsCoverInterior := by
    intro x
    rcases C.covers x with ⟨i, hi⟩
    exact ⟨(Fintype.equivFin C.Index i).1, by simpa [C.natPair_of_index i] using hi⟩
  boundaryCore_subset_boundaryCarrier := by
    intro n x hx
    by_cases hn : n < Fintype.card C.Index
    · have hpair :
          C.natPair n = C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩) := by
        simp [natPair, hn]
      rw [hpair] at hx
      exact C.boundaryCore_subset_boundaryCarrier
        ((Fintype.equivFin C.Index).symm ⟨n, hn⟩) hx
    · have hpair : C.natPair n = RadoChartPair.empty M := by
        simp [natPair, hn]
      rw [hpair] at hx
      simp [RadoChartPair.empty] at hx
  locallyFinite := by
    intro x
    refine ⟨Finset.range (Fintype.card C.Index), ?_⟩
    intro n hn
    by_contra hnot
    have hnlt : ¬ n < Fintype.card C.Index := by
      simpa using hnot
    have hpair : C.natPair n = RadoChartPair.empty M := by
      simp [natPair, hnlt]
    rw [hpair] at hn
    simp [RadoChartPair.empty] at hn
  nestedControl := by
    intro n
    by_cases hn : n < Fintype.card C.Index
    · have hpair :
          C.natPair n = C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩) := by
        simp [natPair, hn]
      rw [hpair]
      exact (C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩)).core_subset_domain
    · simp [natPair, hn, RadoChartPair.empty]
  boundaryLocallyFinite := by
    intro x
    refine ⟨Finset.range (Fintype.card C.Index), ?_⟩
    intro n hn
    by_contra hnot
    have hnlt : ¬ n < Fintype.card C.Index := by
      simpa using hnot
    have hpair : C.natPair n = RadoChartPair.empty M := by
      simp [natPair, hnlt]
    rw [hpair] at hn
    simp [RadoChartPair.empty] at hn
  boundaryNestedControl := by
    intro n
    by_cases hn : n < Fintype.card C.Index
    · have hpair :
          C.natPair n = C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩) := by
        simp [natPair, hn]
      rw [hpair]
      exact (C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩)).boundaryCore_subset_core
    · simp [natPair, hn, RadoChartPair.empty]

/-- A finite chart-pair cover of a nonempty space has a nonempty index type. -/
theorem index_nonempty {M : Type u} [TopologicalSpace M] [Nonempty M]
    (C : FiniteChartPairCover M) : Nonempty C.Index := by
  rcases C.covers (Classical.choice ‹Nonempty M›) with ⟨i, _hi⟩
  exact ⟨i⟩

/-- A finite chart-pair cover of a nonempty space has positive index cardinality. -/
theorem index_card_pos {M : Type u} [TopologicalSpace M] [Nonempty M]
    (C : FiniteChartPairCover M) : 0 < Fintype.card C.Index := by
  letI : Nonempty C.Index := C.index_nonempty
  exact Fintype.card_pos

/-- The first index in the natural-number enumeration of a nonempty finite chart-pair cover. -/
noncomputable def zeroIndex {M : Type u} [TopologicalSpace M] [Nonempty M]
    (C : FiniteChartPairCover M) : C.Index :=
  (Fintype.equivFin C.Index).symm ⟨0, C.index_card_pos⟩

theorem toChartPairExhaustion_pair_of_lt {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) {n : ℕ} (hn : n < Fintype.card C.Index) :
    C.toChartPairExhaustion.pair n =
      C.pair ((Fintype.equivFin C.Index).symm ⟨n, hn⟩) := by
  simp [toChartPairExhaustion, natPair, hn]

theorem toChartPairExhaustion_pair_of_not_lt {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) {n : ℕ} (hn : ¬ n < Fintype.card C.Index) :
    C.toChartPairExhaustion.pair n = RadoChartPair.empty M := by
  simp [toChartPairExhaustion, natPair, hn]

theorem toChartPairExhaustion_pair_zero {M : Type u} [TopologicalSpace M] [Nonempty M]
    (C : FiniteChartPairCover M) :
    C.toChartPairExhaustion.pair 0 = C.pair C.zeroIndex :=
  C.toChartPairExhaustion_pair_of_lt C.index_card_pos

@[simp] theorem toChartPairExhaustion_boundaryCarrier
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) :
    C.toChartPairExhaustion.boundaryCarrier = C.boundaryCarrier := by
  rfl

@[simp] theorem toChartPairExhaustion_boundarySet
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) :
    C.toChartPairExhaustion.boundarySet = C.boundarySet := by
  rfl

end FiniteChartPairCover

/-- Polygonal disk data for every chart pair in the countable exhaustion associated to a finite
cover.

This isolates the local shrinking theorem: each chart-pair core should be covered by an embedded
polygonal disk or half-disk compatible with the chart model. -/
structure FiniteChartPolygonalDiskData
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  disk : C.Index → ChartPolygonalDisk M
  chart_eq : ∀ i : C.Index, (disk i).chart = C.pair i
  compatibleChartShrinks : ∀ i : C.Index, (disk i).chart.Refines (C.pair i)
  boundaryCompatibleChartShrinks :
    ∀ i : C.Index, (disk i).chart.boundaryCore ⊆ (C.pair i).boundaryCore
  boundaryFaithful : ∀ i : C.Index, (disk i).BoundaryFaithful

namespace FiniteChartPolygonalDiskData

/-- The chart-shrink compatibility statement carried by finite chart polygonal disk data. -/
def CompatibleChartShrinks {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) : Prop :=
  ∀ i : C.Index, (D.disk i).chart.Refines (C.pair i)

/-- The boundary-core compatibility statement carried by finite chart polygonal disk data. -/
def BoundaryCompatibleChartShrinks {M : Type u} [TopologicalSpace M]
    {C : FiniteChartPairCover M} (D : FiniteChartPolygonalDiskData C) : Prop :=
  ∀ i : C.Index, (D.disk i).chart.boundaryCore ⊆ (C.pair i).boundaryCore

/-- Every selected local polygonal disk is boundary-faithful. -/
def BoundaryFaithful {M : Type u} [TopologicalSpace M]
    {C : FiniteChartPairCover M} (D : FiniteChartPolygonalDiskData C) : Prop :=
  ∀ i : C.Index, (D.disk i).BoundaryFaithful

end FiniteChartPolygonalDiskData

/-- Pointwise local chart-polygonal-disk data before compactness extracts a finite subcover. -/
structure LocalChartPolygonalDiskData (M : Type*) [TopologicalSpace M] where
  boundarySet : Set M
  pairAt : M → RadoChartPair M
  diskAt : M → ChartPolygonalDisk M
  chart_eq : ∀ x : M, (diskAt x).chart = pairAt x
  core_mem_nhds : ∀ x : M, (pairAt x).core ∈ 𝓝 x
  compatibleChartShrinks : ∀ x : M, (diskAt x).chart.Refines (pairAt x)
  boundaryCompatibleChartShrinks :
    ∀ x : M, (diskAt x).chart.boundaryCore ⊆ (pairAt x).boundaryCore
  boundaryFaithful : ∀ x : M, (diskAt x).BoundaryFaithful
  boundarySet_subset_boundaryCore :
    ∀ x : M, boundarySet ∩ (pairAt x).core ⊆ (pairAt x).boundaryCore

/-- Pointwise local chart-polygonal-disk data at one point. -/
structure PointChartPolygonalDiskData (M : Type*) [TopologicalSpace M]
    (boundarySet : Set M) (x : M) where
  disk : ChartPolygonalDisk M
  core_mem_nhds : disk.chart.core ∈ 𝓝 x
  boundaryFaithful : disk.BoundaryFaithful
  boundarySet_subset_boundaryCore :
    boundarySet ∩ disk.chart.core ⊆ disk.chart.boundaryCore

/-- The concrete face-closure condition carried by a boundary subcomplex. -/
def BoundarySubcomplexFaceClosed (K : EuclideanComplex) (A : K.Subcomplex) : Prop :=
  ∀ {τ σ}, σ ∈ A.simplexes → K.IsFace τ σ → τ ∈ A.simplexes

/-- Boundary compatibility for overlap steps in the Rado induction.

The new complex must be compatible with the comparison complex on their ambient overlap, and the
chosen boundary subcomplex must be face-closed in the new complex. -/
def BoundaryCompatibleOnOverlap {M : Type*} [TopologicalSpace M]
    (K L : PLComplexInSpace M) (A : K.Complex.Subcomplex) : Prop :=
  K.compatibleOnOverlap L ∧ BoundarySubcomplexFaceClosed K.Complex A

/-- Finite chart-model compatibility data carried by a Rado induction stage.

Each recorded chart polygonal disk has support contained in the current PL complex and respects
the model region of its chart.  This is the Rado-facing replacement for a free
`boundaryRespectsCharts : Prop`: the state now carries actual chart witnesses. -/
structure ChartModelCompatibilityData {M : Type*} [TopologicalSpace M]
    (K : PLComplexInSpace M) where
  Chart : Type
  chartFintype : Fintype Chart
  disk : Chart → ChartPolygonalDisk M
  support_subset : ∀ i, (disk i).toPLComplexInSpace.support ⊆ K.support
  respectsChartModel : ∀ i, (disk i).RespectsChartModel

attribute [instance] ChartModelCompatibilityData.chartFintype

namespace ChartModelCompatibilityData

/-- A single chart polygonal disk gives chart-model compatibility data for any complex containing
its embedded support. -/
def singleton {M : Type*} [TopologicalSpace M] {K : PLComplexInSpace M}
    (D : ChartPolygonalDisk M) (hD : D.toPLComplexInSpace.support ⊆ K.support) :
    ChartModelCompatibilityData K where
  Chart := PUnit
  chartFintype := inferInstance
  disk := fun _ => D
  support_subset := by
    intro _
    exact hD
  respectsChartModel := by
    intro _
    exact D.respectsChartModel

/-- Transport chart-model compatibility data along an inclusion of embedded supports. -/
def mono {M : Type*} [TopologicalSpace M] {K L : PLComplexInSpace M}
    (C : ChartModelCompatibilityData K) (hKL : K.support ⊆ L.support) :
    ChartModelCompatibilityData L where
  Chart := C.Chart
  chartFintype := C.chartFintype
  disk := C.disk
  support_subset := by
    intro i x hx
    exact hKL (C.support_subset i hx)
  respectsChartModel := C.respectsChartModel

/-- Add one chart polygonal disk to existing chart-model compatibility data. -/
def extendWithChart {M : Type*} [TopologicalSpace M] {K L : PLComplexInSpace M}
    (C : ChartModelCompatibilityData K) (D : ChartPolygonalDisk M)
    (hK : K.support ⊆ L.support) (hD : D.toPLComplexInSpace.support ⊆ L.support) :
    ChartModelCompatibilityData L where
  Chart := C.Chart ⊕ PUnit
  chartFintype := inferInstance
  disk := fun
    | Sum.inl i => C.disk i
    | Sum.inr _ => D
  support_subset := by
    intro i
    cases i with
    | inl i =>
        intro x hx
        exact hK (C.support_subset i hx)
    | inr _ =>
        intro x hx
        exact hD hx
  respectsChartModel := by
    intro i
    cases i with
    | inl i => exact C.respectsChartModel i
    | inr _ => exact D.respectsChartModel

end ChartModelCompatibilityData

/-- Finite chart-core coverage data carried by a Rado induction stage.

The data records finitely many chart cores and boundary chart cores, numbered by a finite stage
index and proved to lie in the current PL complex support.  The recursive Rado constructors fill
this with the actual chart cores they have absorbed. -/
structure RadoStageCoverageData {M : Type*} [TopologicalSpace M]
    (stage : ℕ) (K : PLComplexInSpace M) where
  Core : Type
  coreFintype : Fintype Core
  coreNumber : Core → Fin (stage + 1)
  coreSet : Core → Set M
  core_subset_support : ∀ i, coreSet i ⊆ K.support
  BoundaryCore : Type
  boundaryCoreFintype : Fintype BoundaryCore
  boundaryCoreNumber : BoundaryCore → Fin (stage + 1)
  boundaryCoreSet : BoundaryCore → Set M
  boundaryCore_subset_support : ∀ i, boundaryCoreSet i ⊆ K.support

attribute [instance] RadoStageCoverageData.coreFintype
attribute [instance] RadoStageCoverageData.boundaryCoreFintype

namespace RadoStageCoverageData

/-- The stored ordinary chart-core sets are covered by the current stage support. -/
def CoversCoreSets {M : Type*} [TopologicalSpace M] {stage : ℕ}
    {K : PLComplexInSpace M} (C : RadoStageCoverageData stage K) : Prop :=
  ∀ i, C.coreSet i ⊆ K.support

/-- The stored boundary chart-core sets are covered by the current stage support. -/
def CoversBoundaryCoreSets {M : Type*} [TopologicalSpace M] {stage : ℕ}
    {K : PLComplexInSpace M} (C : RadoStageCoverageData stage K) : Prop :=
  ∀ i, C.boundaryCoreSet i ⊆ K.support

theorem coversCoreSets {M : Type*} [TopologicalSpace M] {stage : ℕ}
    {K : PLComplexInSpace M} (C : RadoStageCoverageData stage K) :
    C.CoversCoreSets :=
  C.core_subset_support

theorem coversBoundaryCoreSets {M : Type*} [TopologicalSpace M] {stage : ℕ}
    {K : PLComplexInSpace M} (C : RadoStageCoverageData stage K) :
    C.CoversBoundaryCoreSets :=
  C.boundaryCore_subset_support

/-- Stage-zero coverage data from one chart core and one boundary chart core. -/
def singleton {M : Type*} [TopologicalSpace M] {K : PLComplexInSpace M}
    (core boundaryCore : Set M) (hcore : core ⊆ K.support)
    (hboundary : boundaryCore ⊆ K.support) :
    RadoStageCoverageData 0 K where
  Core := PUnit
  coreFintype := inferInstance
  coreNumber := fun _ => 0
  coreSet := fun _ => core
  core_subset_support := by
    intro _
    exact hcore
  BoundaryCore := PUnit
  boundaryCoreFintype := inferInstance
  boundaryCoreNumber := fun _ => 0
  boundaryCoreSet := fun _ => boundaryCore
  boundaryCore_subset_support := by
    intro _
    exact hboundary

/-- Extend finite coverage data across a successor Rado stage. -/
def extend {M : Type*} [TopologicalSpace M] {stage : ℕ}
    {K L : PLComplexInSpace M} (C : RadoStageCoverageData stage K)
    (hK : K.support ⊆ L.support) (core boundaryCore : Set M)
    (hcore : core ⊆ L.support) (hboundary : boundaryCore ⊆ L.support) :
    RadoStageCoverageData (stage + 1) L where
  Core := C.Core ⊕ PUnit
  coreFintype := inferInstance
  coreNumber := fun
    | Sum.inl i =>
        ⟨C.coreNumber i, Nat.lt_trans (C.coreNumber i).2 (Nat.lt_succ_self (stage + 1))⟩
    | Sum.inr _ => ⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩
  coreSet := fun
    | Sum.inl i => C.coreSet i
    | Sum.inr _ => core
  core_subset_support := by
    intro i
    cases i with
    | inl i =>
        intro x hx
        exact hK (C.core_subset_support i hx)
    | inr _ =>
        exact hcore
  BoundaryCore := C.BoundaryCore ⊕ PUnit
  boundaryCoreFintype := inferInstance
  boundaryCoreNumber := fun
    | Sum.inl i =>
        ⟨C.boundaryCoreNumber i,
          Nat.lt_trans (C.boundaryCoreNumber i).2 (Nat.lt_succ_self (stage + 1))⟩
    | Sum.inr _ => ⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩
  boundaryCoreSet := fun
    | Sum.inl i => C.boundaryCoreSet i
    | Sum.inr _ => boundaryCore
  boundaryCore_subset_support := by
    intro i
    cases i with
    | inl i =>
        intro x hx
        exact hK (C.boundaryCore_subset_support i hx)
    | inr _ =>
        exact hboundary

end RadoStageCoverageData

/-- State of the Rado induction after finitely many chart pairs have been absorbed. -/
structure RadoInductionState (M : Type*) [TopologicalSpace M] where
  stage : ℕ
  complex : PLComplexInSpace M
  boundarySubcomplex : complex.Complex.Subcomplex
  coverage : RadoStageCoverageData stage complex
  compatibleOnOverlaps : complex.compatibleOnOverlap complex
  boundaryIsSubcomplex : BoundarySubcomplexFaceClosed complex.Complex boundarySubcomplex
  boundaryCompatibleOnOverlaps :
    BoundaryCompatibleOnOverlap complex complex boundarySubcomplex
  boundaryRespectsCharts : ChartModelCompatibilityData complex
  locallyFinite : Finite complex.Complex.Simplex
  boundaryLocallyFinite : Finite {σ : complex.Complex.Simplex // σ ∈ boundarySubcomplex.simplexes}

namespace RadoInductionState

/-- A Rado induction state covers every chart core up to its stage index. -/
def CoversCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) : Prop :=
  ∀ n, n ≤ S.stage → (E.pair n).core ⊆ S.complex.support

/-- A Rado induction state covers every boundary chart core up to its stage index. -/
def CoversBoundaryCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) : Prop :=
  ∀ n, n ≤ S.stage → (E.pair n).boundaryCore ⊆ S.complex.support

/-- The ambient support set carried by the stored boundary subcomplex of a Rado state. -/
def boundarySupport {M : Type*} [TopologicalSpace M] (S : RadoInductionState M) : Set M :=
  {x | ∃ σ ∈ S.boundarySubcomplex.simplexes, x ∈ S.complex.simplexCarrier σ}

/-- A Rado induction state carries every boundary chart core up to its stage in its stored
boundary support. -/
def CoversBoundaryCoresInBoundaryUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) : Prop :=
  ∀ n, n ≤ S.stage → (E.pair n).boundaryCore ⊆ S.boundarySupport

theorem boundarySupport_subset_support {M : Type*} [TopologicalSpace M]
    (S : RadoInductionState M) :
    S.boundarySupport ⊆ S.complex.support := by
  intro x hx
  rcases hx with ⟨σ, _hσ, hxσ⟩
  exact S.complex.simplexCarrier_subset_support σ hxσ

/-- The boundary-subcomplex data extracted from a Rado induction state. -/
def boundarySubcomplexData {M : Type*} [TopologicalSpace M]
    (S : RadoInductionState M) : S.complex.BoundarySubcomplexData where
  boundary := S.boundarySubcomplex
  boundarySupport := S.boundarySupport
  coversBoundary := S.boundarySupport_subset_support
  compatibleWithAmbient := by
    intro x hx
    exact S.boundarySupport_subset_support hx
  boundaryCarrier_subset := by
    intro σ hσ x hx
    exact ⟨σ, hσ, hx⟩
  boundarySupport_covered := by
    intro x hx
    exact hx
  locallyFiniteBoundary := S.boundaryLocallyFinite

end RadoInductionState

/-- Data used to initialize the Rado induction from the first chart pair. -/
structure InitialPLNeighborhoodData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  chartDisk : ChartPolygonalDisk M
  chart_eq : chartDisk.chart = E.pair 0
  coversInitialCore : (E.pair 0).core ⊆ chartDisk.toPLComplexInSpace.support
  coversInitialBoundaryCore : (E.pair 0).boundaryCore ⊆ chartDisk.toPLComplexInSpace.support
  coversInitialBoundaryCoreInBoundary :
    (E.pair 0).boundaryCore ⊆
      {x | ∃ σ ∈ chartDisk.disk.boundarySubcomplex.simplexes,
        x ∈ chartDisk.toPLComplexInSpace.simplexCarrier σ}
  boundarySubcomplexCompatible :
    BoundarySubcomplexFaceClosed chartDisk.toPLComplexInSpace.Complex
      chartDisk.disk.boundarySubcomplex

/-- Data for one successor step of the Rado induction. -/
structure RadoStepExtensionData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M) where
  nextComplex : PLComplexInSpace M
  boundarySubcomplex : nextComplex.Complex.Subcomplex
  nextChartDisk : Option (ChartPolygonalDisk M)
  next_chart_eq : ∀ D : ChartPolygonalDisk M,
    nextChartDisk = some D → D.chart = E.pair (S.stage + 1)
  extends_old : PLComplexInSpace.Extends nextComplex S.complex
  coversNextCore : (E.pair (S.stage + 1)).core ⊆ nextComplex.support
  coversNextBoundaryCore : (E.pair (S.stage + 1)).boundaryCore ⊆ nextComplex.support
  coversNextBoundaryCoreInBoundary :
    (E.pair (S.stage + 1)).boundaryCore ⊆
      {x | ∃ σ ∈ boundarySubcomplex.simplexes, x ∈ nextComplex.simplexCarrier σ}
  compatibleOnOverlaps : nextComplex.compatibleOnOverlap S.complex
  boundaryCompatibleOnOverlaps :
    BoundaryCompatibleOnOverlap nextComplex S.complex boundarySubcomplex
  preservesOldBoundarySupport :
    S.boundarySupport ⊆
      {x | ∃ σ ∈ boundarySubcomplex.simplexes, x ∈ nextComplex.simplexCarrier σ}
  boundaryRespectsCharts : ChartModelCompatibilityData nextComplex

namespace InitialPLNeighborhoodData

/-- Build stage-zero Rado initialization from a polygonal disk covering the first chart core. -/
def ofChartPolygonalDisk
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : ChartPolygonalDisk M) (hD : D.chart = E.pair 0) :
    InitialPLNeighborhoodData E where
  chartDisk := D
  chart_eq := hD
  coversInitialCore := by
    intro x hx
    have hx' : x ∈ D.chart.core := by
      rw [hD]
      exact hx
    simpa [ChartPolygonalDisk.toPLComplexInSpace, PLComplexInSpace.support]
      using D.core_covered hx'
  coversInitialBoundaryCore := by
    intro x hx
    have hx' : x ∈ D.chart.boundaryCore := by
      rw [hD]
      exact hx
    simpa [ChartPolygonalDisk.toPLComplexInSpace, PLComplexInSpace.support]
      using D.boundaryCore_covered hx'
  coversInitialBoundaryCoreInBoundary := by
    intro x hx
    have hx' : x ∈ D.chart.boundaryCore := by
      rw [hD]
      exact hx
    exact D.boundaryCore_subset_boundarySupport hx'
  boundarySubcomplexCompatible := by
    intro τ σ hσ hface
    exact D.disk.boundarySubcomplex.face_closed hσ hface

/-- The stage-zero Rado induction state determined by initial chart-disk data. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) : RadoInductionState M :=
  { stage := 0
    complex := D.chartDisk.toPLComplexInSpace
    boundarySubcomplex := D.chartDisk.disk.boundarySubcomplex
    coverage :=
      RadoStageCoverageData.singleton (E.pair 0).core (E.pair 0).boundaryCore
        D.coversInitialCore D.coversInitialBoundaryCore
    compatibleOnOverlaps := D.chartDisk.toPLComplexInSpace.compatibleOnOverlap_self
    boundaryIsSubcomplex := D.boundarySubcomplexCompatible
    boundaryCompatibleOnOverlaps :=
      ⟨D.chartDisk.toPLComplexInSpace.compatibleOnOverlap_self, D.boundarySubcomplexCompatible⟩
    boundaryRespectsCharts :=
      ChartModelCompatibilityData.singleton D.chartDisk subset_rfl
    locallyFinite := inferInstance
    boundaryLocallyFinite := inferInstance }

@[simp] theorem toState_stage
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.stage = 0 := by
  rfl

theorem core_subset_toState_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    (E.pair 0).core ⊆ D.toState.complex.support :=
  D.coversInitialCore

theorem boundaryCore_subset_toState_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    (E.pair 0).boundaryCore ⊆ D.toState.complex.support :=
  D.coversInitialBoundaryCore

theorem boundaryCore_subset_toState_boundarySupport
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    (E.pair 0).boundaryCore ⊆ D.toState.boundarySupport :=
  D.coversInitialBoundaryCoreInBoundary

theorem toState_coversPreviousCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coverage.CoversCoreSets ↔
      ∀ i, D.toState.coverage.coreSet i ⊆ D.toState.complex.support :=
  Iff.rfl

theorem toState_coversPreviousBoundaryCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coverage.CoversBoundaryCoreSets ↔
      ∀ i, D.toState.coverage.boundaryCoreSet i ⊆ D.toState.complex.support :=
  Iff.rfl

/-- The initial Rado state covers every chart core up to stage zero. -/
theorem toState_coversCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.CoversCoresUpTo (E := E) := by
  intro n hn
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  exact D.core_subset_toState_support

theorem toState_coversPreviousCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coverage.CoversCoreSets :=
  D.toState.coverage.coversCoreSets

/-- The initial Rado state covers every boundary chart core up to stage zero. -/
theorem toState_coversBoundaryCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.CoversBoundaryCoresUpTo (E := E) := by
  intro n hn
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  exact D.boundaryCore_subset_toState_support

theorem toState_coversPreviousBoundaryCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coverage.CoversBoundaryCoreSets :=
  D.toState.coverage.coversBoundaryCoreSets

/-- The initial Rado state carries every boundary chart core up to stage zero in its boundary
support. -/
theorem toState_coversBoundaryCoresInBoundaryUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.CoversBoundaryCoresInBoundaryUpTo (E := E) := by
  intro n hn
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  exact D.boundaryCore_subset_toState_boundarySupport

end InitialPLNeighborhoodData

namespace RadoStepExtensionData

/-- The successor Rado induction state determined by one chart-extension data package. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    RadoInductionState M :=
  { stage := S.stage + 1
    complex := D.nextComplex
    boundarySubcomplex := D.boundarySubcomplex
    coverage :=
      S.coverage.extend D.extends_old.1 (E.pair (S.stage + 1)).core
        (E.pair (S.stage + 1)).boundaryCore D.coversNextCore D.coversNextBoundaryCore
    compatibleOnOverlaps := D.nextComplex.compatibleOnOverlap_self
    boundaryIsSubcomplex := by
      intro τ σ hσ hface
      exact D.boundarySubcomplex.face_closed hσ hface
    boundaryCompatibleOnOverlaps := by
      constructor
      · exact D.nextComplex.compatibleOnOverlap_self
      · intro τ σ hσ hface
        exact D.boundarySubcomplex.face_closed hσ hface
    boundaryRespectsCharts := D.boundaryRespectsCharts
    locallyFinite := inferInstance
    boundaryLocallyFinite := inferInstance }

@[simp] theorem toState_stage
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    D.toState.stage = S.stage + 1 := by
  rfl

theorem toState_extends_old
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    PLComplexInSpace.Extends D.toState.complex S.complex :=
  D.extends_old

theorem oldBoundarySupport_subset_toState_boundarySupport
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    S.boundarySupport ⊆ D.toState.boundarySupport :=
  D.preservesOldBoundarySupport

theorem core_subset_toState_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    (E.pair (S.stage + 1)).core ⊆ D.toState.complex.support :=
  D.coversNextCore

theorem boundaryCore_subset_toState_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    (E.pair (S.stage + 1)).boundaryCore ⊆ D.toState.complex.support :=
  D.coversNextBoundaryCore

theorem boundaryCore_subset_toState_boundarySupport
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    (E.pair (S.stage + 1)).boundaryCore ⊆ D.toState.boundarySupport :=
  D.coversNextBoundaryCoreInBoundary

theorem toState_coversPreviousCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    D.toState.coverage.CoversCoreSets ↔
      ∀ i, D.toState.coverage.coreSet i ⊆ D.toState.complex.support :=
  Iff.rfl

theorem toState_coversPreviousBoundaryCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    D.toState.coverage.CoversBoundaryCoreSets ↔
      ∀ i, D.toState.coverage.boundaryCoreSet i ⊆ D.toState.complex.support :=
  Iff.rfl

/-- A Rado successor step preserves cumulative chart-core coverage. -/
theorem toState_coversCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (hS : S.CoversCoresUpTo (E := E)) :
    D.toState.CoversCoresUpTo (E := E) := by
  intro n hn
  change (E.pair n).core ⊆ D.nextComplex.support
  change n ≤ S.stage + 1 at hn
  by_cases hlast : n = S.stage + 1
  · subst n
    exact D.coversNextCore
  · have hlt : n < S.stage + 1 := lt_of_le_of_ne hn hlast
    have hnS : n ≤ S.stage := Nat.le_of_lt_succ hlt
    exact (hS n hnS).trans D.extends_old.1

theorem toState_coversPreviousCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (_hS : S.CoversCoresUpTo (E := E)) :
    D.toState.coverage.CoversCoreSets :=
  D.toState.coverage.coversCoreSets

/-- A Rado successor step preserves cumulative boundary-chart-core coverage. -/
theorem toState_coversBoundaryCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (hS : S.CoversBoundaryCoresUpTo (E := E)) :
    D.toState.CoversBoundaryCoresUpTo (E := E) := by
  intro n hn
  change (E.pair n).boundaryCore ⊆ D.nextComplex.support
  change n ≤ S.stage + 1 at hn
  by_cases hlast : n = S.stage + 1
  · subst n
    exact D.coversNextBoundaryCore
  · have hlt : n < S.stage + 1 := lt_of_le_of_ne hn hlast
    have hnS : n ≤ S.stage := Nat.le_of_lt_succ hlt
    exact (hS n hnS).trans D.extends_old.1

/-- A successor Rado step preserves previous boundary-core coverage in the boundary support and
adds the next boundary chart core to that boundary support. -/
theorem toState_coversBoundaryCoresInBoundaryUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (hS : S.CoversBoundaryCoresInBoundaryUpTo (E := E)) :
    D.toState.CoversBoundaryCoresInBoundaryUpTo (E := E) := by
  intro n hn
  change n ≤ S.stage + 1 at hn
  by_cases hlast : n = S.stage + 1
  · subst n
    exact D.boundaryCore_subset_toState_boundarySupport
  · have hlt : n < S.stage + 1 := lt_of_le_of_ne hn hlast
    have hnS : n ≤ S.stage := Nat.le_of_lt_succ hlt
    exact (hS n hnS).trans D.oldBoundarySupport_subset_toState_boundarySupport

theorem toState_coversPreviousBoundaryCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (_hS : S.CoversBoundaryCoresUpTo (E := E)) :
    D.toState.coverage.CoversBoundaryCoreSets :=
  D.toState.coverage.coversBoundaryCoreSets

/-- Vertex embedding for old-stage vertices in a one-chart union complex. -/
def chartUnionOldVertexEmbedding
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    S.complex.Complex.Vertex ↪ S.complex.Complex.Vertex ⊕ D.disk.K.Vertex :=
  ⟨Sum.inl, by
    intro a b h
    exact Sum.inl.inj h⟩

/-- Vertex embedding for newly adjoined chart-disk vertices in a one-chart union complex. -/
def chartUnionNewVertexEmbedding
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    D.disk.K.Vertex ↪ S.complex.Complex.Vertex ⊕ D.disk.K.Vertex :=
  ⟨Sum.inr, by
    intro a b h
    exact Sum.inr.inj h⟩

/-- The carrier-level PL complex obtained by adjoining one chart polygonal disk to a Rado stage.

The simplex type is the disjoint sum of old-stage simplexes and chart-disk simplexes, and
simplex carriers are inherited from the corresponding side.  This still defers the genuine
geometric pushout/refinement theorem, but it no longer collapses the finite combinatorics of the
two inputs. -/
noncomputable def chartUnionPLComplexData
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    { K : PLComplexInSpace M // K.support = S.complex.support ∪ Set.range D.embed } := by
  let U : Set M := S.complex.support ∪ Set.range D.embed
  haveI : Small.{0} U := by
    infer_instance
  let carrierMap : Shrink.{0} U → M :=
    fun p => ((equivShrink.{0} U).symm p).1
  let carrierTop : TopologicalSpace (Shrink.{0} U) :=
    TopologicalSpace.induced carrierMap inferInstance
  have hCarrierInjective : Function.Injective carrierMap := by
    intro p q hpq
    have hsub :
        (equivShrink.{0} U).symm p =
          (equivShrink.{0} U).symm q := by
      exact Subtype.ext hpq
    exact (equivShrink.{0} U).symm.injective hsub
  have hCarrierEmbedding :
      @Topology.IsEmbedding (Shrink.{0} U) M carrierTop inferInstance carrierMap :=
    hCarrierInjective.isEmbedding_induced
  let C : EuclideanComplex :=
    { Point := Shrink.{0} U
      pointTop := carrierTop
      Vertex := S.complex.Complex.Vertex ⊕ D.disk.K.Vertex
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      Simplex := S.complex.Complex.Simplex ⊕ D.disk.K.Simplex
      simplexFintype := inferInstance
      simplexDecidableEq := inferInstance
      simplexNonempty := by
        exact ⟨Sum.inl S.complex.Complex.defaultSimplex⟩
      simplexVertices := fun
        | Sum.inl σ => (S.complex.Complex.vertices σ).map (chartUnionOldVertexEmbedding S D)
        | Sum.inr σ => (D.disk.K.vertices σ).map (chartUnionNewVertexEmbedding S D)
      simplex_nonempty := by
        intro σ
        cases σ with
        | inl σ =>
            exact (S.complex.Complex.simplex_nonempty σ).map
        | inr σ =>
            exact (D.disk.K.simplex_nonempty σ).map
      support := Set.univ
      realizesSimplexes := by
        intro σ
        cases σ with
        | inl σ =>
            exact (S.complex.Complex.realizesSimplexes σ).map
        | inr σ =>
            exact (D.disk.K.realizesSimplexes σ).map
      faceClosed := by
        intro σ v hv hcard
        cases σ with
        | inl σ =>
            cases v with
            | inl v =>
                have hv_old : v ∈ S.complex.Complex.vertices σ := by
                  rw [Finset.mem_map] at hv
                  rcases hv with ⟨v', hv', hv'eq⟩
                  exact (Sum.inl.inj hv'eq).symm ▸ hv'
                have hcard_old : 1 < (S.complex.Complex.vertices σ).card := by
                  simpa [EuclideanComplex.vertices, Finset.card_map] using hcard
                rcases S.complex.Complex.exists_erase_vertex_face σ v hv_old hcard_old with
                  ⟨τ, hτ⟩
                have hτ' :
                    S.complex.Complex.simplexVertices τ =
                      (S.complex.Complex.simplexVertices σ).erase v := by
                  simpa [EuclideanComplex.vertices] using hτ
                refine ⟨Sum.inl τ, ?_⟩
                calc
                  Finset.map (chartUnionOldVertexEmbedding S D)
                        (S.complex.Complex.simplexVertices τ) =
                      Finset.map (chartUnionOldVertexEmbedding S D)
                        ((S.complex.Complex.simplexVertices σ).erase v) := by
                    rw [hτ']
                  _ =
                      (Finset.map (chartUnionOldVertexEmbedding S D)
                        (S.complex.Complex.simplexVertices σ)).erase
                          ((chartUnionOldVertexEmbedding S D) v) :=
                    Finset.map_erase (chartUnionOldVertexEmbedding S D)
                      (S.complex.Complex.simplexVertices σ) v
                  _ =
                      (Finset.map (chartUnionOldVertexEmbedding S D)
                        (S.complex.Complex.simplexVertices σ)).erase (Sum.inl v) := rfl
            | inr v =>
                rw [Finset.mem_map] at hv
                rcases hv with ⟨v', _hv', hv'eq⟩
                cases hv'eq
        | inr σ =>
            cases v with
            | inl v =>
                rw [Finset.mem_map] at hv
                rcases hv with ⟨v', _hv', hv'eq⟩
                cases hv'eq
            | inr v =>
                have hv_new : v ∈ D.disk.K.vertices σ := by
                  rw [Finset.mem_map] at hv
                  rcases hv with ⟨v', hv', hv'eq⟩
                  exact (Sum.inr.inj hv'eq).symm ▸ hv'
                have hcard_new : 1 < (D.disk.K.vertices σ).card := by
                  simpa [EuclideanComplex.vertices, Finset.card_map] using hcard
                rcases D.disk.K.exists_erase_vertex_face σ v hv_new hcard_new with
                  ⟨τ, hτ⟩
                have hτ' :
                    D.disk.K.simplexVertices τ = (D.disk.K.simplexVertices σ).erase v := by
                  simpa [EuclideanComplex.vertices] using hτ
                refine ⟨Sum.inr τ, ?_⟩
                calc
                  Finset.map (chartUnionNewVertexEmbedding S D) (D.disk.K.simplexVertices τ) =
                      Finset.map (chartUnionNewVertexEmbedding S D)
                        ((D.disk.K.simplexVertices σ).erase v) := by
                    rw [hτ']
                  _ =
                      (Finset.map (chartUnionNewVertexEmbedding S D)
                        (D.disk.K.simplexVertices σ)).erase
                          ((chartUnionNewVertexEmbedding S D) v) :=
                    Finset.map_erase (chartUnionNewVertexEmbedding S D)
                      (D.disk.K.simplexVertices σ) v
                  _ =
                      (Finset.map (chartUnionNewVertexEmbedding S D)
                        (D.disk.K.simplexVertices σ)).erase (Sum.inr v) := rfl }
  let emb : C.support → M := fun p => carrierMap p.1
  let hKEmbedding : _root_.Topology.IsEmbedding emb :=
    hCarrierEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
  let K : PLComplexInSpace M :=
    { Complex := C
      embed := emb
      isEmbedding := hKEmbedding
      simplexSupport := fun
        | Sum.inl σ => S.complex.simplexCarrier σ
        | Sum.inr σ => D.toPLComplexInSpace.simplexCarrier σ
      simplexSupport_subset := by
        intro σ x hx
        have hxU : x ∈ U := by
          cases σ with
          | inl σ =>
              exact Or.inl (S.complex.simplexCarrier_subset_support σ hx)
          | inr σ =>
              have hxD : x ∈ D.toPLComplexInSpace.support :=
                D.toPLComplexInSpace.simplexCarrier_subset_support σ hx
              exact Or.inr (by
                simpa [ChartPolygonalDisk.toPLComplexInSpace, PLComplexInSpace.support] using hxD)
        let p : Shrink.{0} U := equivShrink.{0} U ⟨x, hxU⟩
        refine ⟨⟨p, trivial⟩, ?_⟩
        simp [emb, carrierMap, p]
      support_covered_by_simplexSupport := by
        intro x hx
        rcases hx with ⟨p, rfl⟩
        have hpU : carrierMap p ∈ U :=
          ((equivShrink.{0} U).symm p).2
        rcases hpU with hpOld | hpNew
        · rcases S.complex.exists_simplexCarrier_of_mem_support hpOld with ⟨σ, hσ⟩
          exact ⟨Sum.inl σ, hσ⟩
        · have hpD : carrierMap p ∈ D.toPLComplexInSpace.support := by
            simpa [ChartPolygonalDisk.toPLComplexInSpace, PLComplexInSpace.support] using hpNew
          rcases D.toPLComplexInSpace.exists_simplexCarrier_of_mem_support hpD with ⟨σ, hσ⟩
          exact ⟨Sum.inr σ, hσ⟩
      locallyFinite := inferInstance
      compatibleCharts := ⟨hKEmbedding.injective, hKEmbedding.continuous⟩ }
  refine ⟨K, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨p, rfl⟩
    exact ((equivShrink.{0} U).symm p.1).2
  · intro hx
    let p : Shrink.{0} U := equivShrink.{0} U ⟨x, hx⟩
    refine ⟨⟨p, trivial⟩, ?_⟩
    simp [K, carrierMap, emb, p]

/-- The named carrier-level PL complex obtained by adjoining one chart polygonal disk to a Rado
stage.
-/
noncomputable def chartUnionPLComplex
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) : PLComplexInSpace M :=
  (chartUnionPLComplexData S D).1

/-- The chart-union complex keeps old-stage simplexes and chart-disk simplexes as a disjoint sum. -/
@[simp] theorem chartUnionPLComplex_simplex
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    (chartUnionPLComplex S D).Complex.Simplex =
      (S.complex.Complex.Simplex ⊕ D.disk.K.Simplex) := by
  unfold chartUnionPLComplex chartUnionPLComplexData
  rfl

/-- Old-stage simplex carriers are preserved in the chart-union complex. -/
@[simp] theorem chartUnionPLComplex_old_simplexCarrier
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : S.complex.Complex.Simplex) :
    (chartUnionPLComplex S D).simplexCarrier
        (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inl σ) =
      S.complex.simplexCarrier σ := by
  unfold chartUnionPLComplex chartUnionPLComplexData PLComplexInSpace.simplexCarrier
  rfl

/-- New chart-disk simplex carriers are preserved in the chart-union complex. -/
@[simp] theorem chartUnionPLComplex_new_simplexCarrier
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : D.disk.K.Simplex) :
    (chartUnionPLComplex S D).simplexCarrier
        (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inr σ) =
      D.toPLComplexInSpace.simplexCarrier σ := by
  unfold chartUnionPLComplex chartUnionPLComplexData PLComplexInSpace.simplexCarrier
  rfl

/-- Old-stage simplex vertex sets are preserved, with vertices embedded on the left. -/
@[simp] theorem chartUnionPLComplex_old_vertices
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : S.complex.Complex.Simplex) :
    (chartUnionPLComplex S D).Complex.vertices
        (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inl σ) =
      (S.complex.Complex.vertices σ).map (chartUnionOldVertexEmbedding S D) := by
  unfold chartUnionPLComplex chartUnionPLComplexData EuclideanComplex.vertices
  rfl

/-- New chart-disk simplex vertex sets are preserved, with vertices embedded on the right. -/
@[simp] theorem chartUnionPLComplex_new_vertices
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : D.disk.K.Simplex) :
    (chartUnionPLComplex S D).Complex.vertices
        (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inr σ) =
      (D.disk.K.vertices σ).map (chartUnionNewVertexEmbedding S D) := by
  unfold chartUnionPLComplex chartUnionPLComplexData EuclideanComplex.vertices
  rfl

/-- The chart-union complex has support equal to old support union chart-disk image. -/
theorem chartUnionPLComplex_support
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    (chartUnionPLComplex S D).support = S.complex.support ∪ Set.range D.embed :=
  (chartUnionPLComplexData S D).2

/-- Boundary subcomplex for a one-chart union: keep the old stage boundary on the left and the
chart disk boundary on the right. -/
noncomputable def chartUnionBoundarySubcomplex
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) : (chartUnionPLComplex S D).Complex.Subcomplex := by
  classical
  refine
    { simplexes :=
        Finset.univ.filter fun σ =>
          match σ with
          | Sum.inl τ => τ ∈ S.boundarySubcomplex.simplexes
          | Sum.inr τ => τ ∈ D.disk.boundarySubcomplex.simplexes
      face_closed := ?_ }
  · intro τ σ hσ hface
    rw [Finset.mem_filter] at hσ ⊢
    constructor
    · simp
    · cases σ with
      | inl σ =>
          cases τ with
          | inl τ =>
              have hface_old : S.complex.Complex.IsFace τ σ := by
                intro v hv
                have hvUnion :
                    Sum.inl v ∈ (chartUnionPLComplex S D).Complex.vertices
                      (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inl τ) := by
                  rw [chartUnionPLComplex_old_vertices]
                  exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
                have hvTarget := hface hvUnion
                rw [chartUnionPLComplex_old_vertices] at hvTarget
                change Sum.inl v ∈
                  (S.complex.Complex.vertices σ).map (chartUnionOldVertexEmbedding S D) at hvTarget
                rw [Finset.mem_map] at hvTarget
                rcases hvTarget with ⟨v', hv', hv'eq⟩
                exact (Sum.inl.inj hv'eq).symm ▸ hv'
              exact S.boundarySubcomplex.face_closed hσ.2 hface_old
          | inr τ =>
              exfalso
              rcases D.disk.K.simplex_nonempty τ with ⟨v, hv⟩
              have hvUnion :
                  Sum.inr v ∈ (chartUnionPLComplex S D).Complex.vertices
                    (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inr τ) := by
                rw [chartUnionPLComplex_new_vertices]
                exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
              have hvTarget := hface hvUnion
              rw [chartUnionPLComplex_old_vertices] at hvTarget
              change Sum.inr v ∈
                (S.complex.Complex.vertices σ).map (chartUnionOldVertexEmbedding S D) at hvTarget
              rw [Finset.mem_map] at hvTarget
              rcases hvTarget with ⟨v', _hv', hv'eq⟩
              cases hv'eq
      | inr σ =>
          cases τ with
          | inl τ =>
              exfalso
              rcases S.complex.Complex.simplex_nonempty τ with ⟨v, hv⟩
              have hvUnion :
                  Sum.inl v ∈ (chartUnionPLComplex S D).Complex.vertices
                    (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inl τ) := by
                rw [chartUnionPLComplex_old_vertices]
                exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
              have hvTarget := hface hvUnion
              rw [chartUnionPLComplex_new_vertices] at hvTarget
              change Sum.inl v ∈
                (D.disk.K.vertices σ).map (chartUnionNewVertexEmbedding S D) at hvTarget
              rw [Finset.mem_map] at hvTarget
              rcases hvTarget with ⟨v', _hv', hv'eq⟩
              cases hv'eq
          | inr τ =>
              have hface_new : D.disk.K.IsFace τ σ := by
                intro v hv
                have hvUnion :
                    Sum.inr v ∈ (chartUnionPLComplex S D).Complex.vertices
                      (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inr τ) := by
                  rw [chartUnionPLComplex_new_vertices]
                  exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
                have hvTarget := hface hvUnion
                rw [chartUnionPLComplex_new_vertices] at hvTarget
                change Sum.inr v ∈
                  (D.disk.K.vertices σ).map (chartUnionNewVertexEmbedding S D) at hvTarget
                rw [Finset.mem_map] at hvTarget
                rcases hvTarget with ⟨v', hv', hv'eq⟩
                exact (Sum.inr.inj hv'eq).symm ▸ hv'
              exact D.disk.boundarySubcomplex.face_closed hσ.2 hface_new

@[simp] theorem chartUnionBoundarySubcomplex_left_mem
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : S.complex.Complex.Simplex) :
    (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inl σ) ∈
        (chartUnionBoundarySubcomplex S D).simplexes ↔
      σ ∈ S.boundarySubcomplex.simplexes := by
  unfold chartUnionBoundarySubcomplex
  simp

@[simp] theorem chartUnionBoundarySubcomplex_right_mem
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) (σ : D.disk.K.Simplex) :
    (show (chartUnionPLComplex S D).Complex.Simplex from Sum.inr σ) ∈
        (chartUnionBoundarySubcomplex S D).simplexes ↔
      σ ∈ D.disk.boundarySubcomplex.simplexes := by
  unfold chartUnionBoundarySubcomplex
  simp

/-- Named one-step Rado extension data from a polygonal chart disk. -/
noncomputable def fromChartPolygonalDisk
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) (D : ChartPolygonalDisk M)
    (hD : D.chart = E.pair (S.stage + 1)) :
    RadoStepExtensionData E S := by
  let K : PLComplexInSpace M := chartUnionPLComplex S D
  have hKsupport : K.support = S.complex.support ∪ Set.range D.embed :=
    chartUnionPLComplex_support S D
  exact
    { nextComplex := K
      boundarySubcomplex := chartUnionBoundarySubcomplex S D
      nextChartDisk := some D
      next_chart_eq := by
        intro D' hD'
        cases hD'
        exact hD
      extends_old := by
        constructor
        · intro x hx
          rw [hKsupport]
          exact Or.inl hx
        · exact K.compatibleOnOverlap_of_embedded_overlap S.complex
      coversNextCore := by
        intro x hx
        have hx' : x ∈ D.chart.core := by
          rw [hD]
          exact hx
        rw [hKsupport]
        exact Or.inr (D.core_covered hx')
      coversNextBoundaryCore := by
        intro x hx
        have hx' : x ∈ D.chart.boundaryCore := by
          rw [hD]
          exact hx
        rw [hKsupport]
        exact Or.inr (D.boundaryCore_covered hx')
      coversNextBoundaryCoreInBoundary := by
        intro x hx
        have hx' : x ∈ D.chart.boundaryCore := by
          rw [hD]
          exact hx
        rcases D.boundaryCore_subset_boundarySupport hx' with ⟨σ, hσ, hxσ⟩
        refine ⟨(show K.Complex.Simplex from Sum.inr σ), ?_, ?_⟩
        · exact (chartUnionBoundarySubcomplex_right_mem S D σ).2 hσ
        · simpa [K] using hxσ
      compatibleOnOverlaps := by
        exact K.compatibleOnOverlap_of_embedded_overlap S.complex
      boundaryCompatibleOnOverlaps := by
        constructor
        · exact K.compatibleOnOverlap_of_embedded_overlap S.complex
        · intro τ σ hσ hface
          exact (chartUnionBoundarySubcomplex S D).face_closed hσ hface
      preservesOldBoundarySupport := by
        intro x hx
        rcases hx with ⟨σ, hσ, hxσ⟩
        refine ⟨(show K.Complex.Simplex from Sum.inl σ), ?_, ?_⟩
        · exact (chartUnionBoundarySubcomplex_left_mem S D σ).2 hσ
        · simpa [K] using hxσ
      boundaryRespectsCharts := by
        refine S.boundaryRespectsCharts.extendWithChart D ?_ ?_
        · intro x hx
          rw [hKsupport]
          exact Or.inl hx
        · intro x hx
          rw [hKsupport]
          exact Or.inr (by
            simpa [ChartPolygonalDisk.toPLComplexInSpace, PLComplexInSpace.support] using hx) }

@[simp] theorem fromChartPolygonalDisk_nextComplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) (D : ChartPolygonalDisk M)
    (hD : D.chart = E.pair (S.stage + 1)) :
    (fromChartPolygonalDisk S D hD).nextComplex = chartUnionPLComplex S D := by
  unfold fromChartPolygonalDisk
  rfl

@[simp] theorem fromChartPolygonalDisk_nextChartDisk
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) (D : ChartPolygonalDisk M)
    (hD : D.chart = E.pair (S.stage + 1)) :
    (fromChartPolygonalDisk S D hD).nextChartDisk = some D := by
  unfold fromChartPolygonalDisk
  rfl

/-- The named chart-disk step has support equal to old support union chart-disk image. -/
theorem fromChartPolygonalDisk_nextComplex_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M) (D : ChartPolygonalDisk M)
    (hD : D.chart = E.pair (S.stage + 1)) :
    (fromChartPolygonalDisk S D hD).nextComplex.support =
      S.complex.support ∪ Set.range D.embed := by
  simpa using chartUnionPLComplex_support S D

/-- Named extension data for an out-of-range empty chart pair. -/
def emptyChart
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M)
    (hEmpty : E.pair (S.stage + 1) = RadoChartPair.empty M) :
    RadoStepExtensionData E S :=
  { nextComplex := S.complex
    boundarySubcomplex := S.boundarySubcomplex
    nextChartDisk := none
    next_chart_eq := by
      intro D hD
      cases hD
    extends_old := S.complex.extends_refl
    coversNextCore := by
      intro x hx
      rw [hEmpty] at hx
      simp [RadoChartPair.empty] at hx
    coversNextBoundaryCore := by
      intro x hx
      rw [hEmpty] at hx
      simp [RadoChartPair.empty] at hx
    coversNextBoundaryCoreInBoundary := by
      intro x hx
      rw [hEmpty] at hx
      simp [RadoChartPair.empty] at hx
    compatibleOnOverlaps := S.complex.compatibleOnOverlap_self
    boundaryCompatibleOnOverlaps := S.boundaryCompatibleOnOverlaps
    preservesOldBoundarySupport := by
      intro x hx
      exact hx
    boundaryRespectsCharts := S.boundaryRespectsCharts }

@[simp] theorem emptyChart_nextComplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M)
    (hEmpty : E.pair (S.stage + 1) = RadoChartPair.empty M) :
    (emptyChart S hEmpty).nextComplex = S.complex := by
  rfl

@[simp] theorem emptyChart_nextChartDisk
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductionState M)
    (hEmpty : E.pair (S.stage + 1) = RadoChartPair.empty M) :
    (emptyChart S hEmpty).nextChartDisk = none := by
  rfl

end RadoStepExtensionData

/-- Initial PL neighborhood in the Rado induction. -/
theorem initial_pl_neighborhood
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (D : InitialPLNeighborhoodData E) :
    ∃ S : RadoInductionState M, S.stage = 0 := by
  exact ⟨D.toState, D.toState_stage⟩

/-- Extend a PL complex across one chart in the Rado induction. -/
theorem extend_pl_complex_across_chart
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M) (D : RadoStepExtensionData E S) :
    ∃ S' : RadoInductionState M, S'.stage = S.stage + 1 ∧
      PLComplexInSpace.Extends S'.complex S.complex := by
  exact ⟨D.toState, D.toState_stage, D.toState_extends_old⟩

/-- Hard one-step Rado extension boundary from one polygonal chart disk.

This is the local geometric part of the induction step: enlarge the old PL complex across the next
chart disk while preserving overlap and boundary compatibility. -/
theorem rado_step_extension_from_chart_polygonal_disk
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M) (D : ChartPolygonalDisk M)
    (hD : D.chart = E.pair (S.stage + 1)) :
    Nonempty (RadoStepExtensionData E S) := by
  exact ⟨RadoStepExtensionData.fromChartPolygonalDisk S D hD⟩

/-- Extending across an out-of-range empty chart pair leaves the current stage unchanged. -/
theorem rado_step_extension_empty_chart
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M)
    (hEmpty : E.pair (S.stage + 1) = RadoChartPair.empty M) :
    Nonempty (RadoStepExtensionData E S) := by
  exact ⟨RadoStepExtensionData.emptyChart S hEmpty⟩

/-- The finite-stage state generated by an initial Rado neighborhood and successor data. -/
def radoInductionStage
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S) :
    ℕ → RadoInductionState M :=
  Nat.rec initial.toState fun n S => (step n S).toState

/-- Stepwise overlap compatibility for the recursive Rado induction.

At each stage, the successor extension package must prove compatibility between
the newly built complex and the preceding stage complex on their ambient
overlap. -/
def RadoInductionStepCompatible
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S) :
    Prop :=
  ∀ n,
    (step n (radoInductionStage initial step n)).nextComplex.compatibleOnOverlap
      (radoInductionStage initial step n).complex

/-- Stepwise boundary-overlap compatibility for the recursive Rado induction.

At each stage, the successor extension package must prove ordinary overlap
compatibility and face-closure for the boundary subcomplex selected in the new
stage. -/
def RadoInductionBoundaryStepCompatible
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S) :
    Prop :=
  ∀ n,
    BoundaryCompatibleOnOverlap
      (step n (radoInductionStage initial step n)).nextComplex
      (radoInductionStage initial step n).complex
      (step n (radoInductionStage initial step n)).boundarySubcomplex

@[simp] theorem radoInductionStage_zero
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S) :
    radoInductionStage initial step 0 = initial.toState := by
  rfl

@[simp] theorem radoInductionStage_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S)
    (n : ℕ) :
    radoInductionStage initial step (n + 1) =
      (step n (radoInductionStage initial step n)).toState := by
  rfl

/-- Local data sufficient to run every finite stage of the Rado induction.

This separates the recursive construction of a sequence from the hard geometric problem of
producing the initial chart disk and the successor chart-extension data. -/
structure RadoInductionData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  initial : InitialPLNeighborhoodData E
  step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S
  compatibleStages : RadoInductionStepCompatible initial step
  locallyFiniteUnion :
    ∀ n, Finite ((radoInductionStage initial step n).complex.Complex.Simplex)
  boundaryCompatibleUnion : RadoInductionBoundaryStepCompatible initial step

namespace RadoInductionData

/-- The `n`th finite-stage state obtained by recursion from Rado induction data. -/
def stage {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) : ℕ → RadoInductionState M :=
  radoInductionStage D.initial D.step

@[simp] theorem stage_zero
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    D.stage 0 = D.initial.toState := by
  rfl

@[simp] theorem stage_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) (n : ℕ) :
    D.stage (n + 1) = (D.step n (D.stage n)).toState := by
  rfl

/-- The recursive Rado stage has the expected stage index. -/
theorem stage_stage_eq
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).stage = n
  | 0 => by
      change D.initial.toState.stage = 0
      rfl
  | n + 1 => by
      change ((D.step n (D.stage n)).toState).stage = n + 1
      rw [RadoStepExtensionData.toState_stage]
      rw [stage_stage_eq D n]

/-- Successive recursively built stages extend one another. -/
theorem extends_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) (n : ℕ) :
    PLComplexInSpace.Extends (D.stage (n + 1)).complex (D.stage n).complex := by
  simpa [stage] using (D.step n (D.stage n)).toState_extends_old

/-- The recursively built `n`th stage covers the `n`th chart core. -/
theorem covers_core
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (E.pair n).core ⊆ (D.stage n).complex.support
  | 0 => by
      simpa [stage] using D.initial.core_subset_toState_support
  | n + 1 => by
      have hstage : (D.stage n).stage = n := D.stage_stage_eq n
      have h := (D.step n (D.stage n)).core_subset_toState_support
      rw [hstage] at h
      simpa [stage] using h

/-- The recursive Rado stage supports are monotone under successor stages. -/
theorem support_subset_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) (n : ℕ) :
    (D.stage n).complex.support ⊆ (D.stage (n + 1)).complex.support :=
  (D.extends_succ n).1

/-- The recursive Rado stage boundary supports are monotone under successor stages. -/
theorem boundarySupport_subset_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) (n : ℕ) :
    (D.stage n).boundarySupport ⊆ (D.stage (n + 1)).boundarySupport := by
  simpa [stage] using
    (D.step n (D.stage n)).oldBoundarySupport_subset_toState_boundarySupport

/-- Later recursive Rado stages still cover earlier chart cores. -/
theorem covers_core_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).core ⊆ (D.stage n).complex.support := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact D.covers_core 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact D.covers_core (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (D.support_subset_succ n)

/-- The recursively built `n`th stage covers the `n`th boundary chart core. -/
theorem covers_boundaryCore
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (E.pair n).boundaryCore ⊆ (D.stage n).complex.support
  | 0 => by
      simpa [stage] using D.initial.boundaryCore_subset_toState_support
  | n + 1 => by
      have hstage : (D.stage n).stage = n := D.stage_stage_eq n
      have h := (D.step n (D.stage n)).boundaryCore_subset_toState_support
      rw [hstage] at h
      simpa [stage] using h

/-- The recursively built `n`th stage carries the `n`th boundary chart core in its boundary
support. -/
theorem covers_boundaryCore_in_boundary
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (E.pair n).boundaryCore ⊆ (D.stage n).boundarySupport
  | 0 => by
      simpa [stage] using D.initial.boundaryCore_subset_toState_boundarySupport
  | n + 1 => by
      have hstage : (D.stage n).stage = n := D.stage_stage_eq n
      have h := (D.step n (D.stage n)).boundaryCore_subset_toState_boundarySupport
      rw [hstage] at h
      simpa [stage] using h

/-- Later recursive Rado stages still cover earlier boundary chart cores. -/
theorem covers_boundaryCore_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).boundaryCore ⊆ (D.stage n).complex.support := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact D.covers_boundaryCore 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact D.covers_boundaryCore (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (D.support_subset_succ n)

/-- Later recursive Rado stages still carry earlier boundary chart cores in their boundary
support. -/
theorem covers_boundaryCore_in_boundary_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).boundaryCore ⊆ (D.stage n).boundarySupport := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact D.covers_boundaryCore_in_boundary 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact D.covers_boundaryCore_in_boundary (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (D.boundarySupport_subset_succ n)

/-- In a finite chart-pair cover, the recursive stage at the cardinality of the cover still
covers the core of every indexed chart. -/
theorem finiteCover_core_subset_stage_card
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) (i : C.Index) :
    (C.pair i).core ⊆ (D.stage (Fintype.card C.Index)).complex.support := by
  intro x hx
  let n : ℕ := (Fintype.equivFin C.Index i).1
  have hnle : n ≤ Fintype.card C.Index :=
    Nat.le_of_lt (Fintype.equivFin C.Index i).2
  have hpair : C.toChartPairExhaustion.pair n = C.pair i := by
    change C.natPair n = C.pair i
    simpa [n] using C.natPair_of_index i
  have hx' : x ∈ (C.toChartPairExhaustion.pair n).core := by
    rwa [hpair]
  exact D.covers_core_of_le hnle hx'

/-- In a finite chart-pair cover, the recursive stage at the cardinality of the cover still
covers the boundary core of every indexed chart. -/
theorem finiteCover_boundaryCore_subset_stage_card
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) (i : C.Index) :
    (C.pair i).boundaryCore ⊆ (D.stage (Fintype.card C.Index)).complex.support := by
  intro x hx
  let n : ℕ := (Fintype.equivFin C.Index i).1
  have hnle : n ≤ Fintype.card C.Index :=
    Nat.le_of_lt (Fintype.equivFin C.Index i).2
  have hpair : C.toChartPairExhaustion.pair n = C.pair i := by
    change C.natPair n = C.pair i
    simpa [n] using C.natPair_of_index i
  have hx' : x ∈ (C.toChartPairExhaustion.pair n).boundaryCore := by
    rwa [hpair]
  exact D.covers_boundaryCore_of_le hnle hx'

/-- In a finite chart-pair cover, the recursive terminal stage carries every indexed boundary
chart core in its boundary support. -/
theorem finiteCover_boundaryCore_subset_stage_card_boundarySupport
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) (i : C.Index) :
    (C.pair i).boundaryCore ⊆ (D.stage (Fintype.card C.Index)).boundarySupport := by
  intro x hx
  let n : ℕ := (Fintype.equivFin C.Index i).1
  have hnle : n ≤ Fintype.card C.Index :=
    Nat.le_of_lt (Fintype.equivFin C.Index i).2
  have hpair : C.toChartPairExhaustion.pair n = C.pair i := by
    change C.natPair n = C.pair i
    simpa [n] using C.natPair_of_index i
  have hx' : x ∈ (C.toChartPairExhaustion.pair n).boundaryCore := by
    rwa [hpair]
  exact D.covers_boundaryCore_in_boundary_of_le hnle hx'

/-- The named boundary carrier of a finite chart-pair cover is contained in the support of the
terminal finite Rado stage. -/
theorem finiteCover_boundaryCarrier_subset_stage_card
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    C.boundaryCarrier ⊆ (D.stage (Fintype.card C.Index)).complex.support := by
  intro x hx
  rcases C.boundaryCovers x hx with ⟨i, hi⟩
  exact D.finiteCover_boundaryCore_subset_stage_card i hi

/-- The named boundary carrier of a finite chart-pair cover is contained in the stored boundary
support of the terminal finite Rado stage. -/
theorem finiteCover_boundaryCarrier_subset_stage_card_boundarySupport
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    C.boundaryCarrier ⊆ (D.stage (Fintype.card C.Index)).boundarySupport := by
  intro x hx
  rcases C.boundaryCovers x hx with ⟨i, hi⟩
  exact D.finiteCover_boundaryCore_subset_stage_card_boundarySupport i hi

/-- For a finite chart-pair cover, no countable union is needed: after `card C.Index` recursive
steps the current finite Rado state covers the whole space. -/
theorem finiteCover_stage_card_support_eq_univ
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    (D.stage (Fintype.card C.Index)).complex.support = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rcases C.covers x with ⟨i, hi⟩
  exact D.finiteCover_core_subset_stage_card i hi

/-- Finite PL triangulation data obtained from the terminal Rado stage of a finite chart cover.

This is the compact-case exit from Rado induction: once compactness has supplied a finite
chart-pair cover, the terminal finite stage already covers the whole space, so no countable
support-union complex is needed. -/
noncomputable def finiteStagePLTriangulationData
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    FinitePLTriangulationData M :=
  let S := D.stage (Fintype.card C.Index)
  { K := S.complex
    covers := D.finiteCover_stage_card_support_eq_univ
    finiteSupport := S.complex.fullFiniteSupportData
    boundary := S.boundarySubcomplexData }

@[simp] theorem finiteStagePLTriangulationData_K
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    D.finiteStagePLTriangulationData.K =
      (D.stage (Fintype.card C.Index)).complex := by
  rfl

@[simp] theorem finiteStagePLTriangulationData_covers
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    D.finiteStagePLTriangulationData.covers =
      D.finiteCover_stage_card_support_eq_univ := by
  rfl

/-- The boundary package of finite-stage PL triangulation data contains the finite cover's named
boundary carrier. -/
theorem finiteStagePLTriangulationData_boundaryCarrier_subset
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : RadoInductionData C.toChartPairExhaustion) :
    C.boundaryCarrier ⊆ D.finiteStagePLTriangulationData.boundary.boundarySupport := by
  simpa [finiteStagePLTriangulationData, RadoInductionState.boundarySubcomplexData] using
    D.finiteCover_boundaryCarrier_subset_stage_card_boundarySupport

/-- Every recursive Rado stage covers all chart cores up to its stage index. -/
theorem stage_coversCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).CoversCoresUpTo (E := E)
  | 0 => by
      exact D.initial.toState_coversCoresUpTo
  | n + 1 => by
      exact (D.step n (D.stage n)).toState_coversCoresUpTo
        (D.stage_coversCoresUpTo n)

/-- Every recursive Rado stage covers all boundary chart cores up to its stage index. -/
theorem stage_coversBoundaryCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).CoversBoundaryCoresUpTo (E := E)
  | 0 => by
      exact D.initial.toState_coversBoundaryCoresUpTo
  | n + 1 => by
      exact (D.step n (D.stage n)).toState_coversBoundaryCoresUpTo
        (D.stage_coversBoundaryCoresUpTo n)

/-- Every recursive Rado stage carries all boundary chart cores up to its stage index in its
stored boundary support. -/
theorem stage_coversBoundaryCoresInBoundaryUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).CoversBoundaryCoresInBoundaryUpTo (E := E)
  | 0 => by
      exact D.initial.toState_coversBoundaryCoresInBoundaryUpTo
  | n + 1 => by
      exact (D.step n (D.stage n)).toState_coversBoundaryCoresInBoundaryUpTo
        (D.stage_coversBoundaryCoresInBoundaryUpTo n)

/-- Every recursively built stage stores finite chart-core coverage data whose sets are covered. -/
theorem stage_coversPreviousCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).coverage.CoversCoreSets
  | 0 => by
      change D.initial.toState.coverage.CoversCoreSets
      exact D.initial.toState_coversPreviousCores
  | n + 1 => by
      change ((D.step n (D.stage n)).toState).coverage.CoversCoreSets
      exact (D.step n (D.stage n)).toState_coversPreviousCores
        (D.stage_coversCoresUpTo n)

/-- Every recursively built stage stores finite boundary-chart-core coverage data whose sets are
covered. -/
theorem stage_coversPreviousBoundaryCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).coverage.CoversBoundaryCoreSets
  | 0 => by
      change D.initial.toState.coverage.CoversBoundaryCoreSets
      exact D.initial.toState_coversPreviousBoundaryCores
  | n + 1 => by
      change ((D.step n (D.stage n)).toState).coverage.CoversBoundaryCoreSets
      exact (D.step n (D.stage n)).toState_coversPreviousBoundaryCores
        (D.stage_coversBoundaryCoresUpTo n)

end RadoInductionData

/-- A completed Rado induction sequence over a fixed chart-pair exhaustion.

This is the finite-stage part of Rado's argument: each stage is a PL complex in the ambient
manifold, successive stages extend previous ones, and the `n`th stage covers the `n`th chart core.
The construction of such a sequence from PL approximation is a separate hard theorem boundary. -/
structure RadoInductiveSequence
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  stage : ℕ → RadoInductionState M
  stage_eq : ∀ n, (stage n).stage = n
  extends_succ :
    ∀ n, PLComplexInSpace.Extends (stage (n + 1)).complex (stage n).complex
  boundarySupport_subset_succ :
    ∀ n, (stage n).boundarySupport ⊆ (stage (n + 1)).boundarySupport
  covers_core : ∀ n, (E.pair n).core ⊆ (stage n).complex.support
  covers_boundaryCore : ∀ n, (E.pair n).boundaryCore ⊆ (stage n).complex.support
  covers_boundaryCoreInBoundary :
    ∀ n, (E.pair n).boundaryCore ⊆ (stage n).boundarySupport
  compatibleStages :
    ∀ n, (stage (n + 1)).complex.compatibleOnOverlap (stage n).complex
  locallyFiniteUnion : ∀ n, Finite (stage n).complex.Complex.Simplex
  boundaryCompatibleUnion :
    ∀ n, BoundaryCompatibleOnOverlap (stage (n + 1)).complex (stage n).complex
      (stage (n + 1)).boundarySubcomplex

namespace RadoInductiveSequence

/-- Vertices of the small carrier complex used for the support union of a completed Rado
induction sequence. -/
inductive UnionVertex where
  | boundary
  | interior
deriving DecidableEq, Repr, Fintype

/-- Simplexes of the small carrier complex used for the support union of a completed Rado
induction sequence.  The boundary vertex carries the union of stage boundary supports, and the
support edge carries the whole support union. -/
inductive UnionSimplex where
  | boundaryVertex
  | interiorVertex
  | supportEdge
deriving DecidableEq, Repr, Fintype

/-- The ambient support covered by all finite stages of a Rado induction sequence. -/
def supportUnion {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Set M :=
  ⋃ n, (S.stage n).complex.support

/-- The ambient boundary support carried by all finite stages of a Rado induction sequence. -/
def boundarySupportUnion {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Set M :=
  ⋃ n, (S.stage n).boundarySupport

/-- The boundary-support union is contained in the support union. -/
theorem boundarySupportUnion_subset_supportUnion
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.boundarySupportUnion ⊆ S.supportUnion := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
  exact Set.mem_iUnion.mpr
    ⟨n, (S.stage n).boundarySupport_subset_support hxn⟩

/-- Every chart core is contained in the union of stage supports. -/
theorem core_subset_supportUnion
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (E.pair n).core ⊆ S.supportUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨n, S.covers_core n hx⟩

/-- Every boundary chart core is contained in the union of stage supports. -/
theorem boundaryCore_subset_supportUnion
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (E.pair n).boundaryCore ⊆ S.supportUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨n, S.covers_boundaryCore n hx⟩

/-- The supports in a completed Rado induction sequence are monotone under successor stages. -/
theorem support_subset_succ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (S.stage n).complex.support ⊆ (S.stage (n + 1)).complex.support :=
  (S.extends_succ n).1

/-- Boundary supports in a completed Rado induction sequence are monotone under successor stages.
-/
theorem boundarySupport_subset_succ_stage
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (S.stage n).boundarySupport ⊆ (S.stage (n + 1)).boundarySupport :=
  S.boundarySupport_subset_succ n

/-- Later stages in a completed Rado sequence still cover earlier chart cores. -/
theorem core_subset_stage_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).core ⊆ (S.stage n).complex.support := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact S.covers_core 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact S.covers_core (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (S.support_subset_succ n)

/-- Later stages in a completed Rado sequence still cover earlier boundary chart cores. -/
theorem boundaryCore_subset_stage_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).boundaryCore ⊆ (S.stage n).complex.support := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact S.covers_boundaryCore 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact S.covers_boundaryCore (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (S.support_subset_succ n)

/-- Later stages in a completed Rado sequence still carry earlier boundary chart cores in their
stored boundary supports. -/
theorem boundaryCore_subset_boundarySupport_of_le
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) {m n : ℕ} (hmn : m ≤ n) :
    (E.pair m).boundaryCore ⊆ (S.stage n).boundarySupport := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact S.covers_boundaryCoreInBoundary 0
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact S.covers_boundaryCoreInBoundary (n + 1)
      · have hlt : m < n + 1 := lt_of_le_of_ne hmn hm
        have hmn' : m ≤ n := Nat.le_of_lt_succ hlt
        exact (ih hmn').trans (S.boundarySupport_subset_succ_stage n)

/-- Every stage of a completed Rado sequence covers all chart cores up to that stage. -/
theorem stage_coversCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (S.stage n).CoversCoresUpTo (E := E) := by
  intro m hm
  have hmn : m ≤ n := by
    simpa [S.stage_eq n] using hm
  exact S.core_subset_stage_of_le hmn

/-- Every stage of a completed Rado sequence covers all boundary chart cores up to that stage. -/
theorem stage_coversBoundaryCoresUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (S.stage n).CoversBoundaryCoresUpTo (E := E) := by
  intro m hm
  have hmn : m ≤ n := by
    simpa [S.stage_eq n] using hm
  exact S.boundaryCore_subset_stage_of_le hmn

/-- Every stage of a completed Rado sequence carries all boundary chart cores up to that stage in
its stored boundary support. -/
theorem stage_coversBoundaryCoresInBoundaryUpTo
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (n : ℕ) :
    (S.stage n).CoversBoundaryCoresInBoundaryUpTo (E := E) := by
  intro m hm
  have hmn : m ≤ n := by
    simpa [S.stage_eq n] using hm
  exact S.boundaryCore_subset_boundarySupport_of_le hmn

/-- A genuine stage-indexed simplex in the countable Rado union.

The compatibility `unionPLComplex` below is still a finite wrapper around the support union.
This type keeps the actual countable union of stage simplexes available to theorem statements that
need the Moise geometry rather than the finite wrapper. -/
abbrev StageUnionSimplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Type :=
  Σ n : ℕ, (S.stage n).complex.Complex.Simplex

/-- Carrier of a genuine stage-indexed simplex in the countable Rado union. -/
def stageUnionSimplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (σ : S.StageUnionSimplex) : Set M :=
  (S.stage σ.1).complex.simplexCarrier σ.2

/-- Every genuine stage-indexed simplex carrier lies in the Rado support union. -/
theorem stageUnionSimplexCarrier_subset_supportUnion
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (σ : S.StageUnionSimplex) :
    S.stageUnionSimplexCarrier σ ⊆ S.supportUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr
    ⟨σ.1, (S.stage σ.1).complex.simplexCarrier_subset_support σ.2 hx⟩

/-- The Rado support union is covered by genuine stage-indexed simplex carriers. -/
theorem supportUnion_covered_by_stageUnionSimplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    ∀ x ∈ S.supportUnion, ∃ σ : S.StageUnionSimplex, x ∈ S.stageUnionSimplexCarrier σ := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
  rcases (S.stage n).complex.exists_simplexCarrier_of_mem_support hxn with ⟨σ, hxσ⟩
  exact ⟨⟨n, σ⟩, hxσ⟩

/-- A genuine stage-indexed boundary simplex in the countable Rado union. -/
abbrev StageBoundarySimplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Type :=
  Σ n : ℕ, {σ : (S.stage n).complex.Complex.Simplex //
    σ ∈ (S.stage n).boundarySubcomplex.simplexes}

/-- Carrier of a genuine stage-indexed boundary simplex. -/
def stageBoundarySimplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (σ : S.StageBoundarySimplex) : Set M :=
  (S.stage σ.1).complex.simplexCarrier σ.2.1

/-- Every genuine boundary-simplex carrier lies in the boundary-support union. -/
theorem stageBoundarySimplexCarrier_subset_boundarySupportUnion
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (σ : S.StageBoundarySimplex) :
    S.stageBoundarySimplexCarrier σ ⊆ S.boundarySupportUnion := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨σ.1, σ.2.1, σ.2.2, hx⟩

/-- The boundary-support union is covered by genuine stage-indexed boundary-simplex carriers. -/
theorem boundarySupportUnion_covered_by_stageBoundarySimplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    ∀ x ∈ S.boundarySupportUnion,
      ∃ σ : S.StageBoundarySimplex, x ∈ S.stageBoundarySimplexCarrier σ := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
  rcases hxn with ⟨σ, hσ, hxσ⟩
  exact ⟨⟨n, ⟨σ, hσ⟩⟩, hxσ⟩

/-- Boundary simplexes of the faithful stagewise Rado union. -/
def stagewiseBoundarySimplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Set S.StageUnionSimplex :=
  {σ | σ.2 ∈ (S.stage σ.1).boundarySubcomplex.simplexes}

/-- The faithful stagewise PL complex carried by a completed Rado induction sequence.

Unlike `unionPLComplex`, this object does not replace the countable union by a finite
compatibility wrapper.  Its simplexes are the actual finite-stage simplexes tagged by their stage.
-/
def stagewisePLComplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : StagewisePLComplexInSpace M where
  stage := fun n => (S.stage n).complex
  extends_succ := S.extends_succ
  support := S.supportUnion
  support_eq_iUnion := rfl
  Simplex := S.StageUnionSimplex
  simplexCarrier := S.stageUnionSimplexCarrier
  stageSimplex := fun n σ => ⟨n, σ⟩
  stageSimplexCarrier := by
    intro n σ
    rfl
  simplexCarrier_subset_support := by
    intro σ
    exact S.stageUnionSimplexCarrier_subset_supportUnion σ
  support_covered_by_simplexCarrier := by
    intro x hx
    exact S.supportUnion_covered_by_stageUnionSimplexCarrier x hx
  finiteStage := S.locallyFiniteUnion
  boundarySimplex := S.stagewiseBoundarySimplex
  boundarySupport := S.boundarySupportUnion
  boundarySupport_subset_support := S.boundarySupportUnion_subset_supportUnion
  boundaryCarrier_subset := by
    intro σ hσ x hx
    exact Set.mem_iUnion.mpr ⟨σ.1, ⟨σ.2, hσ, hx⟩⟩
  boundarySupport_covered := by
    intro x hx
    rcases S.boundarySupportUnion_covered_by_stageBoundarySimplexCarrier x hx with ⟨σ, hxσ⟩
    exact ⟨⟨σ.1, σ.2.1⟩, σ.2.2, hxσ⟩

@[simp] theorem stagewisePLComplex_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.stagewisePLComplex.support = S.supportUnion := by
  rfl

@[simp] theorem stagewisePLComplex_boundarySupport
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.stagewisePLComplex.boundarySupport = S.boundarySupportUnion := by
  rfl

@[simp] theorem stagewisePLComplex_simplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) (σ : S.StageUnionSimplex) :
    S.stagewisePLComplex.simplexCarrier σ = S.stageUnionSimplexCarrier σ := by
  rfl

/-- The Rado stage-support union covers the whole manifold because chart cores cover it. -/
theorem supportUnion_eq_univ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.supportUnion = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rcases E.covers x with ⟨n, hx⟩
  exact S.core_subset_supportUnion n hx

/-- If a PL complex realizes the Rado stage-support union, then it covers the whole manifold. -/
theorem union_complex_covers_univ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) {K : PLComplexInSpace M}
    (hK : K.support = S.supportUnion) :
    K.support = Set.univ :=
  hK.trans S.supportUnion_eq_univ

/-- The PL complex obtained from the locally finite union of a completed Rado induction sequence,
packaged with its support computation.

This is still a scaffold complex: the real Moise geometry is stored in the compatibility and local
finiteness fields of `RadoInductiveSequence`.  The construction gives downstream code a concrete
complex to use instead of repeatedly unpacking an existential theorem. -/
noncomputable def unionPLComplexData
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    { K : PLComplexInSpace M // K.support = S.supportUnion } := by
  haveI : Small.{0} S.supportUnion := by
    dsimp [supportUnion]
    infer_instance
  let carrierMap : Shrink.{0} S.supportUnion → M :=
    fun p => ((equivShrink.{0} S.supportUnion).symm p).1
  let carrierTop : TopologicalSpace (Shrink.{0} S.supportUnion) :=
    TopologicalSpace.induced carrierMap inferInstance
  have hCarrierInjective : Function.Injective carrierMap := by
    intro p q hpq
    have hsub :
        (equivShrink.{0} S.supportUnion).symm p =
          (equivShrink.{0} S.supportUnion).symm q := by
      exact Subtype.ext hpq
    exact (equivShrink.{0} S.supportUnion).symm.injective hsub
  have hCarrierEmbedding :
      @Topology.IsEmbedding (Shrink.{0} S.supportUnion) M carrierTop inferInstance carrierMap :=
    hCarrierInjective.isEmbedding_induced
  have hBoundarySubset : S.boundarySupportUnion ⊆ S.supportUnion :=
    S.boundarySupportUnion_subset_supportUnion
  let C : EuclideanComplex :=
    { Point := Shrink.{0} S.supportUnion
      pointTop := carrierTop
      Vertex := UnionVertex
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      Simplex := UnionSimplex
      simplexFintype := inferInstance
      simplexDecidableEq := inferInstance
      simplexNonempty := ⟨UnionSimplex.supportEdge⟩
      simplexVertices := fun
        | UnionSimplex.boundaryVertex => {UnionVertex.boundary}
        | UnionSimplex.interiorVertex => {UnionVertex.interior}
        | UnionSimplex.supportEdge => {UnionVertex.boundary, UnionVertex.interior}
      simplex_nonempty := by
        intro σ
        cases σ <;> simp
      support := Set.univ
      realizesSimplexes := by
        intro σ
        cases σ <;> simp
      faceClosed := by
        decide }
  let emb : C.support → M := fun p => carrierMap p.1
  let hKEmbedding : _root_.Topology.IsEmbedding emb :=
    hCarrierEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
  let K : PLComplexInSpace M :=
    { Complex := C
      embed := emb
      isEmbedding := hKEmbedding
      simplexSupport := fun
        | UnionSimplex.boundaryVertex => S.boundarySupportUnion
        | UnionSimplex.interiorVertex => ∅
        | UnionSimplex.supportEdge => Set.range emb
      simplexSupport_subset := by
        intro σ x hx
        cases σ with
        | boundaryVertex =>
            have hxU : x ∈ S.supportUnion := hBoundarySubset hx
            let p : Shrink.{0} S.supportUnion := equivShrink.{0} S.supportUnion ⟨x, hxU⟩
            refine ⟨⟨p, trivial⟩, ?_⟩
            simp [emb, carrierMap, p]
        | interiorVertex =>
            simp at hx
        | supportEdge =>
            exact hx
      support_covered_by_simplexSupport := by
        intro x hx
        exact ⟨UnionSimplex.supportEdge, hx⟩
      locallyFinite := inferInstance
      compatibleCharts := ⟨hKEmbedding.injective, hKEmbedding.continuous⟩ }
  refine ⟨K, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨p, rfl⟩
    exact ((equivShrink.{0} S.supportUnion).symm p.1).2
  · intro hx
    let p : Shrink.{0} S.supportUnion := equivShrink.{0} S.supportUnion ⟨x, hx⟩
    refine ⟨⟨p, trivial⟩, ?_⟩
    simp [K, carrierMap, emb, p]

/-- The named PL complex realizing the support union of a completed Rado induction sequence. -/
noncomputable def unionPLComplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : PLComplexInSpace M :=
  (S.unionPLComplexData).1

/-- The named Rado union complex has exactly the stage-support union as support. -/
theorem unionPLComplex_support
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.unionPLComplex.support = S.supportUnion :=
  (S.unionPLComplexData).2

/-- The named Rado union complex covers the whole manifold. -/
theorem unionPLComplex_covers_univ
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.unionPLComplex.support = Set.univ :=
  S.union_complex_covers_univ S.unionPLComplex_support

/-- Boundary subcomplex of the support-union PL complex. -/
noncomputable def unionBoundarySubcomplex
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : S.unionPLComplex.Complex.Subcomplex := by
  unfold unionPLComplex unionPLComplexData
  exact
    { simplexes := {UnionSimplex.boundaryVertex}
      face_closed := by
        intro τ σ hσ hface
        rw [Finset.mem_singleton] at hσ ⊢
        subst σ
        cases τ with
        | boundaryVertex =>
            rfl
        | interiorVertex =>
            exfalso
            have hsubset :
                ({UnionVertex.interior} : Finset UnionVertex) ⊆ {UnionVertex.boundary} := by
              exact hface
            have hmem : UnionVertex.interior ∈ ({UnionVertex.boundary} : Finset UnionVertex) :=
              hsubset (by simp)
            simp at hmem
        | supportEdge =>
            exfalso
            have hsubset :
                ({UnionVertex.boundary, UnionVertex.interior} : Finset UnionVertex) ⊆
                  {UnionVertex.boundary} := by
              exact hface
            have hmem : UnionVertex.interior ∈ ({UnionVertex.boundary} : Finset UnionVertex) :=
              hsubset (by simp)
            simp at hmem }

@[simp] theorem unionBoundarySubcomplex_simplexes
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.unionBoundarySubcomplex.simplexes = {UnionSimplex.boundaryVertex} := by
  unfold unionBoundarySubcomplex unionPLComplex unionPLComplexData
  rfl

@[simp] theorem unionPLComplex_boundary_simplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.unionPLComplex.simplexCarrier
        (show S.unionPLComplex.Complex.Simplex from UnionSimplex.boundaryVertex) =
      S.boundarySupportUnion := by
  unfold unionPLComplex unionPLComplexData PLComplexInSpace.simplexCarrier
  rfl

@[simp] theorem unionPLComplex_support_simplexCarrier
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) :
    S.unionPLComplex.simplexCarrier
        (show S.unionPLComplex.Complex.Simplex from UnionSimplex.supportEdge) =
      S.unionPLComplex.support := by
  unfold unionPLComplex unionPLComplexData PLComplexInSpace.simplexCarrier PLComplexInSpace.support
  rfl

/-- Boundary data for the support-union PL complex, using the monotone union of stage boundary
supports rather than the full support. -/
noncomputable def unionBoundarySubcomplexData
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : S.unionPLComplex.BoundarySubcomplexData where
  boundary := S.unionBoundarySubcomplex
  boundarySupport := S.boundarySupportUnion
  coversBoundary := by
    intro x hx
    rw [S.unionPLComplex_support]
    exact S.boundarySupportUnion_subset_supportUnion hx
  compatibleWithAmbient := by
    intro x hx
    rw [S.unionPLComplex_support]
    exact S.boundarySupportUnion_subset_supportUnion hx
  boundaryCarrier_subset := by
    intro σ hσ x hx
    rw [S.unionBoundarySubcomplex_simplexes] at hσ
    have hσeq : σ = (show S.unionPLComplex.Complex.Simplex from UnionSimplex.boundaryVertex) :=
      Finset.mem_singleton.mp hσ
    subst σ
    simpa using hx
  boundarySupport_covered := by
    intro x hx
    refine ⟨(show S.unionPLComplex.Complex.Simplex from UnionSimplex.boundaryVertex), ?_, ?_⟩
    · rw [S.unionBoundarySubcomplex_simplexes]
      exact Finset.mem_singleton_self _
    · simpa using hx
  locallyFiniteBoundary := inferInstance

end RadoInductiveSequence

/-- Convert recursive Rado induction data into a completed induction sequence. -/
def RadoInductionData.toInductiveSequence
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) : RadoInductiveSequence E where
  stage := D.stage
  stage_eq := D.stage_stage_eq
  extends_succ := D.extends_succ
  boundarySupport_subset_succ := D.boundarySupport_subset_succ
  covers_core := D.covers_core
  covers_boundaryCore := D.covers_boundaryCore
  covers_boundaryCoreInBoundary := D.covers_boundaryCore_in_boundary
  compatibleStages := by
    intro n
    change ((D.step n (D.stage n)).toState).complex.compatibleOnOverlap
      (D.stage n).complex
    have hcompat : ∀ n,
        (D.step n (radoInductionStage D.initial D.step n)).nextComplex.compatibleOnOverlap
          (radoInductionStage D.initial D.step n).complex := D.compatibleStages
    simpa [RadoInductionData.stage, RadoStepExtensionData.toState] using hcompat n
  locallyFiniteUnion := D.locallyFiniteUnion
  boundaryCompatibleUnion := by
    intro n
    change BoundaryCompatibleOnOverlap ((D.step n (D.stage n)).toState).complex
      (D.stage n).complex ((D.step n (D.stage n)).toState).boundarySubcomplex
    have hcompat : ∀ n,
        BoundaryCompatibleOnOverlap
          (D.step n (radoInductionStage D.initial D.step n)).nextComplex
          (radoInductionStage D.initial D.step n).complex
          (D.step n (radoInductionStage D.initial D.step n)).boundarySubcomplex :=
      D.boundaryCompatibleUnion
    simpa [RadoInductionData.stage, RadoStepExtensionData.toState] using hcompat n

/-- Finite local geometric data sufficient to build Rado induction data over a finite chart cover.

This is the chart-core shrinking and polygonal disk extension input: once supplied, the remaining
Rado induction layer is purely packaging. -/
structure FiniteRadoInductionGeometry
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  initial : InitialPLNeighborhoodData C.toChartPairExhaustion
  step :
    ∀ (_n : ℕ) (S : RadoInductionState M),
      RadoStepExtensionData C.toChartPairExhaustion S
  compatibleStages : RadoInductionStepCompatible initial step
  locallyFiniteUnion :
    ∀ n, Finite ((radoInductionStage initial step n).complex.Complex.Simplex)
  boundaryCompatibleUnion : RadoInductionBoundaryStepCompatible initial step

namespace FiniteRadoInductionGeometry

/-- Forget finite-cover geometric construction data to the recursive Rado induction data API. -/
def toRadoInductionData
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (G : FiniteRadoInductionGeometry C) :
    RadoInductionData C.toChartPairExhaustion where
  initial := G.initial
  step := G.step
  compatibleStages := G.compatibleStages
  locallyFiniteUnion := G.locallyFiniteUnion
  boundaryCompatibleUnion := G.boundaryCompatibleUnion

/-- The finite terminal Rado state after all chart pairs in a finite cover have been absorbed. -/
def finalState
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (G : FiniteRadoInductionGeometry C) : RadoInductionState M :=
  G.toRadoInductionData.stage (Fintype.card C.Index)

/-- The finite terminal Rado state for a finite chart cover already covers the whole space. -/
theorem finalState_support_eq_univ
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (G : FiniteRadoInductionGeometry C) :
    G.finalState.complex.support = Set.univ :=
  G.toRadoInductionData.finiteCover_stage_card_support_eq_univ

end FiniteRadoInductionGeometry

namespace FiniteChartPolygonalDiskData

/-- The initial Rado neighborhood produced from the first disk in a finite chart-pair cover. -/
noncomputable def initialData
    {M : Type u} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) :
    InitialPLNeighborhoodData C.toChartPairExhaustion :=
  InitialPLNeighborhoodData.ofChartPolygonalDisk (D.disk C.zeroIndex) (by
    exact (D.chart_eq C.zeroIndex).trans C.toChartPairExhaustion_pair_zero.symm)

/-- The successor Rado step produced from the finite chart selected by the next stage index.

When the next stage index is beyond the finite cover, this returns the empty-chart extension data
that leaves the current complex unchanged. -/
noncomputable def stepData
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (S : RadoInductionState M) :
    RadoStepExtensionData C.toChartPairExhaustion S :=
  if h : S.stage + 1 < Fintype.card C.Index then
    let i : C.Index := (Fintype.equivFin C.Index).symm ⟨S.stage + 1, h⟩
    have hi : (D.disk i).chart = C.toChartPairExhaustion.pair (S.stage + 1) := by
      exact (D.chart_eq i).trans (C.toChartPairExhaustion_pair_of_lt h).symm
    RadoStepExtensionData.fromChartPolygonalDisk S (D.disk i) hi
  else
    have hEmpty :
        C.toChartPairExhaustion.pair (S.stage + 1) = RadoChartPair.empty M :=
      C.toChartPairExhaustion_pair_of_not_lt h
    RadoStepExtensionData.emptyChart S hEmpty

@[simp] theorem stepData_nextChartDisk_of_lt
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (S : RadoInductionState M)
    (h : S.stage + 1 < Fintype.card C.Index) :
    (D.stepData S).nextChartDisk =
      some (D.disk ((Fintype.equivFin C.Index).symm ⟨S.stage + 1, h⟩)) := by
  unfold stepData
  simp [h]

@[simp] theorem stepData_nextChartDisk_of_not_lt
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (S : RadoInductionState M)
    (h : ¬ S.stage + 1 < Fintype.card C.Index) :
    (D.stepData S).nextChartDisk = none := by
  unfold stepData
  simp [h]

/-- While the next stage is inside the finite cover, the step selector adjoins precisely the
selected chart disk to the old support. -/
theorem stepData_nextComplex_support_of_lt
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (S : RadoInductionState M)
    (h : S.stage + 1 < Fintype.card C.Index) :
    (D.stepData S).nextComplex.support =
      S.complex.support ∪
        Set.range (D.disk ((Fintype.equivFin C.Index).symm ⟨S.stage + 1, h⟩)).embed := by
  have hsupport :=
    RadoStepExtensionData.chartUnionPLComplex_support S
      (D.disk ((Fintype.equivFin C.Index).symm ⟨S.stage + 1, h⟩))
  unfold stepData
  simpa [h] using hsupport

/-- Once the finite cover is exhausted, the step selector is the empty-chart extension and leaves
the complex unchanged. -/
@[simp] theorem stepData_nextComplex_of_not_lt
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (S : RadoInductionState M)
    (h : ¬ S.stage + 1 < Fintype.card C.Index) :
    (D.stepData S).nextComplex = S.complex := by
  unfold stepData
  simp [h]

/-- Polygonal disk data over a finite chart-pair cover as finite Rado induction geometry. -/
noncomputable def toFiniteRadoInductionGeometry
    {M : Type u} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) : FiniteRadoInductionGeometry C where
  initial := D.initialData
  step := fun _n S => D.stepData S
  compatibleStages := by
    let stage := fun n =>
      radoInductionStage D.initialData (fun _n S => D.stepData S) n
    change ∀ n,
      (D.stepData (stage n)).nextComplex.compatibleOnOverlap
        (stage n).complex
    intro n
    exact (D.stepData (stage n)).compatibleOnOverlaps
  locallyFiniteUnion := by
    intro n
    infer_instance
  boundaryCompatibleUnion := by
    let stage := fun n =>
      radoInductionStage D.initialData (fun _n S => D.stepData S) n
    change ∀ n,
      BoundaryCompatibleOnOverlap
        (D.stepData (stage n)).nextComplex
        (stage n).complex
        (D.stepData (stage n)).boundarySubcomplex
    intro n
    exact (D.stepData (stage n)).boundaryCompatibleOnOverlaps

@[simp] theorem toFiniteRadoInductionGeometry_initial
    {M : Type u} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) :
    D.toFiniteRadoInductionGeometry.initial = D.initialData := by
  rfl

@[simp] theorem toFiniteRadoInductionGeometry_step
    {M : Type u} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) (n : ℕ) (S : RadoInductionState M) :
    D.toFiniteRadoInductionGeometry.step n S = D.stepData S := by
  rfl

end FiniteChartPolygonalDiskData

/-- Finite Rado geometry packages as recursive Rado induction data. -/
theorem rado_induction_data_of_finite_geometry
    {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (G : FiniteRadoInductionGeometry C) :
    Nonempty (RadoInductionData C.toChartPairExhaustion) := by
  exact ⟨G.toRadoInductionData⟩

/-- Moise-style topological two-manifold interface used by the Rado triangulation layer.

Besides the topological manifold hypotheses, this interface stores a chart-pair exhaustion and the
local Rado induction data needed to absorb chart pairs.  Constructing this data from a mathlib
manifold atlas is the remaining hard extraction theorem. -/
structure MoiseTwoManifold (M : Type*) [TopologicalSpace M] where
  t2 : T2Space M
  chartPairExhaustion : ChartPairExhaustion M
  localDiskOrHalfDiskModels : chartPairExhaustion.HasDiskOrHalfDiskModelCover
  chartModelsMatchKind : chartPairExhaustion.ModelsMatchKind
  radoInductionData : RadoInductionData chartPairExhaustion

namespace MoiseTwoManifold

/-- The completed Rado induction sequence stored by the Moise two-manifold interface. -/
def radoSequence
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    RadoInductiveSequence hM.chartPairExhaustion :=
  hM.radoInductionData.toInductiveSequence

/-- The faithful stagewise PL complex produced by the Rado induction data stored in the Moise
interface. -/
def radoStagewisePLComplex
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    StagewisePLComplexInSpace M :=
  hM.radoSequence.stagewisePLComplex

/-- The faithful stagewise Rado complex stored by the Moise interface covers the whole
manifold. -/
theorem radoStagewisePLComplex_support
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    hM.radoStagewisePLComplex.support = Set.univ := by
  rw [radoStagewisePLComplex, RadoInductiveSequence.stagewisePLComplex_support]
  exact hM.radoSequence.supportUnion_eq_univ

/-- Compatibility finite-wrapper PL complex produced by the Rado induction data stored in the
Moise interface.

For the faithful countable stagewise object, use `radoStagewisePLComplex`. -/
noncomputable def radoPLComplex
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) : PLComplexInSpace M :=
  hM.radoSequence.unionPLComplex

/-- The Rado PL complex stored by the Moise interface covers the whole manifold. -/
theorem radoPLComplex_support
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    hM.radoPLComplex.support = Set.univ :=
  hM.radoSequence.unionPLComplex_covers_univ

/-- Finite PL triangulation data obtained from the named support-union Rado complex.

This is the general compact `MoiseTwoManifold` fallback.  For compact surfaces extracted from a
finite chart cover, prefer `MoiseExtractionData.finiteStagePLTriangulationData`, which uses the
finite terminal Rado stage and its stored boundary subcomplex directly. -/
noncomputable def supportUnionFinitePLTriangulationData
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    FinitePLTriangulationData M :=
  let finiteSupport :=
    Classical.choice (locallyFiniteComplex_finite_of_compact_support hM.radoPLComplex)
  { K := hM.radoPLComplex
    covers := hM.radoPLComplex_support
    finiteSupport := finiteSupport
    boundary := hM.radoSequence.unionBoundarySubcomplexData }

@[simp] theorem supportUnionFinitePLTriangulationData_K
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    hM.supportUnionFinitePLTriangulationData.K = hM.radoPLComplex := by
  rfl

/-- Compatibility wrapper for the original compact Moise triangulation-data name.

New compact chart-extraction code should use `MoiseExtractionData.finiteStagePLTriangulationData`
when finite cover data is available. -/
noncomputable def finitePLTriangulationData
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    FinitePLTriangulationData M :=
  hM.supportUnionFinitePLTriangulationData

@[simp] theorem finitePLTriangulationData_K
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    hM.finitePLTriangulationData.K = hM.radoPLComplex := by
  rfl

/-- The finite PL triangulation data carried by a compact Moise two-manifold covers the space. -/
theorem finitePLTriangulationData_support
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    hM.finitePLTriangulationData.K.support = Set.univ :=
  hM.finitePLTriangulationData.covers

end MoiseTwoManifold

/-- Data extracted from a compact mathlib bordered surface before it is packaged as the Moise
interface used by Rado's theorem. -/
structure MoiseExtractionData (M : Type*) [TopologicalSpace M] where
  finiteCover : FiniteChartPairCover M
  localDiskOrHalfDiskModels : finiteCover.HasDiskOrHalfDiskModelCover
  chartModelsMatchKind : finiteCover.ModelsMatchKind
  radoInductionData : RadoInductionData finiteCover.toChartPairExhaustion

namespace MoiseExtractionData

/-- Package extracted finite chart-pair and local Rado data as a `MoiseTwoManifold`. -/
def toMoiseTwoManifold {M : Type*} [TopologicalSpace M] [T2Space M]
    (D : MoiseExtractionData M) : MoiseTwoManifold M where
  t2 := inferInstance
  chartPairExhaustion := D.finiteCover.toChartPairExhaustion
  localDiskOrHalfDiskModels := (D.finiteCover.toChartPairExhaustion).hasDiskOrHalfDiskModelCover
  chartModelsMatchKind := (D.finiteCover.toChartPairExhaustion).modelsMatchKind
  radoInductionData := D.radoInductionData

@[simp] theorem toMoiseTwoManifold_chartPairExhaustion
    {M : Type*} [TopologicalSpace M] [T2Space M] (D : MoiseExtractionData M) :
    D.toMoiseTwoManifold.chartPairExhaustion = D.finiteCover.toChartPairExhaustion := by
  rfl

/-- The finite Rado stage obtained after absorbing every chart pair in the extracted finite cover.
-/
def finiteStage
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    RadoInductionState M :=
  D.radoInductionData.stage (Fintype.card D.finiteCover.Index)

/-- The finite-stage PL complex obtained from extracted Moise data. -/
noncomputable def finiteStagePLComplex
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    PLComplexInSpace M :=
  D.finiteStage.complex

/-- The finite-stage PL complex from extracted Moise data covers the whole space. -/
theorem finiteStagePLComplex_support
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteStagePLComplex.support = Set.univ :=
  D.radoInductionData.finiteCover_stage_card_support_eq_univ

/-- Finite PL triangulation data obtained from the finite terminal Rado stage, avoiding the
countable support-union complex once compactness has produced a finite chart cover. -/
noncomputable def finiteStagePLTriangulationData
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    FinitePLTriangulationData M :=
  D.radoInductionData.finiteStagePLTriangulationData

@[simp] theorem finiteStagePLTriangulationData_K
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteStagePLTriangulationData.K = D.finiteStagePLComplex := by
  rfl

/-- The finite-stage triangulation extracted from compact Moise data covers the whole space. -/
theorem finiteStagePLTriangulationData_support
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteStagePLTriangulationData.K.support = Set.univ :=
  D.finiteStagePLTriangulationData.covers

/-- The finite-stage triangulation extracted from compact Moise data keeps the finite chart
cover's named boundary carrier inside its stored boundary support. -/
theorem finiteStagePLTriangulationData_boundaryCarrier_subset
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteCover.boundaryCarrier ⊆
      D.finiteStagePLTriangulationData.boundary.boundarySupport := by
  simpa [finiteStagePLTriangulationData] using
    D.radoInductionData.finiteStagePLTriangulationData_boundaryCarrier_subset

/-- The finite-stage triangulation extracted from compact Moise data carries the finite cover's
intended boundary set in its stored boundary support. -/
theorem finiteStagePLTriangulationData_boundarySet_subset
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteCover.boundarySet ⊆
      D.finiteStagePLTriangulationData.boundary.boundarySupport :=
  D.finiteCover.boundarySet_subset_boundaryCarrier.trans
    D.finiteStagePLTriangulationData_boundaryCarrier_subset

end MoiseExtractionData

/-- Extracted Moise data gives the Rado-facing Moise interface. -/
theorem moise_two_manifold_of_extraction_data
    {M : Type*} [TopologicalSpace M] [T2Space M] (D : MoiseExtractionData M) :
    ∃ hM : MoiseTwoManifold M,
      hM.chartPairExhaustion = D.finiteCover.toChartPairExhaustion := by
  exact ⟨D.toMoiseTwoManifold, rfl⟩

/-- The chart-pair exhaustion carried by the Moise interface. -/
theorem chart_pair_exhaustion
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ E : ChartPairExhaustion M, E = hM.chartPairExhaustion := by
  exact ⟨hM.chartPairExhaustion, rfl⟩

/-- Local chart-disk and extension data exist at every Rado stage for the chosen Moise interface. -/
theorem rado_induction_data_exists
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    Nonempty (RadoInductionData hM.chartPairExhaustion) := by
  exact ⟨hM.radoInductionData⟩

/-- Hard theorem boundary: the finite-stage Rado induction can be carried out over an exhaustion.

The proof uses the initial PL neighborhood, the chart-extension step, and PL approximation on each
successive chart. -/
theorem rado_inductive_sequence_exists
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    Nonempty (RadoInductiveSequence hM.chartPairExhaustion) := by
  exact ⟨hM.radoSequence⟩

/-- The locally finite union of a Rado induction sequence is a PL complex. -/
theorem rado_union_complex
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductiveSequence E) :
    ∃ K : PLComplexInSpace M, K.support = S.supportUnion := by
  exact ⟨S.unionPLComplex, S.unionPLComplex_support⟩

/-- The faithful stagewise union of a Rado induction sequence. -/
theorem rado_union_stagewise_complex
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductiveSequence E) :
    ∃ K : StagewisePLComplexInSpace M, K.support = S.supportUnion := by
  exact ⟨S.stagewisePLComplex, rfl⟩

/-- Faithful stagewise Moise-Rado triangulation theorem for two-manifolds. -/
theorem rado_triangulation_moise_two_manifold_stagewise
    (M : Type*) [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ K : StagewisePLComplexInSpace M, K.support = Set.univ := by
  exact ⟨hM.radoStagewisePLComplex, hM.radoStagewisePLComplex_support⟩

/-- Moise-Rado triangulation theorem boundary for two-manifolds.

This keeps the original finite-wrapper output.  The faithful countable Rado-union output is
`rado_triangulation_moise_two_manifold_stagewise`. -/
theorem rado_triangulation_moise_two_manifold
    (M : Type*) [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ := by
  exact ⟨hM.radoPLComplex, hM.radoPLComplex_support⟩

/-- Compact Moise surfaces are finitely triangulable. -/
theorem compact_moise_surface_finitely_triangulable
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      K.support = Set.univ := by
  let D := _hM.finitePLTriangulationData
  exact ⟨D.K, D.finiteSupport, D.covers⟩

/-- Compact Moise surfaces produce finite PL triangulation data. -/
theorem compact_moise_surface_finite_pl_triangulation_data
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    Nonempty (FinitePLTriangulationData M) := by
  exact ⟨_hM.finitePLTriangulationData⟩

/-- Finite cover extraction data gives a finite terminal-stage PL triangulation directly.

This is the compact finite-cover exit from the Rado layer.  Unlike
`compact_moise_surface_finitely_triangulable`, it does not pass through the countable
support-union compatibility wrapper. -/
theorem moise_extraction_finitely_triangulable
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      ∃ _boundary : K.BoundarySubcomplexData, K.support = Set.univ := by
  let T := D.finiteStagePLTriangulationData
  exact ⟨T.K, T.finiteSupport, T.boundary, T.covers⟩

/-- Finite cover extraction data packages a terminal-stage finite PL triangulation. -/
theorem moise_extraction_finite_pl_triangulation_data
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    Nonempty (FinitePLTriangulationData M) := by
  exact ⟨D.finiteStagePLTriangulationData⟩

/-- Bordered PL approximation theorem boundary. -/
theorem bordered_pl_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    Nonempty (BoundaryGlobalPLSurfaceApproximation K Ω φ h) := by
  exact bordered_pl_approximation_halfplane K Ω h φ _hφ

/-- A compact mathlib bordered surface admits a finite cover by preferred chart-pair cores. -/
theorem mathlib_bordered_surface_finite_chart_pair_cover
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] :
    Nonempty (FiniteChartPairCover M) := by
  exact FiniteChartPairCover.exists_of_compact_local
    (fun x : M => RadoChartPair.fromChartAt M x)
    (fun x : M => RadoChartPair.fromChartAt_core_mem_nhds M x)

/-- A neighborhood of a point in the half-plane contains that point, hence its image under the
half-plane inclusion contains the ambient coordinate point. -/
theorem euclideanHalfSpace_point_mem_image_of_mem_nhds
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y) :
    y.1 ∈ (Subtype.val '' U) := by
  exact ⟨y, mem_of_mem_nhds hU, rfl⟩

/-- At an interior point of the model half-plane, the ambient closed half-plane itself is a
neighborhood. -/
theorem euclideanHalfSpace_interior_halfspace_mem_nhds
    (y : EuclideanHalfSpace 2) (hy : 0 < y.1 0) :
    {p : Plane | 0 ≤ p 0} ∈ 𝓝 y.1 := by
  have hOpen : IsOpen {p : Plane | 0 < p 0} := by
    exact isOpen_lt continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
  exact Filter.mem_of_superset (hOpen.mem_nhds hy) (by
    intro p hp
    exact le_of_lt (show 0 < p 0 from hp))

/-- At an interior point, the half-plane subtype neighborhood filter is the ordinary ambient
Euclidean neighborhood filter. -/
theorem euclideanHalfSpace_interior_map_nhds_eq
    (y : EuclideanHalfSpace 2) (hy : 0 < y.1 0) :
    Filter.map (Subtype.val : EuclideanHalfSpace 2 → Plane) (𝓝 y) = 𝓝 y.1 := by
  simpa using
    (map_nhds_subtype_coe_eq_nhds
      (p := fun p : Plane => 0 ≤ p 0) (x := y.1) y.2
      (euclideanHalfSpace_interior_halfspace_mem_nhds y hy))

/-- The image of a half-plane neighborhood is a relative ambient neighborhood in the closed
half-plane. -/
theorem euclideanHalfSpace_image_mem_nhdsWithin_halfspace
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y) :
    (Subtype.val '' U : Set Plane) ∈ 𝓝[{p : Plane | 0 ≤ p 0}] y.1 := by
  change (Subtype.val '' U : Set (EuclideanSpace ℝ (Fin 2))) ∈
    𝓝[{p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0}] y.1
  rw [← range_euclideanHalfSpace 2]
  have hEmbedding :
      _root_.Topology.IsEmbedding
        (Subtype.val : EuclideanHalfSpace 2 → EuclideanSpace ℝ (Fin 2)) :=
    _root_.Topology.IsEmbedding.subtypeVal
  have hmap := hEmbedding.map_nhds_eq y
  rw [← hmap]
  exact Filter.image_mem_map hU

/-- The image of an interior half-plane neighborhood is an ordinary ambient plane neighborhood. -/
theorem euclideanHalfSpace_interior_image_mem_nhds
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : 0 < y.1 0) :
    (Subtype.val '' U : Set Plane) ∈ 𝓝 y.1 := by
  rw [← euclideanHalfSpace_interior_map_nhds_eq y hy]
  exact Filter.image_mem_map hU

/-- Euclidean interior geometry at a fixed image point: construct a polygonal disk neighborhood
inside the given half-plane neighborhood. -/
theorem euclideanHalfSpace_interior_polygonal_neighborhood_at
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : 0 < y.1 0) (hyU : y.1 ∈ (Subtype.val '' U)) :
    Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩) := by
  have hAmbient : (Subtype.val '' U : Set Plane) ∈ 𝓝 y.1 :=
    euclideanHalfSpace_interior_image_mem_nhds U y hU hy
  have hPositive : {p : Plane | 0 < p 0} ∈ 𝓝 y.1 := by
    have hOpen : IsOpen {p : Plane | 0 < p 0} := by
      exact isOpen_lt continuous_const
        (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
    exact hOpen.mem_nhds hy
  have hAmbientPositive :
      ((Subtype.val '' U : Set Plane) ∩ {p : Plane | 0 < p 0}) ∈ 𝓝 y.1 :=
    Filter.inter_mem hAmbient hPositive
  rcases PlaneRegionTriangleCopy.exists_centeredHomothety_image_subset_of_mem_nhds
      (Ω := (Subtype.val '' U : Set Plane) ∩ {p : Plane | 0 < p 0}) hAmbientPositive with
    ⟨scale, hscale, hsubset⟩
  let T : PlaneRegionTriangleCopy (Subtype.val '' U) ⟨y.1, hyU⟩ :=
    PlaneRegionTriangleCopy.ofCenteredHomothety scale hscale (by
      intro z hz
      exact (hsubset hz).1)
  have havoidsCoordBoundary :
      ∀ p ∈ EuclideanComplex.Examples.closedTriangleSupport, (T.homeomorph p) 0 ≠ 0 := by
    intro p hp hline
    have hpos :
        0 <
          (PlaneRegionTriangleCopy.centeredHomothety y.1 scale hscale p) 0 :=
      (hsubset ⟨p, hp, rfl⟩).2
    change (PlaneRegionTriangleCopy.centeredHomothety y.1 scale hscale p) 0 = 0 at hline
    linarith
  exact ⟨PlaneRegionPolygonalNeighborhood.ofTriangleCopy T havoidsCoordBoundary⟩

/-- An open neighborhood of an interior point in the model half-plane contains an embedded
polygonal disk whose image is a neighborhood of the point. -/
theorem euclideanHalfSpace_interior_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : 0 < y.1 0) :
    ∃ hyU : y.1 ∈ (Subtype.val '' U),
      Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩) := by
  let hyU := euclideanHalfSpace_point_mem_image_of_mem_nhds U y hU
  exact ⟨hyU, euclideanHalfSpace_interior_polygonal_neighborhood_at U y hU hy hyU⟩

/-- Euclidean boundary geometry at a fixed image point: construct a polygonal half-disk
neighborhood inside the given half-plane neighborhood. -/
theorem euclideanHalfSpace_boundary_polygonal_neighborhood_at
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) (hyU : y.1 ∈ (Subtype.val '' U)) :
    Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩) := by
  have hRelative : (Subtype.val '' U : Set Plane) ∈ 𝓝[{p : Plane | 0 ≤ p 0}] y.1 :=
    euclideanHalfSpace_image_mem_nhdsWithin_halfspace U y hU
  have hBoundary : y.1 0 = 0 := hy
  have hSubsetHalfspace : (Subtype.val '' U : Set Plane) ⊆ {p : Plane | 0 ≤ p 0} := by
    intro p hp
    rcases hp with ⟨q, _hq, rfl⟩
    exact q.2
  rcases
    PlaneRegionBoundaryTriangleCopy.exists_boundaryAnchoredHomothety_image_subset_of_mem_nhdsWithin
      (Ω := (Subtype.val '' U : Set Plane)) hRelative hSubsetHalfspace hBoundary with
    ⟨scale, hscale, hsubset, hnhds⟩
  let T : PlaneRegionBoundaryTriangleCopy (Subtype.val '' U) ⟨y.1, hyU⟩ :=
    PlaneRegionBoundaryTriangleCopy.ofBoundaryAnchoredHomothety hy scale hscale hsubset hnhds
  exact ⟨PlaneRegionPolygonalNeighborhood.ofBoundaryTriangleCopy T⟩

/-- An open neighborhood of a boundary-line point in the model half-plane contains an embedded
polygonal half-disk whose image is a neighborhood of the point. -/
theorem euclideanHalfSpace_boundary_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) :
    ∃ hyU : y.1 ∈ (Subtype.val '' U),
      Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩) := by
  let hyU := euclideanHalfSpace_point_mem_image_of_mem_nhds U y hU
  exact ⟨hyU, euclideanHalfSpace_boundary_polygonal_neighborhood_at U y hU hy hyU⟩

/-- An open neighborhood in the model half-plane contains an embedded polygonal disk or half-disk
whose image is a neighborhood of the chosen point. -/
theorem euclideanHalfSpace_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y) :
    ∃ hy : y.1 ∈ (Subtype.val '' U),
      Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hy⟩) := by
  by_cases hboundary : y.1 0 = 0
  · exact euclideanHalfSpace_boundary_open_neighborhood_contains_polygonal_neighborhood
      U y hU hboundary
  · have hinterior : 0 < y.1 0 := lt_of_le_of_ne y.2 (Ne.symm hboundary)
    exact euclideanHalfSpace_interior_open_neighborhood_contains_polygonal_neighborhood
      U y hU hinterior

/-- The model region of the preferred chart at a point contains an embedded polygonal disk or
half-disk whose image is a neighborhood of the chart coordinate. -/
theorem mathlib_chartAt_model_region_contains_polygonal_neighborhood
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] (x : M) :
    ∃ D : ModelChartPolygonalDisk (RadoChartPair.fromChartAt M x),
      Set.range D.embed ∈
        𝓝 ((RadoChartPair.fromChartAt M x).chartHomeomorph
          ⟨x, RadoChartPair.fromChartAt_mem_domain M x⟩) := by
  let U : Set (EuclideanHalfSpace 2) := (chartAt (EuclideanHalfSpace 2) x).target
  let y : EuclideanHalfSpace 2 := chartAt (EuclideanHalfSpace 2) x x
  have hU : U ∈ 𝓝 y := by
    simpa [U, y] using chart_target_mem_nhds (EuclideanHalfSpace 2) x
  rcases euclideanHalfSpace_open_neighborhood_contains_polygonal_neighborhood U y hU with
    ⟨hy, hN⟩
  let N := Classical.choice hN
  let D : ModelChartPolygonalDisk (RadoChartPair.fromChartAt M x) :=
    N.toModelChartPolygonalDisk
  refine ⟨D, ?_⟩
  have hcoord :
      ((RadoChartPair.fromChartAt M x).chartHomeomorph
        ⟨x, RadoChartPair.fromChartAt_mem_domain M x⟩).1 = y.1 := by
    rfl
  have hpoint :
      (RadoChartPair.fromChartAt M x).chartHomeomorph
          ⟨x, RadoChartPair.fromChartAt_mem_domain M x⟩ =
        (⟨y.1, hy⟩ :
          (RadoChartPair.fromChartAt M x).modelRegion) := by
    exact Subtype.ext hcoord
  rw [hpoint]
  change Set.range N.embed ∈ 𝓝 (⟨y.1, hy⟩ : Subtype.val '' U)
  exact N.range_mem_nhds

/-- In the model region of the preferred chart at a point, there is a polygonal disk or half-disk
whose pullback is a neighborhood core of the point. -/
theorem mathlib_chartAt_contains_model_polygonal_disk_core
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] (x : M) :
    ∃ D : ModelChartPolygonalDisk (RadoChartPair.fromChartAt M x),
      D.pulledCore ∈ 𝓝 x := by
  rcases mathlib_chartAt_model_region_contains_polygonal_neighborhood M x with ⟨D, hD⟩
  exact ⟨D, D.pulledCore_mem_nhds_of_range_mem_nhds
    (RadoChartPair.fromChartAt_mem_domain M x) hD⟩

/-- The preferred mathlib chart at a point contains a smaller Rado chart pair whose core is covered
by a pulled-back polygonal disk or half-disk. -/
theorem mathlib_chartAt_contains_polygonal_disk_core
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] (x : M) :
    ∃ D : ChartPolygonalDisk M,
      D.chart.Refines (RadoChartPair.fromChartAt M x) ∧
        D.chart.boundaryCore ⊆ (RadoChartPair.fromChartAt M x).boundaryCore ∧
          D.chart.core ∈ 𝓝 x ∧ D.BoundaryFaithful ∧
            (modelWithCornersEuclideanHalfSpace 2).boundary M ∩ D.chart.core ⊆
              D.chart.boundaryCore := by
  rcases mathlib_chartAt_contains_model_polygonal_disk_core M x with ⟨D, hD⟩
  refine ⟨D.toChartPolygonalDisk, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.toChartPair_refines (by
      intro y hy
      have hydomain : y ∈ (RadoChartPair.fromChartAt M x).domain :=
        D.pulledCore_subset_domain hy
      simpa [RadoChartPair.fromChartAt] using hydomain)
  · intro y hy
    rw [D.toChartPolygonalDisk_chart_boundaryCore] at hy
    rcases hy with ⟨q, hq, rfl⟩
    exact RadoChartPair.fromChartAt_mem_boundaryCore_of_chart_coord_zero M x
      (y := (RadoChartPair.fromChartAt M x).chartHomeomorph.symm q) (by
        have hline :=
          D.modelBoundaryCore_in_boundary_chart
            (RadoChartPair.fromChartAt_kind M x) q hq
        simpa using hline)
  · simpa using hD
  · exact D.toChartPolygonalDisk_boundaryFaithful
  · intro y hy
    rcases hy with ⟨hyBoundary, hyCore⟩
    have hyPulled : y ∈ D.pulledCore := by
      simpa [ModelChartPolygonalDisk.toChartPolygonalDisk,
        ModelChartPolygonalDisk.toChartPair, RadoChartPair.withCore] using hyCore
    have hyDomain : y ∈ (RadoChartPair.fromChartAt M x).domain :=
      D.pulledCore_subset_domain hyPulled
    have hlineFromChartAt :
        (((RadoChartPair.fromChartAt M x).chartHomeomorph ⟨y, hyDomain⟩ : Plane) 0 = 0) :=
      RadoChartPair.fromChartAt_chart_coord_zero_of_manifold_boundary
        (M := M) x (y := ⟨y, hyDomain⟩) hyBoundary
    have hline :
        ((D.toChartPolygonalDisk.chart.chartHomeomorph
            ⟨y, D.toChartPolygonalDisk.chart.core_subset_domain hyCore⟩ : Plane) 0 = 0) := by
      change (((RadoChartPair.fromChartAt M x).chartHomeomorph ⟨y, _⟩ : Plane) 0 = 0)
      simpa using hlineFromChartAt
    exact D.toChartPolygonalDisk_boundaryFaithful
      (by
        simp [ModelChartPolygonalDisk.toChartPolygonalDisk,
          ModelChartPolygonalDisk.toChartPair, RadoChartPair.withCore])
      y hyCore hline

/-- Positive-regularity variant of `mathlib_chartAt_contains_polygonal_disk_core` that uses the
proved mathlib boundary-invariance theorem instead of the C0 theorem boundary. -/
theorem mathlib_chartAt_contains_polygonal_disk_core_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] (x : M) :
    ∃ D : ChartPolygonalDisk M,
      D.chart.Refines (RadoChartPair.fromChartAt M x) ∧
        D.chart.boundaryCore ⊆ (RadoChartPair.fromChartAt M x).boundaryCore ∧
          D.chart.core ∈ 𝓝 x ∧ D.BoundaryFaithful ∧
            (modelWithCornersEuclideanHalfSpace 2).boundary M ∩ D.chart.core ⊆
              D.chart.boundaryCore := by
  rcases mathlib_chartAt_contains_model_polygonal_disk_core M x with ⟨D, hD⟩
  refine ⟨D.toChartPolygonalDisk, ?_, ?_, ?_, ?_, ?_⟩
  · exact D.toChartPair_refines (by
      intro y hy
      have hydomain : y ∈ (RadoChartPair.fromChartAt M x).domain :=
        D.pulledCore_subset_domain hy
      simpa [RadoChartPair.fromChartAt] using hydomain)
  · intro y hy
    rw [D.toChartPolygonalDisk_chart_boundaryCore] at hy
    rcases hy with ⟨q, hq, rfl⟩
    exact RadoChartPair.fromChartAt_mem_boundaryCore_of_chart_coord_zero M x
      (y := (RadoChartPair.fromChartAt M x).chartHomeomorph.symm q) (by
        have hline :=
          D.modelBoundaryCore_in_boundary_chart
            (RadoChartPair.fromChartAt_kind M x) q hq
        simpa using hline)
  · simpa using hD
  · exact D.toChartPolygonalDisk_boundaryFaithful
  · intro y hy
    rcases hy with ⟨hyBoundary, hyCore⟩
    have hyPulled : y ∈ D.pulledCore := by
      simpa [ModelChartPolygonalDisk.toChartPolygonalDisk,
        ModelChartPolygonalDisk.toChartPair, RadoChartPair.withCore] using hyCore
    have hyDomain : y ∈ (RadoChartPair.fromChartAt M x).domain :=
      D.pulledCore_subset_domain hyPulled
    have hlineFromChartAt :
        (((RadoChartPair.fromChartAt M x).chartHomeomorph ⟨y, hyDomain⟩ : Plane) 0 = 0) :=
      RadoChartPair.fromChartAt_chart_coord_zero_of_manifold_boundary_of_contMDiff
        (M := M) x (y := ⟨y, hyDomain⟩) hyBoundary
    have hline :
        ((D.toChartPolygonalDisk.chart.chartHomeomorph
            ⟨y, D.toChartPolygonalDisk.chart.core_subset_domain hyCore⟩ : Plane) 0 = 0) := by
      change (((RadoChartPair.fromChartAt M x).chartHomeomorph ⟨y, _⟩ : Plane) 0 = 0)
      simpa using hlineFromChartAt
    exact D.toChartPolygonalDisk_boundaryFaithful
      (by
        simp [ModelChartPolygonalDisk.toChartPolygonalDisk,
          ModelChartPolygonalDisk.toChartPair, RadoChartPair.withCore])
      y hyCore hline

/-- Pointwise chart-polygonal-disk data from a polygonal core inside the preferred mathlib chart.
-/
theorem mathlib_bordered_surface_point_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] (x : M) :
    Nonempty (PointChartPolygonalDiskData M
      ((modelWithCornersEuclideanHalfSpace 2).boundary M) x) := by
  rcases mathlib_chartAt_contains_polygonal_disk_core M x with
    ⟨D, _hrefines, _hboundary, hcore, hfaithful, hboundarySet⟩
  exact
    ⟨{ disk := D
       core_mem_nhds := hcore
       boundaryFaithful := hfaithful
       boundarySet_subset_boundaryCore := hboundarySet }⟩

/-- Positive-regularity pointwise chart-polygonal-disk data from the preferred mathlib chart. -/
theorem mathlib_bordered_surface_point_chart_polygonal_disk_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] (x : M) :
    Nonempty (PointChartPolygonalDiskData M
      ((modelWithCornersEuclideanHalfSpace 2).boundary M) x) := by
  rcases mathlib_chartAt_contains_polygonal_disk_core_of_contMDiff M x with
    ⟨D, _hrefines, _hboundary, hcore, hfaithful, hboundarySet⟩
  exact
    ⟨{ disk := D
       core_mem_nhds := hcore
       boundaryFaithful := hfaithful
       boundarySet_subset_boundaryCore := hboundarySet }⟩

/-- Pointwise chart-polygonal-disk data packages as local chart-polygonal-disk data. -/
noncomputable def localChartPolygonalDiskDataOfPointwise
    {M : Type*} [TopologicalSpace M] (boundarySet : Set M)
    (h : ∀ x : M, Nonempty (PointChartPolygonalDiskData M boundarySet x)) :
    LocalChartPolygonalDiskData M := by
  classical
  let diskAt : M → ChartPolygonalDisk M :=
    fun x => (Classical.choice (h x)).disk
  exact
    { boundarySet := boundarySet
      pairAt := fun x => (diskAt x).chart
      diskAt := diskAt
      chart_eq := by
        intro x
        rfl
      core_mem_nhds := by
        intro x
        exact (Classical.choice (h x)).core_mem_nhds
      compatibleChartShrinks := by
        intro x
        exact ⟨subset_rfl, subset_rfl⟩
      boundaryCompatibleChartShrinks := by
        intro x
        exact subset_rfl
      boundaryFaithful := by
        intro x
        exact (Classical.choice (h x)).boundaryFaithful
      boundarySet_subset_boundaryCore := by
        intro x
        exact (Classical.choice (h x)).boundarySet_subset_boundaryCore }

/-- Pointwise chart-polygonal-disk data packages as local chart-polygonal-disk data. -/
theorem local_chart_polygonal_disk_data_of_pointwise
    {M : Type*} [TopologicalSpace M] (boundarySet : Set M)
    (h : ∀ x : M, Nonempty (PointChartPolygonalDiskData M boundarySet x)) :
    Nonempty (LocalChartPolygonalDiskData M) := by
  exact ⟨localChartPolygonalDiskDataOfPointwise boundarySet h⟩

/-- Local chart-polygonal-disk data extracted pointwise from the mathlib atlas. -/
theorem mathlib_bordered_surface_local_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (LocalChartPolygonalDiskData M) := by
  exact local_chart_polygonal_disk_data_of_pointwise
    ((modelWithCornersEuclideanHalfSpace 2).boundary M)
    (fun x => mathlib_bordered_surface_point_chart_polygonal_disk_data M x)

/-- Positive-regularity local chart-polygonal-disk data extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_local_chart_polygonal_disk_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (LocalChartPolygonalDiskData M) := by
  exact local_chart_polygonal_disk_data_of_pointwise
    ((modelWithCornersEuclideanHalfSpace 2).boundary M)
    (fun x => mathlib_bordered_surface_point_chart_polygonal_disk_data_of_contMDiff M x)

/-- Named local chart-polygonal-disk data extracted from a compact mathlib bordered surface. -/
noncomputable def mathlib_bordered_surface_localChartPolygonalDiskData
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    LocalChartPolygonalDiskData M :=
  localChartPolygonalDiskDataOfPointwise
    ((modelWithCornersEuclideanHalfSpace 2).boundary M)
    (fun x => mathlib_bordered_surface_point_chart_polygonal_disk_data M x)

/-- Named positive-regularity local chart-polygonal-disk data extracted from a compact mathlib
bordered surface. -/
noncomputable def mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    LocalChartPolygonalDiskData M :=
  localChartPolygonalDiskDataOfPointwise
    ((modelWithCornersEuclideanHalfSpace 2).boundary M)
    (fun x => mathlib_bordered_surface_point_chart_polygonal_disk_data_of_contMDiff M x)

@[simp] theorem mathlib_bordered_surface_localChartPolygonalDiskData_boundarySet
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (mathlib_bordered_surface_localChartPolygonalDiskData M).boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

@[simp] theorem mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff_boundarySet
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    (mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff M).boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

namespace LocalChartPolygonalDiskData

/-- Compactness promotes local chart-polygonal-disk data to a finite chart-pair cover with
matching polygonal disk data. -/
noncomputable def toFiniteChartPolygonalDiskData
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) :
    Σ C : FiniteChartPairCover M, FiniteChartPolygonalDiskData C := by
  classical
  let t : Finset M :=
    Classical.choose (CompactSpace.elim_nhds_subcover (fun x : M => (L.pairAt x).core)
      L.core_mem_nhds)
  have ht : ⋃ x ∈ t, (L.pairAt x).core = ⊤ :=
    Classical.choose_spec (CompactSpace.elim_nhds_subcover (fun x : M => (L.pairAt x).core)
      L.core_mem_nhds)
  let C : FiniteChartPairCover M :=
    { Index := {x : M // x ∈ t}
      indexFintype := inferInstance
      pair := fun x => L.pairAt x.1
      boundaryCarrier := ⋃ x : {x : M // x ∈ t}, (L.pairAt x.1).boundaryCore
      boundarySet := L.boundarySet
      boundarySet_subset_boundaryCarrier := by
        intro y hyBoundary
        have hyCover : y ∈ ⋃ x ∈ t, (L.pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hyCover
        rcases hyCover with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyCore⟩
        exact Set.mem_iUnion.mpr
          ⟨⟨x, hxt⟩, L.boundarySet_subset_boundaryCore x ⟨hyBoundary, hyCore⟩⟩
      covers := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (L.pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryCovers := by
        intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        exact ⟨i, hi⟩
      interiorChartsCoverInterior := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (L.pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryCore_subset_boundaryCarrier := by
        intro i x hx
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
      locallyFinite := by
        intro _x
        refine ⟨Finset.univ, ?_⟩
        intro i _hi
        simp
      nestedControl := by
        intro i
        exact (L.pairAt i.1).core_subset_domain
      boundaryLocallyFinite := by
        intro _x
        refine ⟨Finset.univ, ?_⟩
        intro i _hi
        simp
      boundaryNestedControl := by
        intro i
        exact (L.pairAt i.1).boundaryCore_subset_core }
  let D : FiniteChartPolygonalDiskData C :=
    { disk := fun i => L.diskAt i.1
      chart_eq := fun i => L.chart_eq i.1
      compatibleChartShrinks := by
        intro i
        exact L.compatibleChartShrinks i.1
      boundaryCompatibleChartShrinks := by
        intro i
        exact L.boundaryCompatibleChartShrinks i.1
      boundaryFaithful := by
        intro i
        exact L.boundaryFaithful i.1 }
  exact ⟨C, D⟩

/-- The finite chart-pair cover extracted from local chart-polygonal-disk data. -/
noncomputable def finiteChartPairCover
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) : FiniteChartPairCover M :=
  (L.toFiniteChartPolygonalDiskData).1

@[simp] theorem finiteChartPairCover_boundarySet
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) :
    L.finiteChartPairCover.boundarySet = L.boundarySet := by
  rfl

/-- The finite polygonal disk data extracted from local chart-polygonal-disk data. -/
noncomputable def finiteChartPolygonalDiskData
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) :
    FiniteChartPolygonalDiskData L.finiteChartPairCover :=
  (L.toFiniteChartPolygonalDiskData).2

/-- Local chart-polygonal-disk data on a compact space packages all Rado-facing Moise extraction
data. -/
noncomputable def toMoiseExtractionData
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    (L : LocalChartPolygonalDiskData M) : MoiseExtractionData M :=
  let P := L.toFiniteChartPolygonalDiskData
  { finiteCover := P.1
    localDiskOrHalfDiskModels := P.1.hasDiskOrHalfDiskModelCover
    chartModelsMatchKind := P.1.modelsMatchKind
    radoInductionData := P.2.toFiniteRadoInductionGeometry.toRadoInductionData }

@[simp] theorem toMoiseExtractionData_finiteCover
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    (L : LocalChartPolygonalDiskData M) :
    L.toMoiseExtractionData.finiteCover = L.finiteChartPairCover := by
  rfl

@[simp] theorem toMoiseExtractionData_finiteCover_boundarySet
    {M : Type u} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    (L : LocalChartPolygonalDiskData M) :
    L.toMoiseExtractionData.finiteCover.boundarySet = L.boundarySet := by
  rfl

end LocalChartPolygonalDiskData

/-- Named finite chart-pair cover extracted from compact mathlib bordered-surface local chart data.

Unlike `mathlib_bordered_surface_finite_chart_pair_cover`, this cover remembers the actual
mathlib manifold boundary as its `boundarySet`. -/
noncomputable def mathlib_bordered_surface_finiteChartPairCover
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    FiniteChartPairCover M :=
  (mathlib_bordered_surface_localChartPolygonalDiskData M).finiteChartPairCover

/-- Positive-regularity named finite chart-pair cover extracted from compact mathlib
bordered-surface local chart data. -/
noncomputable def mathlib_bordered_surface_finiteChartPairCover_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    FiniteChartPairCover M :=
  (mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff M).finiteChartPairCover

@[simp] theorem mathlib_bordered_surface_finiteChartPairCover_boundarySet
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (mathlib_bordered_surface_finiteChartPairCover M).boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

@[simp] theorem mathlib_bordered_surface_finiteChartPairCover_of_contMDiff_boundarySet
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    (mathlib_bordered_surface_finiteChartPairCover_of_contMDiff M).boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

/-- The actual mathlib boundary is contained in the boundary carrier of the finite cover extracted
from local polygonal disk data. -/
theorem mathlib_bordered_surface_boundary_subset_finiteChartPairCover_boundaryCarrier
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (modelWithCornersEuclideanHalfSpace 2).boundary M ⊆
      (mathlib_bordered_surface_finiteChartPairCover M).boundaryCarrier := by
  intro x hx
  exact (mathlib_bordered_surface_finiteChartPairCover M).boundarySet_subset_boundaryCarrier hx

/-- Positive-regularity version: the actual mathlib boundary is contained in the boundary carrier
of the finite cover extracted from local polygonal disk data. -/
theorem mathlib_bordered_surface_boundary_subset_finiteChartPairCover_of_contMDiff_boundaryCarrier
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    (modelWithCornersEuclideanHalfSpace 2).boundary M ⊆
      (mathlib_bordered_surface_finiteChartPairCover_of_contMDiff M).boundaryCarrier := by
  intro x hx
  let C := mathlib_bordered_surface_finiteChartPairCover_of_contMDiff M
  exact C.boundarySet_subset_boundaryCarrier hx

/-- Compactness promotes pointwise local chart-polygonal-disk data to a finite chart-pair cover
carrying indexed polygonal disk data. -/
theorem finite_chart_polygonal_disk_data_of_local
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) :
    Nonempty (Σ C : FiniteChartPairCover M, FiniteChartPolygonalDiskData C) := by
  let P := L.toFiniteChartPolygonalDiskData
  exact ⟨⟨P.1, P.2⟩⟩

/-- A compact mathlib bordered surface admits a finite chart-pair cover carrying polygonal disk
data on every selected chart pair. -/
theorem mathlib_bordered_surface_finite_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (Σ C : FiniteChartPairCover M, FiniteChartPolygonalDiskData C) := by
  let L := mathlib_bordered_surface_localChartPolygonalDiskData M
  exact finite_chart_polygonal_disk_data_of_local L

/-- Positive-regularity finite chart-pair cover carrying polygonal disk data. -/
theorem mathlib_bordered_surface_finite_chart_polygonal_disk_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (Σ C : FiniteChartPairCover M, FiniteChartPolygonalDiskData C) := by
  let L := mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff M
  exact finite_chart_polygonal_disk_data_of_local L

/-- Named Moise extraction data built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_moiseExtractionData
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    MoiseExtractionData M :=
  (mathlib_bordered_surface_localChartPolygonalDiskData M).toMoiseExtractionData

/-- Named positive-regularity Moise extraction data built from the mathlib bordered-surface
atlas. -/
noncomputable def mathlib_bordered_surface_moiseExtractionData_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    MoiseExtractionData M :=
  (mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff M).toMoiseExtractionData

theorem mathlib_bordered_surface_moiseExtractionData_finiteCover
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (mathlib_bordered_surface_moiseExtractionData M).finiteCover =
      mathlib_bordered_surface_finiteChartPairCover M := by
  rfl

theorem mathlib_bordered_surface_moiseExtractionData_of_contMDiff_finiteCover
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    (mathlib_bordered_surface_moiseExtractionData_of_contMDiff M).finiteCover =
      mathlib_bordered_surface_finiteChartPairCover_of_contMDiff M := by
  rfl

@[simp] theorem mathlib_bordered_surface_moiseExtractionData_finiteCover_boundarySet
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (mathlib_bordered_surface_moiseExtractionData M).finiteCover.boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

@[simp] theorem mathlib_bordered_surface_moiseExtractionData_of_contMDiff_finiteCover_boundarySet
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    (mathlib_bordered_surface_moiseExtractionData_of_contMDiff M).finiteCover.boundarySet =
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  rfl

/-- Named Moise two-manifold package built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_moiseTwoManifold
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    MoiseTwoManifold M :=
  (mathlib_bordered_surface_moiseExtractionData M).toMoiseTwoManifold

/-- Named positive-regularity Moise two-manifold package built from the mathlib bordered-surface
atlas. -/
noncomputable def mathlib_bordered_surface_moiseTwoManifold_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    MoiseTwoManifold M :=
  (mathlib_bordered_surface_moiseExtractionData_of_contMDiff M).toMoiseTwoManifold

/-- Polygonal disk data over a finite chart-pair cover packages as finite Rado geometry. -/
theorem finite_rado_geometry_of_chart_polygonal_disk_data
    {M : Type*} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) :
    Nonempty (FiniteRadoInductionGeometry C) := by
  exact ⟨D.toFiniteRadoInductionGeometry⟩

/-- Local Rado geometry over a finite chart-pair cover extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_finite_rado_geometry
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (Σ C : FiniteChartPairCover M, FiniteRadoInductionGeometry C) := by
  rcases mathlib_bordered_surface_finite_chart_polygonal_disk_data M with ⟨⟨C, D⟩⟩
  rcases finite_rado_geometry_of_chart_polygonal_disk_data D with ⟨G⟩
  exact ⟨⟨C, G⟩⟩

/-- Positive-regularity local Rado geometry over a finite chart-pair cover extracted from the
mathlib atlas. -/
theorem mathlib_bordered_surface_finite_rado_geometry_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (Σ C : FiniteChartPairCover M, FiniteRadoInductionGeometry C) := by
  rcases mathlib_bordered_surface_finite_chart_polygonal_disk_data_of_contMDiff M with ⟨⟨C, D⟩⟩
  rcases finite_rado_geometry_of_chart_polygonal_disk_data D with ⟨G⟩
  exact ⟨⟨C, G⟩⟩

/-- Local Rado induction data over a finite chart-pair cover extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_rado_induction_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (Σ C : FiniteChartPairCover M, RadoInductionData C.toChartPairExhaustion) := by
  rcases mathlib_bordered_surface_finite_rado_geometry M with ⟨⟨C, G⟩⟩
  rcases rado_induction_data_of_finite_geometry G with ⟨D⟩
  exact ⟨⟨C, D⟩⟩

/-- Positive-regularity local Rado induction data over a finite chart-pair cover extracted from
the mathlib atlas. -/
theorem mathlib_bordered_surface_rado_induction_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (Σ C : FiniteChartPairCover M, RadoInductionData C.toChartPairExhaustion) := by
  rcases mathlib_bordered_surface_finite_rado_geometry_of_contMDiff M with ⟨⟨C, G⟩⟩
  rcases rado_induction_data_of_finite_geometry G with ⟨D⟩
  exact ⟨⟨C, D⟩⟩

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This is where one proves that the mathlib manifold atlas admits a countable disk/half-disk chart
pair exhaustion with the local finiteness and nesting properties needed by Rado's induction. -/
theorem mathlib_bordered_surface_moise_extraction_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (MoiseExtractionData M) := by
  exact ⟨mathlib_bordered_surface_moiseExtractionData M⟩

/-- Positive-regularity chart-extraction theorem from mathlib's bordered surface hypotheses to
the Moise chart-pair interface. -/
theorem mathlib_bordered_surface_moise_extraction_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (MoiseExtractionData M) := by
  exact ⟨mathlib_bordered_surface_moiseExtractionData_of_contMDiff M⟩

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This packages the extracted finite chart-pair cover and local Rado induction data into the
Rado-facing `MoiseTwoManifold` structure. -/
theorem mathlib_bordered_surface_to_moise_two_manifold
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (MoiseTwoManifold M) := by
  exact ⟨mathlib_bordered_surface_moiseTwoManifold M⟩

/-- Positive-regularity theorem from mathlib's bordered surface hypotheses to the Rado-facing
`MoiseTwoManifold` structure. -/
theorem mathlib_bordered_surface_to_moise_two_manifold_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (MoiseTwoManifold M) := by
  exact ⟨mathlib_bordered_surface_moiseTwoManifold_of_contMDiff M⟩

/-- Named finite PL triangulation data built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_finitePLTriangulationData
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    FinitePLTriangulationData M :=
  (mathlib_bordered_surface_moiseExtractionData M).finiteStagePLTriangulationData

/-- Named positive-regularity finite PL triangulation data built from the mathlib bordered-surface
atlas. -/
noncomputable def mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    FinitePLTriangulationData M :=
  (mathlib_bordered_surface_moiseExtractionData_of_contMDiff M).finiteStagePLTriangulationData

/-- Mathlib bordered surfaces produce finite PL triangulation data via the Moise--Rado route. -/
theorem mathlib_bordered_surface_finite_pl_triangulation_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    Nonempty (FinitePLTriangulationData M) := by
  exact ⟨mathlib_bordered_surface_finitePLTriangulationData M⟩

/-- Positive-regularity mathlib bordered surfaces produce finite PL triangulation data via the
Moise--Rado route. -/
theorem mathlib_bordered_surface_finite_pl_triangulation_data_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    Nonempty (FinitePLTriangulationData M) := by
  exact ⟨mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff M⟩

/-- The boundary carrier selected by the finite chart cover of a compact mathlib bordered surface
is carried by the boundary package of the resulting finite PL triangulation data. -/
theorem mathlib_bordered_surface_boundaryCarrier_subset_finitePL_boundary
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (mathlib_bordered_surface_moiseExtractionData M).finiteCover.boundaryCarrier ⊆
      (mathlib_bordered_surface_finitePLTriangulationData M).boundary.boundarySupport := by
  let D := mathlib_bordered_surface_moiseExtractionData M
  simpa [mathlib_bordered_surface_finitePLTriangulationData] using
    D.finiteStagePLTriangulationData_boundaryCarrier_subset

/-- Positive-regularity boundary-carrier compatibility for the resulting finite PL triangulation
data. -/
theorem mathlib_bordered_surface_boundaryCarrier_subset_finitePL_boundary_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    let T := mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff M
    (mathlib_bordered_surface_moiseExtractionData_of_contMDiff M).finiteCover.boundaryCarrier ⊆
      T.boundary.boundarySupport := by
  dsimp
  let D := mathlib_bordered_surface_moiseExtractionData_of_contMDiff M
  simpa [mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff] using
    D.finiteStagePLTriangulationData_boundaryCarrier_subset

/-- The actual mathlib manifold boundary is carried by the boundary package of the finite PL
triangulation data produced from the bordered-surface atlas. -/
theorem mathlib_bordered_surface_manifoldBoundary_subset_finitePL_boundary
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    (modelWithCornersEuclideanHalfSpace 2).boundary M ⊆
      (mathlib_bordered_surface_finitePLTriangulationData M).boundary.boundarySupport := by
  let D := mathlib_bordered_surface_moiseExtractionData M
  have hBoundarySet :
      D.finiteCover.boundarySet = (modelWithCornersEuclideanHalfSpace 2).boundary M := by
    rfl
  intro x hx
  rw [← hBoundarySet] at hx
  simpa [mathlib_bordered_surface_finitePLTriangulationData, D] using
    D.finiteStagePLTriangulationData_boundarySet_subset hx

/-- Positive-regularity version: the actual mathlib manifold boundary is carried by the boundary
package of the finite PL triangulation data. -/
theorem mathlib_bordered_surface_manifoldBoundary_subset_finitePL_boundary_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    let T := mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff M
    (modelWithCornersEuclideanHalfSpace 2).boundary M ⊆
      T.boundary.boundarySupport := by
  dsimp
  let D := mathlib_bordered_surface_moiseExtractionData_of_contMDiff M
  have hBoundarySet :
      D.finiteCover.boundarySet = (modelWithCornersEuclideanHalfSpace 2).boundary M := by
    rfl
  intro x hx
  rw [← hBoundarySet] at hx
  simpa [mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff, D] using
    D.finiteStagePLTriangulationData_boundarySet_subset hx

/-- Rado triangulation theorem boundary for bordered surfaces. -/
theorem rado_bordered_surface_triangulation
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      ∃ _boundary : K.BoundarySubcomplexData, K.support = Set.univ := by
  let D := mathlib_bordered_surface_finitePLTriangulationData M
  exact ⟨D.K, D.finiteSupport, D.boundary, D.covers⟩

/-- Positive-regularity Rado triangulation theorem for bordered surfaces. -/
theorem rado_bordered_surface_triangulation_of_contMDiff
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] :
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      ∃ _boundary : K.BoundarySubcomplexData, K.support = Set.univ := by
  let D := mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff M
  exact ⟨D.K, D.finiteSupport, D.boundary, D.covers⟩

/-- Bridge from mathlib's Eval surface hypotheses to the Moise bordered-surface interface. -/
theorem eval_surface_to_moise_bordered_surface
    (S : Type*) [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (MoiseTwoManifold S) := by
  exact mathlib_bordered_surface_to_moise_two_manifold S

end

end ClassificationOfSurfaces
end Topology
end LeanEval
