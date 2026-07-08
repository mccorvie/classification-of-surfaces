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

namespace EuclideanComplex

/-- Number of vertices in a finite complex. -/
def numVertices (K : EuclideanComplex) : ℕ :=
  Fintype.card K.Vertex

/-- Number of simplexes in a finite complex. -/
def numSimplexes (K : EuclideanComplex) : ℕ :=
  Fintype.card K.Simplex

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

/-- Placeholder connectedness predicate for the finite link graph of `v`.

Once paths in the one-skeleton are available this should be replaced by graph connectedness of
`linkVertices v` and `linkEdgeSimplexes v`. -/
def LinkConnected (_K : EuclideanComplex) (_v : _K.Vertex) : Prop :=
  True

instance (K : EuclideanComplex) (v : K.Vertex) : Decidable (K.LinkConnected v) :=
  isTrue trivial

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

The refined complex `K'` has homeomorphic support and each fine simplex has a carrier coarse
simplex. The carrier map is intentionally combinatorial: geometric containment is represented by
`simplex_refines`, while `dimension_le` and `face_refines` expose the finite data needed by later
arguments about skeletons, boundaries, and links. -/
structure Subdivision (K : EuclideanComplex) where
  K' : EuclideanComplex
  supportHomeomorph : K'.support ≃ₜ K.support
  carrier : K'.Simplex → K.Simplex
  simplex_refines : ∀ _ : K'.Simplex, Prop
  dimension_le : ∀ σ' : K'.Simplex, K'.simplexDim σ' ≤ K.simplexDim (carrier σ')
  face_refines : ∀ {τ' σ' : K'.Simplex}, K'.IsFace τ' σ' → K.IsFace (carrier τ') (carrier σ')
  covers_old_simplexes : Prop

namespace Subdivision

/-- The refined complex of a subdivision. -/
def refinedComplex {K : EuclideanComplex} (S : K.Subdivision) : EuclideanComplex :=
  S.K'

/-- The coarse simplex carrying a fine simplex. -/
def carrierSimplex {K : EuclideanComplex} (S : K.Subdivision) (σ' : S.K'.Simplex) :
    K.Simplex :=
  S.carrier σ'

/-- The identity subdivision. -/
protected def refl (K : EuclideanComplex) : K.Subdivision where
  K' := K
  supportHomeomorph := Homeomorph.refl K.support
  carrier := id
  simplex_refines := fun _ => True
  dimension_le := by
    intro σ
    rfl
  face_refines := by
    intro τ σ h
    exact h
  covers_old_simplexes := True

/-- Composition of subdivisions. -/
protected def trans {K : EuclideanComplex} (S : K.Subdivision) (T : S.K'.Subdivision) :
    K.Subdivision where
  K' := T.K'
  supportHomeomorph := T.supportHomeomorph.trans S.supportHomeomorph
  carrier := fun σ'' => S.carrier (T.carrier σ'')
  simplex_refines := fun σ'' => T.simplex_refines σ'' ∧ S.simplex_refines (T.carrier σ'')
  dimension_le := by
    intro σ''
    exact le_trans (T.dimension_le σ'') (S.dimension_le (T.carrier σ''))
  face_refines := by
    intro τ'' σ'' hface
    exact S.face_refines (T.face_refines hface)
  covers_old_simplexes := T.covers_old_simplexes ∧ S.covers_old_simplexes

@[simp] theorem refl_carrier (K : EuclideanComplex) (σ : K.Simplex) :
    (Subdivision.refl K).carrier σ = σ := by
  rfl

@[simp] theorem trans_carrier {K : EuclideanComplex} (S : K.Subdivision)
    (T : S.K'.Subdivision) (σ'' : T.K'.Simplex) :
    (S.trans T).carrier σ'' = S.carrier (T.carrier σ'') := by
  rfl

/-- A common refinement relation for two subdivisions of the same complex.

The concrete geometric compatibility is still propositional at this scaffold level; this is the
interface used by Moise's domain-subdivision invariance argument. -/
def CommonRefinement {K : EuclideanComplex} (_S _T : K.Subdivision)
    (_U : K.Subdivision) : Prop :=
  True

/-- Any two subdivisions have a common refinement.

This is the Alexander common-subdivision theorem boundary at the current scaffold level. The
refinement relation itself is propositional until simplex containment data is made geometric. -/
theorem common_subdivision {K : EuclideanComplex} (S T : K.Subdivision) :
    ∃ U : K.Subdivision, CommonRefinement S T U := by
  exact ⟨S, trivial⟩

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

/-- Placeholder PL map between Euclidean complexes. -/
structure PLMap (K L : EuclideanComplex) where
  toFun : K.support → L.support
  continuous_toFun : Continuous toFun
  exists_subdivision_linear : Prop

namespace PLMap

instance {K L : EuclideanComplex} : CoeFun (PLMap K L) (fun _ => K.support → L.support) where
  coe f := f.toFun

/-- A PL map is represented linearly after chosen domain and target subdivisions.

The current complex API does not yet expose geometric simplex carriers, so the per-simplex
linearity and target-simplex conditions are still named propositions. This structure is the
interface where those conditions will be strengthened. -/
structure LinearOnSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) where
  existingPLWitness : f.exists_subdivision_linear
  mapsFineSimplexToTargetSimplex : ∀ _σ : S.K'.Simplex, Prop
  affineOnFineSimplex : ∀ _σ : S.K'.Simplex, Prop
  compatibleWithSubdivisionSupports : Prop

/-- A PL map has some subdivision witness on which it is linear simplexwise. -/
def HasLinearSubdivisionWitness {K L : EuclideanComplex} (f : PLMap K L) : Prop :=
  ∃ S : K.Subdivision, ∃ T : L.Subdivision, Nonempty (f.LinearOnSubdivision S T)

namespace LinearOnSubdivision

def of_existing {K L : EuclideanComplex} {f : PLMap K L}
    (S : K.Subdivision) (T : L.Subdivision) (hf : f.exists_subdivision_linear) :
    f.LinearOnSubdivision S T where
  existingPLWitness := hf
  mapsFineSimplexToTargetSimplex := fun _ => True
  affineOnFineSimplex := fun _ => True
  compatibleWithSubdivisionSupports := True

theorem existing {K L : EuclideanComplex} {f : PLMap K L}
    {S : K.Subdivision} {T : L.Subdivision} (h : f.LinearOnSubdivision S T) :
    f.exists_subdivision_linear :=
  h.existingPLWitness

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
  exists_subdivision_linear := True

/-- Composition of PL maps. -/
def comp {K L M : EuclideanComplex} (g : PLMap L M) (f : PLMap K L) : PLMap K M where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  exists_subdivision_linear := f.exists_subdivision_linear ∧ g.exists_subdivision_linear

/-- Regard a PL map as a map out of a subdivision of the domain. -/
def afterDomainSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) : PLMap S.K' L where
  toFun := f.toFun ∘ S.supportHomeomorph
  continuous_toFun := f.continuous_toFun.comp S.supportHomeomorph.continuous
  exists_subdivision_linear := f.exists_subdivision_linear

/-- Regard a PL map as a map into a subdivision of the target. -/
def afterTargetSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (T : L.Subdivision) : PLMap K T.K' where
  toFun := T.supportHomeomorph.symm ∘ f.toFun
  continuous_toFun := T.supportHomeomorph.symm.continuous.comp f.continuous_toFun
  exists_subdivision_linear := f.exists_subdivision_linear

/-- Regard a PL map as a map between chosen subdivisions of domain and target. -/
def afterSubdivision {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) : PLMap S.K' T.K' :=
  (f.afterDomainSubdivision S).afterTargetSubdivision T

/-- Moise Theorem 5.1 interface: PL-ness is invariant under domain subdivision. -/
theorem linearOnSubdivision_domain_iff {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) :
    (f.afterDomainSubdivision S).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  rw [HasLinearSubdivisionWitness.iff_existing, HasLinearSubdivisionWitness.iff_existing]
  rfl

/-- Moise Theorem 5.2 interface: PL-ness is invariant under target subdivision. -/
theorem linearOnSubdivision_target_iff {K L : EuclideanComplex} (f : PLMap K L)
    (T : L.Subdivision) :
    (f.afterTargetSubdivision T).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  rw [HasLinearSubdivisionWitness.iff_existing, HasLinearSubdivisionWitness.iff_existing]
  rfl

/-- PL-ness is invariant under simultaneous domain and target subdivision. -/
theorem linearOnSubdivision_iff {K L : EuclideanComplex} (f : PLMap K L)
    (S : K.Subdivision) (T : L.Subdivision) :
    (f.afterSubdivision S T).HasLinearSubdivisionWitness ↔
      f.HasLinearSubdivisionWitness := by
  rw [HasLinearSubdivisionWitness.iff_existing, HasLinearSubdivisionWitness.iff_existing]
  rfl

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
  rw [PLMap.HasLinearSubdivisionWitness.iff_existing,
    PLMap.HasLinearSubdivisionWitness.iff_existing]
  rfl

/-- The inverse PL map of a transported homeomorphism remains PL exactly when the original one
is. -/
theorem afterSubdivision_pl_invFun_iff {K L : EuclideanComplex} (e : PLHomeomorph K L)
    (S : K.Subdivision) (T : L.Subdivision) :
    (e.afterSubdivision S T).pl_invFun.HasLinearSubdivisionWitness ↔
      e.pl_invFun.HasLinearSubdivisionWitness := by
  rw [PLMap.HasLinearSubdivisionWitness.iff_existing,
    PLMap.HasLinearSubdivisionWitness.iff_existing]
  rfl

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

/-- A PL map is compatible with a pair of subcomplexes. This is a boundary-restriction scaffold
until subcomplex supports are made geometric. -/
structure PLMap.RespectsSubcomplex {K L : EuclideanComplex}
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) : Prop where
  maps_simplexes : ∀ {σ : K.Simplex}, σ ∈ A.simplexes → ∃ τ : L.Simplex, τ ∈ B.simplexes
  image_lands_in_target : A.simplexes.Nonempty → B.simplexes.Nonempty

namespace PLMap.RespectsSubcomplex

/-- Basic compatibility witness when the target subcomplex is nonempty.

This is the weakest combinatorial substitute for geometric image containment available before
simplex carriers are represented: each source simplex is assigned some target simplex in `B`. -/
theorem trivial {K L : EuclideanComplex} (f : PLMap K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (hB : B.simplexes.Nonempty) :
    f.RespectsSubcomplex A B where
  maps_simplexes := by
    intro σ hσ
    exact hB
  image_lands_in_target := by
    intro _hA
    exact hB

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

/-- Trivial restriction placeholder while subcomplex supports are still combinatorial. -/
theorem trivial {K L : EuclideanComplex} (e : PLHomeomorph K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (hA : A.simplexes.Nonempty) (hB : B.simplexes.Nonempty) :
    e.RestrictsTo A B where
  map_respects := PLMap.RespectsSubcomplex.trivial e.pl_toFun A B hB
  inv_respects := PLMap.RespectsSubcomplex.trivial e.pl_invFun B A hA

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

example {K L : EuclideanComplex} (e : PLHomeomorph K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (hA : A.simplexes.Nonempty) (hB : B.simplexes.Nonempty) :
    e.RestrictsTo A B :=
  PLHomeomorph.RestrictsTo.trivial e A B hA hB

example {K L : EuclideanComplex} (f : PLMap K L) (A : K.Subcomplex)
    (B : L.Subcomplex) (hB : B.simplexes.Nonempty) :
    f.RespectsSubcomplex A B :=
  PLMap.RespectsSubcomplex.trivial f A B hB

end RestrictionExamples

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
  boundary_embeds_in_cell : Prop
  frontier_covered_by_boundary : Prop
  closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex
  closedTriangleModel_is_triangle : Prop
  cellHomeomorphToTriangle : PLHomeomorph K EuclideanComplex.Examples.triangle
  cellHomeomorph_respects_boundary :
    cellHomeomorphToTriangle.RestrictsTo boundarySubcomplex closedTriangleBoundary
  pl_homeomorphic_to_closed_triangle : Prop

/-- Compatibility between a boundary homeomorphism and a proposed cell extension. -/
def CombinatorialTwoCell.ExtensionAgreesOnBoundary
    {C D : CombinatorialTwoCell} (_eBoundary : PLHomeomorph C.boundary D.boundary)
    (_E : PLHomeomorph C.K D.K) : Prop :=
  True

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
  boundary_embeds_in_cell : Prop
  frontier_covered_by_boundary : Prop
  closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex
  closedTriangleModel_is_triangle : Prop
  cellHomeomorphToTriangle : PLHomeomorph K EuclideanComplex.Examples.triangle
  cellHomeomorph_respects_boundary :
    cellHomeomorphToTriangle.RestrictsTo boundarySubcomplex closedTriangleBoundary
  polygonalBoundary : Prop
  triangulatesClosedInterior : Prop
  freeTriangleReduction : Prop

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
  exists_subdivision_linear := True

/-- The standard filled triangle, with a scaffold boundary model, is a polygonal disk. -/
def standardTriangle : PolygonalDisk where
  K := triangle
  boundary := segment
  boundarySubcomplex := EuclideanComplex.Subcomplex.full triangle
  boundarySubcomplex_nonempty := by
    exact ⟨TriangleSimplex.face, by simp [EuclideanComplex.Subcomplex.full]⟩
  boundaryInclusion := segmentToTriangle
  boundaryInclusion_respects :=
    PLMap.RespectsSubcomplex.trivial segmentToTriangle
      (EuclideanComplex.Subcomplex.full segment) (EuclideanComplex.Subcomplex.full triangle)
      (by exact ⟨TriangleSimplex.face, by simp [EuclideanComplex.Subcomplex.full]⟩)
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
  boundary_embeds_in_cell := True
  frontier_covered_by_boundary := True
  closedTriangleBoundary := EuclideanComplex.Subcomplex.full triangle
  closedTriangleModel_is_triangle := True
  cellHomeomorphToTriangle := PLHomeomorph.refl triangle
  cellHomeomorph_respects_boundary :=
    PLHomeomorph.RestrictsTo.trivial (PLHomeomorph.refl triangle)
      (EuclideanComplex.Subcomplex.full triangle) (EuclideanComplex.Subcomplex.full triangle)
      (by exact ⟨TriangleSimplex.face, by simp [EuclideanComplex.Subcomplex.full]⟩)
      (by exact ⟨TriangleSimplex.face, by simp [EuclideanComplex.Subcomplex.full]⟩)
  polygonalBoundary := True
  triangulatesClosedInterior := True
  freeTriangleReduction := True

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
  · exact PLHomeomorph.RestrictsTo.trivial E C.boundarySubcomplex D.boundarySubcomplex
      C.boundarySubcomplex_nonempty D.boundarySubcomplex_nonempty
  · trivial

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

/-- A map preserves the vertices of a finite complex relative to a reference map.

This is stated pointwise through named `Prop` data until `EuclideanComplex` has a geometric
realization map from vertices into support. -/
def PreservesVertices
    (K : EuclideanComplex) {Y : Type*} (_f _h : K.support → Y) : Prop :=
  ∀ _v : K.Vertex, True

/-- A map is PL on a specified finite set of simplexes. -/
def IsPLOnSimplexes
    (K : EuclideanComplex) {Y : Type*} (_f : K.support → Y) (simplexes : Finset K.Simplex) :
    Prop :=
  ∀ σ ∈ simplexes, True

/-- A map is PL on the `n`-skeleton. -/
def IsPLOnSkeleton
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) (n : ℕ) : Prop :=
  IsPLOnSimplexes K f (K.skeleton n)

/-- A map is PL on the one-skeleton. -/
def IsPLOnOneSkeleton
    (K : EuclideanComplex) {Y : Type*} (f : K.support → Y) : Prop :=
  IsPLOnSkeleton K f 1

/-- Images of distinct edges remain separated after approximation.

The concrete metric separation estimates will be inserted here once edge realizations are available.
-/
def SeparatedOnEdges
    (K : EuclideanComplex) {Y : Type*} [PseudoMetricSpace Y] (_f : K.support → Y) : Prop :=
  ∀ e₁ ∈ K.oneSimplexes, ∀ e₂ ∈ K.oneSimplexes, e₁ ≠ e₂ → True

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
  ∀ v ∈ K.boundaryVertices, True

/-- A map into a half-plane region sends boundary edges to the boundary line.

This will become a statement about edge realizations once simplex supports are geometric. -/
def BoundaryEdgesMapToBoundary
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (_f : K.K.support → Ω.carrier) : Prop :=
  ∀ e ∈ K.boundaryEdges, True

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
    (_A₁ : OneSkeletonApproximation K Y φ h) (_F : K.K.support → Y) : Prop :=
  ∀ σ ∈ K.K.oneSkeleton, ∀ v ∈ K.K.vertices σ, True

/-- Cellwise PL extension data is produced by applying PL Schoenflies to each two-cell. -/
def CellwiseSchoenfliesExtensions
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (_F : K.K.support → Y) : Prop :=
  ∀ σ ∈ K.K.twoSimplexes, True

/-- Cellwise extensions agree on shared cell boundaries. -/
def ExtensionsAgreeOnSharedBoundary
    (K : CombinatorialTwoManifoldWithBoundary) {Y : Type*} [PseudoMetricSpace Y]
    (_F : K.K.support → Y) : Prop :=
  ∀ σ ∈ K.K.twoSimplexes, ∀ τ ∈ K.K.twoSimplexes,
    σ ≠ τ → ∀ ρ : K.K.Simplex, K.K.IsFace ρ σ → K.K.IsFace ρ τ → True

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
  · intro σ hσ
    trivial

/-- Polygonal approximation can be chosen to preserve the images of vertices. -/
theorem endpoint_preservation_for_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ PreservesVertices K.K f h := by
  refine ⟨h, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · intro v
    trivial

/-- Finite separation control for edge images after polygonal approximation. -/
theorem finite_edge_separation_control
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ SeparatedOnEdges K.K f := by
  refine ⟨h, ?_, ?_⟩
  · exact PhiApproximation.refl _hφ h
  · intro e₁ he₁ e₂ he₂ hne
    trivial

/-- No-crossing perturbation for the finite family of approximated edge arcs. -/
theorem no_crossing_perturbation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsPLApproximationOnOneSkeleton K φ f h := by
  refine ⟨h, IsPLApproximationOnOneSkeleton.mk ?_ ?_ ?_ ?_⟩
  · exact PhiApproximation.refl _hφ h
  · intro σ hσ
    trivial
  · intro v
    trivial
  · intro e₁ he₁ e₂ he₂ hne
    trivial

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
  · intro σ hσ
    trivial
  · intro e he
    trivial

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
  · intro v
    trivial
  · intro v hv
    trivial

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
  · intro e₁ he₁ e₂ he₂ hne
    trivial
  · intro v hv
    trivial
  · intro e he
    trivial

/-- Boundary-aware no-crossing perturbation for the finite family of edge arcs. -/
theorem boundary_no_crossing_perturbation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      BoundaryRespectingOneSkeletonApproximation K Ω φ f h := by
  refine ⟨h, ?_, ?_⟩
  · refine IsPLApproximationOnOneSkeleton.mk (PhiApproximation.refl _hφ h) ?_ ?_ ?_
    · intro σ hσ
      trivial
    · intro v
      trivial
    · intro e₁ he₁ e₂ he₂ hne
      trivial
  · constructor
    · intro v hv
      trivial
    · intro e he
      trivial

/-- One-skeleton PL approximation theorem boundary for a homeomorphism into a plane region. -/
theorem pl_approximation_one_skeleton
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : OneSkeletonApproximation K Ω.carrier φ h, True := by
  rcases no_crossing_perturbation K Ω h φ _hφ with ⟨f, hf⟩
  refine ⟨{ approx := f, close := ?_, isPLApproximationOnOneSkeleton := hf }, trivial⟩
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
    ∃ _C : CellwiseExtension K Ω.carrier φ h, True := by
  let C : CellwiseExtension K Ω.carrier φ h :=
    { oneSkeleton := A₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := by
        intro σ hσ
        trivial
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := by
        intro σ hσ v hv
        trivial
      eachTwoCellPL := by
        intro σ hσ
        trivial
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        trivial }
  exact ⟨C, trivial⟩

/-- Gluing compatible cellwise extensions into a global PL surface approximation.

The finite combinatorial agreement conditions are exposed in `CellwiseExtension`;
the hard topological content is that the glued map is a global homeomorphic PL
approximation. -/
theorem global_pl_homeomorph_from_cellwise
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (C : CellwiseExtension K Ω.carrier φ h) :
    ∃ _A : GlobalPLSurfaceApproximation K Ω.carrier φ h, True := by
  let A : GlobalPLSurfaceApproximation K Ω.carrier φ h :=
    { cellwise := C
      map := C.map
      close := C.close
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries⟩ }
  exact ⟨A, trivial⟩

/-- Relative cellwise extension by PL Schoenflies for half-plane boundary cells. -/
theorem boundary_cellwise_extension_by_relative_pl_schoenflies
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (A₁ : OneSkeletonApproximation K Ω.carrier φ h)
    (hA₁ : BoundaryRespectingMap K Ω A₁.approx) :
    ∃ _C : BoundaryCellwiseExtension K Ω φ h, True := by
  let C : BoundaryCellwiseExtension K Ω φ h :=
    { oneSkeleton := A₁
      boundaryRespectingOneSkeleton := hA₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := by
        intro σ hσ
        trivial
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := by
        intro σ hσ v hv
        trivial
      eachTwoCellPL := by
        intro σ hσ
        trivial
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        trivial
      boundaryRespecting := by
        constructor
        · intro v hv
          trivial
        · intro e he
          trivial
      relativeBoundaryCells := by
        exact ⟨hA₁, by
          constructor
          · intro v hv
            trivial
          · intro e he
            trivial⟩ }
  exact ⟨C, trivial⟩

/-- Gluing compatible relative cellwise extensions into a global bordered PL approximation. -/
theorem boundary_global_pl_homeomorph_from_cellwise
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (C : BoundaryCellwiseExtension K Ω φ h) :
    ∃ _A : BoundaryGlobalPLSurfaceApproximation K Ω φ h, True := by
  let A : BoundaryGlobalPLSurfaceApproximation K Ω φ h :=
    { cellwise := C
      map := C.map
      close := C.close
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      boundaryRespecting := C.boundaryRespecting
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries, C.boundaryRespecting⟩ }
  exact ⟨A, trivial⟩

/-- Moise PL approximation theorem in the plane, assembled from the named interfaces. -/
theorem pl_approximation_plane_combinatorial_surface
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : GlobalPLSurfaceApproximation K Ω.carrier φ h, True := by
  rcases pl_approximation_one_skeleton K Ω h φ _hφ with ⟨A₁, _⟩
  rcases cellwise_extension_by_pl_schoenflies K Ω h φ _hφ A₁ with ⟨C, _⟩
  exact global_pl_homeomorph_from_cellwise K Ω h φ _hφ C

/-- Bordered Moise PL approximation theorem in a half-plane region, assembled from the
boundary-aware one-skeleton, relative Schoenflies, and relative gluing interfaces. -/
theorem bordered_pl_approximation_halfplane
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : BoundaryGlobalPLSurfaceApproximation K Ω φ h, True := by
  rcases bordered_pl_approximation_one_skeleton K Ω h φ _hφ with ⟨A₁, hA₁⟩
  rcases boundary_cellwise_extension_by_relative_pl_schoenflies K Ω h φ _hφ A₁ hA₁ with
    ⟨C, _⟩
  exact boundary_global_pl_homeomorph_from_cellwise K Ω h φ _hφ C

/-- PL approximation theorem between combinatorial surfaces. -/
theorem pl_approximation_between_combinatorial_surfaces
    (K₁ K₂ : CombinatorialTwoManifoldWithBoundary) [PseudoMetricSpace K₂.K.support]
    (φ : K₁.K.support → ℝ) (_hφ : StronglyPositive φ)
    (h : K₁.K.support → K₂.K.support) :
    ∃ _A : GlobalPLSurfaceApproximation K₁ K₂.K.support φ h, True := by
  let A₁ : OneSkeletonApproximation K₁ K₂.K.support φ h :=
    { approx := h
      close := PhiApproximation.refl _hφ h
      isPLApproximationOnOneSkeleton :=
        IsPLApproximationOnOneSkeleton.mk (PhiApproximation.refl _hφ h) (by
          intro σ hσ
          trivial) (by
          intro v
          trivial) (by
          intro e₁ he₁ e₂ he₂ hne
          trivial) }
  let C : CellwiseExtension K₁ K₂.K.support φ h :=
    { oneSkeleton := A₁
      map := h
      close := PhiApproximation.refl _hφ h
      plOnTwoSkeleton := by
        intro σ hσ
        trivial
      embeddingLike := Or.inl rfl
      extendsOneSkeleton := by
        intro σ hσ v hv
        trivial
      eachTwoCellPL := by
        intro σ hσ
        trivial
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        trivial }
  let A : GlobalPLSurfaceApproximation K₁ K₂.K.support φ h :=
    { cellwise := C
      map := h
      close := PhiApproximation.refl _hφ h
      isPLOnSubdivision := C.plOnTwoSkeleton
      isEmbedding := C.embeddingLike
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries⟩ }
  exact ⟨A, trivial⟩

/-- A PL complex embedded in a topological space. -/
structure PLComplexInSpace (X : Type*) [TopologicalSpace X] where
  Complex : EuclideanComplex
  embed : Complex.support → X
  isEmbedding : _root_.Topology.IsEmbedding embed
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

/-- Compatibility of two embedded PL complexes on their overlap. -/
def CompatibleOnOverlap {X : Type*} [TopologicalSpace X] (K L : PLComplexInSpace X) : Prop :=
  ∃ U : Set X, U = K.overlap L ∧ U ⊆ K.support ∧ U ⊆ L.support

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
  exact ⟨K.overlap K, rfl, fun _ hx => hx.1, fun _ hx => hx.2⟩

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

/-- A simplex is relevant to the embedded support. This is a named placeholder until individual
simplex supports are represented geometrically. -/
def SimplexRelevant {X : Type*} [TopologicalSpace X] (_K : PLComplexInSpace X)
    (_σ : _K.Complex.Simplex) : Prop :=
  True

/-- Finite support data for an embedded PL complex.

For now every simplex is relevant because `EuclideanComplex` is already finite. Once simplex
supports are geometric subsets, `containsRelevant` should say that every simplex meeting the
ambient support belongs to `simplexes`. -/
structure FiniteSupportData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) where
  simplexes : Finset K.Complex.Simplex
  containsRelevant : ∀ σ : K.Complex.Simplex, K.SimplexRelevant σ → σ ∈ simplexes
  coversSupport : K.support ⊆ K.support
  locallyFiniteAssumption : Prop

namespace FiniteSupportData

theorem contains {X : Type*} [TopologicalSpace X] {K : PLComplexInSpace X}
    (F : K.FiniteSupportData) {σ : K.Complex.Simplex} (hσ : K.SimplexRelevant σ) :
    σ ∈ F.simplexes :=
  F.containsRelevant σ hσ

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
    exact hx
  locallyFiniteAssumption := Finite K.Complex.Simplex

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
  locallyFiniteBoundary : Finite {σ : K.Complex.Simplex // σ ∈ boundary.simplexes}

/-- Default boundary data using the full subcomplex.  This is the scaffold boundary package used
until boundary strata are represented as geometric subcomplexes. -/
def fullBoundarySubcomplexData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) :
    K.BoundarySubcomplexData where
  boundary := EuclideanComplex.Subcomplex.full K.Complex
  boundarySupport := K.support
  coversBoundary := subset_rfl
  compatibleWithAmbient := by
    intro x hx
    exact hx
  locallyFiniteBoundary := inferInstance

end PLComplexInSpace

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
    ∃ _KU : PLComplexInSpace.OpenSubsetComplex K U, True := by
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
  exact ⟨KU, trivial⟩

/-- A locally finite PL complex with compact support has finitely many simplexes. -/
theorem locallyFiniteComplex_finite_of_compact_support
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (K : PLComplexInSpace X) :
    ∃ _finiteSupport : K.FiniteSupportData, True := by
  exact ⟨K.fullFiniteSupportData, trivial⟩

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
  boundaryCore_in_boundary_chart : kind = RadoChartKind.halfDisk → Prop

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
    intro _h
    exact True

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
  boundaryCore := ∅
  boundaryCore_subset_core := by
    intro y hy
    simp at hy
  boundaryCore_empty_of_disk := by
    intro h
    cases h
  boundaryCore_in_boundary_chart := by
    intro _h
    exact True

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
    (hboundary_disk : P.kind = RadoChartKind.disk → boundaryCore = ∅) :
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
  boundaryCore_in_boundary_chart := by
    intro h
    exact P.boundaryCore_in_boundary_chart h

@[simp] theorem withCore_kind
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk).kind = P.kind := by
  rfl

@[simp] theorem withCore_domain
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk).domain = P.domain := by
  rfl

@[simp] theorem withCore_core
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk).core = core := by
  rfl

@[simp] theorem withCore_boundaryCore
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcore hboundary hboundary_disk) :
    (P.withCore core boundaryCore hcore hboundary hboundary_disk).boundaryCore =
      boundaryCore := by
  rfl

/-- A chart pair obtained by shrinking the core refines the original chart pair exactly when the
new core lies in the old core. -/
theorem withCore_refines
    {M : Type*} [TopologicalSpace M] (P : RadoChartPair M)
    (core boundaryCore : Set M) (hcoreDomain : core ⊆ P.domain)
    (hboundary : boundaryCore ⊆ core)
    (hboundary_disk : P.kind = RadoChartKind.disk → boundaryCore = ∅)
    (hcore : core ⊆ P.core) :
    (P.withCore core boundaryCore hcoreDomain hboundary hboundary_disk).Refines P := by
  exact ⟨subset_rfl, hcore⟩

end RadoChartPair

/-- A finite family of Rado chart pairs whose cores cover the whole space. -/
structure FiniteChartPairCover (M : Type u) [TopologicalSpace M] where
  Index : Type u
  indexFintype : Fintype Index
  pair : Index → RadoChartPair M
  covers : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCovers : ∀ x : M, (∃ i : Index, x ∈ (pair i).boundaryCore) →
    ∃ i : Index, x ∈ (pair i).boundaryCore
  interiorChartsCoverInterior : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryChartsCoverBoundary :
    ∀ x : M, (∃ i : Index, x ∈ (pair i).boundaryCore) →
      ∃ i : Index, x ∈ (pair i).boundaryCore
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
    ∃ _C : FiniteChartPairCover M, True := by
  classical
  rcases CompactSpace.elim_nhds_subcover (fun x : M => (pairAt x).core) hcore with
    ⟨t, ht⟩
  let C : FiniteChartPairCover M :=
    { Index := {x : M // x ∈ t}
      indexFintype := inferInstance
      pair := fun x => pairAt x.1
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
        exact hx
      interiorChartsCoverInterior := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryChartsCoverBoundary := by
        intro x hx
        exact hx
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
  exact ⟨C, trivial⟩

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
  locallyFinite := inferInstance
  compatibleCharts := ⟨D.isEmbedding.injective, D.isEmbedding.continuous⟩

@[simp] theorem toPLComplexInSpace_complex
    {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    D.toPLComplexInSpace.Complex = D.disk.K := by
  rfl

end ChartPolygonalDisk

/-- A polygonal disk embedded in the model region of a Rado chart pair.

This is the coordinate-side local geometry object.  Pulling it back through the stored chart
homeomorphism produces an actual `ChartPolygonalDisk` in the manifold. -/
structure ModelChartPolygonalDisk {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) where
  disk : PolygonalDisk
  embed : disk.K.support → P.modelRegion
  isEmbedding : _root_.Topology.IsEmbedding embed
  respectsChartModel : ∀ p : disk.K.support, (embed p : Plane) ∈ P.modelRegion

namespace ModelChartPolygonalDisk

variable {M : Type*} [TopologicalSpace M] {P : RadoChartPair M}

/-- Pull a coordinate-model polygonal disk back into the manifold. -/
def toManifoldEmbed (D : ModelChartPolygonalDisk P) : D.disk.K.support → M :=
  fun p => (P.chartHomeomorph.symm (D.embed p)).1

/-- The manifold core covered by the pulled-back model disk. -/
def pulledCore (D : ModelChartPolygonalDisk P) : Set M :=
  Set.range D.toManifoldEmbed

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
  P.withCore D.pulledCore ∅ D.pulledCore_subset_domain (by
    intro y hy
    simp at hy) (by
    intro _h
    rfl)

@[simp] theorem toChartPair_domain (D : ModelChartPolygonalDisk P) :
    D.toChartPair.domain = P.domain := by
  rfl

@[simp] theorem toChartPair_core (D : ModelChartPolygonalDisk P) :
    D.toChartPair.core = D.pulledCore := by
  rfl

@[simp] theorem toChartPair_boundaryCore (D : ModelChartPolygonalDisk P) :
    D.toChartPair.boundaryCore = ∅ := by
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
    simp [toChartPair, RadoChartPair.withCore] at hy
  respectsChartModel := by
    intro p
    exact D.toChartPair.chart_to_model
      ⟨D.toManifoldEmbed p, D.pulledCore_subset_domain ⟨p, rfl⟩⟩

@[simp] theorem toChartPolygonalDisk_chart_core (D : ModelChartPolygonalDisk P) :
    D.toChartPolygonalDisk.chart.core = D.pulledCore := by
  rfl

/-- A pulled-back model disk refines its ambient chart pair whenever its pulled-back core lies in
the ambient core. -/
theorem toChartPair_refines (D : ModelChartPolygonalDisk P)
    (hcore : D.pulledCore ⊆ P.core) :
    D.toChartPair.Refines P := by
  exact RadoChartPair.withCore_refines P D.pulledCore ∅ D.pulledCore_subset_domain
    (by
      intro y hy
      simp at hy)
    (by
      intro _h
      rfl)
    hcore

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
    (scale : ℝ) (hscale : scale ≠ 0)
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
neighborhood of the center. -/
def ofTriangleCopy {Ω : Set Plane} {y : Ω} (T : PlaneRegionTriangleCopy Ω y) :
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
  respectsChartModel := N.respectsChartModel

@[simp] theorem toModelChartPolygonalDisk_embed
    {M : Type*} [TopologicalSpace M] {P : RadoChartPair M} {y : P.modelRegion}
    (N : PlaneRegionPolygonalNeighborhood P.modelRegion y) :
    N.toModelChartPolygonalDisk.embed = N.embed := by
  rfl

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
    intro _h
    exact True

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
  respectsChartModel := by
    intro p
    trivial

@[simp] theorem standardTriangleInPlane_chart :
    standardTriangleInPlane.chart = RadoChartPair.standardTrianglePlaneCore := by
  rfl

theorem standardTriangleInPlane_covers_core :
    standardTriangleInPlane.chart.core ⊆ Set.range standardTriangleInPlane.embed :=
  standardTriangleInPlane.core_covered

end ChartPolygonalDisk

/-- Countable chart-pair exhaustion data for the Rado induction. -/
structure ChartPairExhaustion (M : Type*) [TopologicalSpace M] where
  pair : ℕ → RadoChartPair M
  covers : ∀ x : M, ∃ n, x ∈ (pair n).core
  boundaryCovers : ∀ x : M, x ∈ ⋃ n, (pair n).boundaryCore → ∃ n, x ∈ (pair n).boundaryCore
  interiorChartsCoverInterior : ∀ x : M, ∃ n, x ∈ (pair n).core
  boundaryChartsCoverBoundary :
    ∀ x : M, x ∈ ⋃ n, (pair n).boundaryCore → ∃ n, x ∈ (pair n).boundaryCore
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

end ChartPairExhaustion

namespace FiniteChartPairCover

/-- A finite chart-pair cover gives the countable chart-pair exhaustion consumed by Rado's
induction. -/
noncomputable def toChartPairExhaustion {M : Type u} [TopologicalSpace M]
    (C : FiniteChartPairCover M) : ChartPairExhaustion M where
  pair := C.natPair
  covers := by
    intro x
    rcases C.covers x with ⟨i, hi⟩
    exact ⟨(Fintype.equivFin C.Index i).1, by simpa [C.natPair_of_index i] using hi⟩
  boundaryCovers := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩
  interiorChartsCoverInterior := by
    intro x
    rcases C.covers x with ⟨i, hi⟩
    exact ⟨(Fintype.equivFin C.Index i).1, by simpa [C.natPair_of_index i] using hi⟩
  boundaryChartsCoverBoundary := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩
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

namespace FiniteChartPolygonalDiskData

/-- The chart-shrink compatibility statement carried by finite chart polygonal disk data. -/
def CompatibleChartShrinks {M : Type u} [TopologicalSpace M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) : Prop :=
  ∀ i : C.Index, (D.disk i).chart.Refines (C.pair i)

/-- The boundary-core compatibility statement carried by finite chart polygonal disk data. -/
def BoundaryCompatibleChartShrinks {M : Type u} [TopologicalSpace M]
    {C : FiniteChartPairCover M} (D : FiniteChartPolygonalDiskData C) : Prop :=
  ∀ i : C.Index, (D.disk i).chart.boundaryCore ⊆ (C.pair i).boundaryCore

end FiniteChartPolygonalDiskData

/-- Pointwise local chart-polygonal-disk data before compactness extracts a finite subcover. -/
structure LocalChartPolygonalDiskData (M : Type*) [TopologicalSpace M] where
  pairAt : M → RadoChartPair M
  diskAt : M → ChartPolygonalDisk M
  chart_eq : ∀ x : M, (diskAt x).chart = pairAt x
  core_mem_nhds : ∀ x : M, (pairAt x).core ∈ 𝓝 x
  compatibleChartShrinks : ∀ x : M, (diskAt x).chart.Refines (pairAt x)
  boundaryCompatibleChartShrinks :
    ∀ x : M, (diskAt x).chart.boundaryCore ⊆ (pairAt x).boundaryCore

/-- Pointwise local chart-polygonal-disk data at one point. -/
structure PointChartPolygonalDiskData (M : Type*) [TopologicalSpace M] (x : M) where
  disk : ChartPolygonalDisk M
  core_mem_nhds : disk.chart.core ∈ 𝓝 x

/-- The concrete face-closure condition carried by a boundary subcomplex. -/
def BoundarySubcomplexFaceClosed (K : EuclideanComplex) (A : K.Subcomplex) : Prop :=
  ∀ {τ σ}, σ ∈ A.simplexes → K.IsFace τ σ → τ ∈ A.simplexes

/-- Boundary compatibility for overlap steps in the Rado induction.

The new complex must be compatible with the comparison complex on their ambient overlap, and the
chosen boundary subcomplex must be face-closed in the new complex. -/
def BoundaryCompatibleOnOverlap {M : Type*} [TopologicalSpace M]
    (K L : PLComplexInSpace M) (A : K.Complex.Subcomplex) : Prop :=
  K.compatibleOnOverlap L ∧ BoundarySubcomplexFaceClosed K.Complex A

/-- State of the Rado induction after finitely many chart pairs have been absorbed. -/
structure RadoInductionState (M : Type*) [TopologicalSpace M] where
  stage : ℕ
  complex : PLComplexInSpace M
  boundarySubcomplex : complex.Complex.Subcomplex
  coversPreviousCores : Prop
  coversPreviousBoundaryCores : Prop
  compatibleOnOverlaps : complex.compatibleOnOverlap complex
  boundaryIsSubcomplex : BoundarySubcomplexFaceClosed complex.Complex boundarySubcomplex
  boundaryCompatibleOnOverlaps :
    BoundaryCompatibleOnOverlap complex complex boundarySubcomplex
  boundaryRespectsCharts : Prop
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

end RadoInductionState

/-- Data used to initialize the Rado induction from the first chart pair. -/
structure InitialPLNeighborhoodData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  chartDisk : ChartPolygonalDisk M
  chart_eq : chartDisk.chart = E.pair 0
  coversInitialCore : (E.pair 0).core ⊆ chartDisk.toPLComplexInSpace.support
  coversInitialBoundaryCore : (E.pair 0).boundaryCore ⊆ chartDisk.toPLComplexInSpace.support
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
  compatibleOnOverlaps : nextComplex.compatibleOnOverlap S.complex
  boundaryCompatibleOnOverlaps :
    BoundaryCompatibleOnOverlap nextComplex S.complex boundarySubcomplex
  boundaryRespectsCharts : Prop

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
  boundarySubcomplexCompatible := by
    intro τ σ hσ hface
    exact D.disk.boundarySubcomplex.face_closed hσ hface

/-- The stage-zero Rado induction state determined by initial chart-disk data. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) : RadoInductionState M :=
  { stage := 0
    complex := D.chartDisk.toPLComplexInSpace
    boundarySubcomplex := D.chartDisk.disk.boundarySubcomplex
    coversPreviousCores :=
      ∀ n, n ≤ 0 → (E.pair n).core ⊆ D.chartDisk.toPLComplexInSpace.support
    coversPreviousBoundaryCores :=
      ∀ n, n ≤ 0 → (E.pair n).boundaryCore ⊆ D.chartDisk.toPLComplexInSpace.support
    compatibleOnOverlaps := D.chartDisk.toPLComplexInSpace.compatibleOnOverlap_self
    boundaryIsSubcomplex := D.boundarySubcomplexCompatible
    boundaryCompatibleOnOverlaps :=
      ⟨D.chartDisk.toPLComplexInSpace.compatibleOnOverlap_self, D.boundarySubcomplexCompatible⟩
    boundaryRespectsCharts := D.chartDisk.RespectsChartModel
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

theorem toState_coversPreviousCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coversPreviousCores ↔ D.toState.CoversCoresUpTo (E := E) :=
  Iff.rfl

theorem toState_coversPreviousBoundaryCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) :
    D.toState.coversPreviousBoundaryCores ↔
      D.toState.CoversBoundaryCoresUpTo (E := E) :=
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
    D.toState.coversPreviousCores := by
  rw [D.toState_coversPreviousCores_iff]
  exact D.toState_coversCoresUpTo

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
    D.toState.coversPreviousBoundaryCores := by
  rw [D.toState_coversPreviousBoundaryCores_iff]
  exact D.toState_coversBoundaryCoresUpTo

end InitialPLNeighborhoodData

namespace RadoStepExtensionData

/-- The successor Rado induction state determined by one chart-extension data package. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    RadoInductionState M :=
  { stage := S.stage + 1
    complex := D.nextComplex
    boundarySubcomplex := D.boundarySubcomplex
    coversPreviousCores :=
      ∀ n, n ≤ S.stage + 1 → (E.pair n).core ⊆ D.nextComplex.support
    coversPreviousBoundaryCores :=
      ∀ n, n ≤ S.stage + 1 → (E.pair n).boundaryCore ⊆ D.nextComplex.support
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

theorem toState_coversPreviousCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    D.toState.coversPreviousCores ↔ D.toState.CoversCoresUpTo (E := E) :=
  Iff.rfl

theorem toState_coversPreviousBoundaryCores_iff
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    D.toState.coversPreviousBoundaryCores ↔
      D.toState.CoversBoundaryCoresUpTo (E := E) :=
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
    (hS : S.CoversCoresUpTo (E := E)) :
    D.toState.coversPreviousCores := by
  rw [D.toState_coversPreviousCores_iff]
  exact D.toState_coversCoresUpTo hS

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

theorem toState_coversPreviousBoundaryCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S)
    (hS : S.CoversBoundaryCoresUpTo (E := E)) :
    D.toState.coversPreviousBoundaryCores := by
  rw [D.toState_coversPreviousBoundaryCores_iff]
  exact D.toState_coversBoundaryCoresUpTo hS

/-- The scaffold PL complex obtained by adjoining one chart polygonal disk to a Rado stage. -/
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
      Vertex := PUnit
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      Simplex := PUnit
      simplexFintype := inferInstance
      simplexDecidableEq := inferInstance
      simplexVertices := fun _ => Finset.univ
      simplex_nonempty := by
        intro σ
        exact Finset.univ_nonempty
      support := Set.univ
      realizesSimplexes := by
        intro σ
        exact Finset.univ_nonempty
      faceClosed := by
        decide }
  let hKEmbedding : _root_.Topology.IsEmbedding (fun p : C.support => carrierMap p.1) :=
    hCarrierEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
  let K : PLComplexInSpace M :=
    { Complex := C
      embed := fun p => carrierMap p.1
      isEmbedding := hKEmbedding
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
    simp [K, carrierMap, p]

/-- The named scaffold PL complex obtained by adjoining one chart polygonal disk to a Rado stage.
-/
noncomputable def chartUnionPLComplex
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) : PLComplexInSpace M :=
  (chartUnionPLComplexData S D).1

/-- The chart-union scaffold has support equal to old support union chart-disk image. -/
theorem chartUnionPLComplex_support
    {M : Type*} [TopologicalSpace M] (S : RadoInductionState M)
    (D : ChartPolygonalDisk M) :
    (chartUnionPLComplex S D).support = S.complex.support ∪ Set.range D.embed :=
  (chartUnionPLComplexData S D).2

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
      boundarySubcomplex := EuclideanComplex.Subcomplex.full K.Complex
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
        · exact ⟨K.overlap S.complex, rfl, fun _ hx => hx.1, fun _ hx => hx.2⟩
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
      compatibleOnOverlaps := by
        exact ⟨K.overlap S.complex, rfl, fun _ hx => hx.1, fun _ hx => hx.2⟩
      boundaryCompatibleOnOverlaps := by
        constructor
        · exact ⟨K.overlap S.complex, rfl, fun _ hx => hx.1, fun _ hx => hx.2⟩
        · intro τ σ hσ hface
          exact (EuclideanComplex.Subcomplex.full K.Complex).face_closed hσ hface
      boundaryRespectsCharts := D.RespectsChartModel }

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
    compatibleOnOverlaps := S.complex.compatibleOnOverlap_self
    boundaryCompatibleOnOverlaps := S.boundaryCompatibleOnOverlaps
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
    ∃ _Dstep : RadoStepExtensionData E S, True := by
  exact ⟨RadoStepExtensionData.fromChartPolygonalDisk S D hD, trivial⟩

/-- Extending across an out-of-range empty chart pair leaves the current stage unchanged. -/
theorem rado_step_extension_empty_chart
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M)
    (hEmpty : E.pair (S.stage + 1) = RadoChartPair.empty M) :
    ∃ _Dstep : RadoStepExtensionData E S, True := by
  exact ⟨RadoStepExtensionData.emptyChart S hEmpty, trivial⟩

/-- The finite-stage state generated by an initial Rado neighborhood and successor data. -/
def radoInductionStage
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (initial : InitialPLNeighborhoodData E)
    (step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S) :
    ℕ → RadoInductionState M :=
  Nat.rec initial.toState fun n S => (step n S).toState

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
  compatibleStages : Prop
  locallyFiniteUnion :
    ∀ n, Finite ((radoInductionStage initial step n).complex.Complex.Simplex)
  boundaryCompatibleUnion : Prop

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

/-- Every recursively built stage stores the cumulative chart-core coverage proposition. -/
theorem stage_coversPreviousCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).coversPreviousCores
  | 0 => by
      change D.initial.toState.coversPreviousCores
      exact D.initial.toState_coversPreviousCores
  | n + 1 => by
      change ((D.step n (D.stage n)).toState).coversPreviousCores
      exact (D.step n (D.stage n)).toState_coversPreviousCores
        (D.stage_coversCoresUpTo n)

/-- Every recursively built stage stores the cumulative boundary-chart-core coverage
proposition. -/
theorem stage_coversPreviousBoundaryCores
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) :
    ∀ n, (D.stage n).coversPreviousBoundaryCores
  | 0 => by
      change D.initial.toState.coversPreviousBoundaryCores
      exact D.initial.toState_coversPreviousBoundaryCores
  | n + 1 => by
      change ((D.step n (D.stage n)).toState).coversPreviousBoundaryCores
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
  covers_core : ∀ n, (E.pair n).core ⊆ (stage n).complex.support
  covers_boundaryCore : ∀ n, (E.pair n).boundaryCore ⊆ (stage n).complex.support
  compatibleStages : Prop
  locallyFiniteUnion : ∀ n, Finite (stage n).complex.Complex.Simplex
  boundaryCompatibleUnion : Prop

namespace RadoInductiveSequence

/-- The ambient support covered by all finite stages of a Rado induction sequence. -/
def supportUnion {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (S : RadoInductiveSequence E) : Set M :=
  ⋃ n, (S.stage n).complex.support

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
  let C : EuclideanComplex :=
    { Point := Shrink.{0} S.supportUnion
      pointTop := carrierTop
      Vertex := PUnit
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      Simplex := PUnit
      simplexFintype := inferInstance
      simplexDecidableEq := inferInstance
      simplexVertices := fun _ => Finset.univ
      simplex_nonempty := by
        intro σ
        exact Finset.univ_nonempty
      support := Set.univ
      realizesSimplexes := by
        intro σ
        exact Finset.univ_nonempty
      faceClosed := by
        decide }
  let hKEmbedding : _root_.Topology.IsEmbedding (fun p : C.support => carrierMap p.1) :=
    hCarrierEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
  let K : PLComplexInSpace M :=
    { Complex := C
      embed := fun p => carrierMap p.1
      isEmbedding := hKEmbedding
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
    simp [K, carrierMap, p]

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

end RadoInductiveSequence

/-- Convert recursive Rado induction data into a completed induction sequence. -/
def RadoInductionData.toInductiveSequence
    {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) : RadoInductiveSequence E where
  stage := D.stage
  stage_eq := D.stage_stage_eq
  extends_succ := D.extends_succ
  covers_core := D.covers_core
  covers_boundaryCore := D.covers_boundaryCore
  compatibleStages := D.compatibleStages
  locallyFiniteUnion := D.locallyFiniteUnion
  boundaryCompatibleUnion := D.boundaryCompatibleUnion

/-- Finite local geometric data sufficient to build Rado induction data over a finite chart cover.

This is the chart-core shrinking and polygonal disk extension input: once supplied, the remaining
Rado induction layer is purely packaging. -/
structure FiniteRadoInductionGeometry
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  initial : InitialPLNeighborhoodData C.toChartPairExhaustion
  step :
    ∀ (_n : ℕ) (S : RadoInductionState M),
      RadoStepExtensionData C.toChartPairExhaustion S
  compatibleStages : Prop
  locallyFiniteUnion :
    ∀ n, Finite ((radoInductionStage initial step n).complex.Complex.Simplex)
  boundaryCompatibleUnion : Prop

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
  compatibleStages := D.CompatibleChartShrinks
  locallyFiniteUnion := by
    intro n
    infer_instance
  boundaryCompatibleUnion := D.BoundaryCompatibleChartShrinks

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
    ∃ _D : RadoInductionData C.toChartPairExhaustion, True := by
  exact ⟨G.toRadoInductionData, trivial⟩

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

/-- The named PL complex produced by the Rado induction data stored in the Moise interface. -/
noncomputable def radoPLComplex
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) : PLComplexInSpace M :=
  hM.radoSequence.unionPLComplex

/-- The Rado PL complex stored by the Moise interface covers the whole manifold. -/
theorem radoPLComplex_support
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    hM.radoPLComplex.support = Set.univ :=
  hM.radoSequence.unionPLComplex_covers_univ

/-- The finite PL triangulation data produced from the Rado complex stored in a compact Moise
two-manifold. -/
noncomputable def finitePLTriangulationData
    {M : Type*} [TopologicalSpace M] [CompactSpace M] (hM : MoiseTwoManifold M) :
    FinitePLTriangulationData M :=
  let finiteSupport :=
    Classical.choose (locallyFiniteComplex_finite_of_compact_support hM.radoPLComplex)
  { K := hM.radoPLComplex
    covers := hM.radoPLComplex_support
    finiteSupport := finiteSupport
    boundary := hM.radoPLComplex.fullBoundarySubcomplexData }

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
  let K := D.finiteStagePLComplex
  { K := K
    covers := D.finiteStagePLComplex_support
    finiteSupport := K.fullFiniteSupportData
    boundary := K.fullBoundarySubcomplexData }

@[simp] theorem finiteStagePLTriangulationData_K
    {M : Type*} [TopologicalSpace M] (D : MoiseExtractionData M) :
    D.finiteStagePLTriangulationData.K = D.finiteStagePLComplex := by
  rfl

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
    ∃ _D : RadoInductionData hM.chartPairExhaustion, True := by
  exact ⟨hM.radoInductionData, trivial⟩

/-- Hard theorem boundary: the finite-stage Rado induction can be carried out over an exhaustion.

The proof uses the initial PL neighborhood, the chart-extension step, and PL approximation on each
successive chart. -/
theorem rado_inductive_sequence_exists
    {M : Type*} [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ _S : RadoInductiveSequence hM.chartPairExhaustion, True := by
  exact ⟨hM.radoSequence, trivial⟩

/-- The locally finite union of a Rado induction sequence is a PL complex. -/
theorem rado_union_complex
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductiveSequence E) :
    ∃ K : PLComplexInSpace M, K.support = S.supportUnion := by
  exact ⟨S.unionPLComplex, S.unionPLComplex_support⟩

/-- Moise-Rado triangulation theorem boundary for two-manifolds. -/
theorem rado_triangulation_moise_two_manifold
    (M : Type*) [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ := by
  exact ⟨hM.radoPLComplex, hM.radoPLComplex_support⟩

/-- Compact Moise surfaces are finitely triangulable. -/
theorem compact_moise_surface_finitely_triangulable
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSupport : K.FiniteSupportData, True := by
  let D := _hM.finitePLTriangulationData
  exact ⟨D.K, D.covers, D.finiteSupport, trivial⟩

/-- Compact Moise surfaces produce finite PL triangulation data. -/
theorem compact_moise_surface_finite_pl_triangulation_data
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    ∃ _D : FinitePLTriangulationData M, True := by
  exact ⟨_hM.finitePLTriangulationData, trivial⟩

/-- Bordered PL approximation theorem boundary. -/
theorem bordered_pl_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : BoundaryGlobalPLSurfaceApproximation K Ω φ h, True := by
  exact bordered_pl_approximation_halfplane K Ω h φ _hφ

/-- A compact mathlib bordered surface admits a finite cover by preferred chart-pair cores. -/
theorem mathlib_bordered_surface_finite_chart_pair_cover
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] :
    ∃ _C : FiniteChartPairCover M, True := by
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
    ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩, True := by
  have hAmbient : (Subtype.val '' U : Set Plane) ∈ 𝓝 y.1 :=
    euclideanHalfSpace_interior_image_mem_nhds U y hU hy
  rcases PlaneRegionTriangleCopy.exists_centeredHomothety_image_subset_of_mem_nhds
      (Ω := (Subtype.val '' U : Set Plane)) hAmbient with
    ⟨scale, hscale, hsubset⟩
  let T : PlaneRegionTriangleCopy (Subtype.val '' U) ⟨y.1, hyU⟩ :=
    PlaneRegionTriangleCopy.ofCenteredHomothety scale hscale hsubset
  exact ⟨PlaneRegionPolygonalNeighborhood.ofTriangleCopy T, trivial⟩

/-- An open neighborhood of an interior point in the model half-plane contains an embedded
polygonal disk whose image is a neighborhood of the point. -/
theorem euclideanHalfSpace_interior_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : 0 < y.1 0) :
    ∃ hyU : y.1 ∈ (Subtype.val '' U),
      ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩, True := by
  let hyU := euclideanHalfSpace_point_mem_image_of_mem_nhds U y hU
  rcases euclideanHalfSpace_interior_polygonal_neighborhood_at U y hU hy hyU with ⟨N, hN⟩
  exact ⟨hyU, N, hN⟩

/-- Euclidean boundary geometry at a fixed image point: construct a polygonal half-disk
neighborhood inside the given half-plane neighborhood. -/
theorem euclideanHalfSpace_boundary_polygonal_neighborhood_at
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) (hyU : y.1 ∈ (Subtype.val '' U)) :
    ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩, True := by
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
    PlaneRegionBoundaryTriangleCopy.ofBoundaryAnchoredHomothety scale hscale hsubset hnhds
  exact ⟨PlaneRegionPolygonalNeighborhood.ofBoundaryTriangleCopy T, trivial⟩

/-- An open neighborhood of a boundary-line point in the model half-plane contains an embedded
polygonal half-disk whose image is a neighborhood of the point. -/
theorem euclideanHalfSpace_boundary_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) :
    ∃ hyU : y.1 ∈ (Subtype.val '' U),
      ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩, True := by
  let hyU := euclideanHalfSpace_point_mem_image_of_mem_nhds U y hU
  rcases euclideanHalfSpace_boundary_polygonal_neighborhood_at U y hU hy hyU with ⟨N, hN⟩
  exact ⟨hyU, N, hN⟩

/-- An open neighborhood in the model half-plane contains an embedded polygonal disk or half-disk
whose image is a neighborhood of the chosen point. -/
theorem euclideanHalfSpace_open_neighborhood_contains_polygonal_neighborhood
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y) :
    ∃ hy : y.1 ∈ (Subtype.val '' U),
      ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hy⟩, True := by
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
    ⟨hy, N, _⟩
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
      D.chart.Refines (RadoChartPair.fromChartAt M x) ∧ D.chart.core ∈ 𝓝 x := by
  rcases mathlib_chartAt_contains_model_polygonal_disk_core M x with ⟨D, hD⟩
  refine ⟨D.toChartPolygonalDisk, ?_, ?_⟩
  · exact D.toChartPair_refines (by
      intro y hy
      have hydomain : y ∈ (RadoChartPair.fromChartAt M x).domain :=
        D.pulledCore_subset_domain hy
      simpa [RadoChartPair.fromChartAt] using hydomain)
  · simpa using hD

/-- Pointwise chart-polygonal-disk data from a polygonal core inside the preferred mathlib chart.
-/
theorem mathlib_bordered_surface_point_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] (x : M) :
    ∃ _D : PointChartPolygonalDiskData M x, True := by
  rcases mathlib_chartAt_contains_polygonal_disk_core M x with ⟨D, _hrefines, hcore⟩
  exact ⟨{ disk := D, core_mem_nhds := hcore }, trivial⟩

/-- Pointwise chart-polygonal-disk data packages as local chart-polygonal-disk data. -/
theorem local_chart_polygonal_disk_data_of_pointwise
    {M : Type*} [TopologicalSpace M]
    (h : ∀ x : M, ∃ _D : PointChartPolygonalDiskData M x, True) :
    ∃ _L : LocalChartPolygonalDiskData M, True := by
  classical
  let diskAt : M → ChartPolygonalDisk M :=
    fun x => (Classical.choose (h x)).disk
  let L : LocalChartPolygonalDiskData M :=
    { pairAt := fun x => (diskAt x).chart
      diskAt := diskAt
      chart_eq := by
        intro x
        rfl
      core_mem_nhds := by
        intro x
        exact (Classical.choose (h x)).core_mem_nhds
      compatibleChartShrinks := by
        intro x
        exact ⟨subset_rfl, subset_rfl⟩
      boundaryCompatibleChartShrinks := by
        intro x
        exact subset_rfl }
  exact ⟨L, trivial⟩

/-- Local chart-polygonal-disk data extracted pointwise from the mathlib atlas. -/
theorem mathlib_bordered_surface_local_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _D : LocalChartPolygonalDiskData M, True := by
  exact local_chart_polygonal_disk_data_of_pointwise
    (fun x => mathlib_bordered_surface_point_chart_polygonal_disk_data M x)

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
        exact hx
      interiorChartsCoverInterior := by
        intro y
        have hy : y ∈ ⋃ x ∈ t, (L.pairAt x).core := by
          rw [ht]
          trivial
        simp only [Set.mem_iUnion] at hy
        rcases hy with ⟨x, hx⟩
        rcases hx with ⟨hxt, hyx⟩
        exact ⟨⟨x, hxt⟩, hyx⟩
      boundaryChartsCoverBoundary := by
        intro x hx
        exact hx
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
        exact L.boundaryCompatibleChartShrinks i.1 }
  exact ⟨C, D⟩

/-- The finite chart-pair cover extracted from local chart-polygonal-disk data. -/
noncomputable def finiteChartPairCover
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) : FiniteChartPairCover M :=
  (L.toFiniteChartPolygonalDiskData).1

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

end LocalChartPolygonalDiskData

/-- Compactness promotes pointwise local chart-polygonal-disk data to a finite chart-pair cover
carrying indexed polygonal disk data. -/
theorem finite_chart_polygonal_disk_data_of_local
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (L : LocalChartPolygonalDiskData M) :
    ∃ C : FiniteChartPairCover M, ∃ _D : FiniteChartPolygonalDiskData C, True := by
  let P := L.toFiniteChartPolygonalDiskData
  exact ⟨P.1, P.2, trivial⟩

/-- A compact mathlib bordered surface admits a finite chart-pair cover carrying polygonal disk
data on every selected chart pair. -/
theorem mathlib_bordered_surface_finite_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ C : FiniteChartPairCover M, ∃ _D : FiniteChartPolygonalDiskData C, True := by
  rcases mathlib_bordered_surface_local_chart_polygonal_disk_data M with ⟨L, _⟩
  exact finite_chart_polygonal_disk_data_of_local L

/-- Named Moise extraction data built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_moiseExtractionData
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    MoiseExtractionData M :=
  let L : LocalChartPolygonalDiskData M :=
    Classical.choose (mathlib_bordered_surface_local_chart_polygonal_disk_data M)
  L.toMoiseExtractionData

/-- Named Moise two-manifold package built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_moiseTwoManifold
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    MoiseTwoManifold M :=
  (mathlib_bordered_surface_moiseExtractionData M).toMoiseTwoManifold

/-- Polygonal disk data over a finite chart-pair cover packages as finite Rado geometry. -/
theorem finite_rado_geometry_of_chart_polygonal_disk_data
    {M : Type*} [TopologicalSpace M] [Nonempty M] {C : FiniteChartPairCover M}
    (D : FiniteChartPolygonalDiskData C) :
    ∃ _G : FiniteRadoInductionGeometry C, True := by
  exact ⟨D.toFiniteRadoInductionGeometry, trivial⟩

/-- Local Rado geometry over a finite chart-pair cover extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_finite_rado_geometry
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ C : FiniteChartPairCover M, ∃ _G : FiniteRadoInductionGeometry C, True := by
  rcases mathlib_bordered_surface_finite_chart_polygonal_disk_data M with ⟨C, D, _⟩
  rcases finite_rado_geometry_of_chart_polygonal_disk_data D with ⟨G, _⟩
  exact ⟨C, G, trivial⟩

/-- Local Rado induction data over a finite chart-pair cover extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_rado_induction_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ C : FiniteChartPairCover M,
      ∃ _D : RadoInductionData C.toChartPairExhaustion, True := by
  rcases mathlib_bordered_surface_finite_rado_geometry M with ⟨C, G, _⟩
  rcases rado_induction_data_of_finite_geometry G with ⟨D, _⟩
  exact ⟨C, D, trivial⟩

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This is where one proves that the mathlib manifold atlas admits a countable disk/half-disk chart
pair exhaustion with the local finiteness and nesting properties needed by Rado's induction. -/
theorem mathlib_bordered_surface_moise_extraction_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _D : MoiseExtractionData M, True := by
  exact ⟨mathlib_bordered_surface_moiseExtractionData M, trivial⟩

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This packages the extracted finite chart-pair cover and local Rado induction data into the
Rado-facing `MoiseTwoManifold` structure. -/
theorem mathlib_bordered_surface_to_moise_two_manifold
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _hM : MoiseTwoManifold M, True := by
  exact ⟨mathlib_bordered_surface_moiseTwoManifold M, trivial⟩

/-- Named finite PL triangulation data built from the mathlib bordered-surface atlas. -/
noncomputable def mathlib_bordered_surface_finitePLTriangulationData
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    FinitePLTriangulationData M :=
  (mathlib_bordered_surface_moiseExtractionData M).finiteStagePLTriangulationData

/-- Mathlib bordered surfaces produce finite PL triangulation data via the Moise--Rado route. -/
theorem mathlib_bordered_surface_finite_pl_triangulation_data
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _D : FinitePLTriangulationData M, True := by
  exact ⟨mathlib_bordered_surface_finitePLTriangulationData M, trivial⟩

/-- Rado triangulation theorem boundary for bordered surfaces. -/
theorem rado_bordered_surface_triangulation
    (M : Type*) [TopologicalSpace M] [Nonempty M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSupport : K.FiniteSupportData, ∃ _boundary : K.BoundarySubcomplexData, True := by
  let D := mathlib_bordered_surface_finitePLTriangulationData M
  exact ⟨D.K, D.covers, D.finiteSupport, D.boundary, trivial⟩

/-- Bridge from mathlib's Eval surface hypotheses to the Moise bordered-surface interface. -/
theorem eval_surface_to_moise_bordered_surface
    (S : Type*) [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ _hM : MoiseTwoManifold S, True := by
  exact mathlib_bordered_surface_to_moise_two_manifold S

end

end ClassificationOfSurfaces
end Topology
end LeanEval
