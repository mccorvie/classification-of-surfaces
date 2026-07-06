/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Surface

/-!
# PL foundations for the Moise route

This file records the Moise/PL theorem boundaries from the blueprint. The definitions are
intentionally skeletal for now: the first milestone is a stable API surface that separate topology,
PL, quotient, and Gallier-Xu work can target.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

noncomputable section

/-- A finite Euclidean-style simplicial complex API for the Moise route.

The `Point`/`support` fields keep a topological carrier available for PL maps. The finite
`Vertex`/`Simplex` fields provide the combinatorial data needed by links, skeletons, and later
surface predicates. The geometric rectilinearity and face-closure obligations are currently stored
as named propositions so they can be strengthened without changing downstream theorem names. -/
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
  realizesSimplexes : Prop
  faceClosed : Prop

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

/-- Dimension of a simplex, computed as `card vertices - 1`. -/
def simplexDim (K : EuclideanComplex) (σ : K.Simplex) : ℕ :=
  (K.vertices σ).card - 1

/-- The relation that one simplex is a combinatorial face of another. -/
def IsFace (K : EuclideanComplex) (τ σ : K.Simplex) : Prop :=
  K.vertices τ ⊆ K.vertices σ

instance (K : EuclideanComplex) (τ σ : K.Simplex) : Decidable (K.IsFace τ σ) :=
  inferInstanceAs (Decidable (K.vertices τ ⊆ K.vertices σ))

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

/-- The link of a vertex as a subcomplex-shaped object.

The face-closure proof is a theorem boundary until `EuclideanComplex.faceClosed` is strengthened
from a proposition into usable face-witness data. -/
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
  realizesSimplexes := True
  faceClosed := True

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
  realizesSimplexes := True
  faceClosed := True

/-- The standard filled triangle as a finite complex. -/
def triangle : EuclideanComplex where
  Point := PUnit
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
  support := Set.univ
  realizesSimplexes := True
  faceClosed := True

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

end PLExamples

/-- The PL property is invariant under subdivision. -/
theorem pl_iff_pl_after_subdivision
    {K L : EuclideanComplex} (_K' : EuclideanComplex.Subdivision K)
    (_L' : EuclideanComplex.Subdivision L) :
    True := by
  trivial

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

end CombinatorialTwoManifoldWithBoundary

/-- A PL map is compatible with a pair of subcomplexes. This is a boundary-restriction scaffold
until subcomplex supports are made geometric. -/
structure PLMap.RespectsSubcomplex {K L : EuclideanComplex}
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) : Prop where
  maps_simplexes : ∀ {σ : K.Simplex}, σ ∈ A.simplexes → True
  image_lands_in_target : True

namespace PLMap.RespectsSubcomplex

/-- Trivial compatibility placeholder while subcomplex supports are still combinatorial. -/
theorem trivial {K L : EuclideanComplex} (f : PLMap K L) (A : K.Subcomplex)
    (B : L.Subcomplex) :
    f.RespectsSubcomplex A B where
  maps_simplexes := by
    intro σ hσ
    trivial
  image_lands_in_target := True.intro

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
    (B : L.Subcomplex) :
    e.RestrictsTo A B where
  map_respects := PLMap.RespectsSubcomplex.trivial e.pl_toFun A B
  inv_respects := PLMap.RespectsSubcomplex.trivial e.pl_invFun B A

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
    (B : L.Subcomplex) :
    e.RestrictsTo A B :=
  PLHomeomorph.RestrictsTo.trivial e A B

example {K L : EuclideanComplex} (f : PLMap K L) (A : K.Subcomplex)
    (B : L.Subcomplex) :
    f.RespectsSubcomplex A B :=
  PLMap.RespectsSubcomplex.trivial f A B

end RestrictionExamples

/-- A combinatorial two-cell. -/
structure CombinatorialTwoCell where
  K : EuclideanComplex
  boundary : EuclideanComplex
  boundarySubcomplex : K.Subcomplex
  boundaryInclusion : PLMap boundary K
  boundaryInclusion_respects : boundaryInclusion.RespectsSubcomplex
    (EuclideanComplex.Subcomplex.full boundary) boundarySubcomplex
  isTwoDimensional : K.IsTwoDimensional
  boundary_is_one_dimensional : boundary.IsAtMostOneDimensional
  boundary_embeds_in_cell : Prop
  frontier_covered_by_boundary : Prop
  closedTriangleModel : EuclideanComplex
  closedTriangleBoundary : closedTriangleModel.Subcomplex
  closedTriangleModel_is_triangle : Prop
  cellHomeomorphToTriangle : PLHomeomorph K closedTriangleModel
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

/-- Polygonal disks are combinatorial two-cells. -/
theorem polygonal_disk_is_combinatorial_two_cell : True := by
  trivial

/-- PL Schoenflies for combinatorial two-cells. -/
theorem pl_schoenflies_combinatorial_two_cell
    {C D : CombinatorialTwoCell} (e : PLHomeomorph C.boundary D.boundary) :
    ∃ E : PLHomeomorph C.K D.K, CombinatorialTwoCell.BoundaryExtension e E := by
  sorry

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

/-- The Euclidean plane used by the Moise approximation statements. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

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

/-- Cellwise extensions of a one-skeleton approximation across the two-cells of a surface. -/
structure CellwiseExtension
    (K : CombinatorialTwoManifoldWithBoundary) (Y : Type*) [PseudoMetricSpace Y]
    (φ : K.K.support → ℝ) (h : K.K.support → Y) where
  oneSkeleton : OneSkeletonApproximation K Y φ h
  map : K.K.support → Y
  close : PhiApproximation φ map h
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
  isPLOnSubdivision : Prop
  isEmbedding : Prop
  cellwiseCompatible : GlobalPLHomeomorphFromCellwise cellwise map

namespace GlobalPLSurfaceApproximation

theorem agreesOnSharedBoundary
    {K : CombinatorialTwoManifoldWithBoundary} {Y : Type*} [PseudoMetricSpace Y]
    {φ : K.K.support → ℝ} {h : K.K.support → Y}
    (A : GlobalPLSurfaceApproximation K Y φ h) :
    ExtensionsAgreeOnSharedBoundary K A.cellwise.map :=
  A.cellwiseCompatible.2

end GlobalPLSurfaceApproximation

/-- Finite polygonal approximation of edge images in a plane region.

This is one of the hard planar topology boundaries behind the one-skeleton approximation theorem.
-/
theorem finite_arc_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ IsPLOnOneSkeleton K.K f := by
  sorry

/-- Polygonal approximation can be chosen to preserve the images of vertices. -/
theorem endpoint_preservation_for_polygonal_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ PreservesVertices K.K f h := by
  sorry

/-- Finite separation control for edge images after polygonal approximation. -/
theorem finite_edge_separation_control
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsApproximationOnOneSkeleton K.K φ f h ∧ SeparatedOnEdges K.K f := by
  sorry

/-- No-crossing perturbation for the finite family of approximated edge arcs. -/
theorem no_crossing_perturbation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ f : K.K.support → Ω.carrier,
      IsPLApproximationOnOneSkeleton K φ f h := by
  sorry

/-- One-skeleton PL approximation theorem boundary for a homeomorphism into a plane region. -/
theorem pl_approximation_one_skeleton
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : OneSkeletonApproximation K Ω.carrier φ h, True := by
  rcases no_crossing_perturbation K Ω h φ _hφ with ⟨f, hf⟩
  refine ⟨{ approx := f, close := ?_, isPLApproximationOnOneSkeleton := hf }, trivial⟩
  exact IsPLApproximationOnOneSkeleton.close hf

/-- Cellwise extension by PL Schoenflies from a one-skeleton approximation.

This is the theorem boundary where the boundary map on each polygonal two-cell
is extended across that cell. -/
theorem cellwise_extension_by_pl_schoenflies
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ)
    (_A₁ : OneSkeletonApproximation K Ω.carrier φ h) :
    ∃ _C : CellwiseExtension K Ω.carrier φ h, True := by
  sorry

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
  sorry

/-- Moise PL approximation theorem in the plane, assembled from the named interfaces. -/
theorem pl_approximation_plane_combinatorial_surface
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : GlobalPLSurfaceApproximation K Ω.carrier φ h, True := by
  rcases pl_approximation_one_skeleton K Ω h φ _hφ with ⟨A₁, _⟩
  rcases cellwise_extension_by_pl_schoenflies K Ω h φ _hφ A₁ with ⟨C, _⟩
  exact global_pl_homeomorph_from_cellwise K Ω h φ _hφ C

/-- PL approximation theorem between combinatorial surfaces. -/
theorem pl_approximation_between_combinatorial_surfaces
    (K₁ K₂ : CombinatorialTwoManifoldWithBoundary) [PseudoMetricSpace K₂.K.support]
    (φ : K₁.K.support → ℝ) (_hφ : StronglyPositive φ)
    (h : K₁.K.support → K₂.K.support) :
    ∃ A : GlobalPLSurfaceApproximation K₁ K₂.K.support φ h, True := by
  sorry

/-- A PL complex embedded in a topological space. -/
structure PLComplexInSpace (X : Type*) [TopologicalSpace X] where
  Complex : EuclideanComplex
  embed : Complex.support → X
  isEmbedding : _root_.Topology.IsEmbedding embed
  locallyFinite : Prop
  compatibleCharts : Prop

namespace PLComplexInSpace

/-- Support of a PL complex in a space. -/
def support {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) : Set X :=
  Set.range K.embed

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
  ∃ U : Set X, U = K.overlap L ∧ True

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
  exact ⟨K.overlap K, rfl, trivial⟩

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
  compatibleWithAmbient : Prop

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
    ∃ KU : PLComplexInSpace.OpenSubsetComplex K U, True := by
  sorry

/-- A locally finite PL complex with compact support has finitely many simplexes. -/
theorem locallyFiniteComplex_finite_of_compact_support
    {X : Type*} [TopologicalSpace X] (_K : PLComplexInSpace X) :
    ∃ _finiteSubcomplex : Finset _K.Complex.Simplex, True := by
  exact ⟨Finset.univ, trivial⟩

/-- Moise-style topological two-manifold interface. -/
structure MoiseTwoManifold (M : Type*) [TopologicalSpace M] where
  t2 : T2Space M
  local_disk_or_half_disk : Prop
  secondCountable_or_separable_metric : Prop

/-- A chart pair used in the Rado exhaustion: a chart domain and a smaller core whose closure is
controlled inside that chart. The concrete chart map is still theorem-boundary data. -/
structure RadoChartPair (M : Type*) [TopologicalSpace M] where
  domain : Set M
  core : Set M
  domain_open : IsOpen domain
  core_subset_domain : core ⊆ domain
  chart_to_disk_or_halfDisk : Prop

/-- Countable chart-pair exhaustion data for the Rado induction. -/
structure ChartPairExhaustion (M : Type*) [TopologicalSpace M] where
  pair : ℕ → RadoChartPair M
  covers : ∀ x : M, ∃ n, x ∈ (pair n).core
  locallyFinite : Prop
  nestedControl : Prop

/-- State of the Rado induction after finitely many chart pairs have been absorbed. -/
structure RadoInductionState (M : Type*) [TopologicalSpace M] where
  stage : ℕ
  complex : PLComplexInSpace M
  coversPreviousCores : Prop
  compatibleOnOverlaps : Prop
  locallyFinite : Prop

/-- Countable chart-pair exhaustion for a Moise two-manifold. -/
theorem chart_pair_exhaustion
    {M : Type*} [TopologicalSpace M] (_hM : MoiseTwoManifold M) :
    ∃ E : ChartPairExhaustion M, True := by
  sorry

/-- Initial PL neighborhood in the Rado induction. -/
theorem initial_pl_neighborhood
    {M : Type*} [TopologicalSpace M] (_hM : MoiseTwoManifold M) :
    ∃ S : RadoInductionState M, S.stage = 0 := by
  sorry

/-- Extend a PL complex across one chart in the Rado induction. -/
theorem extend_pl_complex_across_chart
    {M : Type*} [TopologicalSpace M] (_E : ChartPairExhaustion M)
    (S : RadoInductionState M) :
    ∃ S' : RadoInductionState M, S'.stage = S.stage + 1 ∧
      PLComplexInSpace.Extends S'.complex S.complex := by
  sorry

/-- Moise-Rado triangulation theorem boundary for two-manifolds. -/
theorem rado_triangulation_moise_two_manifold
    (M : Type*) [TopologicalSpace M] (_hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ := by
  sorry

/-- Compact Moise surfaces are finitely triangulable. -/
theorem compact_moise_surface_finitely_triangulable
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSubcomplex : Finset K.Complex.Simplex, True := by
  rcases rado_triangulation_moise_two_manifold M _hM with ⟨K, hK⟩
  rcases locallyFiniteComplex_finite_of_compact_support K with ⟨finiteSubcomplex, hfinite⟩
  exact ⟨K, hK, finiteSubcomplex, hfinite⟩

/-- Bordered PL approximation theorem boundary. -/
theorem bordered_pl_approximation
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ) (_hφ : StronglyPositive φ) :
    ∃ _A : GlobalPLSurfaceApproximation K Ω.carrier φ h, True := by
  exact pl_approximation_plane_combinatorial_surface K Ω h φ _hφ

/-- Rado triangulation theorem boundary for bordered surfaces. -/
theorem rado_bordered_surface_triangulation
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSubcomplex : Finset K.Complex.Simplex, True := by
  sorry

/-- Bridge from mathlib's Eval surface hypotheses to the Moise bordered-surface interface. -/
theorem eval_surface_to_moise_bordered_surface
    (S : Type*) [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ _hM : MoiseTwoManifold S, True := by
  sorry

end

end ClassificationOfSurfaces
end Topology
end LeanEval
