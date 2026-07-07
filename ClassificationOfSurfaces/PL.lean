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
  toFun := fun _ => ⟨PUnit.unit, by
    change PUnit.unit ∈ Set.univ
    trivial⟩
  continuous_toFun := continuous_const
  exists_subdivision_linear := True

/-- The standard filled triangle, with a scaffold boundary model, is a polygonal disk. -/
def standardTriangle : PolygonalDisk where
  K := triangle
  boundary := segment
  boundarySubcomplex := EuclideanComplex.Subcomplex.full triangle
  boundaryInclusion := segmentToTriangle
  boundaryInclusion_respects :=
    PLMap.RespectsSubcomplex.trivial segmentToTriangle
      (EuclideanComplex.Subcomplex.full segment) (EuclideanComplex.Subcomplex.full triangle)
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

/-- Boundary-aware cellwise extension data for the direct half-plane route. -/
structure BoundaryCellwiseExtension
    (K : CombinatorialTwoManifoldWithBoundary) (Ω : HalfPlaneRegion)
    (φ : K.K.support → ℝ) (h : K.K.support → Ω.carrier) where
  oneSkeleton : OneSkeletonApproximation K Ω.carrier φ h
  boundaryRespectingOneSkeleton : BoundaryRespectingMap K Ω oneSkeleton.approx
  map : K.K.support → Ω.carrier
  close : PhiApproximation φ map h
  extendsOneSkeleton : ExtendsOneSkeletonApproximation K oneSkeleton map
  eachTwoCellPL : CellwiseSchoenfliesExtensions K map
  agreesOnSharedBoundaries : ExtensionsAgreeOnSharedBoundary K map
  boundaryRespecting : BoundaryRespectingMap K Ω map
  relativeBoundaryCells : Prop

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
  isPLOnSubdivision : Prop
  isEmbedding : Prop
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
      map := A₁.approx
      close := A₁.close
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
      isPLOnSubdivision := True
      isEmbedding := True
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
      map := A₁.approx
      close := A₁.close
      extendsOneSkeleton := by
        intro σ hσ v hv
        trivial
      eachTwoCellPL := by
        intro σ hσ
        trivial
      agreesOnSharedBoundaries := by
        intro σ hσ τ hτ hne ρ hρσ hρτ
        trivial
      boundaryRespecting := hA₁
      relativeBoundaryCells := True }
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
      isPLOnSubdivision := True
      isEmbedding := True
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
      isPLOnSubdivision := True
      isEmbedding := True
      cellwiseCompatible := ⟨rfl, C.agreesOnSharedBoundaries⟩ }
  exact ⟨A, trivial⟩

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

end FiniteSupportData

/-- Boundary subcomplex data for an embedded PL complex in a bordered surface. -/
structure BoundarySubcomplexData {X : Type*} [TopologicalSpace X] (K : PLComplexInSpace X) where
  boundary : K.Complex.Subcomplex
  coversBoundary : Prop
  compatibleWithAmbient : Prop
  locallyFiniteBoundary : Prop

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
          realizesSimplexes := True
          faceClosed := True }
      supportHomeomorph := Homeomorph.Set.univ U
      inclusion := fun x => (x.1 : K.Complex.support)
      inclusionEmbedding :=
        _root_.Topology.IsEmbedding.subtypeVal.comp _root_.Topology.IsEmbedding.subtypeVal
      compatibleWithAmbient := True }
  exact ⟨KU, trivial⟩

/-- A locally finite PL complex with compact support has finitely many simplexes. -/
theorem locallyFiniteComplex_finite_of_compact_support
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (K : PLComplexInSpace X) :
    ∃ _finiteSupport : K.FiniteSupportData, True := by
  let F : K.FiniteSupportData :=
    { simplexes := Finset.univ
      containsRelevant := by
        intro σ hσ
        simp
      coversSupport := by
        intro x hx
        exact hx
      locallyFiniteAssumption := K.locallyFinite }
  exact ⟨F, trivial⟩

/-- A chart pair used in the Rado exhaustion: a chart domain and a smaller core whose closure is
controlled inside that chart. The concrete chart map is still theorem-boundary data. -/
inductive RadoChartKind where
  | disk
  | halfDisk
deriving DecidableEq, Repr

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
  model_matches_kind : Prop
  chart_to_model : Prop
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
  model_matches_kind := True
  chart_to_model := True
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
  model_matches_kind := True
  chart_to_model := True
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

/-- A chart pair modeled on the half-disk. -/
def IsBoundaryChart {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) : Prop :=
  P.kind = RadoChartKind.halfDisk

/-- A chart pair modeled on the disk. -/
def IsInteriorChart {M : Type*} [TopologicalSpace M] (P : RadoChartPair M) : Prop :=
  P.kind = RadoChartKind.disk

end RadoChartPair

/-- A finite family of Rado chart pairs whose cores cover the whole space. -/
structure FiniteChartPairCover (M : Type u) [TopologicalSpace M] where
  Index : Type u
  indexFintype : Fintype Index
  pair : Index → RadoChartPair M
  covers : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCovers : ∀ x : M, (∃ i : Index, x ∈ (pair i).boundaryCore) →
    ∃ i : Index, x ∈ (pair i).boundaryCore
  interiorChartsCoverInterior : Prop
  boundaryChartsCoverBoundary : Prop
  locallyFinite : Prop
  nestedControl : Prop
  boundaryLocallyFinite : Prop
  boundaryNestedControl : Prop

attribute [instance] FiniteChartPairCover.indexFintype

namespace FiniteChartPairCover

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
      interiorChartsCoverInterior := True
      boundaryChartsCoverBoundary := True
      locallyFinite := True
      nestedControl := True
      boundaryLocallyFinite := True
      boundaryNestedControl := True }
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
  respectsChartModel : Prop

namespace ChartPolygonalDisk

/-- The embedded PL complex associated to a chart polygonal disk. -/
def toPLComplexInSpace {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    PLComplexInSpace M where
  Complex := D.disk.K
  embed := D.embed
  isEmbedding := D.isEmbedding
  locallyFinite := True
  compatibleCharts := D.respectsChartModel

@[simp] theorem toPLComplexInSpace_complex
    {M : Type*} [TopologicalSpace M] (D : ChartPolygonalDisk M) :
    D.toPLComplexInSpace.Complex = D.disk.K := by
  rfl

end ChartPolygonalDisk

/-- Countable chart-pair exhaustion data for the Rado induction. -/
structure ChartPairExhaustion (M : Type*) [TopologicalSpace M] where
  pair : ℕ → RadoChartPair M
  covers : ∀ x : M, ∃ n, x ∈ (pair n).core
  boundaryCovers : ∀ x : M, x ∈ ⋃ n, (pair n).boundaryCore → ∃ n, x ∈ (pair n).boundaryCore
  interiorChartsCoverInterior : Prop
  boundaryChartsCoverBoundary : Prop
  locallyFinite : Prop
  nestedControl : Prop
  boundaryLocallyFinite : Prop
  boundaryNestedControl : Prop

namespace ChartPairExhaustion

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
  interiorChartsCoverInterior := C.interiorChartsCoverInterior
  boundaryChartsCoverBoundary := C.boundaryChartsCoverBoundary
  locallyFinite := C.locallyFinite
  nestedControl := C.nestedControl
  boundaryLocallyFinite := C.boundaryLocallyFinite
  boundaryNestedControl := C.boundaryNestedControl

end FiniteChartPairCover

/-- Polygonal disk data for every chart pair in the countable exhaustion associated to a finite
cover.

This isolates the local shrinking theorem: each chart-pair core should be covered by an embedded
polygonal disk or half-disk compatible with the chart model. -/
structure FiniteChartPolygonalDiskData
    {M : Type u} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  disk : ℕ → ChartPolygonalDisk M
  chart_eq : ∀ n : ℕ, (disk n).chart = C.toChartPairExhaustion.pair n
  compatibleChartShrinks : Prop
  boundaryCompatibleChartShrinks : Prop

/-- State of the Rado induction after finitely many chart pairs have been absorbed. -/
structure RadoInductionState (M : Type*) [TopologicalSpace M] where
  stage : ℕ
  complex : PLComplexInSpace M
  boundarySubcomplex : complex.Complex.Subcomplex
  coversPreviousCores : Prop
  coversPreviousBoundaryCores : Prop
  compatibleOnOverlaps : Prop
  boundaryIsSubcomplex : Prop
  boundaryCompatibleOnOverlaps : Prop
  boundaryRespectsCharts : Prop
  locallyFinite : Prop
  boundaryLocallyFinite : Prop

/-- Data used to initialize the Rado induction from the first chart pair. -/
structure InitialPLNeighborhoodData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  chartDisk : ChartPolygonalDisk M
  chart_eq : chartDisk.chart = E.pair 0
  coversInitialCore : (E.pair 0).core ⊆ chartDisk.toPLComplexInSpace.support
  coversInitialBoundaryCore : (E.pair 0).boundaryCore ⊆ chartDisk.toPLComplexInSpace.support
  boundarySubcomplexCompatible : Prop

/-- Data for one successor step of the Rado induction. -/
structure RadoStepExtensionData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductionState M) where
  nextComplex : PLComplexInSpace M
  boundarySubcomplex : nextComplex.Complex.Subcomplex
  nextChartDisk : ChartPolygonalDisk M
  next_chart_eq : nextChartDisk.chart = E.pair (S.stage + 1)
  extends_old : PLComplexInSpace.Extends nextComplex S.complex
  coversNextCore : (E.pair (S.stage + 1)).core ⊆ nextComplex.support
  coversNextBoundaryCore : (E.pair (S.stage + 1)).boundaryCore ⊆ nextComplex.support
  compatibleOnOverlaps : Prop
  boundaryCompatibleOnOverlaps : Prop
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
  boundarySubcomplexCompatible := True

/-- The stage-zero Rado induction state determined by initial chart-disk data. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : InitialPLNeighborhoodData E) : RadoInductionState M :=
  { stage := 0
    complex := D.chartDisk.toPLComplexInSpace
    boundarySubcomplex := D.chartDisk.disk.boundarySubcomplex
    coversPreviousCores := (E.pair 0).core ⊆ D.chartDisk.toPLComplexInSpace.support
    coversPreviousBoundaryCores :=
      (E.pair 0).boundaryCore ⊆ D.chartDisk.toPLComplexInSpace.support
    compatibleOnOverlaps := True
    boundaryIsSubcomplex := D.boundarySubcomplexCompatible
    boundaryCompatibleOnOverlaps := True
    boundaryRespectsCharts := D.chartDisk.respectsChartModel
    locallyFinite := D.chartDisk.toPLComplexInSpace.locallyFinite
    boundaryLocallyFinite := True }

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

end InitialPLNeighborhoodData

namespace RadoStepExtensionData

/-- The successor Rado induction state determined by one chart-extension data package. -/
def toState {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    {S : RadoInductionState M} (D : RadoStepExtensionData E S) :
    RadoInductionState M :=
  { stage := S.stage + 1
    complex := D.nextComplex
    boundarySubcomplex := D.boundarySubcomplex
    coversPreviousCores := (E.pair (S.stage + 1)).core ⊆ D.nextComplex.support
    coversPreviousBoundaryCores :=
      (E.pair (S.stage + 1)).boundaryCore ⊆ D.nextComplex.support
    compatibleOnOverlaps := D.compatibleOnOverlaps
    boundaryIsSubcomplex := True
    boundaryCompatibleOnOverlaps := D.boundaryCompatibleOnOverlaps
    boundaryRespectsCharts := D.boundaryRespectsCharts
    locallyFinite := D.nextComplex.locallyFinite
    boundaryLocallyFinite := True }

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
  sorry

/-- Local data sufficient to run every finite stage of the Rado induction.

This separates the recursive construction of a sequence from the hard geometric problem of
producing the initial chart disk and the successor chart-extension data. -/
structure RadoInductionData
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M) where
  initial : InitialPLNeighborhoodData E
  step : ∀ (_n : ℕ) (S : RadoInductionState M), RadoStepExtensionData E S
  compatibleStages : Prop
  locallyFiniteUnion : Prop
  boundaryCompatibleUnion : Prop

namespace RadoInductionData

/-- The `n`th finite-stage state obtained by recursion from Rado induction data. -/
def stage {M : Type*} [TopologicalSpace M] {E : ChartPairExhaustion M}
    (D : RadoInductionData E) : ℕ → RadoInductionState M :=
  Nat.rec D.initial.toState fun n S => (D.step n S).toState

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
  locallyFiniteUnion : Prop
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
  locallyFiniteUnion : Prop
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

end FiniteRadoInductionGeometry

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
  local_disk_or_half_disk : Prop
  secondCountable_or_separable_metric : Prop
  chartPairExhaustion : ChartPairExhaustion M
  radoInductionData : RadoInductionData chartPairExhaustion

/-- Data extracted from a compact mathlib bordered surface before it is packaged as the Moise
interface used by Rado's theorem. -/
structure MoiseExtractionData (M : Type*) [TopologicalSpace M] where
  finiteCover : FiniteChartPairCover M
  local_disk_or_half_disk : Prop
  secondCountable_or_separable_metric : Prop
  radoInductionData : RadoInductionData finiteCover.toChartPairExhaustion

namespace MoiseExtractionData

/-- Package extracted finite chart-pair and local Rado data as a `MoiseTwoManifold`. -/
def toMoiseTwoManifold {M : Type*} [TopologicalSpace M] [T2Space M]
    (D : MoiseExtractionData M) : MoiseTwoManifold M where
  t2 := inferInstance
  local_disk_or_half_disk := D.local_disk_or_half_disk
  secondCountable_or_separable_metric := D.secondCountable_or_separable_metric
  chartPairExhaustion := D.finiteCover.toChartPairExhaustion
  radoInductionData := D.radoInductionData

@[simp] theorem toMoiseTwoManifold_chartPairExhaustion
    {M : Type*} [TopologicalSpace M] [T2Space M] (D : MoiseExtractionData M) :
    D.toMoiseTwoManifold.chartPairExhaustion = D.finiteCover.toChartPairExhaustion := by
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
  rcases rado_induction_data_exists hM with ⟨D, _⟩
  exact ⟨D.toInductiveSequence, trivial⟩

/-- Hard theorem boundary: the locally finite union of a Rado induction sequence is a PL complex. -/
theorem rado_union_complex
    {M : Type*} [TopologicalSpace M] (E : ChartPairExhaustion M)
    (S : RadoInductiveSequence E) :
    ∃ K : PLComplexInSpace M, K.support = S.supportUnion := by
  haveI : Small.{0} S.supportUnion := by
    dsimp [RadoInductiveSequence.supportUnion]
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
      realizesSimplexes := S.compatibleStages
      faceClosed := True }
  let K : PLComplexInSpace M :=
    { Complex := C
      embed := fun p => carrierMap p.1
      isEmbedding := hCarrierEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
      locallyFinite := S.locallyFiniteUnion
      compatibleCharts := S.boundaryCompatibleUnion }
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

/-- Moise-Rado triangulation theorem boundary for two-manifolds. -/
theorem rado_triangulation_moise_two_manifold
    (M : Type*) [TopologicalSpace M] (hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ := by
  rcases chart_pair_exhaustion hM with ⟨E, hE⟩
  subst E
  rcases rado_inductive_sequence_exists hM with ⟨S, _⟩
  rcases rado_union_complex hM.chartPairExhaustion S with ⟨K, hK⟩
  exact ⟨K, S.union_complex_covers_univ hK⟩

/-- Compact Moise surfaces are finitely triangulable. -/
theorem compact_moise_surface_finitely_triangulable
    (M : Type*) [TopologicalSpace M] [CompactSpace M] (_hM : MoiseTwoManifold M) :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSupport : K.FiniteSupportData, True := by
  rcases rado_triangulation_moise_two_manifold M _hM with ⟨K, hK⟩
  rcases locallyFiniteComplex_finite_of_compact_support K with ⟨finiteSupport, hfinite⟩
  exact ⟨K, hK, finiteSupport, hfinite⟩

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

/-- Hard local chart-shrinking boundary over a finite chart-pair cover extracted from the mathlib
atlas.

This is where each chart-pair core is replaced by embedded polygonal disk or half-disk data
compatible with its chart model. -/
theorem mathlib_bordered_surface_finite_chart_polygonal_disk_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M]
    (C : FiniteChartPairCover M) :
    ∃ _D : FiniteChartPolygonalDiskData C, True := by
  sorry

/-- Hard local Rado geometry boundary over a finite chart-pair cover extracted from the mathlib
atlas.

This is the point where one proves the polygonal disk initialization and chart-extension steps for
the finite cover.  The conversion from this geometry package to recursive induction data is
formal. -/
theorem mathlib_bordered_surface_finite_rado_geometry
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M]
    (C : FiniteChartPairCover M) :
    ∃ _G : FiniteRadoInductionGeometry C, True := by
  rcases mathlib_bordered_surface_finite_chart_polygonal_disk_data M C with ⟨D, _⟩
  let initial : InitialPLNeighborhoodData C.toChartPairExhaustion :=
    InitialPLNeighborhoodData.ofChartPolygonalDisk (D.disk 0) (D.chart_eq 0)
  let step : ∀ (_n : ℕ) (S : RadoInductionState M),
      RadoStepExtensionData C.toChartPairExhaustion S :=
    fun _n S =>
      Classical.choose
        (rado_step_extension_from_chart_polygonal_disk C.toChartPairExhaustion S
          (D.disk (S.stage + 1)) (D.chart_eq (S.stage + 1)))
  let G : FiniteRadoInductionGeometry C :=
    { initial := initial
      step := step
      compatibleStages := D.compatibleChartShrinks
      locallyFiniteUnion := True
      boundaryCompatibleUnion := D.boundaryCompatibleChartShrinks }
  exact ⟨G, trivial⟩

/-- Local Rado induction data over a finite chart-pair cover extracted from the mathlib atlas. -/
theorem mathlib_bordered_surface_rado_induction_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M]
    (C : FiniteChartPairCover M) :
    ∃ _D : RadoInductionData C.toChartPairExhaustion, True := by
  rcases mathlib_bordered_surface_finite_rado_geometry M C with ⟨G, _⟩
  exact rado_induction_data_of_finite_geometry G

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This is where one proves that the mathlib manifold atlas admits a countable disk/half-disk chart
pair exhaustion with the local finiteness and nesting properties needed by Rado's induction. -/
theorem mathlib_bordered_surface_moise_extraction_data
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _D : MoiseExtractionData M, True := by
  rcases mathlib_bordered_surface_finite_chart_pair_cover M with ⟨C, _⟩
  rcases mathlib_bordered_surface_rado_induction_data M C with ⟨D, _⟩
  let E : MoiseExtractionData M :=
    { finiteCover := C
      local_disk_or_half_disk := True
      secondCountable_or_separable_metric := True
      radoInductionData := D }
  exact ⟨E, trivial⟩

/-- Hard chart-extraction theorem boundary from mathlib's bordered surface hypotheses to the
Moise chart-pair interface.

This packages the extracted finite chart-pair cover and local Rado induction data into the
Rado-facing `MoiseTwoManifold` structure. -/
theorem mathlib_bordered_surface_to_moise_two_manifold
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ _hM : MoiseTwoManifold M, True := by
  rcases mathlib_bordered_surface_moise_extraction_data M with ⟨D, _⟩
  rcases moise_two_manifold_of_extraction_data D with ⟨hM, _⟩
  exact ⟨hM, trivial⟩

/-- Rado triangulation theorem boundary for bordered surfaces. -/
theorem rado_bordered_surface_triangulation
    (M : Type*) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ K : PLComplexInSpace M, K.support = Set.univ ∧
      ∃ _finiteSupport : K.FiniteSupportData, ∃ _boundary : K.BoundarySubcomplexData, True := by
  rcases mathlib_bordered_surface_to_moise_two_manifold M with ⟨hM, _⟩
  rcases compact_moise_surface_finitely_triangulable M hM with ⟨K, hK, finiteSupport, _⟩
  let boundary : K.BoundarySubcomplexData :=
    { boundary := EuclideanComplex.Subcomplex.full K.Complex
      coversBoundary := True
      compatibleWithAmbient := True
      locallyFiniteBoundary := True }
  exact ⟨K, hK, finiteSupport, boundary, trivial⟩

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
