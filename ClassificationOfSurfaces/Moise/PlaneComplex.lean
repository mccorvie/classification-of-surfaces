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

namespace PlaneComplex

open scoped BigOperators

/-- Evaluate barycentric coordinates using the positioned vertices of `K`. -/
private def barycentricEvaluation (K : PlaneComplex) (x : K.Vertex → ℝ) : Plane :=
  ∑ v, x v • K.position v

private lemma barycentricEvaluation_eq_sum_of_eq_zero (K : PlaneComplex)
    {t : Finset K.Vertex} {x : K.Vertex → ℝ} (hzero : ∀ v ∉ t, x v = 0) :
    barycentricEvaluation K x = ∑ v ∈ t, x v • K.position v := by
  unfold barycentricEvaluation
  exact (Finset.sum_subset (Finset.subset_univ t) fun v _ hv ↦ by simp [hzero v hv]).symm

private lemma sum_subtype_eq_one (K : PlaneComplex) {t : Finset K.Vertex}
    {x : K.Vertex → ℝ} (hsum : ∑ v, x v = 1) (hzero : ∀ v ∉ t, x v = 0) :
    ∑ v : t, x v = 1 := by
  rw [Finset.univ_eq_attach, Finset.sum_attach]
  exact (Finset.sum_subset (Finset.subset_univ t) fun v _ hv ↦ hzero v hv).trans hsum

private lemma affineCombination_eq_barycentricEvaluation (K : PlaneComplex)
    {t : Finset K.Vertex} {x : K.Vertex → ℝ} (hsum : ∑ v, x v = 1)
    (hzero : ∀ v ∉ t, x v = 0) :
    Finset.univ.affineCombination ℝ (fun v : t ↦ K.position v) (fun v ↦ x v) =
      barycentricEvaluation K x := by
  have hsum' := sum_subtype_eq_one K hsum hzero
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum']
  rw [Finset.univ_eq_attach]
  calc
    _ = ∑ v ∈ t, x v • K.position v := Finset.sum_attach t _
    _ = barycentricEvaluation K x :=
      (barycentricEvaluation_eq_sum_of_eq_zero K hzero).symm

private lemma range_position_restrict (K : PlaneComplex) (t : Finset K.Vertex) :
    Set.range (fun v : t ↦ K.position v) = K.position '' (t : Set K.Vertex) := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

private lemma barycentricEvaluation_mem_cellCarrier (K : PlaneComplex)
    {t : Finset K.Vertex} {x : K.Vertex → ℝ} (hx : x ∈ stdSimplex ℝ K.Vertex)
    (hzero : ∀ v ∉ t, x v = 0) : barycentricEvaluation K x ∈ K.cellCarrier t := by
  have hsum' := sum_subtype_eq_one K hx.2 hzero
  have hmem : Finset.univ.affineCombination ℝ (fun v : t ↦ K.position v) (fun v ↦ x v) ∈
      convexHull ℝ (Set.range fun v : t ↦ K.position v) :=
    affineCombination_mem_convexHull (fun v _ ↦ hx.1 v) hsum'
  rw [affineCombination_eq_barycentricEvaluation K hx.2 hzero,
    range_position_restrict] at hmem
  exact hmem

private lemma exists_supported_barycentricEvaluation_eq_of_mem_cellCarrier (K : PlaneComplex)
    {t : Finset K.Vertex} {p : Plane} (hp : p ∈ K.cellCarrier t) :
    ∃ x : K.Vertex → ℝ, x ∈ stdSimplex ℝ K.Vertex ∧
      (∀ v ∉ t, x v = 0) ∧ barycentricEvaluation K x = p := by
  classical
  rw [cellCarrier, ← Finset.coe_image] at hp
  obtain ⟨w, hw_nonneg, hw_sum, hw_eval⟩ := (Finset.mem_convexHull' (R := ℝ)).mp hp
  have hw_sum' : ∑ v ∈ t, w (K.position v) = 1 := by
    rw [Finset.sum_image K.position_injective.injOn] at hw_sum
    exact hw_sum
  have hw_eval' : ∑ v ∈ t, w (K.position v) • K.position v = p := by
    rw [Finset.sum_image K.position_injective.injOn] at hw_eval
    exact hw_eval
  let x : K.Vertex → ℝ := fun v ↦ if v ∈ t then w (K.position v) else 0
  have hxzero : ∀ v ∉ t, x v = 0 := by
    intro v hv
    simp [x, hv]
  have hxsum : ∑ v, x v = 1 := by
    calc
      ∑ v, x v = ∑ v ∈ t, x v :=
        (Finset.sum_subset (Finset.subset_univ t) fun v _ hv ↦ by simp [hxzero v hv]).symm
      _ = ∑ v ∈ t, w (K.position v) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [x, hv]
      _ = 1 := hw_sum'
  refine ⟨x, ⟨?_, hxsum⟩, hxzero, ?_⟩
  · intro v
    by_cases hv : v ∈ t
    · simpa [x, hv] using hw_nonneg _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    · simp [x, hv]
  · calc
      barycentricEvaluation K x = ∑ v ∈ t, x v • K.position v :=
        barycentricEvaluation_eq_sum_of_eq_zero K hxzero
      _ = ∑ v ∈ t, w (K.position v) • K.position v := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [x, hv]
      _ = p := hw_eval'

private lemma image_subface (K : PlaneComplex) {t s : Finset K.Vertex} (hst : s ⊆ t) :
    (fun v : t ↦ K.position v) '' {v : t | (v : K.Vertex) ∈ s} =
      K.position '' (s : Set K.Vertex) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨⟨v, hst hv⟩, hv, rfl⟩

private lemma eq_zero_of_barycentricEvaluation_mem_cellCarrier (K : PlaneComplex)
    {t s : Finset K.Vertex} (ht : t ∈ K.simplexes) (hst : s ⊆ t)
    {x : K.Vertex → ℝ} (hsum : ∑ v, x v = 1) (hzero : ∀ v ∉ t, x v = 0)
    (heval : barycentricEvaluation K x ∈ K.cellCarrier s) : ∀ v ∉ s, x v = 0 := by
  intro v hvs
  by_cases hvt : v ∈ t
  · let s' : Set t := {i | (i : K.Vertex) ∈ s}
    have hmem : barycentricEvaluation K x ∈
        affineSpan ℝ ((fun i : t ↦ K.position i) '' s') := by
      rw [show (fun i : t ↦ K.position i) '' s' =
          K.position '' (s : Set K.Vertex) by
        exact image_subface K hst]
      exact convexHull_subset_affineSpan _ heval
    have hcombmem : Finset.univ.affineCombination ℝ
        (fun i : t ↦ K.position i) (fun i ↦ x i) ∈
        affineSpan ℝ ((fun i : t ↦ K.position i) '' s') := by
      rw [affineCombination_eq_barycentricEvaluation K hsum hzero]
      exact hmem
    exact (K.affineIndependent t ht).eq_zero_of_affineCombination_mem_affineSpan
      (sum_subtype_eq_one K hsum hzero) hcombmem (Finset.mem_univ ⟨v, hvt⟩)
      (by simpa [s'] using hvs)
  · exact hzero v hvt

private lemma barycentricEvaluation_injective_of_supported (K : PlaneComplex)
    {t : Finset K.Vertex} (ht : t ∈ K.simplexes) {x y : K.Vertex → ℝ}
    (hxsum : ∑ v, x v = 1) (hysum : ∑ v, y v = 1)
    (hxzero : ∀ v ∉ t, x v = 0) (hyzero : ∀ v ∉ t, y v = 0)
    (hxy : barycentricEvaluation K x = barycentricEvaluation K y) : x = y := by
  have hxcomb := affineCombination_eq_barycentricEvaluation K hxsum hxzero
  have hycomb := affineCombination_eq_barycentricEvaluation K hysum hyzero
  have hrestrict : (fun v : t ↦ x v) = fun v : t ↦ y v :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ _).mp
      (K.affineIndependent t ht) _ _
      (sum_subtype_eq_one K hxsum hxzero)
      (sum_subtype_eq_one K hysum hyzero)
      (hxcomb.trans (hxy.trans hycomb.symm))
  funext v
  by_cases hvt : v ∈ t
  · exact congrFun hrestrict ⟨v, hvt⟩
  · rw [hxzero v hvt, hyzero v hvt]

private lemma continuous_barycentricEvaluation (K : PlaneComplex) :
    Continuous (barycentricEvaluation K) := by
  unfold barycentricEvaluation
  fun_prop

/-- **Theorem boundary** (realization compatibility; elementary).

A purely two-dimensional plane complex induces a geometric triangulation of its support: send
each point to its barycentric coordinates in the face containing it.  This connects the ambient
Moise machinery to the project's faithful triangulation object; it is elementary (no surface
topology), and is a good first proof task on this route. -/
theorem toGeometricTriangulation (K : PlaneComplex) (hpure : K.IsPure2) :
    Nonempty (GeometricTriangulation K.support) := by
  classical
  let f : GeometricRealization K.Vertex K.cells → K.support := fun x ↦
    ⟨barycentricEvaluation K x, by
      obtain ⟨t, ht, hzero⟩ := x.property.2
      exact K.cellCarrier_subset_support (Finset.mem_filter.mp ht).1
        (barycentricEvaluation_mem_cellCarrier K x.property.1 hzero)⟩
  have hf_continuous : Continuous f := by
    apply Continuous.subtype_mk
    exact (continuous_barycentricEvaluation K).comp continuous_subtype_val
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    obtain ⟨t, ht, hxzero⟩ := x.property.2
    obtain ⟨u, hu, hyzero⟩ := y.property.2
    have ht' : t ∈ K.simplexes := (Finset.mem_filter.mp ht).1
    have hu' : u ∈ K.simplexes := (Finset.mem_filter.mp hu).1
    have heval : barycentricEvaluation K x = barycentricEvaluation K y :=
      congrArg Subtype.val hxy
    have hxmem : barycentricEvaluation K x ∈ K.cellCarrier t :=
      barycentricEvaluation_mem_cellCarrier K x.property.1 hxzero
    have hymem : barycentricEvaluation K y ∈ K.cellCarrier u :=
      barycentricEvaluation_mem_cellCarrier K y.property.1 hyzero
    have hyinter : barycentricEvaluation K y ∈ K.cellCarrier (t ∩ u) := by
      have hinter : barycentricEvaluation K y ∈ K.cellCarrier t ∩ K.cellCarrier u :=
        ⟨by rwa [← heval], hymem⟩
      rw [cellCarrier, cellCarrier, K.face_inter t ht' u hu'] at hinter
      exact hinter
    have hyzero_inter : ∀ v ∉ t ∩ u, y.1 v = 0 :=
      eq_zero_of_barycentricEvaluation_mem_cellCarrier K hu' Finset.inter_subset_right
        y.property.1.2 hyzero hyinter
    have hyzero_t : ∀ v ∉ t, y.1 v = 0 := by
      intro v hvt
      exact hyzero_inter v fun hv ↦ hvt (Finset.mem_inter.mp hv).1
    exact barycentricEvaluation_injective_of_supported K ht' x.property.1.2 y.property.1.2
      hxzero hyzero_t heval
  have hf_surjective : Function.Surjective f := by
    intro p
    obtain ⟨s, hs, hp⟩ := Set.mem_iUnion₂.mp p.property
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    have hp_t : (p : Plane) ∈ K.cellCarrier t := by
      exact convexHull_mono (Set.image_mono hst) hp
    obtain ⟨x, hxstd, hxzero, hxeval⟩ :=
      exists_supported_barycentricEvaluation_eq_of_mem_cellCarrier K hp_t
    let x' : GeometricRealization K.Vertex K.cells :=
      ⟨x, hxstd, t, Finset.mem_filter.mpr ⟨ht, htcard⟩, hxzero⟩
    refine ⟨x', Subtype.ext ?_⟩
    exact hxeval
  have hf_homeomorph : IsHomeomorph f :=
    (isHomeomorph_iff_continuous_bijective).mpr
      ⟨hf_continuous, hf_injective, hf_surjective⟩
  exact ⟨{
    Vertex := K.Vertex
    faces := K.cells
    faces_card := fun _ ht ↦ (Finset.mem_filter.mp ht).2
    homeo := hf_homeomorph.homeomorph f
  }⟩

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
