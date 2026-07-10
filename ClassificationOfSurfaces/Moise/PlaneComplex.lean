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

variable (K : PlaneComplex)

theorem mem_simplexes_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    t ∈ K.simplexes :=
  (Finset.mem_filter.mp ht).1

theorem card_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) : t.card = 3 :=
  (Finset.mem_filter.mp ht).2

/-- Barycentric evaluation: the point of the plane with the given barycentric weights. -/
noncomputable def baryEval (x : K.Vertex → ℝ) : Plane :=
  ∑ v, x v • K.position v

theorem continuous_baryEval :
    Continuous fun x : K.Vertex → ℝ => K.baryEval x := by
  unfold baryEval
  exact continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const

theorem baryEval_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    K.baryEval x = ∑ v ∈ t, x v • K.position v :=
  (Finset.sum_subset (Finset.subset_univ t)
    (fun v _ hv => by rw [hsupp v hv, zero_smul])).symm

theorem sum_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    ∑ v, x v = ∑ v ∈ t, x v :=
  (Finset.sum_subset (Finset.subset_univ t) (fun v _ hv => hsupp v hv)).symm

/-- Barycentric evaluation of weights supported on a face lands in that face's carrier. -/
theorem baryEval_mem_cellCarrier {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) (h0 : ∀ v, 0 ≤ x v) (h1 : ∑ v, x v = 1) :
    K.baryEval x ∈ K.cellCarrier t := by
  have hsum_t : ∑ v ∈ t, x v = 1 := by
    rw [← K.sum_eq_sum_of_support hsupp]
    exact h1
  rw [K.baryEval_eq_sum_of_support hsupp, cellCarrier,
    ← Finset.centerMass_eq_of_sum_1 _ _ hsum_t]
  exact Finset.centerMass_mem_convexHull t (fun v _ => h0 v) (by rw [hsum_t]; norm_num)
    (fun v hv => Set.mem_image_of_mem _ hv)

/-- Every point of a face carrier has barycentric weights supported on that face. -/
theorem exists_weights_of_mem_cellCarrier {p : Plane} {t : Finset K.Vertex}
    (hp : p ∈ K.cellCarrier t) :
    ∃ x : K.Vertex → ℝ, (∀ v ∉ t, x v = 0) ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v = 1) ∧
      K.baryEval x = p := by
  classical
  rw [cellCarrier, ← Finset.coe_image, Finset.convexHull_eq] at hp
  obtain ⟨w, hw0, hw1, hwp⟩ := hp
  have himg : ∀ g : Plane → ℝ, ∑ q ∈ t.image K.position, g q = ∑ v ∈ t, g (K.position v) :=
    fun g => Finset.sum_image fun v _ v' _ h => K.position_injective h
  refine ⟨fun v => if v ∈ t then w (K.position v) else 0, fun v hv => by simp [hv], ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ t
    · simpa [hv] using hw0 _ (Finset.mem_image_of_mem _ hv)
    · simp [hv]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, ← himg]
    exact hw1
  · have hsupp : ∀ v ∉ t, (fun v => if v ∈ t then w (K.position v) else 0) v = 0 :=
      fun v hv => by simp [hv]
    rw [K.baryEval_eq_sum_of_support hsupp]
    have hite : ∑ v ∈ t, (if v ∈ t then w (K.position v) else 0) • K.position v =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_congr rfl fun v hv => by rw [if_pos hv]
    have himg2 : ∑ q ∈ t.image K.position, w q • q =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_image fun v _ v' _ h => K.position_injective h
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hwp
    simp only [id_eq] at hwp
    rw [hite, ← himg2]
    exact hwp

/-- Barycentric weights on an affinely independent face are unique. -/
theorem baryEval_injOn_face {t : Finset K.Vertex} (ht : t ∈ K.simplexes)
    {x y : K.Vertex → ℝ}
    (hx : ∀ v ∉ t, x v = 0) (hy : ∀ v ∉ t, y v = 0)
    (hx1 : ∑ v, x v = 1) (hy1 : ∑ v, y v = 1)
    (heq : K.baryEval x = K.baryEval y) : x = y := by
  classical
  have hAI := K.affineIndependent t ht
  have hx1' : ∑ v : ↥t, x v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => x v), ← K.sum_eq_sum_of_support hx]
    exact hx1
  have hy1' : ∑ v : ↥t, y v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => y v), ← K.sum_eq_sum_of_support hy]
    exact hy1
  have hxcomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => x v.1) = K.baryEval x := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hx1',
      K.baryEval_eq_sum_of_support hx, ← Finset.sum_coe_sort t (fun v => x v • K.position v)]
  have hycomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => y v.1) = K.baryEval y := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hy1',
      K.baryEval_eq_sum_of_support hy, ← Finset.sum_coe_sort t (fun v => y v • K.position v)]
  have hind := hAI.indicator_eq_of_affineCombination_eq Finset.univ Finset.univ _ _ hx1' hy1'
    (by rw [hxcomb, hycomb, heq])
  funext v
  by_cases hv : v ∈ t
  · have := congrFun hind ⟨v, hv⟩
    simpa using this
  · rw [hx v hv, hy v hv]

end PlaneComplex

/-- **Realization bridge** (elementary): a purely two-dimensional plane complex induces a
geometric triangulation of its support, by barycentric coordinates in the face containing each
point.  Injectivity is the uniqueness of barycentric coordinates on each affinely independent
face, glued across faces by the face-to-face intersection condition. -/
theorem PlaneComplex.toGeometricTriangulation (K : PlaneComplex) (hpure : K.IsPure2) :
    Nonempty (GeometricTriangulation K.support) := by
  classical
  have hmem : ∀ x : GeometricRealization K.Vertex K.cells, K.baryEval x.1 ∈ K.support := by
    rintro ⟨x, ⟨h0, h1⟩, t, ht, hsupp⟩
    exact Set.mem_biUnion (K.mem_simplexes_of_mem_cells ht)
      (K.baryEval_mem_cellCarrier hsupp h0 h1)
  set φ : GeometricRealization K.Vertex K.cells → K.support :=
    fun x => ⟨K.baryEval x.1, hmem x⟩ with hφ
  have hcont : Continuous φ :=
    Continuous.subtype_mk (K.continuous_baryEval.comp continuous_subtype_val) _
  have hinj : Function.Injective φ := by
    rintro ⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩ ⟨y, ⟨hy0, hy1⟩, u, hu, hysupp⟩ heqφ
    have heval : K.baryEval x = K.baryEval y := congrArg Subtype.val heqφ
    have hpx := K.baryEval_mem_cellCarrier hxsupp hx0 hx1
    have hpy := K.baryEval_mem_cellCarrier hysupp hy0 hy1
    have hpint : K.baryEval x ∈ K.cellCarrier (t ∩ u) := by
      have hfi := K.face_inter t (K.mem_simplexes_of_mem_cells ht) u
        (K.mem_simplexes_of_mem_cells hu)
      have : K.baryEval x ∈
          convexHull ℝ (K.position '' t) ∩ convexHull ℝ (K.position '' u) :=
        ⟨hpx, by rw [heval]; exact hpy⟩
      rw [hfi] at this
      exact this
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hpint
    have hzt : ∀ v ∉ t, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_left hmem)
    have hzu : ∀ v ∉ u, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_right hmem)
    have hxz : x = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells ht)
      hxsupp hzt hx1 hz1 (by rw [hzeval])
    have hyz : y = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells hu)
      hysupp hzu hy1 hz1 (by rw [hzeval, ← heval])
    exact Subtype.ext (hxz.trans hyz.symm)
  have hsurj : Function.Surjective φ := by
    rintro ⟨p, hp⟩
    rw [support, Set.mem_iUnion₂] at hp
    obtain ⟨σ, hσ, hpσ⟩ := hp
    obtain ⟨t, ht, hσt, htcard⟩ := hpure σ hσ
    have hpt : p ∈ K.cellCarrier t := by
      rw [cellCarrier] at hpσ ⊢
      exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hσt)) hpσ
    have htcells : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hpt
    exact ⟨⟨x, ⟨hx0, hx1⟩, t, htcells, hxsupp⟩, Subtype.ext hxeval⟩
  exact ⟨{ Vertex := K.Vertex
           faces := K.cells
           faces_card := fun t ht => K.card_of_mem_cells ht
           homeo := Continuous.homeoOfEquivCompactToT2
             (f := Equiv.ofBijective φ ⟨hinj, hsurj⟩) hcont }⟩

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
