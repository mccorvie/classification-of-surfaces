/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Mathlib.Topology.Metrizable.Urysohn
import ClassificationOfSurfaces.Moise.ChartPatch
import ClassificationOfSurfaces.Moise.IntrinsicComplex
import ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision
import ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension
import ClassificationOfSurfaces.Moise.FineSubdivision
import ClassificationOfSurfaces.Moise.PLApproximation
import ClassificationOfSurfaces.Moise.AdaptiveTriangulation
import ClassificationOfSurfaces.Moise.AdaptiveFanAffine
import ClassificationOfSurfaces.Moise.EmbeddedComplexValence
import ClassificationOfSurfaces.Moise.IntrinsicMarkedFan
import ClassificationOfSurfaces.Moise.AdaptiveControlledApproximation
import ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation
import ClassificationOfSurfaces.Moise.FrontierGlue
import ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron
import ClassificationOfSurfaces.Moise.RelativeSynchronizedArrangement

/-!
# The Radó chart induction

The skeleton of Moise Ch. 8 (the triangulation theorem for 2-manifolds), extended to bordered
surfaces as required by the Eval statement.

Moise's proof of Thm. 8.3 (Radó): cover the surface by chart pairs (Thm. 8.1; finitely many, by
compactness), and build an increasing sequence of embedded complexes, absorbing one chart core at
each step.  The step adjusts the new chart's polyhedral disk by a PL approximation (Thm. 6.3,
`pl_approximation_two_manifold`) so that it meets the already-built complex simplicially
(conditions (a)-(h) in Moise's proof), and glues (Thm. 7.6).

This file provides the honest objects for that induction:

* `PartialTriangulation S` — an embedded finite complex that need not cover `S`; its realization
  is computed from the combinatorial data exactly as in `GeometricTriangulation`, so junk
  witnesses cannot inhabit it;
* `MoiseChart S` — a disk or half-disk chart with an explicit compact core;
* `moise_finite_chart_cover` — the finite-cover boundary (Moise Thm. 8.1 plus compactness; the
  bordered version).  `PL.lean` already contains a genuine proof of essentially this statement
  (`FiniteChartPairCover.exists_of_compact_local` and the `fromChartAt` constructions); filling
  this boundary is a port, not new mathematics.

**Deliberately not yet stated**: the induction-step boundary.  Its hypothesis package (Moise's
invariants (3)-(5): the built support is a 2-manifold with boundary, previously absorbed cores
lie in its combinatorial interior) is a design decision that should be made together with the
proof attempt, per the Definition Faithfulness rules: refining hypotheses later is expected,
weakening conclusions is not.  Designing that interface is the next task on this route.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open InvarianceOfDomain

/-- A finite two-dimensional complex embedded in `S`, not necessarily covering it.  The
realization is computed from the combinatorial data (as in `GeometricTriangulation`), so the
support of a partial triangulation is a genuine finite polyhedron sitting inside `S`. -/
structure PartialTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: three-element vertex sets. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The embedding of the realization into `S`. -/
  embed : GeometricRealization Vertex faces → S
  /-- `embed` is a topological embedding. -/
  isEmbedding : _root_.Topology.IsEmbedding embed

attribute [instance] PartialTriangulation.vertexFintype
attribute [instance] PartialTriangulation.vertexDecidableEq

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S] (T : PartialTriangulation S)

/-- Forget the ambient embedding and retain the intrinsic finite complex. -/
def toIntrinsic : IntrinsicTwoComplex where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card

@[simp] theorem toIntrinsic_faces : T.toIntrinsic.faces = T.faces := rfl

/-- The part of `S` covered by the partial triangulation. -/
def support : Set S :=
  Set.range T.embed

/-- Restrict the ambient embedding to a set known to contain the support. -/
def embedIntoDomain {U : Set S} (hU : T.support ⊆ U) :
    T.toIntrinsic.realization → U :=
  fun x => ⟨T.embed x, hU ⟨x, rfl⟩⟩

theorem isEmbedding_embedIntoDomain {U : Set S} (hU : T.support ⊆ U) :
    _root_.Topology.IsEmbedding (T.embedIntoDomain hU) :=
  T.isEmbedding.codRestrict U (fun x => hU ⟨x, rfl⟩)

/-- The support of a partial triangulation is compact. -/
theorem isCompact_support : IsCompact T.support :=
  isCompact_range T.isEmbedding.continuous

/-- Re-embed the same finite intrinsic complex in the ambient space.  This is the bookkeeping
operation used after Moise's vanishing chart replacement: only the coordinate embedding changes;
the abstract vertices and maximal faces do not. -/
def reembed (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) : PartialTriangulation S where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card
  embed := f
  isEmbedding := hf

@[simp] theorem reembed_toIntrinsic (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) :
    (T.reembed f hf).toIntrinsic = T.toIntrinsic := rfl

theorem reembed_support (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) :
    (T.reembed f hf).support = Set.range f := rfl

/-- Replace the ambient embedding on a selected part of the intrinsic realization and retain
the old embedding outside.  The analytic frontier argument is deliberately supplied as an
embedding certificate, so this constructor works in the nonmetrized ambient surface. -/
noncomputable def replaceOnOpen (U : Set T.toIntrinsic.realization)
    (g : T.toIntrinsic.realization → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)) :
    PartialTriangulation S :=
  T.reembed (frontierGlue U g T.embed)
    he

theorem replaceOnOpen_support (U : Set T.toIntrinsic.realization)
    (g : T.toIntrinsic.realization → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)) :
    (T.replaceOnOpen U g he).support =
      g '' U ∪ T.embed '' Uᶜ := by
  change Set.range (frontierGlue U g T.embed) = g '' U ∪ T.embed '' Uᶜ
  exact range_frontierGlue

/-- A replacement which fixes every old preimage of a closed buffer retains the interior of
that buffer in its range.  This is the small topological observation that lets the relative
straightening preserve all previously absorbed Radó cores without any ambient isotopy. -/
theorem subset_interior_range_frontierGlue_of_fixedOn
    (U : Set (GeometricRealization T.Vertex T.faces))
    (g : GeometricRealization T.Vertex T.faces → S)
    {A C : Set S} (hA : A ⊆ interior C) (hC : C ⊆ T.support)
    (hfix : ∀ x, T.embed x ∈ C → g x = T.embed x) :
    A ⊆ interior (Set.range (frontierGlue U g T.embed)) := by
  apply hA.trans
  apply interior_mono
  intro z hz
  obtain ⟨x, hx⟩ := hC hz
  by_cases hxU : x ∈ U
  · refine ⟨x, ?_⟩
    rw [frontierGlue_of_mem hxU, hfix x]
    · exact hx
    · simpa only [hx] using hz
  · refine ⟨x, ?_⟩
    rw [frontierGlue_of_notMem hxU]
    exact hx

/-- At ambient-interior points one does not need a neighborhood contained in the fixed set.
Pointwise agreement suffices, because invariance of domain makes the corresponding local sheet
of the new embedding open.  The separate closed-buffer lemma above remains necessary on the
manifold boundary. -/
theorem subset_interior_range_frontierGlue_of_fixedOn_of_isInteriorPoint
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (U : Set (GeometricRealization T.Vertex T.faces))
    (g : GeometricRealization T.Vertex T.faces → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed))
    {A : Set S} (hA : A ⊆ interior T.support)
    (hAi : ∀ z ∈ A,
      (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint z)
    (hfix : ∀ x, T.embed x ∈ A → g x = T.embed x) :
    A ⊆ interior (Set.range (frontierGlue U g T.embed)) := by
  intro z hzA
  obtain ⟨x, hx⟩ := interior_subset (hA hzA)
  have hxA : T.embed x ∈ A := by
    rw [hx]
    exact hzA
  have hvalue : frontierGlue U g T.embed x = T.embed x := by
    by_cases hxU : x ∈ U
    · rw [frontierGlue_of_mem hxU, hfix x]
      exact hxA
    · rw [frontierGlue_of_notMem hxU]
  have hopen :=
    mem_interior_range_of_eq_of_mem_interior_range_of_isInteriorPoint
      (modelWithCornersEuclideanHalfSpace 2)
      T.isEmbedding he (x := x) (by
        change T.embed x ∈ interior (Set.range T.embed)
        rw [hx]
        exact hA hzA) (by
        simpa only [hx] using hAi z hzA)
  rw [hvalue, hx] at hopen
  exact hopen

/-- Restrict a partial triangulation to a selected finite family of maximal faces. -/
def restrictFaces (p : Finset T.Vertex → Prop) [DecidablePred p] : PartialTriangulation S where
  Vertex := T.Vertex
  faces := T.faces.filter p
  faces_card := by
    intro t ht
    exact T.faces_card t (Finset.mem_filter.mp ht).1
  embed := T.embed ∘ T.toIntrinsic.restrictFacesInclusion p
  isEmbedding := T.isEmbedding.comp (T.toIntrinsic.isEmbedding_restrictFacesInclusion p)

theorem restrictFaces_support_subset (p : Finset T.Vertex → Prop) [DecidablePred p] :
    (T.restrictFaces p).support ⊆ T.support := by
  rintro x ⟨y, rfl⟩
  exact ⟨T.toIntrinsic.restrictFacesInclusion p y, rfl⟩

/-- Exact support formula for a finite face restriction. -/
theorem restrictFaces_support (p : Finset T.Vertex → Prop) [DecidablePred p] :
    (T.restrictFaces p).support =
      T.embed '' {x : T.toIntrinsic.realization |
        ∃ t ∈ T.faces, p t ∧ x ∈ T.toIntrinsic.faceCarrier t} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    let x : T.toIntrinsic.realization := T.toIntrinsic.restrictFacesInclusion p z
    refine ⟨x, ?_, rfl⟩
    rcases z.2.2 with ⟨t, ht, hzt⟩
    exact ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2, hzt⟩
  · rintro ⟨x, ⟨t, ht, hpt, hxt⟩, rfl⟩
    let z : (T.toIntrinsic.restrictFaces p).realization :=
      ⟨x.1, x.2.1, ⟨t, Finset.mem_filter.mpr ⟨ht, hpt⟩, hxt⟩⟩
    exact ⟨z, rfl⟩

/-- Replace a partial triangulation by a faithful finite intrinsic subdivision. -/
noncomputable def refine (R : T.toIntrinsic.Subdivision) : PartialTriangulation S where
  Vertex := R.refined.Vertex
  faces := R.refined.faces
  faces_card := R.refined.faces_card
  embed := T.embed ∘ R.homeo
  isEmbedding := T.isEmbedding.comp R.homeo.isEmbedding

@[simp] theorem refine_toIntrinsic (R : T.toIntrinsic.Subdivision) :
    (T.refine R).toIntrinsic = R.refined := rfl

/-- Faithful subdivision changes the finite triangulation data but not its ambient support. -/
theorem refine_support (R : T.toIntrinsic.Subdivision) :
    (T.refine R).support = T.support := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨R.homeo x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨R.homeo.symm x, ?_⟩
    exact congrArg T.embed (R.homeo.apply_symm_apply x)

/-- A compact part of a partial triangulation lying in an ambient open set is carried by a
finite face restriction of a faithful refinement which still lies in that open set.

This is the finite collar extracted from Moise Ch. 8, Thm. 2.  It is the compact ingredient of
the Radó step; the full proof additionally needs the noncompact, locally finite collar whose
mesh tends to zero at its frontier. -/
theorem exists_refinedSubcomplex_between {C U : Set S}
    (hC : IsCompact C) (hCT : C ⊆ T.support) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (R : T.toIntrinsic.Subdivision)
      (keep : Finset (Finset R.refined.Vertex)),
      C ⊆ ((T.refine R).restrictFaces (fun t => t ∈ keep)).support ∧
      ((T.refine R).restrictFaces (fun t => t ∈ keep)).support ⊆ U := by
  classical
  let C₀ : Set T.toIntrinsic.realization := T.embed ⁻¹' C
  let U₀ : Set T.toIntrinsic.realization := T.embed ⁻¹' U
  have hC₀ : IsCompact C₀ := by
    exact T.isEmbedding.isInducing.isCompact_preimage' hC hCT
  have hU₀ : IsOpen U₀ := hU.preimage T.isEmbedding.continuous
  have hC₀U₀ : C₀ ⊆ U₀ := fun x hx => hCU hx
  obtain ⟨L⟩ := T.toIntrinsic.exists_openSubcomplex hC₀ hU₀ hC₀U₀
  refine ⟨L.subdivision, L.keptFaces, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx⟩ := hCT hz
    have hxC₀ : x ∈ C₀ := by
      change T.embed x ∈ C
      simpa [hx] using hz
    obtain ⟨y, hy⟩ := L.covers hxC₀
    refine ⟨y, ?_⟩
    change T.embed (L.subdivision.homeo
      (L.subdivision.refined.restrictFacesInclusion
        (fun t => t ∈ L.keptFaces) y)) = z
    exact (congrArg T.embed hy).trans hx
  · rintro z ⟨y, rfl⟩
    apply L.contained
    exact ⟨y, rfl⟩

/-- A partial triangulation covering all of `S` is a geometric triangulation.  This is the final
conversion at the top of the Radó induction. -/
noncomputable def toGeometricTriangulation (hcovers : T.support = Set.univ) :
    GeometricTriangulation S where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card
  homeo :=
    T.isEmbedding.toHomeomorphOfSurjective (Set.range_eq_univ.mp hcovers)

/-- The edges of a partial triangulation: the two-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

theorem card_of_mem_edges {e : Finset T.Vertex} (he : e ∈ T.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

/-- The boundary edges: edges lying in exactly one face. -/
def boundaryEdges : Finset (Finset T.Vertex) :=
  T.edges.filter fun e => (T.faces.filter fun t => e ⊆ t).card = 1

/-- The image in `S` of the combinatorial boundary: points of the realization supported on a
boundary edge. -/
def boundarySupport : Set S :=
  T.embed '' {x | ∃ e ∈ T.boundaryEdges, ∀ v ∉ e, x.1 v = 0}

/-- The combinatorial interior of the covered region: the support minus the image of the
combinatorial boundary.  The Radó induction keeps every absorbed chart core inside this set
(Moise Ch. 8, Thm. 3, invariant (4)). -/
def combInterior : Set S :=
  T.support \ T.boundarySupport

theorem combInterior_subset_support : T.combInterior ⊆ T.support :=
  Set.sdiff_subset

/-- Transport a pure finite plane complex into an ambient space.  The abstract realization is
identified with the geometric support by barycentric coordinates, then followed by the supplied
ambient embedding. -/
noncomputable def ofPlaneComplex {S : Type*} [TopologicalSpace S]
    (K : PlaneComplex) (hpure : K.IsPure2)
    (e : K.support → S) (he : _root_.Topology.IsEmbedding e) :
    PartialTriangulation S where
  Vertex := K.Vertex
  faces := K.cells
  faces_card := fun t ht => K.card_of_mem_cells ht
  embed := e ∘ K.realizationHomeomorph hpure
  isEmbedding := he.comp (K.realizationHomeomorph hpure).isEmbedding

/-- The transported plane patch covers exactly the ambient range of its support embedding. -/
theorem ofPlaneComplex_support {S : Type*} [TopologicalSpace S]
    (K : PlaneComplex) (hpure : K.IsPure2)
    (e : K.support → S) (he : _root_.Topology.IsEmbedding e) :
    (ofPlaneComplex K hpure e he).support = Set.range e := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    exact ⟨K.realizationHomeomorph hpure z, rfl⟩
  · rintro x ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := (K.realizationHomeomorph hpure).surjective z
    exact ⟨w, rfl⟩

/-- The empty partial triangulation. -/
def empty (S : Type*) [TopologicalSpace S] : PartialTriangulation S where
  Vertex := Empty
  faces := ∅
  faces_card := by simp
  embed := fun x => isEmptyElim x
  isEmbedding := Topology.IsEmbedding.of_subsingleton _

/-- A partial triangulation with no faces covers nothing: its realization is empty. -/
theorem support_eq_empty_of_faces_eq_empty {S : Type*} [TopologicalSpace S]
    (T : PartialTriangulation S) (h : T.faces = ∅) : T.support = ∅ := by
  ext x
  simp only [support, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, rfl⟩
  rcases p.2.2 with ⟨t, ht, -⟩
  rw [h] at ht
  exact absurd ht (Finset.notMem_empty t)

@[simp] theorem empty_support (S : Type*) [TopologicalSpace S] :
    (empty S).support = ∅ :=
  support_eq_empty_of_faces_eq_empty _ rfl

end PartialTriangulation

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- A finite compatible ambient triangle family is a partial triangulation of the ambient
space.  Its support is exactly the union of the face carriers. -/
noncomputable def toPartialTriangulation [Finite K.Face] [T2Space S] :
    PartialTriangulation S := by
  let G := K.finiteSupportGeometricTriangulation
  exact
    { Vertex := G.Vertex
      faces := G.faces
      faces_card := G.faces_card
      embed := Subtype.val ∘ G.homeo
      isEmbedding := _root_.Topology.IsEmbedding.subtypeVal.comp G.homeo.isEmbedding }

theorem toPartialTriangulation_support [Finite K.Face] [T2Space S] :
    K.toPartialTriangulation.support = K.support := by
  let G := K.finiteSupportGeometricTriangulation
  change Set.range (Subtype.val ∘ G.homeo) = K.support
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact (G.homeo x).2
  · intro y hy
    let z : K.support := ⟨y, hy⟩
    refine ⟨G.homeo.symm z, ?_⟩
    exact congrArg Subtype.val (G.homeo.apply_symm_apply z)

end LocallyFiniteTriangleComplex

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- The plane embedding of an intrinsic partial triangulation whose support lies in this chart.
This is the source embedding consumed by intrinsic PL approximation in the Rado step. -/
def partialChartMap (T : PartialTriangulation S) (hdom : T.support ⊆ c.domain) :
    T.toIntrinsic.realization → Plane :=
  fun x => (c.chart (T.embedIntoDomain hdom x) : Plane)

theorem isEmbedding_partialChartMap (T : PartialTriangulation S)
    (hdom : T.support ⊆ c.domain) :
    _root_.Topology.IsEmbedding (c.partialChartMap T hdom) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.isEmbedding.comp (T.isEmbedding_embedIntoDomain hdom))

/-- Include the fixed polygonal model patch into this chart's model region. -/
def patchToModelRegion : c.kind.patchComplex.support → c.kind.modelRegion :=
  fun x => ⟨x.1, c.kind.patchComplex_support_subset_modelRegion x.2⟩

theorem isEmbedding_patchToModelRegion :
    _root_.Topology.IsEmbedding c.patchToModelRegion :=
  _root_.Topology.IsEmbedding.subtypeVal.codRestrict _ _

/-- Embed the fixed polygonal patch into the ambient surface through the inverse chart. -/
def patchEmbed : c.kind.patchComplex.support → S :=
  fun x => (c.chart.symm (c.patchToModelRegion x)).1

theorem isEmbedding_patchEmbed : _root_.Topology.IsEmbedding c.patchEmbed :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp c.isEmbedding_patchToModelRegion)

/-- The concrete finite partial triangulation supplied by one Moise chart. -/
noncomputable def patchPartialTriangulation : PartialTriangulation S :=
  PartialTriangulation.ofPlaneComplex c.kind.patchComplex c.kind.patchComplex_pure
    c.patchEmbed c.isEmbedding_patchEmbed

theorem patchPartialTriangulation_support :
    c.patchPartialTriangulation.support = Set.range c.patchEmbed :=
  PartialTriangulation.ofPlaneComplex_support c.kind.patchComplex
    c.kind.patchComplex_pure c.patchEmbed c.isEmbedding_patchEmbed

/-- The concrete chart patch covers the marked chart core. -/
theorem core_subset_patchPartialTriangulation_support :
    c.core ⊆ c.patchPartialTriangulation.support := by
  rw [c.patchPartialTriangulation_support]
  intro y hy
  rcases c.mem_core_iff.mp hy with ⟨hyDomain, hyCore⟩
  let p : c.kind.modelRegion := c.chart ⟨y, hyDomain⟩
  let q : c.kind.patchComplex.support :=
    ⟨p.1, c.kind.modelCore_subset_patchComplex_support hyCore⟩
  refine ⟨q, ?_⟩
  change (c.chart.symm ⟨q.1, c.kind.patchComplex_support_subset_modelRegion q.2⟩).1 = y
  exact congrArg Subtype.val (c.chart.symm_apply_apply ⟨y, hyDomain⟩)

/-- The model-region subset occupied by the fixed polygonal patch. -/
def patchInModelRegion : Set c.kind.modelRegion :=
  {p | (p : Plane) ∈ c.kind.patchComplex.support}

theorem range_patchToModelRegion :
    Set.range c.patchToModelRegion = c.patchInModelRegion := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hp
    let q : c.kind.patchComplex.support := ⟨p.1, hp⟩
    exact ⟨q, Subtype.ext rfl⟩

/-- Exact chart-domain description of the transported patch support. -/
theorem patchPartialTriangulation_support_eq_chartImage :
    c.patchPartialTriangulation.support =
      Subtype.val '' (c.chart.symm '' c.patchInModelRegion) := by
  rw [c.patchPartialTriangulation_support]
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨c.chart.symm (c.patchToModelRegion q), ?_, rfl⟩
    exact ⟨c.patchToModelRegion q, q.2, rfl⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    let q : c.kind.patchComplex.support := ⟨p.1, hp⟩
    exact ⟨q, congrArg Subtype.val (congrArg c.chart.symm (Subtype.ext rfl))⟩

/-- The marked core lies in the ambient topological interior of the concrete chart patch. -/
theorem core_subset_interior_patchPartialTriangulation_support :
    c.core ⊆ interior c.patchPartialTriangulation.support := by
  intro y hy
  rcases c.mem_core_iff.mp hy with ⟨hyDomain, hyCore⟩
  let p : c.kind.modelRegion := c.chart ⟨y, hyDomain⟩
  have hpInterior : p ∈ interior c.patchInModelRegion :=
    c.kind.modelCore_subset_interior_patchInRegion hyCore
  have hzInterior : c.chart.symm p ∈ interior (c.chart.symm '' c.patchInModelRegion) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hpInterior, rfl⟩
  let O : Set S := Subtype.val '' interior (c.chart.symm '' c.patchInModelRegion)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆ c.patchPartialTriangulation.support := by
    rw [c.patchPartialTriangulation_support_eq_chartImage]
    exact Set.image_mono interior_subset
  apply interior_maximal hOsub hOopen
  refine ⟨c.chart.symm p, hzInterior, ?_⟩
  exact congrArg Subtype.val (c.chart.symm_apply_apply ⟨y, hyDomain⟩)

end MoiseChart

/-! ## The locally finite old-complex overlap in one chart -/

namespace ChartKind

/-- The open disk in which chart-coordinate perturbations are performed.  For a half-disk chart
the model region is a closed subset of this disk; the later bordered approximation must preserve
that half-disk rather than use the extra side. -/
def perturbationRegion (_k : ChartKind) : Set Plane := Metric.ball 0 1

/-- A disk or half-disk model is locally compact in its subtype topology. -/
@[reducible] noncomputable def modelRegionLocallyCompactSpace (k : ChartKind) :
    LocallyCompactSpace k.modelRegion := by
  cases k with
  | disk =>
      exact Metric.isOpen_ball.locallyCompactSpace
  | halfDisk =>
      apply IsLocallyClosed.locallyCompactSpace
      refine ⟨Metric.ball (0 : Plane) 1, {x : Plane | 0 ≤ x 0},
        Metric.isOpen_ball, isClosed_le continuous_const continuous_coordZero, ?_⟩
      rfl

theorem isOpen_perturbationRegion (k : ChartKind) : IsOpen k.perturbationRegion :=
  Metric.isOpen_ball

theorem modelRegion_subset_perturbationRegion (k : ChartKind) :
    k.modelRegion ⊆ k.perturbationRegion := by
  cases k <;> intro p hp
  · exact hp
  · exact hp.1

/-- Inside the open perturbation disk, the closure of the model region adds nothing: closure
only touches the unit sphere and, for a half-disk, the model already contains its edge line. -/
theorem ball_inter_closure_modelRegion_subset (k : ChartKind) :
    Metric.ball (0 : Plane) 1 ∩ closure k.modelRegion ⊆ k.modelRegion := by
  cases k with
  | disk =>
      intro z hz
      exact hz.1
  | halfDisk =>
      rintro z ⟨hzball, hzcl⟩
      refine ⟨hzball, ?_⟩
      have hsub : closure ChartKind.halfDisk.modelRegion ⊆ {x : Plane | 0 ≤ x 0} :=
        closure_minimal (fun x hx ↦ hx.2)
          (isClosed_le continuous_const continuous_coordZero)
      exact hsub hzcl

/-- The chart model, regarded as a subset of its open perturbation disk. -/
def modelInPerturbation (k : ChartKind) : Set k.perturbationRegion :=
  {p | p.1 ∈ k.modelRegion}

theorem isClosed_modelInPerturbation (k : ChartKind) :
    IsClosed k.modelInPerturbation := by
  cases k with
  | disk =>
      have hAll : ChartKind.disk.modelInPerturbation = Set.univ := by
        ext p
        simp [modelInPerturbation, modelRegion, perturbationRegion]
      rw [hAll]
      exact isClosed_univ
  | halfDisk =>
      have hset : ChartKind.halfDisk.modelInPerturbation =
          {p : Metric.ball (0 : Plane) 1 | 0 ≤ p.1 0} := by
        ext p
        constructor
        · intro hp
          exact hp.2
        · intro hp
          exact ⟨p.2, hp⟩
      rw [hset]
      exact (isClosed_le continuous_const
        (continuous_coordZero.comp continuous_subtype_val))

/-- Identify the model-region subtype with its nested closed subtype in the perturbation disk. -/
def modelToPerturbationRange (k : ChartKind) :
    k.modelRegion ≃ₜ k.modelInPerturbation where
  toFun p := ⟨⟨p.1, k.modelRegion_subset_perturbationRegion p.2⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Include a disk or half-disk model into the open disk used for perturbations. -/
def modelToPerturbation (k : ChartKind) :
    k.modelRegion → k.perturbationRegion :=
  fun p ↦ ⟨p.1, k.modelRegion_subset_perturbationRegion p.2⟩

theorem isClosedEmbedding_modelToPerturbation (k : ChartKind) :
    _root_.Topology.IsClosedEmbedding k.modelToPerturbation := by
  have h := (k.isClosed_modelInPerturbation.isClosedEmbedding_subtypeVal).comp
    k.modelToPerturbationRange.isClosedEmbedding
  have heq : k.modelToPerturbation =
      (Subtype.val : k.modelInPerturbation → k.perturbationRegion) ∘
        k.modelToPerturbationRange := by
    funext p
    rfl
  rw [heq]
  exact h

/-- The fixed finite chart patch, regarded inside the open perturbation disk. -/
def patchInPerturbation (k : ChartKind) : Set k.perturbationRegion :=
  {p | p.1 ∈ k.patchComplex.support}

/-- The chart patch remains compact after lifting it to the perturbation-region subtype. -/
theorem isCompact_patchInPerturbation (k : ChartKind) :
    IsCompact k.patchInPerturbation := by
  apply _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    k.patchComplex.isCompact_support
  intro p hp
  exact ⟨⟨p, k.modelRegion_subset_perturbationRegion
    (k.patchComplex_support_subset_modelRegion hp)⟩, rfl⟩

end ChartKind

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- The part of the intrinsic realization whose ambient image lies in a Rado chart domain. -/
def chartOverlap (T : PartialTriangulation S) (c : MoiseChart S) :
    Set T.toIntrinsic.realization :=
  T.embed ⁻¹' c.domain

theorem isOpen_chartOverlap (T : PartialTriangulation S) (c : MoiseChart S) :
    IsOpen (T.chartOverlap c) :=
  c.isOpen_domain.preimage T.isEmbedding.continuous

/-- Include an overlap point into the chart domain through the old partial triangulation. -/
def chartOverlapToDomain (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.domain :=
  fun x ↦ ⟨T.embed x.1, x.2⟩

theorem isEmbedding_chartOverlapToDomain (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapToDomain c) :=
  (T.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal).codRestrict
    c.domain fun x ↦ x.2

/-- Chart coordinates of the old partial triangulation on the overlap. -/
def chartOverlapMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → Plane :=
  fun x ↦ (c.chart (T.chartOverlapToDomain c x) : Plane)

theorem isEmbedding_chartOverlapMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapMap c) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.isEmbedding.comp (T.isEmbedding_chartOverlapToDomain c))

/-- The adaptive conforming triangulation of the whole old-complex/chart overlap. -/
noncomputable abbrev adaptiveOverlapComplex (T : PartialTriangulation S)
    (c : MoiseChart S) :=
  T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex (T.chartOverlap c)
    (T.isOpen_chartOverlap c)

/-- Chart coordinates on the support of the adaptive overlap triangulation. -/
noncomputable def adaptiveOverlapChartMap (T : PartialTriangulation S)
    (c : MoiseChart S) : (T.adaptiveOverlapComplex c).support → Plane :=
  fun p ↦ T.chartOverlapMap c p.1

theorem isEmbedding_adaptiveOverlapChartMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.adaptiveOverlapChartMap c) :=
  (T.isEmbedding_chartOverlapMap c).comp
    _root_.Topology.IsEmbedding.subtypeVal

/-- The overlap map with the chart model retained as codomain. -/
def chartOverlapModelMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.kind.modelRegion :=
  fun x ↦ c.chart (T.chartOverlapToDomain c x)

theorem isEmbedding_chartOverlapModelMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapModelMap c) :=
  c.chart.isEmbedding.comp (T.isEmbedding_chartOverlapToDomain c)

/-- The overlap map into the open perturbation disk. -/
def chartOverlapPerturbationMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.kind.perturbationRegion :=
  c.kind.modelToPerturbation ∘ T.chartOverlapModelMap c

theorem isEmbedding_chartOverlapPerturbationMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapPerturbationMap c) :=
  c.kind.isClosedEmbedding_modelToPerturbation.isEmbedding.comp
    (T.isEmbedding_chartOverlapModelMap c)

/-- The old polyhedral overlap is closed in the chart model. -/
theorem isClosedEmbedding_chartOverlapModelMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.chartOverlapModelMap c) := by
  let A : Set c.domain := {y | y.1 ∈ T.support}
  have hAclosed : IsClosed A :=
    T.isCompact_support.isClosed.preimage continuous_subtype_val
  have hrange : Set.range (T.chartOverlapModelMap c) = c.chart '' A := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, rfl⟩
      refine ⟨T.chartOverlapToDomain c x, ?_, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro z ⟨y, hyA, rfl⟩
      obtain ⟨x, hx⟩ := hyA
      let xU : T.chartOverlap c := ⟨x, by
        change T.embed x ∈ c.domain
        rw [hx]
        exact y.2⟩
      refine ⟨xU, ?_⟩
      change c.chart (T.chartOverlapToDomain c xU) = c.chart y
      apply congrArg c.chart
      apply Subtype.ext
      exact hx
  refine ⟨T.isEmbedding_chartOverlapModelMap c, ?_⟩
  rw [hrange]
  exact c.chart.isClosedMap A hAclosed

theorem isClosedEmbedding_chartOverlapPerturbationMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.chartOverlapPerturbationMap c) :=
  c.kind.isClosedEmbedding_modelToPerturbation.comp
    (T.isClosedEmbedding_chartOverlapModelMap c)

/-- Forget the support proof of the adaptive overlap complex.  Coverage makes this a
homeomorphism onto the whole overlap, hence a closed embedding. -/
noncomputable def adaptiveOverlapToOverlap (T : PartialTriangulation S)
    (c : MoiseChart S) : (T.adaptiveOverlapComplex c).support → T.chartOverlap c :=
  Subtype.val

theorem isClosedEmbedding_adaptiveOverlapToOverlap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.adaptiveOverlapToOverlap c) := by
  refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [show Set.range (T.adaptiveOverlapToOverlap c) =
      (T.adaptiveOverlapComplex c).support by
    exact Subtype.range_val]
  rw [T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex_support
    (T.chartOverlap c) (T.isOpen_chartOverlap c)]
  exact isClosed_univ

/-- Chart coordinates of the adaptive overlap, with the open perturbation disk retained as
codomain. -/
noncomputable def adaptiveOverlapPerturbationMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    (T.adaptiveOverlapComplex c).support → c.kind.perturbationRegion :=
  T.chartOverlapPerturbationMap c ∘ T.adaptiveOverlapToOverlap c

theorem isClosedEmbedding_adaptiveOverlapPerturbationMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.adaptiveOverlapPerturbationMap c) :=
  (T.isClosedEmbedding_chartOverlapPerturbationMap c).comp
    (T.isClosedEmbedding_adaptiveOverlapToOverlap c)

/-- The adaptive overlap as the relative plane graph realization used by the locally finite
Chapter 6 approximation. -/
noncomputable def adaptiveOverlapGraphRealization [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    (T.adaptiveOverlapComplex c).PlaneGraphRealization :=
  LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
    c.kind.perturbationRegion
    c.kind.isOpen_perturbationRegion (T.adaptiveOverlapChartMap c)
    (T.isEmbedding_adaptiveOverlapChartMap c)
    (fun p ↦ (T.adaptiveOverlapPerturbationMap c p).2)
    (by
      have heq : (fun p ↦
          (⟨T.adaptiveOverlapChartMap c p,
            (T.adaptiveOverlapPerturbationMap c p).2⟩ :
            c.kind.perturbationRegion)) = T.adaptiveOverlapPerturbationMap c := by
        funext p
        apply Subtype.ext
        rfl
      rw [heq]
      exact (T.isClosedEmbedding_adaptiveOverlapPerturbationMap c).isClosed_range)

/-- Crossing-weld plan, item 1, first entry condition: distinct faces of the adaptive overlap
complex carry distinct vertex triples. -/
theorem injective_faceVertices_adaptiveOverlapComplex (T : PartialTriangulation S)
    (c : MoiseChart S) :
    Function.Injective (T.adaptiveOverlapComplex c).faceVertices :=
  T.toIntrinsic.adaptiveGlobalFanFaceVertices_injective (T.chartOverlap c)
    (T.isOpen_chartOverlap c)

/-- Crossing-weld plan, item 1, second entry condition, in honest existential form: a strongly
positive tolerance on the chart overlap whose region-safe reduction separates every vertex of
the adaptive overlap complex from every face not containing it, in chart coordinates.  This is
the locally finite analogue of the finite `exists_uniform_vertex_face_separation`. -/
theorem exists_separating_control_adaptiveOverlap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ phi : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ phi ∧
      LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces
        (T.adaptiveOverlapGraphRealization c)
        (fun p ↦ regionSafeControl c.kind.perturbationRegion
          (T.chartOverlapMap c) phi p.1) := by
  classical
  have hmem : ∀ x : T.chartOverlap c,
      x ∈ (T.adaptiveOverlapComplex c).support := by
    intro x
    rw [T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex_support
      (T.chartOverlap c) (T.isOpen_chartOverlap c)]
    trivial
  refine ⟨fun x ↦ LocallyFiniteTriangleComplex.vertexSeparationControl
    (T.adaptiveOverlapGraphRealization c) ⟨x, hmem x⟩, ?_, ?_⟩
  · intro C hC _
    have himage : IsCompact ((fun x : T.chartOverlap c ↦
        (⟨x, hmem x⟩ : (T.adaptiveOverlapComplex c).support)) '' C) :=
      hC.image (continuous_id.subtype_mk _)
    obtain ⟨eps, heps, hepsLe⟩ :=
      LocallyFiniteTriangleComplex.stronglyPositiveOn_vertexSeparationControl
        (G := T.adaptiveOverlapGraphRealization c) _ himage (Set.subset_univ _)
    exact ⟨eps, heps, fun x hx ↦ hepsLe _ ⟨x, hx, rfl⟩⟩
  · apply LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces.mono
      (LocallyFiniteTriangleComplex.separatesVerticesFromFaces_vertexSeparationControl
        (G := T.adaptiveOverlapGraphRealization c))
    intro p
    exact regionSafeControl_le_left _ _ _ _

/-- Crossing-weld plan, item 2, disjointness half: a replacement taking its overlap values in
the chart domain never collides with the old embedding outside the overlap.  Together with
`range_frontierGlue`, this is the crossing-disjointness input of
`isEmbedding_frontierGlue_of_matches`. -/
theorem disjoint_image_chartOverlap_embed_compl (T : PartialTriangulation S)
    (c : MoiseChart S) {g : T.toIntrinsic.realization → S}
    (hg : ∀ x ∈ T.chartOverlap c, g x ∈ c.domain) :
    Disjoint (g '' T.chartOverlap c) (T.embed '' (T.chartOverlap c)ᶜ) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyz⟩
  apply hy
  change T.embed y ∈ c.domain
  rw [hyz]
  exact hg x hx

/-- Crossing-weld plan, item 2, matching half (Moise's vanishing tolerance).  One strongly
positive control on the chart overlap such that EVERY chart-coordinate replacement of the old
embedding within that control matches the old embedding at the overlap frontier.

The plane-metric reduction `regionSafeControl` is deliberately not enough here: a C0 chart may
shear plane-close points apart near its frontier (compose a chart with the twist
`(r, θ) ↦ (r, θ + 1/(1-r))` of the disk: a radial displacement of a quarter of the distance to
the sphere is torn to unbounded angular displacement).  The modulus must therefore be extracted
from the chart homeomorphism itself.  This is the metric-target version; the surface version
`exists_chartMatchingControl` metrizes the compact second-countable surface and applies it. -/
theorem exists_chartMatchingControl_of_metricSpace {S' : Type*} [MetricSpace S']
    (T : PartialTriangulation S') (c : MoiseChart S') :
    ∃ mu : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : T.chartOverlap c → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S'),
        (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : T.chartOverlap c,
          dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y) →
        MatchesAtFrontier (T.chartOverlap c) g T.embed := by
  classical
  by_cases hFr : (frontier (T.chartOverlap c)).Nonempty
  swap
  · refine ⟨fun _ ↦ 1, fun C _ _ ↦ ⟨1, one_pos, fun _ _ ↦ le_rfl⟩, ?_⟩
    intro g' g hgval hclose x hx
    exact absurd ⟨x, hx⟩ hFr
  -- the compact frontier trace on the old complex
  have hFrCompact : IsCompact (T.embed '' frontier (T.chartOverlap c)) :=
    isClosed_frontier.isCompact.image T.isEmbedding.continuous
  have hFrNe : (T.embed '' frontier (T.chartOverlap c)).Nonempty := hFr.image _
  -- the surface scale, vanishing at the frontier
  set sS : T.chartOverlap c → ℝ := fun y ↦
    Metric.infDist (T.embed y.1) (T.embed '' frontier (T.chartOverlap c)) with hsS
  have hsSpos : ∀ y : T.chartOverlap c, 0 < sS y := by
    intro y
    apply (hFrCompact.isClosed.notMem_iff_infDist_pos hFrNe).mp
    rintro ⟨x, hxFr, hxy⟩
    have hxval : x = y.1 := T.isEmbedding.injective hxy
    rw [hxval] at hxFr
    exact hxFr.2 (mem_interior_iff_mem_nhds.mpr
      ((T.isOpen_chartOverlap c).mem_nhds y.2))
  have hsScont : Continuous sS :=
    (Metric.continuous_infDist_pt _).comp
      (T.isEmbedding.continuous.comp continuous_subtype_val)
  -- the inverse chart on the model region
  set psi : c.kind.modelRegion → S' := fun z ↦ (c.chart.symm z).1 with hpsi
  have hpsiCont : Continuous psi :=
    continuous_subtype_val.comp c.chart.symm.continuous
  have hpsiModel : ∀ y : T.chartOverlap c,
      psi (T.chartOverlapModelMap c y) = T.embed y.1 := by
    intro y
    change (c.chart.symm (c.chart (T.chartOverlapToDomain c y))).1 = T.embed y.1
    rw [c.chart.symm_apply_apply]
    rfl
  -- the admissible chart moduli at one overlap point
  set A : T.chartOverlap c → Set ℝ := fun y ↦
    {r | 0 ≤ r ∧ r ≤ 1 ∧ ∀ z : c.kind.modelRegion,
      dist (z : Plane) (T.chartOverlapMap c y) < r →
        dist (psi z) (T.embed y.1) ≤ sS y} with hA
  have hANe : ∀ y, (A y).Nonempty := by
    intro y
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    intro z hz
    exact absurd hz (not_lt.mpr dist_nonneg)
  have hAbdd : ∀ y, BddAbove (A y) := fun y ↦ ⟨1, fun r hr ↦ hr.2.1⟩
  -- one admissible modulus works uniformly on every compact set of the overlap
  have hUniform : ∀ C : Set (T.chartOverlap c), IsCompact C → C.Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C, min δ 1 ∈ A y := by
    intro C hC hCne
    obtain ⟨y₀, hy₀C, hy₀min⟩ := hC.exists_isMinOn hCne hsScont.continuousOn
    have hmpos : 0 < sS y₀ := hsSpos y₀
    -- the compact model trace of C and a compact plane neighborhood inside the model
    have hmodelCont : Continuous fun y : T.chartOverlap c ↦
        (T.chartOverlapModelMap c y : Plane) :=
      continuous_subtype_val.comp (T.isEmbedding_chartOverlapModelMap c).continuous
    set Z : Set Plane := (fun y : T.chartOverlap c ↦
      (T.chartOverlapModelMap c y : Plane)) '' C with hZ
    have hZcompact : IsCompact Z := hC.image hmodelCont
    have hZball : Z ⊆ Metric.ball (0 : Plane) 1 := by
      rintro z ⟨y, -, rfl⟩
      exact c.kind.modelRegion_subset_perturbationRegion
        (T.chartOverlapModelMap c y).2
    obtain ⟨δ₀, hδ₀, hthick⟩ :=
      hZcompact.exists_cthickening_subset_open Metric.isOpen_ball hZball
    set Kpl : Set Plane :=
      Metric.cthickening δ₀ Z ∩ closure c.kind.modelRegion with hKpl
    have hKplCompact : IsCompact Kpl :=
      hZcompact.cthickening.inter_right isClosed_closure
    have hKplModel : Kpl ⊆ c.kind.modelRegion := by
      rintro z ⟨hzthick, hzcl⟩
      exact c.kind.ball_inter_closure_modelRegion_subset ⟨hthick hzthick, hzcl⟩
    set KM : Set c.kind.modelRegion := Subtype.val ⁻¹' Kpl with hKM
    have hKMcompact : IsCompact KM :=
      LocallyFiniteTriangleComplex.PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        hKplCompact hKplModel
    -- uniform continuity of the compared distance on the compact product
    set Phi : T.chartOverlap c × c.kind.modelRegion → ℝ := fun p ↦
      dist (psi p.2) (T.embed p.1.1) with hPhi
    have hPhiCont : Continuous Phi := by
      apply Continuous.dist
      · exact hpsiCont.comp continuous_snd
      · exact T.isEmbedding.continuous.comp
          (continuous_subtype_val.comp continuous_fst)
    obtain ⟨δ₁, hδ₁, hδ₁close⟩ :=
      (Metric.uniformContinuousOn_iff.mp
        ((hC.prod hKMcompact).uniformContinuousOn_of_continuous
          hPhiCont.continuousOn)) (sS y₀) hmpos
    refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, ?_⟩
    intro y hyC
    refine ⟨le_min (lt_min hδ₁ hδ₀).le zero_le_one, min_le_right _ _, ?_⟩
    intro z hz
    have hzδ : dist (z : Plane) (T.chartOverlapModelMap c y : Plane) <
        min δ₁ δ₀ := by
      have hval : T.chartOverlapMap c y = (T.chartOverlapModelMap c y : Plane) := rfl
      rw [← hval]
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hcenter : (T.chartOverlapModelMap c y : Plane) ∈ Z :=
      Set.mem_image_of_mem _ hyC
    -- the perturbed point stays in the compact model neighborhood
    have hzK : z ∈ KM := by
      have hzball : (z : Plane) ∈ Metric.closedBall
          (T.chartOverlapModelMap c y : Plane) δ₀ :=
        Metric.mem_closedBall.mpr ((hzδ.trans_le (min_le_right _ _)).le)
      have hz1 : (z : Plane) ∈ Metric.cthickening δ₀ Z :=
        Metric.closedBall_subset_cthickening hcenter δ₀ hzball
      exact ⟨hz1, subset_closure z.2⟩
    -- compare with the unperturbed model point through uniform continuity
    have hpair : ((y, z) : T.chartOverlap c × c.kind.modelRegion) ∈ C ×ˢ KM :=
      ⟨hyC, hzK⟩
    have hbase : ((y, T.chartOverlapModelMap c y) :
        T.chartOverlap c × c.kind.modelRegion) ∈ C ×ˢ KM := by
      refine ⟨hyC, Metric.self_subset_cthickening _ hcenter, ?_⟩
      exact subset_closure (T.chartOverlapModelMap c y).2
    have hdistPair : dist ((y, z) : T.chartOverlap c × c.kind.modelRegion)
        (y, T.chartOverlapModelMap c y) < δ₁ := by
      rw [Prod.dist_eq]
      apply max_lt (by simpa using hδ₁)
      rw [Subtype.dist_eq]
      exact hzδ.trans_le (min_le_left _ _)
    have hPhiZero : Phi (y, T.chartOverlapModelMap c y) = 0 := by
      simp only [hPhi]
      rw [hpsiModel y, dist_self]
    have hlt := hδ₁close _ hpair _ hbase hdistPair
    rw [hPhiZero, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hlt
    exact hlt.le.trans (hy₀min hyC)
  -- the chart matching control: half the supremum of the admissible moduli
  have hsSupPos : ∀ y : T.chartOverlap c, 0 < sSup (A y) := by
    intro y
    obtain ⟨δ, hδ, hmem⟩ := hUniform {y} isCompact_singleton ⟨y, rfl⟩
    exact lt_of_lt_of_le (lt_min hδ one_pos) (le_csSup (hAbdd y) (hmem y rfl))
  refine ⟨fun y ↦ sSup (A y) / 2, ?_, ?_⟩
  · intro C hC _
    rcases C.eq_empty_or_nonempty with rfl | hCne
    · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
    obtain ⟨δ, hδ, hmem⟩ := hUniform C hC hCne
    refine ⟨min δ 1 / 2, by positivity, ?_⟩
    intro y hy
    have := le_csSup (hAbdd y) (hmem y hy)
    linarith
  · intro g' g hgval hclose x hx
    rw [tendsto_iff_dist_tendsto_zero]
    have hbase : Filter.Tendsto (fun y' : T.toIntrinsic.realization ↦
        2 * dist (T.embed y') (T.embed x))
        (nhdsWithin x (T.chartOverlap c)) (nhds 0) := by
      have hcont : Filter.Tendsto (fun y' : T.toIntrinsic.realization ↦
          dist (T.embed y') (T.embed x))
          (nhdsWithin x (T.chartOverlap c)) (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.mp
          ((T.isEmbedding.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
      have h2 := hcont.const_mul (2 : ℝ)
      rw [mul_zero] at h2
      exact h2
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hbase
    filter_upwards [self_mem_nhdsWithin] with y' hy'
    have hkey : dist (g y') (T.embed y') ≤ sS ⟨y', hy'⟩ := by
      obtain ⟨r, hrA, hr⟩ := exists_lt_of_lt_csSup (hANe ⟨y', hy'⟩)
        (half_lt_self (hsSupPos ⟨y', hy'⟩))
      have hdist : dist ((g' ⟨y', hy'⟩ : Plane)) (T.chartOverlapMap c ⟨y', hy'⟩) < r :=
        lt_of_le_of_lt (hclose ⟨y', hy'⟩) hr
      have hval := hrA.2.2 (g' ⟨y', hy'⟩) hdist
      rw [show g y' = psi (g' ⟨y', hy'⟩) from hgval ⟨y', hy'⟩]
      exact hval
    have hSle : sS ⟨y', hy'⟩ ≤ dist (T.embed y') (T.embed x) :=
      Metric.infDist_le_dist_of_mem ⟨x, hx, rfl⟩
    calc
      dist (g y') (T.embed x) ≤
          dist (g y') (T.embed y') + dist (T.embed y') (T.embed x) :=
        dist_triangle _ _ _
      _ ≤ dist (T.embed y') (T.embed x) + dist (T.embed y') (T.embed x) :=
        add_le_add (hkey.trans hSle) le_rfl
      _ = 2 * dist (T.embed y') (T.embed x) := by ring

/-- Relative form of the chart matching control.  On an arbitrary open subset of the chart
overlap, one control simultaneously makes the replacement converge to the old embedding at the
new frontier and keeps its image disjoint from the unchanged complement. -/
theorem exists_chartMatchingControlOn_of_metricSpace
    {S' : Type*} [MetricSpace S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (hsub : U ⊆ T.chartOverlap c) :
    ∃ mu : U → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : U → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S'),
        (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : U,
          dist (g' y : Plane)
            (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ≤ mu y) →
        MatchesAtFrontier U g T.embed ∧
          Disjoint (g '' U) (T.embed '' Uᶜ) := by
  classical
  let toOverlap : U → T.chartOverlap c := fun y ↦ ⟨y.1, hsub y.2⟩
  have htoOverlapCont : Continuous toOverlap :=
    Continuous.subtype_mk continuous_subtype_val _
  let model : U → c.kind.modelRegion :=
    fun y ↦ T.chartOverlapModelMap c (toOverlap y)
  let coord : U → Plane := fun y ↦ (model y : Plane)
  have hmodelCont : Continuous model :=
    (T.isEmbedding_chartOverlapModelMap c).continuous.comp htoOverlapCont
  have hcoordCont : Continuous coord :=
    continuous_subtype_val.comp hmodelCont
  by_cases hComp : Uᶜ.Nonempty
  swap
  · refine ⟨fun _ ↦ 1, fun C _ _ ↦ ⟨1, one_pos, fun _ _ ↦ le_rfl⟩, ?_⟩
    intro g' g hgval hclose
    constructor
    · intro x hx
      exfalso
      apply hComp
      have hxcomp : x ∈ Uᶜ := by
        rw [← frontier_compl U] at hx
        exact hU.isClosed_compl.frontier_subset hx
      exact ⟨x, hxcomp⟩
    · rw [Set.disjoint_left]
      rintro z ⟨x, hx, rfl⟩ ⟨y, hy, -⟩
      exact hComp ⟨y, hy⟩
  have hCompCompact : IsCompact (T.embed '' Uᶜ) :=
    hU.isClosed_compl.isCompact.image T.isEmbedding.continuous
  have hCompNe : (T.embed '' Uᶜ).Nonempty := hComp.image _
  set sS : U → ℝ := fun y ↦
    Metric.infDist (T.embed y.1) (T.embed '' Uᶜ) / 2 with hsS
  have hsSpos : ∀ y : U, 0 < sS y := by
    intro y
    rw [hsS]
    apply half_pos
    apply (hCompCompact.isClosed.notMem_iff_infDist_pos hCompNe).mp
    rintro ⟨x, hxComp, hxy⟩
    have hxval : x = y.1 := T.isEmbedding.injective hxy
    rw [hxval] at hxComp
    exact hxComp y.2
  have hsScont : Continuous sS := by
    rw [hsS]
    exact ((Metric.continuous_infDist_pt _).comp
      (T.isEmbedding.continuous.comp continuous_subtype_val)).div_const 2
  set psi : c.kind.modelRegion → S' := fun z ↦ (c.chart.symm z).1 with hpsi
  have hpsiCont : Continuous psi :=
    continuous_subtype_val.comp c.chart.symm.continuous
  have hpsiModel : ∀ y : U, psi (model y) = T.embed y.1 := by
    intro y
    change (c.chart.symm
      (c.chart (T.chartOverlapToDomain c (toOverlap y)))).1 = T.embed y.1
    rw [c.chart.symm_apply_apply]
    rfl
  set A : U → Set ℝ := fun y ↦
    {r | 0 ≤ r ∧ r ≤ 1 ∧ ∀ z : c.kind.modelRegion,
      dist (z : Plane) (coord y) < r →
        dist (psi z) (T.embed y.1) ≤ sS y} with hA
  have hANe : ∀ y, (A y).Nonempty := by
    intro y
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    intro z hz
    exact absurd hz (not_lt.mpr dist_nonneg)
  have hAbdd : ∀ y, BddAbove (A y) := fun y ↦ ⟨1, fun r hr ↦ hr.2.1⟩
  have hUniform : ∀ C : Set U, IsCompact C → C.Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C, min δ 1 ∈ A y := by
    intro C hC hCne
    obtain ⟨y₀, hy₀C, hy₀min⟩ :=
      hC.exists_isMinOn hCne hsScont.continuousOn
    have hmpos : 0 < sS y₀ := hsSpos y₀
    set Z : Set Plane := coord '' C with hZ
    have hZcompact : IsCompact Z := hC.image hcoordCont
    have hZball : Z ⊆ Metric.ball (0 : Plane) 1 := by
      rintro z ⟨y, -, rfl⟩
      exact c.kind.modelRegion_subset_perturbationRegion (model y).2
    obtain ⟨δ₀, hδ₀, hthick⟩ :=
      hZcompact.exists_cthickening_subset_open Metric.isOpen_ball hZball
    set Kpl : Set Plane :=
      Metric.cthickening δ₀ Z ∩ closure c.kind.modelRegion with hKpl
    have hKplCompact : IsCompact Kpl :=
      hZcompact.cthickening.inter_right isClosed_closure
    have hKplModel : Kpl ⊆ c.kind.modelRegion := by
      rintro z ⟨hzthick, hzcl⟩
      exact c.kind.ball_inter_closure_modelRegion_subset
        ⟨hthick hzthick, hzcl⟩
    set KM : Set c.kind.modelRegion := Subtype.val ⁻¹' Kpl with hKM
    have hKMcompact : IsCompact KM :=
      LocallyFiniteTriangleComplex.PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        hKplCompact hKplModel
    set Phi : U × c.kind.modelRegion → ℝ := fun p ↦
      dist (psi p.2) (T.embed p.1.1) with hPhi
    have hPhiCont : Continuous Phi := by
      apply Continuous.dist
      · exact hpsiCont.comp continuous_snd
      · exact T.isEmbedding.continuous.comp
          (continuous_subtype_val.comp continuous_fst)
    obtain ⟨δ₁, hδ₁, hδ₁close⟩ :=
      (Metric.uniformContinuousOn_iff.mp
        ((hC.prod hKMcompact).uniformContinuousOn_of_continuous
          hPhiCont.continuousOn)) (sS y₀) hmpos
    refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, ?_⟩
    intro y hyC
    refine ⟨le_min (lt_min hδ₁ hδ₀).le zero_le_one,
      min_le_right _ _, ?_⟩
    intro z hz
    have hzδ : dist (z : Plane) (coord y) < min δ₁ δ₀ :=
      lt_of_lt_of_le hz (min_le_left _ _)
    have hcenter : coord y ∈ Z := Set.mem_image_of_mem _ hyC
    have hzK : z ∈ KM := by
      have hzball : (z : Plane) ∈ Metric.closedBall (coord y) δ₀ :=
        Metric.mem_closedBall.mpr ((hzδ.trans_le (min_le_right _ _)).le)
      have hz1 : (z : Plane) ∈ Metric.cthickening δ₀ Z :=
        Metric.closedBall_subset_cthickening hcenter δ₀ hzball
      exact ⟨hz1, subset_closure z.2⟩
    have hpair : ((y, z) : U × c.kind.modelRegion) ∈ C ×ˢ KM :=
      ⟨hyC, hzK⟩
    have hbase : ((y, model y) : U × c.kind.modelRegion) ∈ C ×ˢ KM := by
      refine ⟨hyC, Metric.self_subset_cthickening _ hcenter, ?_⟩
      exact subset_closure (model y).2
    have hdistPair : dist ((y, z) : U × c.kind.modelRegion)
        (y, model y) < δ₁ := by
      rw [Prod.dist_eq]
      apply max_lt (by simpa using hδ₁)
      rw [Subtype.dist_eq]
      exact hzδ.trans_le (min_le_left _ _)
    have hPhiZero : Phi (y, model y) = 0 := by
      simp only [hPhi]
      rw [hpsiModel y, dist_self]
    have hlt := hδ₁close _ hpair _ hbase hdistPair
    rw [hPhiZero, Real.dist_eq, sub_zero,
      abs_of_nonneg dist_nonneg] at hlt
    exact hlt.le.trans (hy₀min hyC)
  have hsSupPos : ∀ y : U, 0 < sSup (A y) := by
    intro y
    obtain ⟨δ, hδ, hmem⟩ :=
      hUniform {y} isCompact_singleton ⟨y, rfl⟩
    exact lt_of_lt_of_le (lt_min hδ one_pos)
      (le_csSup (hAbdd y) (hmem y rfl))
  refine ⟨fun y ↦ sSup (A y) / 2, ?_, ?_⟩
  · intro C hC _
    rcases C.eq_empty_or_nonempty with rfl | hCne
    · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
    obtain ⟨δ, hδ, hmem⟩ := hUniform C hC hCne
    refine ⟨min δ 1 / 2, by positivity, ?_⟩
    intro y hy
    have := le_csSup (hAbdd y) (hmem y hy)
    linarith
  · intro g' g hgval hclose
    constructor
    · intro x hx
      rw [tendsto_iff_dist_tendsto_zero]
      have hbase : Filter.Tendsto
          (fun y' : T.toIntrinsic.realization ↦
            2 * dist (T.embed y') (T.embed x))
          (nhdsWithin x U) (nhds 0) := by
        have hcont : Filter.Tendsto
            (fun y' : T.toIntrinsic.realization ↦
              dist (T.embed y') (T.embed x))
            (nhdsWithin x U) (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp
            ((T.isEmbedding.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
        have h2 := hcont.const_mul (2 : ℝ)
        rw [mul_zero] at h2
        exact h2
      apply squeeze_zero'
        (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hbase
      filter_upwards [self_mem_nhdsWithin] with y' hy'
      have hkey : dist (g y') (T.embed y') ≤ sS ⟨y', hy'⟩ := by
        obtain ⟨r, hrA, hr⟩ :=
          exists_lt_of_lt_csSup (hANe ⟨y', hy'⟩)
            (half_lt_self (hsSupPos ⟨y', hy'⟩))
        have hdist : dist ((g' ⟨y', hy'⟩ : Plane))
            (coord ⟨y', hy'⟩) < r :=
          lt_of_le_of_lt (hclose ⟨y', hy'⟩) hr
        have hval := hrA.2.2 (g' ⟨y', hy'⟩) hdist
        rw [show g y' = psi (g' ⟨y', hy'⟩) from hgval ⟨y', hy'⟩]
        exact hval
      have hxcomp : x ∈ Uᶜ := by
        rw [← frontier_compl U] at hx
        exact hU.isClosed_compl.frontier_subset hx
      have hSle : sS ⟨y', hy'⟩ ≤
          dist (T.embed y') (T.embed x) := by
        rw [hsS]
        have hinf : Metric.infDist (T.embed y') (T.embed '' Uᶜ) ≤
            dist (T.embed y') (T.embed x) :=
          Metric.infDist_le_dist_of_mem ⟨x, hxcomp, rfl⟩
        have hnonneg : 0 ≤ Metric.infDist (T.embed y') (T.embed '' Uᶜ) :=
          Metric.infDist_nonneg
        linarith
      calc
        dist (g y') (T.embed x) ≤
            dist (g y') (T.embed y') + dist (T.embed y') (T.embed x) :=
          dist_triangle _ _ _
        _ ≤ dist (T.embed y') (T.embed x) +
            dist (T.embed y') (T.embed x) :=
          add_le_add (hkey.trans hSle) le_rfl
        _ = 2 * dist (T.embed y') (T.embed x) := by ring
    · rw [Set.disjoint_left]
      rintro z ⟨x, hxU, rfl⟩ ⟨y, hyComp, hyEq⟩
      have hkey : dist (g x) (T.embed x) ≤ sS ⟨x, hxU⟩ := by
        obtain ⟨r, hrA, hr⟩ :=
          exists_lt_of_lt_csSup (hANe ⟨x, hxU⟩)
            (half_lt_self (hsSupPos ⟨x, hxU⟩))
        have hdist : dist ((g' ⟨x, hxU⟩ : Plane))
            (coord ⟨x, hxU⟩) < r :=
          lt_of_le_of_lt (hclose ⟨x, hxU⟩) hr
        have hval := hrA.2.2 (g' ⟨x, hxU⟩) hdist
        rw [show g x = psi (g' ⟨x, hxU⟩) from hgval ⟨x, hxU⟩]
        exact hval
      have hinf : Metric.infDist (T.embed x) (T.embed '' Uᶜ) ≤
          dist (T.embed x) (T.embed y) :=
        Metric.infDist_le_dist_of_mem ⟨y, hyComp, rfl⟩
      have heqdist : dist (T.embed x) (T.embed y) =
          dist (g x) (T.embed x) := by
        rw [← hyEq, dist_comm]
      rw [hsS] at hkey
      have hpos := hsSpos ⟨x, hxU⟩
      rw [hsS] at hpos
      linarith

/-- Crossing-weld plan, item 2, matching half, on the ambient surface.  The statement is
metric-free; the compact second-countable surface is metrized and the metric-target version is
applied at the compatible metric. -/
theorem exists_chartMatchingControl [T2Space S] [CompactSpace S]
    [SecondCountableTopology S] (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ mu : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : T.chartOverlap c → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S),
        (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : T.chartOverlap c,
          dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y) →
        MatchesAtFrontier (T.chartOverlap c) g T.embed := by
  letI : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  exact exists_chartMatchingControl_of_metricSpace T c

/-- The geometric certificate retained from a controlled chart replacement.  Besides the
homeomorphism from the source open set, it records that every replacement face is exactly a
polygonal closed disk.  Keeping this witness exposed is what the final Radó conforming step
needs in order to take a finite arrangement near the compact chart patch. -/
structure PolygonalReplacementPresentation
    (X : Type*) [TopologicalSpace X] (V : Set Plane) where
  complex : LocallyFiniteTriangleComplex V
  sourceHomeomorph : X ≃ₜ complex.support
  facePolygon : complex.Face → PolygonalCircle
  /-- The plane map used to fill each abstract source triangle. -/
  faceFillingMap : complex.Face → Plane → Plane
  /-- The ambient face map is the retained filling in standard triangle coordinates. -/
  faceMap_eq : ∀ f x, (complex.faceMap f x).1 =
    faceFillingMap f (complex.facePlaneHomeomorph f x).1
  /-- The filling is genuinely finite PL, so its boundary marks can be pulled back to a
  finite source subdivision in the relative conforming step. -/
  faceCertificate : ∀ f, Nonempty (FinitePLHomeomorphBetween
    (faceFillingMap f) LocallyFiniteTriangleComplex.standardFaceRegion
      (facePolygon f).closedRegion)
  faceClosedRegion_subset : ∀ f, (facePolygon f).closedRegion ⊆ V
  faceCarrier_eq : ∀ f,
    complex.faceCarrier f =
      {q : V | q.1 ∈ (facePolygon f).closedRegion}

/-- The source points carried by one named polygonal replacement face. -/
def PolygonalReplacementPresentation.sourceFaceSet
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (Q : PolygonalReplacementPresentation U V) (f : Q.complex.Face) :
    Set K.realization :=
  {x | ∃ hx : x ∈ U,
    (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ Q.complex.faceCarrier f}

/-- Finite-source bookkeeping retained from an adaptive polygonal replacement.

Faces are grouped into finite adaptive tiles.  Any finite tile family is represented exactly
by a finite family of faces at one common midpoint level of the original intrinsic complex.
This is the missing source-side content behind Moise's conditions (f)--(h); keeping it separate
from the coordinate presentation lets the finite arrangement machinery remain generic. -/
structure PolygonalReplacementSourceAtlas
    (K : IntrinsicTwoComplex) (U : Set K.realization) (V : Set Plane)
    (Q : PolygonalReplacementPresentation U V) where
  Tile : Type
  tileDecidableEq : DecidableEq Tile
  tile : Q.complex.Face → Tile
  tileFaces : Tile → Finset Q.complex.Face
  mem_tileFaces : ∀ t f, f ∈ tileFaces t ↔ tile f = t
  sourceTileCarrier : Tile → Set K.realization
  sourceTileCarrier_subset_open : ∀ t, sourceTileCarrier t ⊆ U
  sourceTileCarrier_locallyFinite :
    LocallyFinite fun t ↦ {x : U | x.1 ∈ sourceTileCarrier t}
  sourceTileCarrier_eq_faces : ∀ t,
    sourceTileCarrier t =
      ⋃ f : {f : Q.complex.Face // f ∈ tileFaces t},
        Q.sourceFaceSet f.1
  /-- An original maximal face containing each retained source fan face. -/
  sourceFaceParent : Q.complex.Face → K.Face
  sourceFaceSet_subset_parent : ∀ f,
    Q.sourceFaceSet f ⊆ K.faceCarrier (sourceFaceParent f).1
  /-- Every retained source face has one affine formula in the original intrinsic barycentric
  coordinates as a function of its standard planar face coordinates. -/
  sourceFaceStandardAffine : ∀ f : Q.complex.Face,
    ∃ a : Plane →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : Q.complex.ClosedFace f,
        (Q.sourceHomeomorph.symm
          (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := Q.complex) f x)).1.1 =
          a (Q.complex.facePlaneHomeomorph f x).1
  commonLevel : Finset Tile → ℕ
  levelFaces : (F : Finset Tile) → Finset (K.LevelFace (commonLevel F))
  sourceTiles_eq_levelFaces : ∀ F : Finset Tile,
    (⋃ t : {t : Tile // t ∈ F}, sourceTileCarrier t.1) =
      ⋃ u : {u : K.LevelFace (commonLevel F) // u ∈ levelFaces F},
        K.levelFaceCarrier u.1

attribute [instance] PolygonalReplacementSourceAtlas.tileDecidableEq

namespace PolygonalReplacementPresentation

variable {X : Type*} [TopologicalSpace X] {V : Set Plane}

open LocallyFiniteTriangleComplex.PlaneGraphRealization

/-- The canonical source parametrization of one retained replacement face.  It is obtained by
pulling the replacement face parametrization back through the presentation homeomorphism, so it
uses exactly the same abstract barycentric coordinates as `Q.complex.faceMap`. -/
noncomputable def sourceFaceMap
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face) :
    Q.complex.ClosedFace f → X :=
  Q.sourceHomeomorph.symm ∘ faceToSupport (K := Q.complex) f

theorem sourceHomeomorph_sourceFaceMap
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face)
    (x : Q.complex.ClosedFace f) :
    Q.sourceHomeomorph (Q.sourceFaceMap f x) =
      faceToSupport (K := Q.complex) f x := by
  exact Q.sourceHomeomorph.apply_symm_apply _

/-- Each canonical source face parametrization is an embedding. -/
theorem isEmbedding_sourceFaceMap [T2Space V]
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face) :
    _root_.Topology.IsEmbedding (Q.sourceFaceMap f) := by
  exact Q.sourceHomeomorph.symm.isEmbedding.comp
    (Q.complex.isEmbedding_faceToSupport f)

/-- Two canonical source-face points agree exactly when their zero-extended barycentric
coordinates agree.  This is the source-side face-to-face law inherited from the retained
replacement complex. -/
theorem sourceFaceMap_eq_iff [T2Space V]
    (Q : PolygonalReplacementPresentation X V)
    {f g : Q.complex.Face}
    {x : Q.complex.ClosedFace f} {y : Q.complex.ClosedFace g} :
    Q.sourceFaceMap f x = Q.sourceFaceMap g y ↔
      extendFaceCoordinates (Q.complex.faceVertices f) x =
        extendFaceCoordinates (Q.complex.faceVertices g) y := by
  rw [← Q.sourceHomeomorph.injective.eq_iff,
    Q.sourceHomeomorph_sourceFaceMap f x,
    Q.sourceHomeomorph_sourceFaceMap g y]
  constructor
  · intro h
    exact Q.complex.faceMap_eq_iff.mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact Q.complex.faceMap_eq_iff.mpr h

/-- The canonical source parametrization has exactly the retained source face as its range. -/
theorem range_val_sourceFaceMap
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (Q : PolygonalReplacementPresentation U V) (f : Q.complex.Face) :
    Set.range (fun z ↦ (Q.sourceFaceMap f z).1) = Q.sourceFaceSet f := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    refine ⟨(Q.sourceFaceMap f z).2, ?_⟩
    rw [Q.sourceHomeomorph_sourceFaceMap f z]
    exact Set.mem_range_self z
  · rintro x ⟨hxU, hxFace⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqFace : q ∈ faceInSupport (K := Q.complex) f := by
      rw [Q.complex.faceInSupport_eq_preimage]
      exact hxFace
    obtain ⟨z, hz⟩ := hqFace
    refine ⟨z, ?_⟩
    change (Q.sourceHomeomorph.symm
      (faceToSupport (K := Q.complex) f z)).1 = x
    rw [hz]
    exact congrArg Subtype.val (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

/-- Only finitely many polygonal replacement faces meet a compact chart set.  This is the
finiteness cut used before passing to the common supporting-line arrangement. -/
theorem finite_facesMeeting
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    {f : Q.complex.Face | (Q.complex.faceCarrier f ∩ C).Nonempty}.Finite :=
  Q.complex.locallyFinite.finite_nonempty_inter_compact hC

/-- The finite subtype of replacement faces meeting a specified compact chart set. -/
noncomputable def FacesMeeting
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (hC : IsCompact C) : Type :=
  {f : Q.complex.Face | (Q.complex.faceCarrier f ∩ C).Nonempty}

noncomputable instance facesMeetingFintype
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (hC : IsCompact C) : Fintype (Q.FacesMeeting C hC) :=
  (Q.finite_facesMeeting hC).fintype

noncomputable instance facesMeetingDecidableEq
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (hC : IsCompact C) : DecidableEq (Q.FacesMeeting C hC) :=
  Classical.decEq _

/-- A compact part of a locally finite replacement support is carried by the finitely many
faces which meet it.  This is the exact compact-to-finite cut used in Moise's condition (b). -/
theorem support_inter_subset_iUnion_facesMeeting
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    Q.complex.support ∩ C ⊆
      ⋃ f : Q.FacesMeeting C hC, Q.complex.faceCarrier f.1 := by
  rintro x ⟨hxSupport, hxC⟩
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxSupport
  let F : Q.FacesMeeting C hC :=
    ⟨f, ⟨x, hxf, hxC⟩⟩
  exact Set.mem_iUnion.mpr ⟨F, hxf⟩

/-- On the selected finite family, the preceding carrier union is the union of the retained
polygonal closed disks. -/
theorem support_inter_subset_selectedClosedRegion
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    Q.complex.support ∩ C ⊆
      {x : V | x.1 ∈ PolygonalFamily.closedRegion
        (fun f : Q.FacesMeeting C hC ↦ Q.facePolygon f.1)} := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp
    (Q.support_inter_subset_iUnion_facesMeeting hC hx)
  apply Set.mem_iUnion.mpr
  refine ⟨f, ?_⟩
  change x ∈ {q : V | q.1 ∈ (Q.facePolygon f.1).closedRegion}
  rw [← Q.faceCarrier_eq f.1]
  exact hxf

/-- The finite replacement faces which meet the fixed chart patch. -/
abbrev PatchFaces (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :=
  Q.FacesMeeting k.patchInPerturbation k.isCompact_patchInPerturbation

end PolygonalReplacementPresentation

namespace PolygonalReplacementSourceAtlas

/-- The finite family of adaptive source tiles touched by an arbitrary compact coordinate set.
This is the relative form needed after deleting the protected old trace: the compact set used
in the weld need not be the whole fixed chart patch. -/
noncomputable def tilesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    Finset A.Tile :=
  Finset.univ.image fun f : Q.FacesMeeting C hC ↦ A.tile f.1

theorem mem_tilesMeeting_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (t : A.Tile) :
    t ∈ A.tilesMeeting C hC ↔
      ∃ f : Q.FacesMeeting C hC, A.tile f.1 = t := by
  simp [PolygonalReplacementSourceAtlas.tilesMeeting]

/-- All replacement fan faces belonging to a tile touched by `C`. -/
noncomputable def tileFaceFinsetMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    Finset Q.complex.Face :=
  (A.tilesMeeting C hC).biUnion A.tileFaces

abbrev TileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :=
  {f : Q.complex.Face // f ∈ A.tileFaceFinsetMeeting C hC}

theorem mem_tileFaceFinsetMeeting_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : Q.complex.Face) :
    f ∈ A.tileFaceFinsetMeeting C hC ↔
      ∃ t ∈ A.tilesMeeting C hC, f ∈ A.tileFaces t := by
  simp [PolygonalReplacementSourceAtlas.tileFaceFinsetMeeting]

/-- Every face meeting `C` belongs to the whole-tile closure of the selected family. -/
theorem faceMeeting_mem_tileFaceFinsetMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : Q.FacesMeeting C hC) :
    f.1 ∈ A.tileFaceFinsetMeeting C hC := by
  apply (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mpr
  refine ⟨A.tile f.1, ?_, ?_⟩
  · exact (A.mem_tilesMeeting_iff C hC (A.tile f.1)).mpr ⟨f, rfl⟩
  · exact (A.mem_tileFaces (A.tile f.1) f.1).2 rfl

/-- Closing under the adaptive tiles touched by `C` is exactly the union of their named
replacement faces. -/
theorem sourceTilesMeeting_eq_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ t : {t : A.Tile // t ∈ A.tilesMeeting C hC},
        A.sourceTileCarrier t.1) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    rw [A.sourceTileCarrier_eq_faces t.1] at hxt
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxt
    let f' : A.TileFacesMeeting C hC :=
      ⟨f.1, (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mpr
        ⟨t.1, t.2, f.2⟩⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩
  · intro x hx
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, hft⟩ :=
      (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mp f.2
    let t' : {t : A.Tile // t ∈ A.tilesMeeting C hC} := ⟨t, ht⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t', ?_⟩
    rw [A.sourceTileCarrier_eq_faces t]
    let f' : {q : Q.complex.Face // q ∈ A.tileFaces t} := ⟨f.1, hft⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩

/-- The source selected by an arbitrary compact coordinate set is a literal finite subcomplex
at one common midpoint level of the original intrinsic triangulation. -/
theorem sourceTileFacesMeeting_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 := by
  rw [← A.sourceTilesMeeting_eq_faces C hC]
  exact A.sourceTiles_eq_levelFaces (A.tilesMeeting C hC)

theorem isCompact_sourceTileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    IsCompact (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) := by
  rw [A.sourceTileFacesMeeting_eq_levelFaces C hC]
  exact isCompact_iUnion fun u ↦ K.isCompact_levelFaceCarrier u.1

theorem sourceTileFacesMeeting_subset_open
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) ⊆ U := by
  intro x hx
  obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
  exact hxFace.choose

/-- The coordinate preimage of `C` is contained in its whole-tile source closure. -/
theorem coordinatePreimage_subset_sourceTileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ C} ⊆
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rintro x ⟨hxU, hxC⟩
  let y := Q.sourceHomeomorph ⟨x, hxU⟩
  have hySelected := Q.support_inter_subset_iUnion_facesMeeting hC ⟨y.2, hxC⟩
  obtain ⟨f, hyFace⟩ := Set.mem_iUnion.mp hySelected
  let f' : A.TileFacesMeeting C hC :=
    ⟨f.1, A.faceMeeting_mem_tileFaceFinsetMeeting C hC f⟩
  apply Set.mem_iUnion.mpr
  exact ⟨f', hxU, hyFace⟩

/-- The finite family of adaptive source tiles touched by the compact patch.  The conforming
extension must retain whole tiles, rather than only the individual fan faces which happen to
meet the patch. -/
noncomputable def patchTiles
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    Finset A.Tile :=
  Finset.univ.image fun f : Q.PatchFaces k ↦ A.tile f.1

theorem mem_patchTiles_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (t : A.Tile) :
    t ∈ A.patchTiles ↔ ∃ f : Q.PatchFaces k, A.tile f.1 = t := by
  simp [PolygonalReplacementSourceAtlas.patchTiles]

/-- All replacement fan faces belonging to a tile touched by the patch. -/
noncomputable def patchTileFaceFinset
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    Finset Q.complex.Face :=
  A.patchTiles.biUnion A.tileFaces

abbrev PatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :=
  {f : Q.complex.Face // f ∈ A.patchTileFaceFinset}

theorem mem_patchTileFaceFinset_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : Q.complex.Face) :
    f ∈ A.patchTileFaceFinset ↔
      ∃ t ∈ A.patchTiles, f ∈ A.tileFaces t := by
  simp [PolygonalReplacementSourceAtlas.patchTileFaceFinset]

/-- Every face which meets the patch belongs to the whole-tile closure. -/
theorem patchFace_mem_patchTileFaceFinset
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : Q.PatchFaces k) :
    f.1 ∈ A.patchTileFaceFinset := by
  apply (A.mem_patchTileFaceFinset_iff f.1).mpr
  refine ⟨A.tile f.1, ?_, ?_⟩
  · exact (A.mem_patchTiles_iff (A.tile f.1)).mpr ⟨f, rfl⟩
  · exact (A.mem_tileFaces (A.tile f.1) f.1).2 rfl

/-- Closing under touched adaptive tiles changes the finite coordinate family, but its source is
still exactly the union of those finitely many named tiles. -/
theorem sourcePatchTiles_eq_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ t : {t : A.Tile // t ∈ A.patchTiles}, A.sourceTileCarrier t.1) =
      ⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    rw [A.sourceTileCarrier_eq_faces t.1] at hxt
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxt
    let f' : A.PatchTileFaces :=
      ⟨f.1, (A.mem_patchTileFaceFinset_iff f.1).mpr ⟨t.1, t.2, f.2⟩⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩
  · intro x hx
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, hft⟩ := (A.mem_patchTileFaceFinset_iff f.1).mp f.2
    let t' : {t : A.Tile // t ∈ A.patchTiles} := ⟨t, ht⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t', ?_⟩
    rw [A.sourceTileCarrier_eq_faces t]
    let f' : {q : Q.complex.Face // q ∈ A.tileFaces t} := ⟨f.1, hft⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩

/-- The whole-tile closure is therefore a literal finite subcomplex at one common midpoint
level of the original intrinsic triangulation. -/
theorem sourcePatchTileFaces_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) =
      ⋃ u : {u : K.LevelFace (A.commonLevel A.patchTiles) //
          u ∈ A.levelFaces A.patchTiles},
        K.levelFaceCarrier u.1 := by
  rw [← A.sourcePatchTiles_eq_faces]
  exact A.sourceTiles_eq_levelFaces A.patchTiles

/-- The tile-closed source selected for the finite weld is compact.  This is the compact
subpolyhedron on which the later relative boundary extension is allowed to change the old
triangulation. -/
theorem isCompact_sourcePatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    IsCompact (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) := by
  rw [A.sourcePatchTileFaces_eq_levelFaces]
  exact isCompact_iUnion fun u ↦ K.isCompact_levelFaceCarrier u.1

/-- Every point of the tile-closed source subcomplex still lies in the open region on which
the controlled replacement was constructed. -/
theorem sourcePatchTileFaces_subset_open
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) ⊆ U := by
  intro x hx
  obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
  exact hxFace.choose

/-- The whole old trace over the fixed patch is carried by the tile-closed source selection.
This is the source-side coverage needed before cutting the old complex along its finite
attaching boundary. -/
theorem coordinatePreimage_patch_subset_sourcePatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ k.patchInPerturbation} ⊆
      ⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1 := by
  rintro x ⟨hxU, hxPatch⟩
  let y := Q.sourceHomeomorph ⟨x, hxU⟩
  have hySelected := Q.support_inter_subset_iUnion_facesMeeting
    k.isCompact_patchInPerturbation ⟨y.2, hxPatch⟩
  obtain ⟨f, hyFace⟩ := Set.mem_iUnion.mp hySelected
  let f' : A.PatchTileFaces := ⟨f.1, A.patchFace_mem_patchTileFaceFinset f⟩
  apply Set.mem_iUnion.mpr
  exact ⟨f', hxU, hyFace⟩

end PolygonalReplacementSourceAtlas

namespace PolygonalReplacementPresentation

variable {X : Type*} [TopologicalSpace X] {V : Set Plane}

/-- The polygonal disk belonging to one replacement face meeting the chart patch. -/
def patchFacePolygon (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    Q.PatchFaces k → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The fixed patch lies in the enclosing triangle used for the finite family of all
replacement faces which meet it.  The point is that every chart patch lies in the unit ball,
while `PolygonalFamily.enclosingRadius` is at least one. -/
theorem patchComplex_support_subset_arrangementMesh
    (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    k.patchComplex.support ⊆
      (PolygonalFamily.arrangementMesh (Q.patchFacePolygon k)).toPlaneComplex.support := by
  rw [PolygonalFamily.arrangementMesh_support,
    PolygonalFamily.enclosingMesh, TriangleMesh.single_support]
  apply k.patchComplex_support_subset_modelRegion.trans
  apply k.modelRegion_subset_perturbationRegion.trans
  apply Metric.ball_subset_closedBall.trans
  apply (Metric.closedBall_subset_closedBall
    (le_max_right
      ((PolygonalFamily.isCompact_closedRegion
        (Q.patchFacePolygon k)).isBounded.subset_closedBall (0 : Plane)).choose 1)).trans
  exact PolygonalCircle.closedBall_subset_enclosingTriangle
    (PolygonalFamily.enclosingRadius_pos (Q.patchFacePolygon k))

/-- The old replacement trace over the fixed patch is contained in the finite polygonal family
selected above. -/
theorem support_inter_patch_subset_closedRegion
    (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    Q.complex.support ∩ k.patchInPerturbation ⊆
      {x : k.perturbationRegion |
        x.1 ∈ PolygonalFamily.closedRegion (Q.patchFacePolygon k)} := by
  exact Q.support_inter_subset_selectedClosedRegion
    k.isCompact_patchInPerturbation

/-- The fixed patch as a triangle mesh, for synchronization with the replacement polygons. -/
noncomputable def patchTriangleMesh (k : ChartKind) : TriangleMesh :=
  k.patchComplex.toTriangleMesh

/-- The finite old-side coordinate mesh in the common old/patch arrangement. -/
noncomputable def patchOldMesh (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh (Q.patchFacePolygon k)
    (patchTriangleMesh k) (fun _ ↦ True)

/-- The finite new-patch coordinate mesh in the same common arrangement. -/
noncomputable def patchNewMesh (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh (Q.patchFacePolygon k)
    (patchTriangleMesh k)

theorem patchOldMesh_support (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    (Q.patchOldMesh k).toPlaneComplex.support =
      PolygonalFamily.closedRegion (Q.patchFacePolygon k) := by
  simpa [patchOldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support
      (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True))

theorem patchNewMesh_support (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    (Q.patchNewMesh k).toPlaneComplex.support = k.patchComplex.support := by
  have hsub : (patchTriangleMesh k).toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (Q.patchFacePolygon k)).toPlaneComplex.support := by
    rw [patchTriangleMesh, k.patchComplex.toTriangleMesh_support
      k.patchComplex_pure]
    exact Q.patchComplex_support_subset_arrangementMesh k
  exact (PolygonalFamily.targetSynchronizedMesh_support
    (Q.patchFacePolygon k) (patchTriangleMesh k) hsub).trans
      (k.patchComplex.toTriangleMesh_support k.patchComplex_pure)

/-- Both coordinate sides are restrictions of one ambient triangle mesh, so every retained
maximal face is a triangle. -/
theorem patchMeshes_triangle_card (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    ∀ t ∈ (Q.patchOldMesh k).triangles ∪ (Q.patchNewMesh k).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (Q.patchOldMesh k).card_triangle t htOld
  · exact (Q.patchNewMesh k).card_triangle t htNew

/-- The two finite coordinate sides satisfy the joint surface edge-incidence bound. -/
theorem patchMeshes_joint_edge_valence (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (e : Finset (Q.patchOldMesh k).Vertex) (he : e.card = 2) :
    (((Q.patchOldMesh k).triangles ∪
        (Q.patchNewMesh k).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence
    (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True) e he

theorem patchMeshes_surface_edge_valence (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    ∀ e ∈ ((Q.patchOldMesh k).triangles ∪
        (Q.patchNewMesh k).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((Q.patchOldMesh k).triangles ∪
          (Q.patchNewMesh k).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact Q.patchMeshes_joint_edge_valence k e (Finset.mem_powersetCard.mp het).2

/-- The two coordinate embeddings agree exactly when their common barycentric coordinates do.
This is both interface clauses (`hagree` and `hsep`) of the later ambient weld, before composing
with the chart homeomorphism. -/
theorem patchMeshes_coordinateEmbed_eq_iff (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (x : GeometricRealization (Q.patchOldMesh k).Vertex
      (Q.patchOldMesh k).triangles)
    (y : GeometricRealization (Q.patchNewMesh k).Vertex
      (Q.patchNewMesh k).triangles) :
    (Q.patchOldMesh k).coordinateEmbed x =
        (Q.patchNewMesh k).coordinateEmbed y ↔
      (x : (Q.patchOldMesh k).Vertex → ℝ) =
        (y : (Q.patchNewMesh k).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement (Q.patchFacePolygon k)
    (patchTriangleMesh k)
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem
        (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem
        (Q.patchFacePolygon k) (patchTriangleMesh k)).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- If the retained source coordinates land in a closed model region, the whole replacement
support does too. -/
theorem support_subset_modelRegion_of_coordinate (k : ChartKind)
    (Q : PolygonalReplacementPresentation X V)
    (g' : X → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    Q.complex.support ⊆ {z : V | z.1 ∈ k.modelRegion} := by
  intro z hz
  let zSupport : Q.complex.support := ⟨z, hz⟩
  obtain ⟨y, hy⟩ := Q.sourceHomeomorph.surjective zSupport
  have hyval : (Q.sourceHomeomorph y).1.1 = z.1 :=
    congrArg (fun w : Q.complex.support ↦ w.1.1) hy
  change z.1 ∈ k.modelRegion
  rw [← hyval, ← hcoord y]
  exact (g' y).2

/-- Consequently every selected face polygon used by the finite patch arrangement lies in the
chart model, including the half-plane condition in the bordered case. -/
theorem patchFaceClosedRegion_subset_modelRegion (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (g' : X → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion (Q.patchFacePolygon k) ⊆ k.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ k.perturbationRegion :=
    Q.faceClosedRegion_subset f.1 hxf
  let z : k.perturbationRegion := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate k g' hcoord hzSupport

/-- The old finite coordinate side transported back to the ambient surface chart. -/
noncomputable def patchOldSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    GeometricRealization (Q.patchOldMesh c.kind).Vertex
      (Q.patchOldMesh c.kind).triangles → S :=
  fun x ↦ (c.chart.symm
    ((Q.patchOldMesh c.kind).coordinateEmbedInto c.kind.modelRegion (by
      rw [Q.patchOldMesh_support c.kind]
      exact Q.patchFaceClosedRegion_subset_modelRegion c.kind g' hcoord) x)).1

/-- The synchronized fixed-patch side transported back by the same chart. -/
noncomputable def patchNewSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion) :
    GeometricRealization (Q.patchNewMesh c.kind).Vertex
      (Q.patchNewMesh c.kind).triangles → S :=
  fun x ↦ (c.chart.symm
    ((Q.patchNewMesh c.kind).coordinateEmbedInto c.kind.modelRegion (by
      rw [Q.patchNewMesh_support c.kind]
      exact c.kind.patchComplex_support_subset_modelRegion) x)).1

theorem isEmbedding_patchOldSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    _root_.Topology.IsEmbedding (Q.patchOldSurfaceEmbed c g' hcoord) := by
  let hmodel : (Q.patchOldMesh c.kind).toPlaneComplex.support ⊆
      c.kind.modelRegion := by
    rw [Q.patchOldMesh_support c.kind]
    exact Q.patchFaceClosedRegion_subset_modelRegion c.kind g' hcoord
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((Q.patchOldMesh c.kind).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion hmodel))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (Q.patchOldMesh c.kind).coordinateEmbedInto
        c.kind.modelRegion hmodel) =
      Q.patchOldSurfaceEmbed c g' hcoord := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_patchNewSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion) :
    _root_.Topology.IsEmbedding (Q.patchNewSurfaceEmbed c) := by
  let hmodel : (Q.patchNewMesh c.kind).toPlaneComplex.support ⊆
      c.kind.modelRegion := by
    rw [Q.patchNewMesh_support c.kind]
    exact c.kind.patchComplex_support_subset_modelRegion
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((Q.patchNewMesh c.kind).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion hmodel))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (Q.patchNewMesh c.kind).coordinateEmbedInto
        c.kind.modelRegion hmodel) = Q.patchNewSurfaceEmbed c := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- After transport by the chart, equality of old- and new-side points is still exactly equality
of their common barycentric coordinate functions. -/
theorem patchSurfaceEmbed_eq_iff {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1)
    (x : GeometricRealization (Q.patchOldMesh c.kind).Vertex
      (Q.patchOldMesh c.kind).triangles)
    (y : GeometricRealization (Q.patchNewMesh c.kind).Vertex
      (Q.patchNewMesh c.kind).triangles) :
    Q.patchOldSurfaceEmbed c g' hcoord x = Q.patchNewSurfaceEmbed c y ↔
      (x : (Q.patchOldMesh c.kind).Vertex → ℝ) =
        (y : (Q.patchNewMesh c.kind).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold patchOldSurfaceEmbed patchNewSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hmodel := c.chart.symm.injective hchart
    have hplane := congrArg Subtype.val hmodel
    exact (Q.patchMeshes_coordinateEmbed_eq_iff c.kind x y).mp hplane
  · intro hxy
    have hplane :=
      (Q.patchMeshes_coordinateEmbed_eq_iff c.kind x y).mpr hxy
    unfold patchOldSurfaceEmbed patchNewSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

/-- The finite compact part of the crossing construction already has exactly the common-vertex
interface consumed by `PartialTriangulation.exists_glued`.  What remains in the global Radó
step is to extend its old side over the complement of the selected adaptive faces. -/
theorem exists_patch_local_weld {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁)
          (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁)
          (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t => t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t => e ⊆ t).card ≤ 2) := by
  refine ⟨(Q.patchOldMesh c.kind).Vertex, inferInstance, inferInstance,
    (Q.patchOldMesh c.kind).triangles, (Q.patchNewMesh c.kind).triangles,
    Q.patchOldSurfaceEmbed c g' hcoord, Q.patchNewSurfaceEmbed c,
    Q.patchMeshes_triangle_card c.kind,
    Q.isEmbedding_patchOldSurfaceEmbed c g' hcoord,
    Q.isEmbedding_patchNewSurfaceEmbed c, ?_, ?_,
    Q.patchMeshes_surface_edge_valence c.kind⟩
  · intro x y hxy
    exact (Q.patchSurfaceEmbed_eq_iff c g' hcoord x y).mpr hxy
  · intro x y hxy
    exact (Q.patchSurfaceEmbed_eq_iff c g' hcoord x y).mp hxy

end PolygonalReplacementPresentation

namespace SynchronizedPatch

variable {ι : Type*} [Fintype ι]

/-- The part of a synchronized arrangement belonging to one named polygon. -/
noncomputable def singlePolygonMesh (J : ι → PolygonalCircle)
    (N : TriangleMesh) (i : ι) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J N (fun j ↦ j = i)

theorem singlePolygonMesh_support (J : ι → PolygonalCircle)
    (N : TriangleMesh) (i : ι) :
    (singlePolygonMesh J N i).toPlaneComplex.support = (J i).closedRegion := by
  rw [singlePolygonMesh, PolygonalFamily.selectedSynchronizedMesh_support]
  simp only [PolygonalFamily.selectedClosedRegion]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hj
    simpa only [hji] using hxj
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩

/-- Every fixed chart patch lies in the enclosing arrangement used to synchronize it with an
arbitrary finite polygonal family. -/
theorem patchComplex_support_subset_arrangementMesh (k : ChartKind)
    (J : ι → PolygonalCircle) :
    k.patchComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support := by
  rw [PolygonalFamily.arrangementMesh_support, PolygonalFamily.enclosingMesh,
    TriangleMesh.single_support]
  apply k.patchComplex_support_subset_modelRegion.trans
  apply k.modelRegion_subset_perturbationRegion.trans
  apply Metric.ball_subset_closedBall.trans
  apply (Metric.closedBall_subset_closedBall
    (le_max_right ((PolygonalFamily.isCompact_closedRegion J).isBounded.subset_closedBall
      (0 : Plane)).choose 1)).trans
  exact PolygonalCircle.closedBall_subset_enclosingTriangle
    (PolygonalFamily.enclosingRadius_pos J)

/-- The old member of the common arrangement, restricted to the chosen polygonal union. -/
noncomputable def synchronizedPatchOldMesh (k : ChartKind)
    (J : ι → PolygonalCircle) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J k.patchComplex.toTriangleMesh (fun _ ↦ True)

/-- The fixed chart patch in the same common arrangement. -/
noncomputable def synchronizedPatchNewMesh (k : ChartKind)
    (J : ι → PolygonalCircle) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh J k.patchComplex.toTriangleMesh

theorem synchronizedPatchOldMesh_support (k : ChartKind)
    (J : ι → PolygonalCircle) :
    (synchronizedPatchOldMesh k J).toPlaneComplex.support =
      PolygonalFamily.closedRegion J := by
  simpa [synchronizedPatchOldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support J k.patchComplex.toTriangleMesh
      (fun _ ↦ True))

theorem synchronizedPatchNewMesh_support (k : ChartKind)
    (J : ι → PolygonalCircle) :
    (synchronizedPatchNewMesh k J).toPlaneComplex.support = k.patchComplex.support := by
  have hsub : k.patchComplex.toTriangleMesh.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support := by
    rw [k.patchComplex.toTriangleMesh_support k.patchComplex_pure]
    exact patchComplex_support_subset_arrangementMesh k J
  exact (PolygonalFamily.targetSynchronizedMesh_support J
    k.patchComplex.toTriangleMesh hsub).trans
    (k.patchComplex.toTriangleMesh_support k.patchComplex_pure)

theorem synchronizedPatchMeshes_triangle_card (k : ChartKind)
    (J : ι → PolygonalCircle) :
    ∀ t ∈ (synchronizedPatchOldMesh k J).triangles ∪
        (synchronizedPatchNewMesh k J).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (synchronizedPatchOldMesh k J).card_triangle t htOld
  · exact (synchronizedPatchNewMesh k J).card_triangle t htNew

theorem synchronizedPatchMeshes_surface_edge_valence (k : ChartKind)
    (J : ι → PolygonalCircle) :
    ∀ e ∈ ((synchronizedPatchOldMesh k J).triangles ∪
        (synchronizedPatchNewMesh k J).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((synchronizedPatchOldMesh k J).triangles ∪
          (synchronizedPatchNewMesh k J).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence J
    k.patchComplex.toTriangleMesh
    (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- Both restrictions of the synchronized arrangement use literally the same ambient vertex
coordinates. -/
theorem synchronizedPatchMeshes_coordinateEmbed_eq_iff (k : ChartKind)
    (J : ι → PolygonalCircle)
    (x : GeometricRealization (synchronizedPatchOldMesh k J).Vertex
      (synchronizedPatchOldMesh k J).triangles)
    (y : GeometricRealization (synchronizedPatchNewMesh k J).Vertex
      (synchronizedPatchNewMesh k J).triangles) :
    (synchronizedPatchOldMesh k J).coordinateEmbed x =
        (synchronizedPatchNewMesh k J).coordinateEmbed y ↔
      (x : (synchronizedPatchOldMesh k J).Vertex → ℝ) =
        (y : (synchronizedPatchNewMesh k J).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement J k.patchComplex.toTriangleMesh
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem J
        k.patchComplex.toTriangleMesh
        (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem J
        k.patchComplex.toTriangleMesh).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- Transport the finite polygonal member of a synchronized patch weld to the surface. -/
noncomputable def synchronizedPatchOldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (synchronizedPatchOldMesh c.kind J).Vertex
      (synchronizedPatchOldMesh c.kind J).triangles → S :=
  fun x ↦ (c.chart.symm
    ((synchronizedPatchOldMesh c.kind J).coordinateEmbedInto c.kind.modelRegion (by
      rw [synchronizedPatchOldMesh_support]
      exact hmodel) x)).1

/-- Transport the fixed-patch member of a synchronized weld by the same chart. -/
noncomputable def synchronizedPatchNewSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) :
    GeometricRealization (synchronizedPatchNewMesh c.kind J).Vertex
      (synchronizedPatchNewMesh c.kind J).triangles → S :=
  fun x ↦ (c.chart.symm
    ((synchronizedPatchNewMesh c.kind J).coordinateEmbedInto c.kind.modelRegion (by
      rw [synchronizedPatchNewMesh_support]
      exact c.kind.patchComplex_support_subset_modelRegion) x)).1

theorem isEmbedding_synchronizedPatchOldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (synchronizedPatchOldSurfaceEmbed c J hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((synchronizedPatchOldMesh c.kind J).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchOldMesh_support]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (synchronizedPatchOldMesh c.kind J).coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchOldMesh_support]
          exact hmodel)) = synchronizedPatchOldSurfaceEmbed c J hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_synchronizedPatchNewSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) :
    _root_.Topology.IsEmbedding (synchronizedPatchNewSurfaceEmbed c J) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((synchronizedPatchNewMesh c.kind J).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchNewMesh_support]
          exact c.kind.patchComplex_support_subset_modelRegion)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (synchronizedPatchNewMesh c.kind J).coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchNewMesh_support]
          exact c.kind.patchComplex_support_subset_modelRegion)) =
      synchronizedPatchNewSurfaceEmbed c J := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem synchronizedPatchSurfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (x : GeometricRealization (synchronizedPatchOldMesh c.kind J).Vertex
      (synchronizedPatchOldMesh c.kind J).triangles)
    (y : GeometricRealization (synchronizedPatchNewMesh c.kind J).Vertex
      (synchronizedPatchNewMesh c.kind J).triangles) :
    synchronizedPatchOldSurfaceEmbed c J hmodel x =
        synchronizedPatchNewSurfaceEmbed c J y ↔
      (x : (synchronizedPatchOldMesh c.kind J).Vertex → ℝ) =
        (y : (synchronizedPatchNewMesh c.kind J).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold synchronizedPatchOldSurfaceEmbed synchronizedPatchNewSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (synchronizedPatchMeshes_coordinateEmbed_eq_iff c.kind J x y).mp hplane
  · intro hxy
    have hplane :=
      (synchronizedPatchMeshes_coordinateEmbed_eq_iff c.kind J x y).mpr hxy
    unfold synchronizedPatchOldSurfaceEmbed synchronizedPatchNewSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

/-- Generic finite synchronized weld for a polygonal old-side family and the fixed chart patch. -/
theorem exists_synchronizedPatch_local_weld
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) := by
  refine ⟨(synchronizedPatchOldMesh c.kind J).Vertex, inferInstance, inferInstance,
    (synchronizedPatchOldMesh c.kind J).triangles,
    (synchronizedPatchNewMesh c.kind J).triangles,
    synchronizedPatchOldSurfaceEmbed c J hmodel,
    synchronizedPatchNewSurfaceEmbed c J,
    synchronizedPatchMeshes_triangle_card c.kind J,
    isEmbedding_synchronizedPatchOldSurfaceEmbed c J hmodel,
    isEmbedding_synchronizedPatchNewSurfaceEmbed c J, ?_, ?_,
    synchronizedPatchMeshes_surface_edge_valence c.kind J⟩
  · intro x y hxy
    exact (synchronizedPatchSurfaceEmbed_eq_iff c J hmodel x y).mpr hxy
  · intro x y hxy
    exact (synchronizedPatchSurfaceEmbed_eq_iff c J hmodel x y).mp hxy

end SynchronizedPatch

/-! ## A synchronized weld against an arbitrary finite target mesh -/

namespace SynchronizedTarget

variable {ι : Type*} [Fintype ι]

/-- The old polygonal member of the common arrangement with an arbitrary finite target mesh. -/
noncomputable def oldMesh (J : ι → PolygonalCircle) (N : TriangleMesh) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J N (fun _ ↦ True)

/-- The prescribed finite target member of the same common arrangement. -/
noncomputable def newMesh (J : ι → PolygonalCircle) (N : TriangleMesh) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh J N

theorem oldMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh) :
    (oldMesh J N).toPlaneComplex.support = PolygonalFamily.closedRegion J := by
  simpa [oldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support J N (fun _ ↦ True))

theorem newMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support) :
    (newMesh J N).toPlaneComplex.support = N.toPlaneComplex.support :=
  PolygonalFamily.targetSynchronizedMesh_support J N hN

theorem meshes_triangle_card (J : ι → PolygonalCircle) (N : TriangleMesh) :
    ∀ t ∈ (oldMesh J N).triangles ∪ (newMesh J N).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (oldMesh J N).card_triangle t htOld
  · exact (newMesh J N).card_triangle t htNew

theorem meshes_surface_edge_valence (J : ι → PolygonalCircle) (N : TriangleMesh) :
    ∀ e ∈ ((oldMesh J N).triangles ∪
        (newMesh J N).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((oldMesh J N).triangles ∪
          (newMesh J N).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence J N
    (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- The two restrictions use the same ambient arrangement vertices, so equality in the plane
is exactly equality of their zero-extended barycentric coordinate functions. -/
theorem meshes_coordinateEmbed_eq_iff (J : ι → PolygonalCircle) (N : TriangleMesh)
    (x : GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles)
    (y : GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles) :
    (oldMesh J N).coordinateEmbed x = (newMesh J N).coordinateEmbed y ↔
      (x : (oldMesh J N).Vertex → ℝ) =
        (y : (newMesh J N).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement J N
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem J N
        (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem J N).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- Transport the selected polygonal member of an arbitrary synchronized weld to the surface. -/
noncomputable def oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles → S :=
  fun x ↦ (c.chart.symm
    ((oldMesh J N).coordinateEmbedInto c.kind.modelRegion (by
      rw [oldMesh_support]
      exact hmodel) x)).1

/-- Transport the prescribed target member of an arbitrary synchronized weld to the surface. -/
noncomputable def newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles → S :=
  fun x ↦ (c.chart.symm
    ((newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
      rw [newMesh_support J N harr]
      exact hmodel) x)).1

theorem isEmbedding_oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (oldSurfaceEmbed c J N hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((oldMesh J N).isEmbedding_coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (oldMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)) = oldSurfaceEmbed c J N hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (newSurfaceEmbed c J N harr hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((newMesh J N).isEmbedding_coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel)) = newSurfaceEmbed c J N harr hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- The target surface embedding has exactly the chart image of the prescribed mesh support. -/
theorem range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Set.range (newSurfaceEmbed c J N harr hmodel) =
      Subtype.val '' (c.chart.symm ''
        {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let p : c.kind.modelRegion :=
      (newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel) x
    refine ⟨c.chart.symm p, ?_, rfl⟩
    refine ⟨p, ?_, rfl⟩
    change (newMesh J N).coordinateEmbed x ∈ N.toPlaneComplex.support
    rw [← newMesh_support J N harr, ← (newMesh J N).range_coordinateEmbed]
    exact Set.mem_range_self x
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    have hpNew : (p : Plane) ∈ (newMesh J N).toPlaneComplex.support := by
      rw [newMesh_support J N harr]
      exact hp
    rw [← (newMesh J N).range_coordinateEmbed] at hpNew
    obtain ⟨x, hx⟩ := hpNew
    refine ⟨x, ?_⟩
    unfold newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hx

/-- Relative interior of the target mesh in the chart model maps to ambient interior in the
surface.  For half-disk charts this includes points on the model boundary line. -/
theorem modelInterior_subset_interior_range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Subtype.val '' (c.chart.symm ''
        interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support}) ⊆
      interior (Set.range (newSurfaceEmbed c J N harr hmodel)) := by
  let P : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ N.toPlaneComplex.support}
  let O : Set S := Subtype.val '' interior (c.chart.symm '' P)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆ Set.range (newSurfaceEmbed c J N harr hmodel) := by
    rw [range_newSurfaceEmbed c J N harr hmodel]
    exact Set.image_mono interior_subset
  rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
  apply interior_maximal hOsub hOopen
  have hzInterior :
      c.chart.symm p ∈ interior (c.chart.symm '' P) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hp, rfl⟩
  exact ⟨c.chart.symm p, hzInterior, rfl⟩

theorem surfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion)
    (x : GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles)
    (y : GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles) :
    oldSurfaceEmbed c J N hold x = newSurfaceEmbed c J N harr hnew y ↔
      (x : (oldMesh J N).Vertex → ℝ) =
        (y : (newMesh J N).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold oldSurfaceEmbed newSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (meshes_coordinateEmbed_eq_iff J N x y).mp hplane
  · intro hxy
    have hplane := (meshes_coordinateEmbed_eq_iff J N x y).mpr hxy
    unfold oldSurfaceEmbed newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

/-- Generic finite synchronized weld for a polygonal old-side family and any prescribed finite
target mesh lying in the chart model. -/
theorem exists_local_weld
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) := by
  refine ⟨(oldMesh J N).Vertex, inferInstance, inferInstance,
    (oldMesh J N).triangles, (newMesh J N).triangles,
    oldSurfaceEmbed c J N hold, newSurfaceEmbed c J N harr hnew,
    meshes_triangle_card J N, isEmbedding_oldSurfaceEmbed c J N hold,
    isEmbedding_newSurfaceEmbed c J N harr hnew, ?_, ?_,
    meshes_surface_edge_valence J N⟩
  · intro x y hxy
    exact (surfaceEmbed_eq_iff c J N harr hold hnew x y).mpr hxy
  · intro x y hxy
    exact (surfaceEmbed_eq_iff c J N harr hold hnew x y).mp hxy

end SynchronizedTarget

/-! ## A synchronized weld retaining additional certificate lines -/

namespace RelativeSynchronizedTarget

variable {ι : Type*} [Fintype ι]

/-- The selected polygonal side of the common arrangement after finitely many additional
certificate cuts. -/
noncomputable def oldMesh (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  PolygonalFamily.selectedRelativeSynchronizedMesh J N lines (fun _ ↦ True)

/-- The target side of the same additionally cut arrangement. -/
noncomputable def newMesh (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  PolygonalFamily.targetRelativeSynchronizedMesh J N lines

theorem oldMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (oldMesh J N lines).toPlaneComplex.support =
      PolygonalFamily.closedRegion J := by
  simpa [oldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedRelativeSynchronizedMesh_support
      J N lines (fun _ ↦ True))

theorem newMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support) :
    (newMesh J N lines).toPlaneComplex.support = N.toPlaneComplex.support :=
  PolygonalFamily.targetRelativeSynchronizedMesh_support J N lines hN

theorem meshes_triangle_card (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    ∀ t ∈ (oldMesh J N lines).triangles ∪ (newMesh J N lines).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (oldMesh J N lines).card_triangle t htOld
  · exact (newMesh J N lines).card_triangle t htNew

theorem meshes_surface_edge_valence
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    ∀ e ∈ ((oldMesh J N lines).triangles ∪
        (newMesh J N lines).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((oldMesh J N lines).triangles ∪
          (newMesh J N lines).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.relativeSynchronizedMeshes_joint_edge_valence
    J N lines (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- Both relative members retain the vertex type of their one ambient arrangement, so planar
equality is precisely equality of zero-extended barycentric coordinates. -/
theorem meshes_coordinateEmbed_eq_iff
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (x : GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles)
    (y : GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles) :
    (oldMesh J N lines).coordinateEmbed x =
        (newMesh J N lines).coordinateEmbed y ↔
      (x : (oldMesh J N lines).Vertex → ℝ) =
        (y : (newMesh J N lines).Vertex → ℝ) := by
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact
        (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
          J N lines (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact
        (PolygonalFamily.targetRelativeSynchronizedMesh_triangle_mem
          J N lines).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

noncomputable def oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles → S :=
  fun x ↦ (c.chart.symm
    ((oldMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
      rw [oldMesh_support]
      exact hmodel) x)).1

noncomputable def newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles → S :=
  fun x ↦ (c.chart.symm
    ((newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
      rw [newMesh_support J N lines harr]
      exact hmodel) x)).1

theorem isEmbedding_oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (oldSurfaceEmbed c J N lines hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((oldMesh J N lines).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [oldMesh_support]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (oldMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)) = oldSurfaceEmbed c J N lines hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding
      (newSurfaceEmbed c J N lines harr hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((newMesh J N lines).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [newMesh_support J N lines harr]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N lines harr]
        exact hmodel)) = newSurfaceEmbed c J N lines harr hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Set.range (newSurfaceEmbed c J N lines harr hmodel) =
      Subtype.val '' (c.chart.symm ''
        {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let p : c.kind.modelRegion :=
      (newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N lines harr]
        exact hmodel) x
    refine ⟨c.chart.symm p, ?_, rfl⟩
    refine ⟨p, ?_, rfl⟩
    change (newMesh J N lines).coordinateEmbed x ∈
      N.toPlaneComplex.support
    rw [← newMesh_support J N lines harr,
      ← (newMesh J N lines).range_coordinateEmbed]
    exact Set.mem_range_self x
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    have hpNew : (p : Plane) ∈
        (newMesh J N lines).toPlaneComplex.support := by
      rw [newMesh_support J N lines harr]
      exact hp
    rw [← (newMesh J N lines).range_coordinateEmbed] at hpNew
    obtain ⟨x, hx⟩ := hpNew
    refine ⟨x, ?_⟩
    unfold newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hx

theorem modelInterior_subset_interior_range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Subtype.val '' (c.chart.symm ''
        interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support}) ⊆
      interior (Set.range
        (newSurfaceEmbed c J N lines harr hmodel)) := by
  let P : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ N.toPlaneComplex.support}
  let O : Set S := Subtype.val '' interior (c.chart.symm '' P)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆
      Set.range (newSurfaceEmbed c J N lines harr hmodel) := by
    rw [range_newSurfaceEmbed c J N lines harr hmodel]
    exact Set.image_mono interior_subset
  rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
  apply interior_maximal hOsub hOopen
  have hzInterior :
      c.chart.symm p ∈ interior (c.chart.symm '' P) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hp, rfl⟩
  exact ⟨c.chart.symm p, hzInterior, rfl⟩

theorem surfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion)
    (x : GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles)
    (y : GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles) :
    oldSurfaceEmbed c J N lines hold x =
        newSurfaceEmbed c J N lines harr hnew y ↔
      (x : (oldMesh J N lines).Vertex → ℝ) =
        (y : (newMesh J N lines).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold oldSurfaceEmbed newSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (meshes_coordinateEmbed_eq_iff J N lines x y).mp hplane
  · intro hxy
    have hplane :=
      (meshes_coordinateEmbed_eq_iff J N lines x y).mpr hxy
    unfold oldSurfaceEmbed newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

end RelativeSynchronizedTarget

namespace PolygonalReplacementSourceAtlas

/-- The polygonal family obtained by closing the faces meeting an arbitrary compact coordinate
set under their whole adaptive source tiles. -/
def tileFacePolygonMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    A.TileFacesMeeting C hC → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The retained finite PL filling certificate for one face in a compactly selected
whole-tile family. -/
noncomputable def tileFaceMeetingCertificate
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : A.TileFacesMeeting C hC) :
    FinitePLHomeomorphBetween (Q.faceFillingMap f.1)
      LocallyFiniteTriangleComplex.standardFaceRegion
      (A.tileFacePolygonMeeting C hC f).closedRegion :=
  Classical.choice (Q.faceCertificate f.1)

/-- Pull the synchronized mesh of one compactly selected polygon back to its standard source
triangle.  The common target refinement includes both the synchronized chart mesh and the
retained PL certificate, so the certified inverse is affine on every resulting source piece. -/
noncomputable def tileFaceMeetingPullback
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (f : A.TileFacesMeeting C hC) :
    (A.tileFaceMeetingCertificate C hC f).PullbackSubdivision
      (SynchronizedPatch.singlePolygonMesh
        (A.tileFacePolygonMeeting C hC) N f).toPlaneComplex :=
  (A.tileFaceMeetingCertificate C hC f).pullbackSubdivision _
    (SynchronizedPatch.singlePolygonMesh
      (A.tileFacePolygonMeeting C hC) N f).toPlaneComplex_isPure2
    (SynchronizedPatch.singlePolygonMesh_support
      (A.tileFacePolygonMeeting C hC) N f)

/-- All target-side coordinate lines required by the retained PL certificates of the finite
selected face family.  Cutting the synchronized arrangement by this one finite list makes every
selected chamber subordinate to every certificate whose polygon contains its interior. -/
noncomputable def tileFaceMeetingCertificateLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (A.TileFacesMeeting C hC)).toList.flatMap fun f ↦
    ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines

theorem tileFaceMeetingPullback_coordinateLine_mem
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (f : A.TileFacesMeeting C hC)
    {a : Plane →ᵃ[ℝ] ℝ}
    (ha : a ∈
      ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines) :
    a ∈ A.tileFaceMeetingCertificateLines C hC N := by
  rw [tileFaceMeetingCertificateLines, List.mem_flatMap]
  exact ⟨f, by simp, ha⟩

/-- The retained certificate lines together with any additional finite conforming cuts. -/
noncomputable def tileFaceMeetingLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  A.tileFaceMeetingCertificateLines C hC N ++ extraLines

theorem tileFaceMeetingPullback_coordinateLine_mem_lines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (f : A.TileFacesMeeting C hC)
    {a : Plane →ᵃ[ℝ] ℝ}
    (ha : a ∈
      ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines) :
    a ∈ A.tileFaceMeetingLines C hC N extraLines := by
  exact List.mem_append_left _
    (A.tileFaceMeetingPullback_coordinateLine_mem C hC N f ha)

/-- Two transverse coordinate cuts through each point in a finite family. -/
noncomputable def coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset α).toList.flatMap fun a ↦
    [BrokenLineData.verticalLine (p a),
      BrokenLineData.horizontalLine (p a)]

theorem verticalLine_mem_coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) (a : α) :
    BrokenLineData.verticalLine (p a) ∈ coordinateAnchorLines p := by
  classical
  rw [coordinateAnchorLines, List.mem_flatMap]
  exact ⟨a, by simp, by simp⟩

theorem horizontalLine_mem_coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) (a : α) :
    BrokenLineData.horizontalLine (p a) ∈ coordinateAnchorLines p := by
  classical
  rw [coordinateAnchorLines, List.mem_flatMap]
  exact ⟨a, by simp, by simp⟩

/-- The certificate-cut synchronized old mesh over the finite selected source family. -/
noncomputable def tileFacesMeetingRelativeOldMesh
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  RelativeSynchronizedTarget.oldMesh
    (A.tileFacePolygonMeeting C hC) N
    (A.tileFaceMeetingLines C hC N extraLines)

/-- The target member of the same certificate-cut synchronized arrangement. -/
noncomputable def tileFacesMeetingRelativeNewMesh
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  RelativeSynchronizedTarget.newMesh
    (A.tileFacePolygonMeeting C hC) N
    (A.tileFaceMeetingLines C hC N extraLines)

theorem tileFacesMeetingRelativeOldMesh_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).toPlaneComplex.support =
      PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) :=
  RelativeSynchronizedTarget.oldMesh_support _ _ _

theorem tileFacesMeetingRelativeNewMesh_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (A.tileFacePolygonMeeting C hC)).toPlaneComplex.support) :
    (A.tileFacesMeetingRelativeNewMesh C hC N extraLines).toPlaneComplex.support =
      N.toPlaneComplex.support :=
  RelativeSynchronizedTarget.newMesh_support _ _ _ hN

/-- A relative synchronized chamber lying in one selected polygon is contained in a maximal
target triangle of that face's retained pullback certificate.  This is the precise payoff of
putting every certificate coordinate line into the one common arrangement. -/
theorem exists_pullbackTargetTriangle_of_relativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (f : A.TileFacesMeeting C hC)
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈ (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (htf : interior
        ((PolygonalFamily.relativeSynchronizedArrangement
          (A.tileFacePolygonMeeting C hC) N
          (A.tileFaceMeetingLines C hC N extraLines)).triangleCarrier t) ⊆
      (A.tileFacePolygonMeeting C hC f).interiorRegion) :
    ∃ u ∈
        ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).triangles,
      (PolygonalFamily.relativeSynchronizedArrangement
          (A.tileFacePolygonMeeting C hC) N
          (A.tileFaceMeetingLines C hC N extraLines)).triangleCarrier t ⊆
        ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).triangleCarrier u := by
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let P := A.tileFaceMeetingPullback C hC N f
  let M := P.target.toTriangleMesh
  have htR : t ∈ R.triangles := by
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp ht |>.1
  let T : R.Triangle := ⟨t, htR⟩
  have hlines :
      ∀ a ∈ M.coordinateLines, a ∈ N.coordinateLines ++ lines := by
    intro a ha
    apply List.mem_append_right
    exact A.tileFaceMeetingPullback_coordinateLine_mem_lines
      C hC N extraLines f ha
  have hhit :
      (interior (R.triangleCarrier t) ∩
        M.toPlaneComplex.support).Nonempty := by
    obtain ⟨x, hx⟩ := R.interior_triangleCarrier_nonempty T
    refine ⟨x, hx, ?_⟩
    change x ∈ M.toPlaneComplex.support
    rw [show M.toPlaneComplex.support = P.target.support by
      exact P.target.toTriangleMesh_support P.target_pure, P.target_support]
    rw [(A.tileFacePolygonMeeting C hC f).closedRegion_eq_union]
    exact Or.inl (htf hx)
  obtain ⟨W, hTW⟩ :=
    TriangleMesh.exists_target_triangle_of_refineByLines_of_interior_inter_support
      (PolygonalFamily.arrangementMesh J) M
      (N.coordinateLines ++ lines) hlines T hhit
  exact ⟨W.1, W.2, hTW⟩

/-- The compactly selected polygonal union remains in the coordinate region of the
replacement presentation. -/
theorem tileFacePolygonMeeting_closedRegion_subset_region
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) ⊆ V := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  exact Q.faceClosedRegion_subset f.1 hxf

/-- The same polygonal union, lifted to the coordinate-region subtype, lies in the support of
the global polygonal replacement complex. -/
theorem tileFacePolygonMeeting_subset_complex_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    {x : V | x.1 ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)} ⊆
      Q.complex.support := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨f.1, ?_⟩
  rw [Q.faceCarrier_eq f.1]
  exact hxf

/-- The coordinate union of a compactly selected tile family is exactly the image of its
common-level source subcomplex. -/
theorem sourceTileFacesMeeting_eq_coordinatePreimage
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) =
      {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1.1 ∈
          PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxU, hxQ⟩ := hxFace
    refine ⟨hxU, Set.mem_iUnion.mpr ⟨f, ?_⟩⟩
    rw [Q.faceCarrier_eq f.1] at hxQ
    simpa [tileFacePolygonMeeting] using hxQ
  · rintro x ⟨hxU, hxFamily⟩
    obtain ⟨f, hxPolygon⟩ := Set.mem_iUnion.mp hxFamily
    apply Set.mem_iUnion.mpr
    refine ⟨f, hxU, ?_⟩
    rw [Q.faceCarrier_eq f.1]
    exact hxPolygon

/-- The certificate-cut synchronized old mesh, regarded as a subspace of the global
replacement support. -/
noncomputable def tileFacesMeetingRelativeOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    GeometricRealization
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles →
      Q.complex.support :=
  fun x => by
    let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
    let p : Plane := M.coordinateEmbed x
    have hpClosed :
        p ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
        ← M.range_coordinateEmbed]
      exact Set.mem_range_self x
    let pV : V :=
      ⟨p, A.tileFacePolygonMeeting_closedRegion_subset_region C hC hpClosed⟩
    exact ⟨pV,
      A.tileFacePolygonMeeting_subset_complex_support C hC hpClosed⟩

theorem isEmbedding_tileFacesMeetingRelativeOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  have hclosed (x : GeometricRealization M.Vertex M.triangles) :
      M.coordinateEmbed x ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
    rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
      ← M.range_coordinateEmbed]
    exact Set.mem_range_self x
  let fV : GeometricRealization M.Vertex M.triangles → V :=
    Set.codRestrict M.coordinateEmbed V fun x =>
      A.tileFacePolygonMeeting_closedRegion_subset_region C hC (hclosed x)
  have hfV : _root_.Topology.IsEmbedding fV :=
    M.isEmbedding_coordinateEmbed.codRestrict V _
  have hfQ : _root_.Topology.IsEmbedding
      (Set.codRestrict fV Q.complex.support fun x =>
        A.tileFacePolygonMeeting_subset_complex_support C hC (hclosed x)) :=
    hfV.codRestrict Q.complex.support _
  convert hfQ using 1
  funext x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Pull the certificate-cut old coordinate triangulation back through the retained source
homeomorphism. -/
noncomputable def tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    GeometricRealization
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles →
      K.realization :=
  Subtype.val ∘ Q.sourceHomeomorph.symm ∘
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines

theorem isEmbedding_tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (Q.sourceHomeomorph.symm.isEmbedding.comp
      (A.isEmbedding_tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines))

/-- Changing only the finite line refinement does not change the source point represented by
one fixed planar coordinate. -/
theorem tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    {extraLines₁ extraLines₂ : List (Plane →ᵃ[ℝ] ℝ)}
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).triangles)
    (y : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).triangles)
    (hxy :
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).coordinateEmbed x =
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).coordinateEmbed y) :
    A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines₁ x =
      A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines₂ y := by
  change
    (Q.sourceHomeomorph.symm
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines₁ x)).1 =
    (Q.sourceHomeomorph.symm
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines₂ y)).1
  apply congrArg Subtype.val
  apply congrArg Q.sourceHomeomorph.symm
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- The intrinsic finite complex underlying the certificate-cut selected source mesh. -/
noncomputable def tileFacesMeetingRelativeSourceComplex
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    IntrinsicTwoComplex := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact
    { Vertex := M.Vertex
      faces := M.triangles
      faces_card := M.card_triangle }

@[simp] theorem tileFacesMeetingRelativeSourceComplex_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (A.tileFacesMeetingRelativeSourceComplex C hC N extraLines).faces =
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles :=
  rfl

/-- The original intrinsic point represented by one used vertex of the certificate-cut local
source mesh. -/
noncomputable def tileFacesMeetingRelativeSourceVertexPoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    K.realization :=
  A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
    ((A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).vertexPoint v)

/-- The same local source vertex, retaining its proof of membership in the replacement
domain. -/
noncomputable def tileFacesMeetingRelativeSourceVertexPointInOpen
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) : U :=
  Q.sourceHomeomorph.symm
    (A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines
      ((A.tileFacesMeetingRelativeSourceComplex
        C hC N extraLines).vertexPoint v))

@[simp] theorem tileFacesMeetingRelativeSourceVertexPointInOpen_val
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    (A.tileFacesMeetingRelativeSourceVertexPointInOpen
      C hC N extraLines v).1 =
      A.tileFacesMeetingRelativeSourceVertexPoint C hC N extraLines v :=
  rfl

/-- In replacement coordinates, a used local source vertex is its literal plane-mesh
vertex. -/
theorem sourceHomeomorph_relativeSourceVertexPointInOpen
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    (Q.sourceHomeomorph
      (A.tileFacesMeetingRelativeSourceVertexPointInOpen
        C hC N extraLines v)).1.1 =
      (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).position v.1 := by
  classical
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  change {w : M.Vertex // ∃ t ∈ M.triangles, w ∈ t} at v
  unfold tileFacesMeetingRelativeSourceVertexPointInOpen
  rw [Q.sourceHomeomorph.apply_symm_apply]
  change
    M.toPlaneComplex.baryEval (Pi.single v.1 1) = M.position v.1
  unfold PlaneComplex.baryEval
  change (∑ w : M.Vertex, Pi.single v.1 1 w • M.position w) =
    M.position v.1
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

theorem injective_tileFacesMeetingRelativeSourceVertexPoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Function.Injective
      (A.tileFacesMeetingRelativeSourceVertexPoint C hC N extraLines) :=
  (A.isEmbedding_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).injective.comp
    (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).injective_vertexPoint

/-- The certificate cuts change only the triangulation, not the selected whole-tile source
support. -/
theorem range_tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Set.range (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rw [A.sourceTileFacesMeeting_eq_coordinatePreimage C hC]
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    let q : Q.complex.support :=
      A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines z
    refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
    have hqClosed :
        q.1.1 ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      change M.coordinateEmbed z ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)
      rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
        ← M.range_coordinateEmbed]
      exact Set.mem_range_self z
    have harg :
        (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines z,
            (Q.sourceHomeomorph.symm q).2⟩ : U) =
          Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [harg, Q.sourceHomeomorph.apply_symm_apply]
    exact hqClosed
  · rintro x ⟨hxU, hxClosed⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqM : q.1.1 ∈ M.toPlaneComplex.support := by
      rw [A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines]
      exact hxClosed
    rw [← M.range_coordinateEmbed] at hqM
    obtain ⟨z, hz⟩ := hqM
    refine ⟨z, ?_⟩
    change
      (Q.sourceHomeomorph.symm
        (A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z)).1 = x
    have hsupportEq :
        A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    rw [hsupportEq]
    exact congrArg Subtype.val
      (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

theorem range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Set.range (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 :=
  (A.range_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).trans
    (A.sourceTileFacesMeeting_eq_levelFaces C hC)

/-- On every certificate-cut synchronized triangle, the pulled-back source embedding is one
affine function in the original intrinsic barycentric coordinates. -/
theorem tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles) :
    ∃ a :
        ((A.tileFacesMeetingRelativeOldMesh
          C hC N extraLines).Vertex → ℝ) →ᵃ[ℝ]
          (K.Vertex → ℝ),
      ∀ x : GeometricRealization
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles,
        (∀ v ∉ t, x.1 v = 0) →
          (A.tileFacesMeetingRelativeSourceEmbed
            C hC N extraLines x).1 = a x.1 := by
  classical
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨htR, f, -, htf⟩ :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J N lines (fun _ ↦ True)).mp ht
  let P := A.tileFaceMeetingPullback C hC N f
  obtain ⟨u, hu, htu⟩ :=
    A.exists_pullbackTargetTriangle_of_relativeOldTriangle
      C hC N extraLines f ht htf
  have huSimplex : u ∈ P.target.simplexes :=
    P.target.mem_simplexes_of_mem_cells hu
  obtain ⟨ainv, hainv⟩ := P.inverseAffine u huSimplex
  obtain ⟨b, hb⟩ := A.sourceFaceStandardAffine f.1
  refine
    ⟨b.comp (ainv.comp M.toPlaneComplex.baryEvalAffine), ?_⟩
  intro x hx
  let p : Plane := M.coordinateEmbed x
  have hpCarrierM : p ∈ M.toPlaneComplex.cellCarrier t := by
    apply M.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  have hpCarrierR : p ∈ R.triangleCarrier t := hpCarrierM
  have hpTarget : p ∈ P.target.cellCarrier u :=
    htu hpCarrierR
  have hpPolygon : p ∈ (J f).closedRegion := by
    let T : R.Triangle := ⟨t, htR⟩
    have hpClosure : p ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hpCarrierR
    simpa only [PolygonalCircle.closedRegion] using
      closure_mono htf hpClosure
  have hpInv :
      (A.tileFaceMeetingCertificate C hC f).inverseOn p ∈
        LocallyFiniteTriangleComplex.standardFaceRegion :=
    (A.tileFaceMeetingCertificate C hC f).inverseOn_mem hpPolygon
  let z : standardTrianglePlaneComplex.support :=
    ⟨(A.tileFaceMeetingCertificate C hC f).inverseOn p, hpInv⟩
  let xf : Q.complex.ClosedFace f.1 :=
    (Q.complex.facePlaneHomeomorph f.1).symm z
  let q : Q.complex.support :=
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines x
  have hqFace :
      q =
        LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
          (K := Q.complex) f.1 xf := by
    apply Subtype.ext
    apply Subtype.ext
    change p = (Q.complex.faceMap f.1 xf).1
    rw [Q.faceMap_eq]
    change p = Q.faceFillingMap f.1
      ((Q.complex.facePlaneHomeomorph f.1) xf).1
    rw [(Q.complex.facePlaneHomeomorph f.1).apply_symm_apply z]
    exact
      ((A.tileFaceMeetingCertificate C hC f).apply_inverseOn hpPolygon).symm
  change (Q.sourceHomeomorph.symm q).1.1 =
    (b.comp (ainv.comp M.toPlaneComplex.baryEvalAffine)) x.1
  rw [hqFace, hb xf]
  have hzapply :
      ((Q.complex.facePlaneHomeomorph f.1) xf).1 = z.1 :=
    congrArg Subtype.val
      ((Q.complex.facePlaneHomeomorph f.1).apply_symm_apply z)
  rw [hzapply]
  simp only [AffineMap.comp_apply, PlaneComplex.baryEvalAffine_apply]
  change b z.1 = b (ainv p)
  apply congrArg b
  change
    (A.tileFaceMeetingCertificate C hC f).inverseOn p = ainv p
  exact hainv hpTarget

/-- Every relative source triangle lies in one original maximal face. -/
theorem exists_parentFace_of_relativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles) :
    ∃ u : K.Face,
      ∀ x : GeometricRealization
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles,
        (∀ v ∉ t, x.1 v = 0) →
          A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x ∈
            K.faceCarrier u.1 := by
  classical
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨htR, f, -, htf⟩ :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J N lines (fun _ ↦ True)).mp ht
  refine ⟨A.sourceFaceParent f.1, ?_⟩
  intro x hx
  let p : Plane := M.coordinateEmbed x
  have hpCarrierM : p ∈ M.toPlaneComplex.cellCarrier t := by
    apply M.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  have hpCarrierR : p ∈ R.triangleCarrier t := hpCarrierM
  have hpPolygon : p ∈ (J f).closedRegion := by
    let T : R.Triangle := ⟨t, htR⟩
    have hpClosure : p ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hpCarrierR
    simpa only [PolygonalCircle.closedRegion] using
      closure_mono htf hpClosure
  let q : Q.complex.support :=
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines x
  apply A.sourceFaceSet_subset_parent f.1
  refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
  have harg :
      (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x,
          (Q.sourceHomeomorph.symm q).2⟩ : U) =
        Q.sourceHomeomorph.symm q :=
    Subtype.ext rfl
  rw [harg, Q.sourceHomeomorph.apply_symm_apply]
  rw [Q.faceCarrier_eq f.1]
  exact hpPolygon

/-- A canonical original parent face for one triangle of the relative source mesh. -/
noncomputable def relativeOldTriangleParent
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) : K.Face :=
  Classical.choose
    (A.exists_parentFace_of_relativeOldTriangle
      C hC N extraLines t.2)

/-- The chosen parent contains the complete image of the relative source triangle. -/
theorem relativeOldTriangleParent_contains
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x ∈
      K.faceCarrier
        (A.relativeOldTriangleParent C hC N extraLines t).1 :=
  Classical.choose_spec
    (A.exists_parentFace_of_relativeOldTriangle
      C hC N extraLines t.2) x hx

/-- The canonical affine formula for the source embedding on one relative triangle. -/
noncomputable def relativeOldTriangleSourceAffine
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    ((A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  Classical.choose
    (A.tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
      C hC N extraLines t.2)

/-- The chosen source affine formula agrees with the source embedding on its triangle. -/
theorem relativeOldTriangleSourceAffine_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x).1 =
      A.relativeOldTriangleSourceAffine C hC N extraLines t x.1 :=
  Classical.choose_spec
    (A.tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
      C hC N extraLines t.2) x hx

/-- On one relative source triangle, the source map is the affine combination of its three
actual source-vertex images. -/
theorem relativeSourceFaceMap_eq_vertex_sum
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x).1 =
      ∑ v : t.1, x.1 v.1 •
        (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          ((A.tileFacesMeetingRelativeSourceComplex
            C hC N extraLines).vertexPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
  classical
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let L := A.tileFacesMeetingRelativeSourceComplex C hC N extraLines
  let a := A.relativeOldTriangleSourceAffine C hC N extraLines t
  let p : t.1 → (M.Vertex → ℝ) := fun v ↦ Pi.single v.1 1
  let w : t.1 → ℝ := fun v ↦ x.1 v.1
  have hsum : ∑ v : t.1, w v = 1 := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach t.1 (fun v ↦ x.1 v)]
    exact
      (Finset.sum_subset (Finset.subset_univ t.1)
        (fun v _ hv => hx v hv)).trans x.2.1.2
  have hcomb :
      (Finset.univ : Finset t.1).affineCombination ℝ p w = x.1 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p, w,
      Pi.single_apply]
    by_cases hzt : z ∈ t.1
    · let zt : t.1 := ⟨z, hzt⟩
      rw [Finset.sum_eq_single zt]
      · simp [zt]
      · intro b _ hb
        have hbval : b.1 ≠ z := by
          intro h
          apply hb
          exact Subtype.ext h
        simp [hbval, Ne.symm hbval]
      · simp
    · have hxz : x.1 z = 0 := hx z hzt
      rw [hxz]
      apply Finset.sum_eq_zero
      intro b _
      have hbval : z ≠ b.1 := fun h => hzt (h ▸ b.2)
      simp [hbval]
  have hmap :
      a x.1 =
        ∑ v : t.1, w v • a (p v) := by
    calc
      a x.1 =
          a ((Finset.univ : Finset t.1).affineCombination ℝ p w) :=
        congrArg a hcomb.symm
      _ =
          (Finset.univ : Finset t.1).affineCombination ℝ (a ∘ p) w :=
        (Finset.univ : Finset t.1).map_affineCombination p w hsum a
      _ = ∑ v : t.1, w v • a (p v) := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
        rfl
  rw [A.relativeOldTriangleSourceAffine_eq
    C hC N extraLines t x hx]
  rw [hmap]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (w v • ·)
  symm
  apply A.relativeOldTriangleSourceAffine_eq
    C hC N extraLines t
  intro z hz
  change Pi.single v.1 1 z = 0
  have hzv : z ≠ v.1 := fun h => hz (h ▸ v.2)
  simp [hzv]

/-- The same abstract triangle, viewed as a maximal triangle of the plane complex generated by
the relative mesh. -/
noncomputable def relativeOldTriangleAsPlaneTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    (((A.tileFacesMeetingRelativeOldMesh C hC N extraLines).toPlaneComplex
      ).toTriangleMesh).Triangle := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact ⟨t.1, by
    change t.1 ∈ M.toPlaneComplex.cells
    rw [M.toPlaneComplex_cells]
    exact t.2⟩

/-- A point of a relative old plane triangle, regarded as the corresponding point of its
barycentric realization. -/
noncomputable def relativeOldTrianglePoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact
    ⟨M.triangleCoords t p.1,
      ⟨M.triangleCoords_nonneg_of_mem t p.2,
        M.sum_triangleCoords t p.1⟩,
      t.1, t.2, M.triangleCoords_support t p.1⟩

@[simp] theorem relativeOldTrianglePoint_coordinateEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).coordinateEmbed
        (A.relativeOldTrianglePoint C hC N extraLines t p) = p.1 := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact M.baryEval_triangleCoords t p.1

theorem relativeOldTrianglePoint_val_eq_triangleCoords
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    (A.relativeOldTrianglePoint C hC N extraLines t p).1 =
      (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCoords t p.1 :=
  rfl

theorem relativeOldTrianglePoint_supported
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    ∀ v ∉ t.1,
      (A.relativeOldTrianglePoint C hC N extraLines t p).1 v = 0 := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  intro v hv
  rw [A.relativeOldTrianglePoint_val_eq_triangleCoords
    C hC N extraLines t p]
  exact M.triangleCoords_apply_of_notMem t hv p.1

/-- The source triangle written in the standard plane coordinates of its original parent
face. -/
noncomputable def relativeOldTriangleParentPlaneAffine
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) : Plane →ᵃ[ℝ] Plane :=
  (K.facePlaneForwardAffine
      (A.relativeOldTriangleParent C hC N extraLines t)).comp
    ((A.relativeOldTriangleSourceAffine C hC N extraLines t).comp
      ((A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCoords t))

theorem relativeOldTriangleParentPlaneAffine_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    A.relativeOldTriangleParentPlaneAffine C hC N extraLines t p.1 =
      (K.facePlaneHomeomorph
        (A.relativeOldTriangleParent C hC N extraLines t)
        ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
            (A.relativeOldTrianglePoint C hC N extraLines t p),
          A.relativeOldTriangleParent_contains C hC N extraLines t _
            (A.relativeOldTrianglePoint_supported
              C hC N extraLines t p)⟩).1 := by
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine]
  simp only [relativeOldTriangleParentPlaneAffine, AffineMap.comp_apply]
  apply congrArg
    (K.facePlaneForwardAffine
      (A.relativeOldTriangleParent C hC N extraLines t))
  calc
    (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        ((A.tileFacesMeetingRelativeOldMesh
          C hC N extraLines).triangleCoords t p.1) =
      (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        (A.relativeOldTrianglePoint C hC N extraLines t p).1 :=
      congrArg
        (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        (A.relativeOldTrianglePoint_val_eq_triangleCoords
          C hC N extraLines t p).symm
    _ = (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
        (A.relativeOldTrianglePoint C hC N extraLines t p)).1 :=
      (A.relativeOldTriangleSourceAffine_eq C hC N extraLines t _
        (A.relativeOldTrianglePoint_supported
          C hC N extraLines t p)).symm

/-- The parent-plane formula is locally injective on its source triangle. -/
theorem relativeOldTriangleParentPlaneAffine_injOn
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Set.InjOn
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t)
      ((A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1) := by
  intro p hp q hq hpq
  let pp : {z : Plane //
      z ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1} := ⟨p, hp⟩
  let qq : {z : Plane //
      z ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1} := ⟨q, hq⟩
  have hchart :
      K.facePlaneHomeomorph
          (A.relativeOldTriangleParent C hC N extraLines t)
          ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
              (A.relativeOldTrianglePoint C hC N extraLines t pp),
            A.relativeOldTriangleParent_contains C hC N extraLines t _
              (A.relativeOldTrianglePoint_supported
                C hC N extraLines t pp)⟩ =
        K.facePlaneHomeomorph
          (A.relativeOldTriangleParent C hC N extraLines t)
          ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
              (A.relativeOldTrianglePoint C hC N extraLines t qq),
            A.relativeOldTriangleParent_contains C hC N extraLines t _
              (A.relativeOldTrianglePoint_supported
                C hC N extraLines t qq)⟩ := by
    apply Subtype.ext
    rw [← A.relativeOldTriangleParentPlaneAffine_eq
        C hC N extraLines t pp,
      ← A.relativeOldTriangleParentPlaneAffine_eq
        C hC N extraLines t qq]
    exact hpq
  have hsource :
      A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          (A.relativeOldTrianglePoint C hC N extraLines t pp) =
        A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          (A.relativeOldTrianglePoint C hC N extraLines t qq) := by
    exact congrArg (fun z => z.1)
      ((K.facePlaneHomeomorph
        (A.relativeOldTriangleParent C hC N extraLines t)).injective hchart)
  have hpoint :
      A.relativeOldTrianglePoint C hC N extraLines t pp =
        A.relativeOldTrianglePoint C hC N extraLines t qq :=
    (A.isEmbedding_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).injective hsource
  calc
    p = (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).coordinateEmbed
          (A.relativeOldTrianglePoint C hC N extraLines t pp) :=
      (A.relativeOldTrianglePoint_coordinateEmbed
        C hC N extraLines t pp).symm
    _ = (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).coordinateEmbed
          (A.relativeOldTrianglePoint C hC N extraLines t qq) :=
      congrArg _ hpoint
    _ = q :=
      A.relativeOldTrianglePoint_coordinateEmbed
        C hC N extraLines t qq

/-- Consequently, the parent-plane formula is a global affine equivalence at the level of
functions. -/
theorem relativeOldTriangleParentPlaneAffine_injective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Function.Injective
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hcarrier :
      M.triangleCarrier t.1 = convexHull ℝ (Set.range p) := by
    unfold TriangleMesh.triangleCarrier
    rw [Set.range_comp, M.range_orderedVertex t]
  apply affineMap_injective_of_injOn_convexHull p
    (M.orderedVertex_affineIndependent t)
  rw [← hcarrier]
  exact A.relativeOldTriangleParentPlaneAffine_injOn
    C hC N extraLines t

theorem relativeOldTriangleParentPlaneAffine_surjective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Function.Surjective
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hcarrier :
      M.triangleCarrier t.1 = convexHull ℝ (Set.range p) := by
    unfold TriangleMesh.triangleCarrier
    rw [Set.range_comp, M.range_orderedVertex t]
  apply affineMap_surjective_of_injOn_convexHull p
    (M.orderedVertex_affineIndependent t)
  rw [← hcarrier]
  exact A.relativeOldTriangleParentPlaneAffine_injOn
    C hC N extraLines t

/-- A canonical original parent of one face at a fixed midpoint level. -/
noncomputable def levelFaceParent
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) : K.Face :=
  ⟨Classical.choose ((K.safeSubdivision n).subordinate s.1 s.2),
    (Classical.choose_spec
      ((K.safeSubdivision n).subordinate s.1 s.2)).1⟩

theorem levelFaceParent_contains
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (x : (K.safeSubdivision n).refined.realization)
    (hx : x ∈ (K.safeSubdivision n).refined.faceCarrier s.1) :
    (K.safeSubdivision n).homeo x ∈
      K.faceCarrier (levelFaceParent K s).1 :=
  (Classical.choose_spec
    ((K.safeSubdivision n).subordinate s.1 s.2)).2 x hx

/-- The canonical affine formula of the midpoint-subdivision homeomorphism on one level
face. -/
noncomputable def levelFaceSourceAffine
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    ((K.safeSubdivision n).refined.Vertex → ℝ) →ᵃ[ℝ]
      (K.Vertex → ℝ) :=
  Classical.choose ((K.safeSubdivision n).affineOnFace s.1 s.2)

theorem levelFaceSourceAffine_eq
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (x : (K.safeSubdivision n).refined.realization)
    (hx : x ∈ (K.safeSubdivision n).refined.faceCarrier s.1) :
    ((K.safeSubdivision n).homeo x).1 =
      levelFaceSourceAffine K s x.1 :=
  Classical.choose_spec
    ((K.safeSubdivision n).affineOnFace s.1 s.2) x hx

/-- A level face, transported to the standard plane chart of its original parent, is affine
in its own standard triangle coordinates. -/
noncomputable def levelFaceParentPlaneAffine
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Plane →ᵃ[ℝ] Plane :=
  (K.facePlaneForwardAffine (levelFaceParent K s)).comp
    ((levelFaceSourceAffine K s).comp
      ((K.safeSubdivision n).refined.facePlaneInverseAffine s))

theorem levelFaceParentPlaneAffine_eq
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (p : standardTrianglePlaneComplex.support) :
    levelFaceParentPlaneAffine K s p.1 =
      (K.facePlaneHomeomorph (levelFaceParent K s)
        ⟨(K.safeSubdivision n).homeo
            ((K.safeSubdivision n).refined.facePlaneHomeomorph s |>.symm p),
          levelFaceParent_contains K s _
            (((K.safeSubdivision n).refined.facePlaneHomeomorph s).symm p).2⟩).1 := by
  let R := K.safeSubdivision n
  let x : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm p
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine]
  simp only [levelFaceParentPlaneAffine, AffineMap.comp_apply]
  apply congrArg (K.facePlaneForwardAffine (levelFaceParent K s))
  calc
    levelFaceSourceAffine K s
        (R.refined.facePlaneInverseAffine s p.1) =
      levelFaceSourceAffine K s x.1.1 := by
        apply congrArg (levelFaceSourceAffine K s)
        exact (R.refined.facePlaneHomeomorph_symm_val s p).symm
    _ = (R.homeo x.1).1 :=
      (levelFaceSourceAffine_eq K s x.1 x.2).symm

/-- The parent-plane formula for a level face is injective on the standard closed triangle. -/
theorem levelFaceParentPlaneAffine_injOn
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Set.InjOn (levelFaceParentPlaneAffine K s)
      standardTrianglePlaneComplex.support := by
  intro p hp q hq hpq
  let pp : standardTrianglePlaneComplex.support := ⟨p, hp⟩
  let qq : standardTrianglePlaneComplex.support := ⟨q, hq⟩
  let R := K.safeSubdivision n
  let x : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm pp
  let y : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm qq
  have hchart :
      K.facePlaneHomeomorph (levelFaceParent K s)
          ⟨R.homeo x.1, levelFaceParent_contains K s x.1 x.2⟩ =
        K.facePlaneHomeomorph (levelFaceParent K s)
          ⟨R.homeo y.1, levelFaceParent_contains K s y.1 y.2⟩ := by
    apply Subtype.ext
    rw [← levelFaceParentPlaneAffine_eq K s pp,
      ← levelFaceParentPlaneAffine_eq K s qq]
    exact hpq
  have hhomeo : R.homeo x.1 = R.homeo y.1 := by
    exact congrArg (fun z => z.1)
      ((K.facePlaneHomeomorph (levelFaceParent K s)).injective hchart)
  have hxy : x = y := by
    apply Subtype.ext
    exact R.homeo.injective hhomeo
  calc
    p = ((R.refined.facePlaneHomeomorph s) x).1 := by
      change pp.1 = ((R.refined.facePlaneHomeomorph s)
        ((R.refined.facePlaneHomeomorph s).symm pp)).1
      exact congrArg Subtype.val
        ((R.refined.facePlaneHomeomorph s).apply_symm_apply pp).symm
    _ = ((R.refined.facePlaneHomeomorph s) y).1 :=
      congrArg (fun z => ((R.refined.facePlaneHomeomorph s) z).1) hxy
    _ = q := by
      change ((R.refined.facePlaneHomeomorph s)
        ((R.refined.facePlaneHomeomorph s).symm qq)).1 = qq.1
      exact congrArg Subtype.val
        ((R.refined.facePlaneHomeomorph s).apply_symm_apply qq)

theorem levelFaceParentPlaneAffine_injective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Function.Injective (levelFaceParentPlaneAffine K s) := by
  apply affineMap_injective_of_injOn_convexHull
    standardTriangleVertex standardTriangleVertex_affineIndependent
  rw [← standardTrianglePlaneComplex_support]
  exact levelFaceParentPlaneAffine_injOn K s

theorem levelFaceParentPlaneAffine_surjective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Function.Surjective (levelFaceParentPlaneAffine K s) := by
  apply affineMap_surjective_of_injOn_convexHull
    standardTriangleVertex standardTriangleVertex_affineIndependent
  rw [← standardTrianglePlaneComplex_support]
  exact levelFaceParentPlaneAffine_injOn K s

/-- Barycentric coordinate of a level face after transport to its original parent plane. -/
noncomputable def levelFaceParentCoord
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (affineBasisOfTriangle
    (levelFaceParentPlaneAffine K s ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent
      (levelFaceParentPlaneAffine K s) (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s))).coord k

@[simp] theorem levelFaceParentCoord_vertex
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k i : Fin 3) :
    levelFaceParentCoord K s k
      (levelFaceParentPlaneAffine K s (standardTriangleVertex i)) =
        if k = i then 1 else 0 := by
  exact AffineBasis.coord_apply _ _ _

theorem levelFaceParentCoord_surjective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) :
    Function.Surjective (levelFaceParentCoord K s k) := by
  simpa only [levelFaceParentCoord] using
    (affineBasisOfTriangle
      (levelFaceParentPlaneAffine K s ∘ standardTriangleVertex)
      (affineIndependent_comp_of_injOn_convexHull
        standardTriangleVertex standardTriangleVertex_affineIndependent
        (levelFaceParentPlaneAffine K s) (by
          rw [← standardTrianglePlaneComplex_support]
          exact levelFaceParentPlaneAffine_injOn K s))).surjective_coord k

theorem levelFaceParentCoord_nonneg
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) (p : standardTrianglePlaneComplex.support) :
    0 ≤ levelFaceParentCoord K s k
      (levelFaceParentPlaneAffine K s p.1) := by
  let F := levelFaceParentPlaneAffine K s
  let b := affineBasisOfTriangle
    (F ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent F (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s))
  have hp :
      F p.1 ∈ convexHull ℝ
        (Set.range (F ∘ standardTriangleVertex)) := by
    rw [Set.range_comp, ← F.image_convexHull,
      ← standardTrianglePlaneComplex_support]
    exact ⟨p.1, p.2, rfl⟩
  have hb : (fun i => b i) = F ∘ standardTriangleVertex := by
    funext i
    rfl
  have hp' : F p.1 ∈ convexHull ℝ (Set.range b) := by
    rw [show Set.range b =
        Set.range (F ∘ standardTriangleVertex) by
      exact congrArg Set.range hb]
    exact hp
  have hpk : 0 ≤ b.coord k (F p.1) := by
    rw [b.convexHull_eq_nonneg_coord] at hp'
    exact hp' k
  exact hpk

/-- A point in the relative interior of an original maximal face cannot also belong to a
distinct original maximal face.  The relative interior is detected in the canonical standard
plane chart. -/
theorem face_eq_of_mem_faceCarriers_of_facePlane_mem_interior
    (K : IntrinsicTwoComplex) (t u : K.Face) (x : K.realization)
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1)
    (hxint :
      (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
        interior standardTrianglePlaneComplex.support) :
    t = u := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro v hvt
    by_contra hvu
    have hxzero : x.1 v = 0 := hxu v hvu
    let p : standardTrianglePlaneComplex.support :=
      K.facePlaneHomeomorph t ⟨x, hxt⟩
    let i : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hvt⟩
    have hpint :
        p.1 ∈ interior
          (standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
            standardTriangleMeshFace.1) := by
      rw [show
          standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
              standardTriangleMeshFace.1 =
            standardTrianglePlaneComplex.support by
        exact standardTriangle_cellCarrier_univ]
      exact hxint
    have hcoordpos :
        0 <
          standardTrianglePlaneComplex.faceCoords
            standardTriangleMeshFace p.1 i := by
      rw [standardTrianglePlaneComplex.faceCoords_apply_of_mem
        standardTriangleMeshFace (Finset.mem_univ i)]
      rw [standardTrianglePlaneComplex.toTriangleMesh.interior_triangleCarrier
        standardTriangleMeshFace] at hpint
      exact hpint
        (standardTrianglePlaneComplex.toTriangleMesh.triangleEquiv
          standardTriangleMeshFace ⟨i, Finset.mem_univ i⟩)
    have hxcoord :
        x.1 v =
          standardTrianglePlaneComplex.faceCoords
            standardTriangleMeshFace p.1 i := by
      calc
        x.1 v =
            ((K.facePlaneHomeomorph t).symm p).1.1 v := by
              have h :=
                (K.facePlaneHomeomorph t).symm_apply_apply ⟨x, hxt⟩
              exact congrFun (congrArg (fun z => z.1.1) h.symm) v
        _ = K.facePlaneInverseAffine t p.1 v :=
          congrFun (K.facePlaneHomeomorph_symm_val t p) v
        _ =
            standardTrianglePlaneComplex.faceCoords
              standardTriangleMeshFace p.1 i := by
          simp only [IntrinsicTwoComplex.facePlaneInverseAffine, AffineMap.comp_apply,
            K.faceCoordExtensionAffine_apply_of_mem _ _ hvt]
          rfl
    linarith
  · rw [K.faces_card t.1 t.2, K.faces_card u.1 u.2]

/-- Pull every fixed-level face coordinate back through every relative source triangle whose
chosen original parent agrees.  Cutting by these finitely many affine lines makes the next
relative source mesh subordinate to the fixed-level triangulation. -/
noncomputable def relativeLevelAlignmentLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ)) (n : ℕ) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  let M := A.tileFacesMeetingRelativeOldMesh C hC N baseExtraLines
  (Finset.univ : Finset M.Triangle).toList.flatMap fun t =>
    (Finset.univ : Finset (K.LevelFace n)).toList.flatMap fun s =>
      if levelFaceParent K s =
          A.relativeOldTriangleParent C hC N baseExtraLines t then
        (Finset.univ : Finset (Fin 3)).toList.map fun k =>
          (levelFaceParentCoord K s k).comp
            (A.relativeOldTriangleParentPlaneAffine
              C hC N baseExtraLines t)
      else
        []

theorem relativeLevelAlignmentLine_mem
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ)) (n : ℕ)
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N baseExtraLines).Triangle)
    (s : K.LevelFace n)
    (hparent :
      levelFaceParent K s =
        A.relativeOldTriangleParent C hC N baseExtraLines t)
    (k : Fin 3) :
    (levelFaceParentCoord K s k).comp
        (A.relativeOldTriangleParentPlaneAffine
          C hC N baseExtraLines t) ∈
      A.relativeLevelAlignmentLines C hC N baseExtraLines n := by
  classical
  unfold relativeLevelAlignmentLines
  apply List.mem_flatMap.mpr
  refine ⟨t, Finset.mem_toList.mpr (Finset.mem_univ t), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), ?_⟩
  rw [if_pos hparent]
  apply List.mem_map.mpr
  exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), rfl⟩

theorem relativeLevelAlignmentLine_surjective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N baseExtraLines).Triangle)
    {n : ℕ} (s : K.LevelFace n) (k : Fin 3) :
    Function.Surjective
      ((levelFaceParentCoord K s k).comp
        (A.relativeOldTriangleParentPlaneAffine
          C hC N baseExtraLines t)) := by
  intro y
  obtain ⟨q, hq⟩ := levelFaceParentCoord_surjective K s k y
  obtain ⟨p, hp⟩ :=
    A.relativeOldTriangleParentPlaneAffine_surjective
      C hC N baseExtraLines t q
  exact ⟨p, by simp only [AffineMap.comp_apply, hp, hq]⟩

/-- The synchronized old coordinate mesh, regarded as a subspace of the global replacement
support. -/
noncomputable def tileFacesMeetingOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    GeometricRealization
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).Vertex
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).triangles →
      Q.complex.support :=
  fun x => by
    let p : Plane :=
      (SynchronizedTarget.oldMesh
        (A.tileFacePolygonMeeting C hC) N).coordinateEmbed x
    have hpClosed :
        p ∈ PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
      rw [← SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N,
        ← (SynchronizedTarget.oldMesh
          (A.tileFacePolygonMeeting C hC) N).range_coordinateEmbed]
      exact Set.mem_range_self x
    let pV : V :=
      ⟨p, A.tileFacePolygonMeeting_closedRegion_subset_region C hC hpClosed⟩
    exact ⟨pV,
      A.tileFacePolygonMeeting_subset_complex_support C hC hpClosed⟩

theorem isEmbedding_tileFacesMeetingOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingOldCoordinateSupport C hC N) := by
  let M := SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N
  have hclosed (x : GeometricRealization M.Vertex M.triangles) :
      M.coordinateEmbed x ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
    rw [← SynchronizedTarget.oldMesh_support
      (A.tileFacePolygonMeeting C hC) N, ← M.range_coordinateEmbed]
    exact Set.mem_range_self x
  let fV : GeometricRealization M.Vertex M.triangles → V :=
    Set.codRestrict M.coordinateEmbed V fun x =>
      A.tileFacePolygonMeeting_closedRegion_subset_region C hC (hclosed x)
  have hfV : _root_.Topology.IsEmbedding fV :=
    M.isEmbedding_coordinateEmbed.codRestrict V _
  have hfQ : _root_.Topology.IsEmbedding
      (Set.codRestrict fV Q.complex.support fun x =>
        A.tileFacePolygonMeeting_subset_complex_support C hC (hclosed x)) :=
    hfV.codRestrict Q.complex.support _
  convert hfQ using 1
  funext x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Pull the synchronized old coordinate triangulation back through the retained source
homeomorphism to the original finite intrinsic realization. -/
noncomputable def tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    GeometricRealization
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).Vertex
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).triangles →
      K.realization :=
  Subtype.val ∘ Q.sourceHomeomorph.symm ∘
    A.tileFacesMeetingOldCoordinateSupport C hC N

theorem isEmbedding_tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    _root_.Topology.IsEmbedding (A.tileFacesMeetingSourceEmbed C hC N) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (Q.sourceHomeomorph.symm.isEmbedding.comp
      (A.isEmbedding_tileFacesMeetingOldCoordinateSupport C hC N))

/-- The synchronized old mesh pulls back onto exactly the finite whole-tile source
subcomplex. -/
theorem range_tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    Set.range (A.tileFacesMeetingSourceEmbed C hC N) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rw [A.sourceTileFacesMeeting_eq_coordinatePreimage C hC]
  let M := SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    let q : Q.complex.support :=
      A.tileFacesMeetingOldCoordinateSupport C hC N z
    refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
    have hqClosed :
        q.1.1 ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      change M.coordinateEmbed z ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)
      rw [← SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N, ← M.range_coordinateEmbed]
      exact Set.mem_range_self z
    have harg :
        (⟨A.tileFacesMeetingSourceEmbed C hC N z,
            (Q.sourceHomeomorph.symm q).2⟩ : U) =
          Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [harg, Q.sourceHomeomorph.apply_symm_apply]
    exact hqClosed
  · rintro x ⟨hxU, hxClosed⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqM : q.1.1 ∈ M.toPlaneComplex.support := by
      rw [SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N]
      exact hxClosed
    rw [← M.range_coordinateEmbed] at hqM
    obtain ⟨z, hz⟩ := hqM
    refine ⟨z, ?_⟩
    change
      (Q.sourceHomeomorph.symm
        (A.tileFacesMeetingOldCoordinateSupport C hC N z)).1 = x
    have hsupportEq :
        A.tileFacesMeetingOldCoordinateSupport C hC N z = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    rw [hsupportEq]
    exact congrArg Subtype.val (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

/-- In intrinsic terms, the range is a literal subcomplex of one finite midpoint level. -/
theorem range_tileFacesMeetingSourceEmbed_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    Set.range (A.tileFacesMeetingSourceEmbed C hC N) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 :=
  (A.range_tileFacesMeetingSourceEmbed C hC N).trans
    (A.sourceTileFacesMeeting_eq_levelFaces C hC)

/-- Every polygon in a compactly selected tile family lies in the chart model whenever the
retained coordinate homeomorphism does. -/
theorem tileFacePolygonMeeting_closedRegion_subset_modelRegion
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) ⊆
      c.kind.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ V := Q.faceClosedRegion_subset f.1 hxf
  let z : V := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate c.kind g' hcoord hzSupport

/-- A compactly selected whole-tile family admits a synchronized local weld with any prescribed
finite target mesh in the same chart model. -/
theorem exists_tileFacesMeeting_local_weld
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1)
    (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (A.tileFacePolygonMeeting C hC)).toPlaneComplex.support)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (F₁ F₂ : Finset (Finset W))
      (e₁ : GeometricRealization W F₁ → S)
      (e₂ : GeometricRealization W F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization W F₁) (y : GeometricRealization W F₂),
        (x : W → ℝ) = (y : W → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization W F₁) (y : GeometricRealization W F₂),
        e₁ x = e₂ y → (x : W → ℝ) = (y : W → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) :=
  SynchronizedTarget.exists_local_weld c
    (A.tileFacePolygonMeeting C hC) N harr
    (A.tileFacePolygonMeeting_closedRegion_subset_modelRegion c C hC g' hcoord)
    hnew

/-- The polygonal family obtained by retaining every fan face in every adaptive tile touched by
the patch. -/
def patchTileFacePolygon
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    A.PatchTileFaces → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The retained finite PL certificate for one face of the tile-closed source family. -/
noncomputable def patchTileFaceCertificate
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : A.PatchTileFaces) :
    FinitePLHomeomorphBetween (Q.faceFillingMap f.1)
      LocallyFiniteTriangleComplex.standardFaceRegion
      (A.patchTileFacePolygon f).closedRegion :=
  Classical.choice (Q.faceCertificate f.1)

/-- Pull the synchronized mesh of one selected polygon back to its standard source triangle.
The target side is first commonly refined with the original Schoenflies certificate, so the
result carries every chart-patch intersection vertex. -/
noncomputable def patchTileFacePullback
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (N : TriangleMesh) (f : A.PatchTileFaces) :
    (A.patchTileFaceCertificate f).PullbackSubdivision
      (SynchronizedPatch.singlePolygonMesh A.patchTileFacePolygon N f).toPlaneComplex :=
  (A.patchTileFaceCertificate f).pullbackSubdivision _
    (SynchronizedPatch.singlePolygonMesh A.patchTileFacePolygon N f).toPlaneComplex_isPure2
    (SynchronizedPatch.singlePolygonMesh_support A.patchTileFacePolygon N f)

/-- The exact coordinate union of the tile-closed family is the image, under the retained source
homeomorphism, of its exact common-level source subcomplex. -/
theorem sourcePatchTileFaces_eq_coordinatePreimage
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) =
      {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1.1 ∈
          PolygonalFamily.closedRegion A.patchTileFacePolygon} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxU, hxQ⟩ := hxFace
    refine ⟨hxU, Set.mem_iUnion.mpr ⟨f, ?_⟩⟩
    rw [Q.faceCarrier_eq f.1] at hxQ
    simpa [patchTileFacePolygon] using hxQ
  · rintro x ⟨hxU, hxFamily⟩
    obtain ⟨f, hxPolygon⟩ := Set.mem_iUnion.mp hxFamily
    apply Set.mem_iUnion.mpr
    refine ⟨f, hxU, ?_⟩
    rw [Q.faceCarrier_eq f.1]
    exact hxPolygon

/-- Every polygon in the tile-closed family still lies in the chart model (including the
half-plane condition in the bordered case). -/
theorem patchTileFaceClosedRegion_subset_modelRegion
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (g' : U → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion A.patchTileFacePolygon ⊆ k.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ k.perturbationRegion := Q.faceClosedRegion_subset f.1 hxf
  let z : k.perturbationRegion := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate k g' hcoord hzSupport

/-- The corrected finite local weld: its old side is closed under whole adaptive source tiles,
so it is exactly supported on a finite common-level source subcomplex. -/
theorem exists_patchTile_local_weld
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U c.kind.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U c.kind.perturbationRegion Q)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) :=
  SynchronizedPatch.exists_synchronizedPatch_local_weld c A.patchTileFacePolygon
    (A.patchTileFaceClosedRegion_subset_modelRegion g' hcoord)

end PolygonalReplacementSourceAtlas

/-- Assemble the controlled polygonal replacement over an arbitrary open chart region whose
coordinate image is closed relative to the chosen plane perturbation region. -/
theorem exists_straightenedChartOpen
    {S' : Type*} [TopologicalSpace S'] [T2Space S'] [CompactSpace S']
    [SecondCountableTopology S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (hsub : U ⊆ T.chartOverlap c)
    (V : Set Plane) (hV : IsOpen V)
    (hVsub : V ⊆ c.kind.perturbationRegion)
    (hmem : ∀ x : U,
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V)
    (hfVclosed : _root_.Topology.IsClosedEmbedding
      (fun x : U ↦
        (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V))) :
    ∃ (Q : PolygonalReplacementPresentation U V)
      (A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
      (g' : U → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S'),
      (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
      (∀ x, x ∉ U → g x = T.embed x) ∧
      MatchesAtFrontier U g T.embed ∧
      ContinuousOn g U ∧
      Set.InjOn g U ∧
      Disjoint (g '' U) (T.embed '' Uᶜ) ∧
      _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
  classical
  letI : MetricSpace S' := TopologicalSpace.metrizableSpaceMetric S'
  let toOverlap : U → T.chartOverlap c := fun x ↦ ⟨x.1, hsub x.2⟩
  have htoOverlapEmbedding : _root_.Topology.IsEmbedding toOverlap := by
    simpa [toOverlap] using _root_.Topology.IsEmbedding.inclusion hsub
  let f : U → Plane := fun x ↦ T.chartOverlapMap c (toOverlap x)
  have hf : Continuous f :=
    (T.isEmbedding_chartOverlapMap c).continuous.comp
      htoOverlapEmbedding.continuous
  obtain ⟨mu, hmu, hmatch⟩ :=
    exists_chartMatchingControlOn_of_metricSpace T c U hU hsub
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  letI : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  letI : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  have hRsupport : R.support = Set.univ := by
    exact IntrinsicTwoComplex.AdaptiveOpenCover.locallyFiniteTriangleComplex_support
      T.toIntrinsic U
      (T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
        (regionSafeControl V f mu)
        (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)) hU
  let toU : R.support → U := Subtype.val
  have htoUclosed : _root_.Topology.IsClosedEmbedding toU := by
    refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [show Set.range toU = R.support by exact Subtype.range_val, hRsupport]
    exact isClosed_univ
  have hfVrestricted : _root_.Topology.IsClosedEmbedding
      (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) := by
    have heq : (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) =
        (fun x : U ↦
          (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V)) ∘ toU := by
      funext p
      apply Subtype.ext
      rfl
    rw [heq]
    exact hfVclosed.comp htoUclosed
  let G : R.PlaneGraphRealization :=
    LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
      V hV (fun p ↦ f p.1)
      ((T.isEmbedding_chartOverlapMap c).comp htoOverlapEmbedding |>.comp
        _root_.Topology.IsEmbedding.subtypeVal)
      (fun p ↦ hmem p.1) hfVrestricted.isClosed_range
  have hGmap : ∀ p, G.map p = f p.1 := fun _ ↦ rfl
  have hGregion : G.region = V := rfl
  obtain ⟨vc, hvc, ec, hec, H, hclose⟩ :=
    IntrinsicTwoComplex.RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison
      T.toIntrinsic U hU V hV f hf hmem mu hmu G hGmap hGregion
  let G' := G.withApproximationControls vc hvc ec hec
  let P := R.polygonalReplacementComplex H
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let q : U ≃ₜ P.support := eU.trans (R.polygonalReplacementHomeomorph H)
  let Q : PolygonalReplacementPresentation U V :=
    { complex := P
      sourceHomeomorph := q
      facePolygon := fun f ↦ R.facePolygonalCircle (G := G') f
      faceFillingMap := fun f ↦ (R.facePLFilling (G := G') f).map
      faceMap_eq := fun _ _ ↦ rfl
      faceCertificate := fun f ↦ (R.facePLFilling (G := G') f).certificate
      faceClosedRegion_subset := fun f ↦ H.closedRegions_mem_region f
      faceCarrier_eq := fun f ↦ R.polygonalReplacementComplex_faceCarrier H f }
  let sourceParent (a : T.toIntrinsic.AdaptiveFanFace U hU) :
      T.toIntrinsic.Face := by
    let Rt := T.toIntrinsic.safeSubdivision a.1.1
    let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
    exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q :=
    { Tile := T.toIntrinsic.AdaptiveFace U
      tileDecidableEq := Classical.decEq _
      tile := fun f ↦ f.1
      tileFaces := T.toIntrinsic.adaptiveFanFacesOver U hU
      mem_tileFaces := fun t f ↦
        T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t f
      sourceTileCarrier := T.toIntrinsic.adaptiveFaceCarrier U
      sourceTileCarrier_subset_open := fun t ↦
        T.toIntrinsic.adaptiveFaceCarrier_subset U t
      sourceTileCarrier_locallyFinite :=
        T.toIntrinsic.locallyFinite_adaptiveFaceCarrierInOpen U hU
      sourceTileCarrier_eq_faces := by
        intro t
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨i, j, z, hz⟩ :=
            T.toIntrinsic.exists_adaptiveFanFaceMap_eq_of_mem_adaptiveFaceCarrier
              U hU t hx
          let a : T.toIntrinsic.AdaptiveFanFace U hU := ⟨t, i, j⟩
          have ha : a ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t :=
            (T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a).2 rfl
          let a' : {f : Q.complex.Face //
              f ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t} := ⟨a, ha⟩
          apply Set.mem_iUnion.mpr
          refine ⟨a', ?_⟩
          let hxU : x ∈ U := T.toIntrinsic.adaptiveFaceCarrier_subset U t hx
          refine ⟨hxU, ?_⟩
          apply (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
            (eU ⟨x, hxU⟩)).2
          change ⟨x, hxU⟩ ∈ R.faceCarrier a
          change ⟨x, hxU⟩ ∈
            Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a)
          rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a]
          exact ⟨z, hz⟩
        · intro x hx
          obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
          obtain ⟨hxU, hxaQ⟩ := hxa
          have hxaR := (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a.1
            (eU ⟨x, hxU⟩)).1 hxaQ
          change ⟨x, hxU⟩ ∈
            Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a.1) at hxaR
          rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a.1] at hxaR
          have hxt :=
            T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a.1 hxaR
          change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1.1 at hxt
          rw [(T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a.1).1 a.2] at hxt
          exact hxt
      sourceFaceParent := sourceParent
      sourceFaceSet_subset_parent := by
        intro a x hx
        change T.toIntrinsic.AdaptiveFanFace U hU at a
        obtain ⟨hxU, hxaQ⟩ := hx
        have hxaR :=
          (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
            (eU ⟨x, hxU⟩)).1 hxaQ
        change ⟨x, hxU⟩ ∈
          Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a) at hxaR
        rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a] at hxaR
        have hxt :=
          T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a hxaR
        change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1 at hxt
        obtain ⟨z, hz, hzx⟩ := hxt
        let Rt := T.toIntrinsic.safeSubdivision a.1.1
        let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
        have hzParent :=
          (Classical.choose_spec h).2 z hz
        change x ∈ T.toIntrinsic.faceCarrier (sourceParent a).1
        change x ∈ T.toIntrinsic.faceCarrier (Classical.choose h)
        rw [← hzx]
        exact hzParent
      sourceFaceStandardAffine := by
        intro a
        change T.toIntrinsic.AdaptiveFanFace U hU at a
        obtain ⟨b, hb⟩ :=
          T.toIntrinsic.adaptiveGlobalFanFaceMap_standardAffine hU a
        refine ⟨b, ?_⟩
        intro x
        have hsource :
            q.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                (K := P) a x) =
              eU.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                (K := R) a x) := by
          change
            eU.symm
                ((R.polygonalReplacementHomeomorph H).symm
                  (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                    (K := P) a x)) =
              eU.symm
                (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                  (K := R) a x)
          congr 1
          exact R.polygonalReplacementInverse_faceToSupport H a x
        change
          (q.symm
            (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
              (K := P) a x)).1.1 =
            b (P.facePlaneHomeomorph a x).1
        rw [hsource]
        change
          (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a x).1.1 =
            b ((T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex U hU
              ).facePlaneHomeomorph a x).1
        exact hb x
      commonLevel := T.toIntrinsic.adaptiveFaceCommonLevel U
      levelFaces := fun F ↦
        (Finset.univ : Finset
          (T.toIntrinsic.LevelFace (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
          fun u ↦ ∃ t ∈ F,
            T.toIntrinsic.levelFaceCarrier u ⊆
              T.toIntrinsic.adaptiveFaceCarrier U t
      sourceTiles_eq_levelFaces := by
        intro F
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
          rw [T.toIntrinsic.adaptiveFaceCarrier_eq_iUnion_commonLevel_descendants
            U F t.2] at hxt
          obtain ⟨u, hxt⟩ := Set.mem_iUnion.mp hxt
          obtain ⟨hut, hxu⟩ := Set.mem_iUnion.mp hxt
          let u' : {u : T.toIntrinsic.LevelFace
              (T.toIntrinsic.adaptiveFaceCommonLevel U F) //
              u ∈ (Finset.univ : Finset
                (T.toIntrinsic.LevelFace
                  (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
                (fun u ↦ ∃ t ∈ F,
                  T.toIntrinsic.levelFaceCarrier u ⊆
                    T.toIntrinsic.adaptiveFaceCarrier U t)} :=
            ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t.1, t.2, hut⟩⟩⟩
          exact Set.mem_iUnion.mpr ⟨u', hxu⟩
        · intro x hx
          obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hx
          obtain ⟨-, t, htF, hut⟩ := Finset.mem_filter.mp u.2
          let t' : {t : T.toIntrinsic.AdaptiveFace U // t ∈ F} := ⟨t, htF⟩
          exact Set.mem_iUnion.mpr ⟨t', hut hxu⟩ }
  have hqmodel : ∀ y : U, (q y).1.1 ∈ c.kind.modelRegion := by
    intro y
    cases hk : c.kind with
    | disk =>
        have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
          hVsub (q y).1.2
        simpa [ChartKind.modelRegion, ChartKind.perturbationRegion, hk] using
          hyPerturb
    | halfDisk =>
        have hfHalf : Set.range f ⊆ HalfPlaneSet := by
          rintro z ⟨x, rfl⟩
          have hx := (T.chartOverlapModelMap c (toOverlap x)).2
          change f x ∈ c.kind.modelRegion at hx
          rw [hk] at hx
          simpa [ChartKind.modelRegion, HalfPlaneSet] using hx.2
        have hgraph : Set.range G'.graphReplacementMap ⊆ HalfPlaneSet := by
          apply IntrinsicTwoComplex.ControlledAdaptiveComplex.range_graphReplacementMap_subset_halfPlane
            T.toIntrinsic U hU f hf (regionSafeControl V f mu)
              (stronglyPositiveOn_regionSafeControl hV hf hmem hmu) G'
          · intro p
            rfl
          · exact hfHalf
        have hhalf : (q y).1.1 ∈ HalfPlaneSet := by
          exact LocallyFiniteTriangleComplex.polygonalReplacementHomeomorph_mem_halfPlane
            G' H hgraph (eU y)
        exact ⟨by
            have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
              hVsub (q y).1.2
            simpa [ChartKind.perturbationRegion, hk] using hyPerturb,
          by simpa [HalfPlaneSet] using hhalf⟩
  let g' : U → c.kind.modelRegion := fun y ↦ ⟨(q y).1.1, hqmodel y⟩
  let g : T.toIntrinsic.realization → S' := fun x ↦
    if hx : x ∈ U then (c.chart.symm (g' ⟨x, hx⟩)).1 else T.embed x
  have hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1 := by
    intro y
    simp [g, y.2]
  have hgoutside : ∀ x, x ∉ U → g x = T.embed x := by
    intro x hx
    simp [g, hx]
  have hgclose : ∀ y : U,
      dist (g' y : Plane)
        (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ≤ mu y := by
    intro y
    change dist (q y).1.1 (f y) ≤ mu y
    have h := hclose (eU y)
    change dist (q y).1.1 (G.map (eU y)) ≤ mu y at h
    rw [hGmap] at h
    exact h
  obtain ⟨hgmatch, hcross⟩ := hmatch g' g hgval hgclose
  have hgcont : ContinuousOn g U := by
    have hg'cont : Continuous g' := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_subtype_val.comp q.continuous))
    have hcomp : Continuous (fun y : U ↦ (c.chart.symm (g' y)).1) :=
      continuous_subtype_val.comp (c.chart.symm.continuous.comp hg'cont)
    rw [continuousOn_iff_continuous_restrict]
    exact hcomp.congr fun y ↦ (hgval y).symm
  have hginj : Set.InjOn g U := by
    intro x hx y hy hxy
    let xU : U := ⟨x, hx⟩
    let yU : U := ⟨y, hy⟩
    have hchart : c.chart.symm (g' xU) = c.chart.symm (g' yU) := by
      apply Subtype.ext
      rw [← hgval xU, ← hgval yU]
      exact hxy
    have hg'eq : g' xU = g' yU := c.chart.symm.injective hchart
    have hqeq : q xU = q yU := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : c.kind.modelRegion => (z : Plane)) hg'eq
    exact congrArg Subtype.val (q.injective hqeq)
  have hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed) :=
    isEmbedding_frontierGlue_of_matches hU hgcont T.isEmbedding.continuous
      hgmatch hginj T.isEmbedding.injective hcross
  exact ⟨Q, A, g', g, fun _ ↦ rfl, hgval, hgoutside, hgmatch, hgcont,
    hginj, hcross, hembed⟩

/-- Straighten the old complex in a chart while fixing every source point whose old image lies
in a prescribed closed protected set.  The perturbation region is obtained by deleting the
protected chart trace; closedness of the full overlap embedding makes the restricted trace
closed in that new open region. -/
theorem exists_straightenedChartAway
    {S' : Type*} [TopologicalSpace S'] [T2Space S'] [CompactSpace S']
    [SecondCountableTopology S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (A : Set S') (hA : IsClosed A) :
    ∃ (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
      (V : Set Plane) (hV : IsOpen V)
      (Q : PolygonalReplacementPresentation U V)
      (Qatlas : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
      (g' : U → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S'),
      V ⊆ c.kind.perturbationRegion ∧
      (∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
        (c.chart.symm z).1 ∈ A) ∧
      (∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
        T.chartOverlapMap c y ∉ V) ∧
      (∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ A) ∧
      (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      U ⊆ T.chartOverlap c ∧
      (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
      (∀ x, T.embed x ∈ A → g x = T.embed x) ∧
      MatchesAtFrontier U g T.embed ∧
      ContinuousOn g U ∧
      Set.InjOn g U ∧
      Disjoint (g '' U) (T.embed '' Uᶜ) ∧
      _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
  classical
  let O : Set T.toIntrinsic.realization := T.chartOverlap c
  let F : O → c.kind.perturbationRegion :=
    T.chartOverlapPerturbationMap c
  let B : Set O := {y | T.embed y.1 ∈ A}
  have hBclosed : IsClosed B := by
    exact hA.preimage
      (T.isEmbedding.continuous.comp continuous_subtype_val)
  let K : Set c.kind.perturbationRegion := F '' B
  have hKclosed : IsClosed K := by
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosedMap B hBclosed
  let V : Set Plane := Subtype.val '' Kᶜ
  have hV : IsOpen V := by
    exact c.kind.isOpen_perturbationRegion.isOpenEmbedding_subtypeVal.isOpenMap
      Kᶜ hKclosed.isOpen_compl
  have hVsub : V ⊆ c.kind.perturbationRegion := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have hVavoid : ∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
      (c.chart.symm z).1 ∈ A := by
    intro z hzV
    let zPert : c.kind.perturbationRegion :=
      c.kind.modelToPerturbation z
    have hzK : zPert ∈ K := by
      by_contra hzK
      apply hzV
      exact ⟨zPert, hzK, rfl⟩
    obtain ⟨y, hyB, hFy⟩ := hzK
    have hmodel : T.chartOverlapModelMap c y = z := by
      apply c.kind.isClosedEmbedding_modelToPerturbation.injective
      exact hFy
    have hsurface : T.embed y.1 = (c.chart.symm z).1 := by
      calc
        T.embed y.1 =
            (c.chart.symm (T.chartOverlapModelMap c y)).1 := by
          symm
          exact congrArg Subtype.val
            (c.chart.symm_apply_apply (T.chartOverlapToDomain c y))
        _ = (c.chart.symm z).1 :=
          congrArg (fun w : c.kind.modelRegion ↦ (c.chart.symm w).1) hmodel
    rw [← hsurface]
    exact hyB
  have hVprotected : ∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
      T.chartOverlapMap c y ∉ V := by
    intro y hyA hyV
    obtain ⟨z, hzNotK, hzval⟩ := hyV
    have hFy : F y = z := by
      apply Subtype.ext
      exact hzval.symm
    apply hzNotK
    rw [← hFy]
    exact ⟨y, hyA, rfl⟩
  let U : Set T.toIntrinsic.realization := Subtype.val '' Bᶜ
  have hU : IsOpen U := by
    exact (T.isOpen_chartOverlap c).isOpenEmbedding_subtypeVal.isOpenMap
      Bᶜ hBclosed.isOpen_compl
  have hsub : U ⊆ T.chartOverlap c := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hUprotected : ∀ y : T.chartOverlap c, y.1 ∉ U →
      T.embed y.1 ∈ A := by
    intro y hyU
    by_contra hyA
    apply hyU
    exact ⟨y, hyA, rfl⟩
  have hmem : ∀ x : U,
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V := by
    intro x
    rcases x.2 with ⟨y, hyB, hyx⟩
    have hyval : y.1 = x.1 := hyx
    have hnotK : F y ∈ Kᶜ := by
      intro hyK
      rcases hyK with ⟨b, hbB, hFb⟩
      have hyb : y = b :=
        (T.isClosedEmbedding_chartOverlapPerturbationMap c).injective
          (by simpa [F] using hFb.symm)
      exact hyB (hyb ▸ hbB)
    refine ⟨F y, hnotK, ?_⟩
    change (F y : Plane) =
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩
    change T.chartOverlapMap c y =
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩
    congr 1
    exact Subtype.ext hyval
  let fV : U → V := fun x ↦
    ⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩
  have hfVembed : _root_.Topology.IsEmbedding fV := by
    apply (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
    have hinc : _root_.Topology.IsEmbedding
        (Set.inclusion hsub : U → T.chartOverlap c) :=
      _root_.Topology.IsEmbedding.inclusion hsub
    have hcomp := (T.isEmbedding_chartOverlapMap c).comp hinc
    simpa [fV, Function.comp_def] using hcomp
  let j : V → c.kind.perturbationRegion :=
    fun z ↦ ⟨z.1, hVsub z.2⟩
  have hjcont : Continuous j :=
    Continuous.subtype_mk continuous_subtype_val _
  have hrange : Set.range fV = j ⁻¹' Set.range F := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x.1, hsub x.2⟩, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨y, hyF⟩
      have hyPlane : (F y : Plane) = z.1 :=
        congrArg Subtype.val hyF
      have hyNotB : y ∈ Bᶜ := by
        intro hyB
        have hjK : j z ∈ K := ⟨y, hyB, hyF⟩
        rcases z.2 with ⟨w, hwNotK, hwz⟩
        have hwEq : w = j z := by
          apply Subtype.ext
          exact hwz
        exact hwNotK (hwEq ▸ hjK)
      let x : U := ⟨y.1, ⟨y, hyNotB, rfl⟩⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hyPlane
  have hfVclosed : _root_.Topology.IsClosedEmbedding fV := by
    refine ⟨hfVembed, ?_⟩
    rw [hrange]
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosed_range.preimage
      hjcont
  obtain ⟨Q, Qatlas, g', g, hgcoord, hgval, hgoutside, hgmatch, hgcont, hginj,
      hcross, hembed⟩ :=
    exists_straightenedChartOpen T c U hU hsub V hV hVsub hmem hfVclosed
  have hgfix : ∀ x, T.embed x ∈ A → g x = T.embed x := by
    intro x hxA
    apply hgoutside x
    rintro ⟨y, hyNotB, hyx⟩
    have hyval : y.1 = x := hyx
    apply hyNotB
    change T.embed y.1 ∈ A
    rw [hyval]
    exact hxA
  exact ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
    hUprotected, hgcoord, hsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross, hembed⟩

end PartialTriangulation

/-- **Theorem boundary** (Moise Thm. 7.6 for partial triangulations).

Two partial triangulations presented on a common vertex type, whose embeddings agree exactly on
the shared part of their realizations (`hagree` and `hsep` together say the images meet only
where the barycentric points coincide), glue to a single partial triangulation on the union face
family, supported on the union of the two images.

The realization of the union family is the set-union of the two realizations, so the glued
embedding is the pasting of the two embeddings along a closed common part; it is a continuous
injection from a compact space into a Hausdorff space, hence an embedding.  The edge-face count
hypothesis is passed through to the glued complex. -/
theorem PartialTriangulation.exists_glued {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (V : Type) [Fintype V] [DecidableEq V]
    (F₁ F₂ : Finset (Finset V))
    (hcard : ∀ t ∈ F₁ ∪ F₂, t.card = 3)
    (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S)
    (he₁ : _root_.Topology.IsEmbedding e₁) (he₂ : _root_.Topology.IsEmbedding e₂)
    (hagree : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y)
    (hsep : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) :
    ∃ T' : PartialTriangulation S,
      T'.support = Set.range e₁ ∪ Set.range e₂ ∧
      ∀ e ∈ T'.edges, (T'.faces.filter fun t => e ⊆ t).card ≤ 2 := by
  classical
  -- the realization of the union family is the union of the realizations
  have hunion : ∀ x : V → ℝ, x ∈ GeometricRealization V (F₁ ∪ F₂) ↔
      x ∈ GeometricRealization V F₁ ∨ x ∈ GeometricRealization V F₂ := by
    intro x
    simp only [GeometricRealization, Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro ⟨hstd, t, ht | ht, hsupp⟩
      · exact Or.inl ⟨hstd, t, ht, hsupp⟩
      · exact Or.inr ⟨hstd, t, ht, hsupp⟩
    · rintro (⟨hstd, t, ht, hsupp⟩ | ⟨hstd, t, ht, hsupp⟩)
      · exact ⟨hstd, t, Or.inl ht, hsupp⟩
      · exact ⟨hstd, t, Or.inr ht, hsupp⟩
  -- the pasted embedding
  have hmem₂ : ∀ x : GeometricRealization V (F₁ ∪ F₂),
      (x : V → ℝ) ∉ GeometricRealization V F₁ → (x : V → ℝ) ∈ GeometricRealization V F₂ :=
    fun x hx => ((hunion x.1).mp x.2).resolve_left hx
  set glue : GeometricRealization V (F₁ ∪ F₂) → S := fun x =>
    if hx : (x : V → ℝ) ∈ GeometricRealization V F₁ then e₁ ⟨x.1, hx⟩
    else e₂ ⟨x.1, hmem₂ x hx⟩ with hglue
  -- the glued value is independent of the side used
  have hglue_left : ∀ (x : GeometricRealization V (F₁ ∪ F₂))
      (hx : (x : V → ℝ) ∈ GeometricRealization V F₁), glue x = e₁ ⟨x.1, hx⟩ := by
    intro x hx
    simp [hglue, hx]
  have hglue_right : ∀ (x : GeometricRealization V (F₁ ∪ F₂))
      (hx : (x : V → ℝ) ∈ GeometricRealization V F₂), glue x = e₂ ⟨x.1, hx⟩ := by
    intro x hx
    by_cases hx₁ : (x : V → ℝ) ∈ GeometricRealization V F₁
    · rw [hglue_left x hx₁]
      exact hagree ⟨x.1, hx₁⟩ ⟨x.1, hx⟩ rfl
    · simp [hglue, hx₁]
  -- injectivity
  have hinj : Function.Injective glue := by
    intro x y hxy
    apply Subtype.ext
    by_cases hx : (x : V → ℝ) ∈ GeometricRealization V F₁ <;>
      by_cases hy : (y : V → ℝ) ∈ GeometricRealization V F₁
    · rw [hglue_left x hx, hglue_left y hy] at hxy
      exact Subtype.mk_eq_mk.mp (he₁.injective hxy)
    · rw [hglue_left x hx, hglue_right y (hmem₂ y hy)] at hxy
      exact hsep ⟨x.1, hx⟩ ⟨y.1, hmem₂ y hy⟩ hxy
    · rw [hglue_right x (hmem₂ x hx), hglue_left y hy] at hxy
      exact (hsep ⟨y.1, hy⟩ ⟨x.1, hmem₂ x hx⟩ hxy.symm).symm
    · rw [hglue_right x (hmem₂ x hx), hglue_right y (hmem₂ y hy)] at hxy
      exact Subtype.mk_eq_mk.mp (he₂.injective hxy)
  -- continuity via closed preimages: both restriction inclusions have compact images
  have hcont : Continuous glue := by
    rw [continuous_iff_isClosed]
    intro C hC
    -- describe the preimage as a union of two compact images
    have hdesc : glue ⁻¹' C =
        ((fun z : GeometricRealization V F₁ =>
          (⟨z.1, (hunion z.1).mpr (Or.inl z.2)⟩ : GeometricRealization V (F₁ ∪ F₂))) ''
            (e₁ ⁻¹' C)) ∪
        ((fun z : GeometricRealization V F₂ =>
          (⟨z.1, (hunion z.1).mpr (Or.inr z.2)⟩ : GeometricRealization V (F₁ ∪ F₂))) ''
            (e₂ ⁻¹' C)) := by
      ext x
      constructor
      · intro hx
        by_cases hx₁ : (x : V → ℝ) ∈ GeometricRealization V F₁
        · refine Or.inl ⟨⟨x.1, hx₁⟩, ?_, Subtype.ext rfl⟩
          rw [Set.mem_preimage, ← hglue_left x hx₁]
          exact hx
        · refine Or.inr ⟨⟨x.1, hmem₂ x hx₁⟩, ?_, Subtype.ext rfl⟩
          rw [Set.mem_preimage, ← hglue_right x (hmem₂ x hx₁)]
          exact hx
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · show glue _ ∈ C
          rw [hglue_left _ z.2]
          exact hz
        · show glue _ ∈ C
          rw [hglue_right _ z.2]
          exact hz
    rw [hdesc]
    have hcompact : ∀ (F : Finset (Finset V)) (e : GeometricRealization V F → S)
        (he : _root_.Topology.IsEmbedding e)
        (ι : GeometricRealization V F → GeometricRealization V (F₁ ∪ F₂))
        (hι : Continuous ι),
        IsCompact (ι '' (e ⁻¹' C)) := by
      intro F e he ι hιc
      exact ((hC.preimage he.continuous).isCompact).image hιc
    refine IsClosed.union ?_ ?_
    · exact (hcompact F₁ e₁ he₁ _
        (Continuous.subtype_mk continuous_subtype_val _)).isClosed
    · exact (hcompact F₂ e₂ he₂ _
        (Continuous.subtype_mk continuous_subtype_val _)).isClosed
  -- assemble the glued partial triangulation
  refine ⟨{ Vertex := V, faces := F₁ ∪ F₂, faces_card := hcard, embed := glue,
            isEmbedding := ?_ }, ?_, ?_⟩
  · exact (hcont.isClosedEmbedding hinj).isEmbedding
  · -- the support is the union of the two images
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      by_cases hx : (x : V → ℝ) ∈ GeometricRealization V F₁
      · exact Or.inl ⟨⟨x.1, hx⟩, (hglue_left x hx).symm⟩
      · exact Or.inr ⟨⟨x.1, hmem₂ x hx⟩, (hglue_right x (hmem₂ x hx)).symm⟩
    · rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨⟨x.1, (hunion x.1).mpr (Or.inl x.2)⟩, hglue_left _ x.2⟩
      · exact ⟨⟨x.1, (hunion x.1).mpr (Or.inr x.2)⟩, hglue_right _ x.2⟩
  · -- An embedded triangle family in a surface automatically has edge valence at most two.
    intro e he
    apply edge_valence_le_two_of_isEmbedding (F₁ ∪ F₂) hcard glue
      ((hcont.isClosedEmbedding hinj).isEmbedding) e
    rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
    exact (Finset.mem_powersetCard.mp het).2

/-- The invariant carried through the bordered Radó induction: the built complex is a
combinatorial surface (every edge in at most two faces), and the region `A` absorbed so far lies
in the topological interior of its support in `S`.

For a surface without boundary this agrees with Moise Ch. 8, Thm. 3, invariant (4), after the
usual identification of topological and combinatorial interior.  The ambient topological
interior is essential in the bordered case: a half-disk core contains points of `∂S`, and those
points belong to the interior of a half-disk neighborhood *as a subset of `S`*, although they lie
on its combinatorial boundary.  Requiring such points to lie in `combInterior` would make the
bordered induction statement false.

This invariant is expected to be *strengthened* during the proof of `moise_induction_step`
(candidates: connected vertex links, and the bordered bookkeeping locating `∂S ∩ support` inside
the combinatorial boundary).  Strengthening tightens the step's hypothesis and conclusion
together and keeps the assembly proof below valid; weakening the step's conclusion instead is
the failure mode this rebuild exists to prevent. -/
structure RadoInvariant {S : Type*} [TopologicalSpace S]
    (T : PartialTriangulation S) (A : Set S) : Prop where
  /-- The finitely many absorbed chart cores form a compact set.  This is needed to choose the
  finite collars and positive separation scales in the induction step. -/
  coresCompact : IsCompact A
  combSurface : ∀ e ∈ T.edges, (T.faces.filter fun t => e ⊆ t).card ≤ 2
  coresInside : A ⊆ interior T.support

theorem RadoInvariant.coresCovered {S : Type*} [TopologicalSpace S]
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    A ⊆ T.support :=
  hT.coresInside.trans interior_subset

/-- The already absorbed compact set has a closed buffer still lying in the ambient interior of
the old support.  Protecting this whole buffer during chart straightening, rather than merely
protecting `A` pointwise, makes preservation of the Radó interior invariant immediate. -/
theorem RadoInvariant.exists_closedBuffer {S : Type*} [TopologicalSpace S]
    [T2Space S] [CompactSpace S]
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ C : Set S,
      IsClosed C ∧ A ⊆ interior C ∧ C ⊆ interior T.support := by
  obtain ⟨V, hVopen, hAV, hclosure⟩ :=
    hT.coresCompact.exists_isOpen_closure_subset
      (isOpen_interior.mem_nhdsSet.mpr hT.coresInside)
  refine ⟨closure V, isClosed_closure, ?_, hclosure⟩
  calc
    A ⊆ V := hAV
    _ = interior V := hVopen.interior_eq.symm
    _ ⊆ interior (closure V) := interior_mono subset_closure

/-- Enlarge the recorded absorbed set without changing the triangulation when the added set is
already in the interior of its support. -/
theorem RadoInvariant.absorb_of_subset {S : Type*} [TopologicalSpace S]
    {T : PartialTriangulation S} {A B : Set S} (hT : RadoInvariant T A)
    (hBcompact : IsCompact B) (hB : B ⊆ interior T.support) :
    RadoInvariant T (A ∪ B) where
  coresCompact := hT.coresCompact.union hBcompact
  combSurface := hT.combSurface
  coresInside := Set.union_subset hT.coresInside hB

/-- A single chart has a concrete finite partial triangulation satisfying the bordered Rado
invariant.  This is the honest nonempty base patch used by the induction step. -/
theorem radoInvariant_chartPatch {S : Type*} [TopologicalSpace S] (c : MoiseChart S) :
    RadoInvariant c.patchPartialTriangulation c.core where
  coresCompact := c.isCompact_core
  combSurface := by
    intro e he
    have hecard := c.patchPartialTriangulation.card_of_mem_edges he
    change (c.kind.patchComplex.cells.filter fun t => e ⊆ t).card ≤ 2
    exact c.kind.patchComplex_edge_valence e hecard
  coresInside := c.core_subset_interior_patchPartialTriangulation_support

/-- If the fixed patch of the new chart already contains the previously absorbed region in its
ambient interior, that patch alone is a valid next induction stage. -/
theorem radoInvariant_chartPatch_absorb {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S) {A : Set S} (hAcompact : IsCompact A)
    (hA : A ⊆ interior c.patchPartialTriangulation.support) :
    RadoInvariant c.patchPartialTriangulation (A ∪ c.core) :=
  by simpa [Set.union_comm] using
    (radoInvariant_chartPatch c).absorb_of_subset hAcompact hA

/-- The empty partial triangulation satisfies the invariant for the empty region: the base case
of the Radó induction. -/
theorem radoInvariant_empty (S : Type*) [TopologicalSpace S] :
    RadoInvariant (PartialTriangulation.empty S) ∅ where
  coresCompact := isCompact_empty
  combSurface := by
    intro e he
    simp only [PartialTriangulation.edges, PartialTriangulation.empty,
      Finset.biUnion_empty] at he
    exact absurd he (Finset.notMem_empty e)
  coresInside := Set.empty_subset _

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

omit [T2Space S] [ConnectedSpace S] [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- A compact Eval surface has a finite cover by boundary-faithful Moise chart cores (Moise
Ch. 8, Thm. 1, plus compactness).  Proved by a finite subcover of the core interiors from the
local chart extraction (`exists_moiseChart_core_mem_nhds`, `Moise/ChartExtraction.lean`). -/
theorem moise_finite_chart_cover :
    ∃ (m : ℕ) (charts : Fin m → MoiseChart S),
      (⋃ i, (charts i).core) = Set.univ ∧
      ∀ i, (charts i).BoundaryFaithful := by
  classical
  choose c hfaithful hcore using exists_moiseChart_core_mem_nhds S
  have hcover : (Set.univ : Set S) ⊆ ⋃ x : S, interior (c x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hcore x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S => interior (c x).core) (fun x => isOpen_interior) hcover
  obtain ⟨m, e⟩ := Finite.exists_equiv_fin t
  let e' := Classical.choice e
  refine ⟨m, fun i => c (e'.symm i).1, ?_, fun i => hfaithful (e'.symm i).1⟩
  apply Set.eq_univ_of_univ_subset
  intro x hx
  rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with ⟨y, hyt, hxy⟩
  exact Set.mem_iUnion.mpr ⟨e' ⟨y, hyt⟩, by
    simpa using interior_subset hxy⟩

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- Compact Eval surfaces are second countable.  We derive this from the finite Moise chart
cover instead of asking typeclass search to infer second countability of the half-space model:
each chart domain is homeomorphic to a second-countable disk or half-disk, and finitely many
open chart domains cover the surface. -/
theorem moise_secondCountableTopology : SecondCountableTopology S := by
  obtain ⟨m, charts, hcover, _⟩ := moise_finite_chart_cover S
  let U : Fin m → Set S := fun i ↦ (charts i).domain
  haveI : ∀ i, SecondCountableTopology (U i) :=
    fun i ↦ (charts i).chart.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · exact fun i ↦ (charts i).isOpen_domain
  · apply Set.eq_univ_of_univ_subset
    intro x _
    rw [← hcover] at *
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show x ∈ ⋃ i, (charts i).core from ‹_›)
    exact Set.mem_iUnion.mpr ⟨i, (charts i).core_subset_domain hi⟩

omit [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- The controlled locally finite polygonal replacement on the full chart overlap assembles
with the unchanged old embedding across the overlap frontier.

This is the analytic half of Moise's crossing step.  The replacement stays in the chart model
(including the closed half-plane in the bordered case), converges to the old embedding at the
frontier, and is disjoint from the unchanged image outside the overlap.  Consequently the
frontier paste is again an embedding of the original finite intrinsic complex. -/
theorem PartialTriangulation.exists_straightenedChartOverlap
    (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ (Q : PolygonalReplacementPresentation (T.chartOverlap c)
        c.kind.perturbationRegion)
      (A : PolygonalReplacementSourceAtlas T.toIntrinsic (T.chartOverlap c)
        c.kind.perturbationRegion Q)
      (g' : T.chartOverlap c → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S),
      (∀ y : T.chartOverlap c,
        (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) ∧
      MatchesAtFrontier (T.chartOverlap c) g T.embed ∧
      ContinuousOn g (T.chartOverlap c) ∧
      Set.InjOn g (T.chartOverlap c) ∧
      Disjoint (g '' T.chartOverlap c) (T.embed '' (T.chartOverlap c)ᶜ) ∧
      _root_.Topology.IsEmbedding
        (frontierGlue (T.chartOverlap c) g T.embed) := by
  letI : SecondCountableTopology S := moise_secondCountableTopology S
  classical
  let U : Set T.toIntrinsic.realization := T.chartOverlap c
  let hU : IsOpen U := T.isOpen_chartOverlap c
  let f : U → Plane := T.chartOverlapMap c
  let hf : Continuous f := (T.isEmbedding_chartOverlapMap c).continuous
  let V : Set Plane := c.kind.perturbationRegion
  let hV : IsOpen V := c.kind.isOpen_perturbationRegion
  have hmem : ∀ x : U, f x ∈ V := by
    intro x
    exact c.kind.modelRegion_subset_perturbationRegion
      (T.chartOverlapModelMap c x).2
  obtain ⟨mu, hmu, hmatch⟩ := T.exists_chartMatchingControl c
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  letI : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  letI : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  have hRsupport : R.support = Set.univ := by
    exact IntrinsicTwoComplex.AdaptiveOpenCover.locallyFiniteTriangleComplex_support
      T.toIntrinsic U
      (T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
        (regionSafeControl V f mu)
        (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)) hU
  let toU : R.support → U := Subtype.val
  have htoUclosed : _root_.Topology.IsClosedEmbedding toU := by
    refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [show Set.range toU = R.support by exact Subtype.range_val, hRsupport]
    exact isClosed_univ
  let fV : R.support → V := fun p ↦ ⟨f p.1, hmem p.1⟩
  have hfVclosed : _root_.Topology.IsClosedEmbedding fV := by
    have heq : fV =
        (c.kind.modelToPerturbation ∘ T.chartOverlapModelMap c) ∘ toU := by
      funext p
      apply Subtype.ext
      rfl
    rw [heq]
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).comp htoUclosed
  let G : R.PlaneGraphRealization :=
    LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
      V hV (fun p ↦ f p.1)
      ((T.isEmbedding_chartOverlapMap c).comp
        _root_.Topology.IsEmbedding.subtypeVal)
      (fun p ↦ hmem p.1) hfVclosed.isClosed_range
  have hGmap : ∀ p, G.map p = f p.1 := fun _ ↦ rfl
  have hGregion : G.region = V := rfl
  obtain ⟨vc, hvc, ec, hec, H, hclose⟩ :=
    IntrinsicTwoComplex.RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison
      T.toIntrinsic U hU V hV f hf hmem mu hmu G hGmap hGregion
  let G' := G.withApproximationControls vc hvc ec hec
  let P := R.polygonalReplacementComplex H
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let q : U ≃ₜ P.support := eU.trans (R.polygonalReplacementHomeomorph H)
  let Q : PolygonalReplacementPresentation U V :=
    { complex := P
      sourceHomeomorph := q
      facePolygon := fun f ↦ R.facePolygonalCircle (G := G') f
      faceFillingMap := fun f ↦ (R.facePLFilling (G := G') f).map
      faceMap_eq := fun _ _ ↦ rfl
      faceCertificate := fun f ↦ (R.facePLFilling (G := G') f).certificate
      faceClosedRegion_subset := fun f ↦ H.closedRegions_mem_region f
      faceCarrier_eq := fun f ↦ R.polygonalReplacementComplex_faceCarrier H f }
  let sourceParent (a : T.toIntrinsic.AdaptiveFanFace U hU) :
      T.toIntrinsic.Face := by
    let Rt := T.toIntrinsic.safeSubdivision a.1.1
    let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
    exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q :=
    { Tile := T.toIntrinsic.AdaptiveFace U
      tileDecidableEq := Classical.decEq _
      tile := fun f ↦ f.1
      tileFaces := T.toIntrinsic.adaptiveFanFacesOver U hU
      mem_tileFaces := fun t f ↦
        T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t f
      sourceTileCarrier := T.toIntrinsic.adaptiveFaceCarrier U
      sourceTileCarrier_subset_open := fun t ↦
        T.toIntrinsic.adaptiveFaceCarrier_subset U t
      sourceTileCarrier_locallyFinite :=
        T.toIntrinsic.locallyFinite_adaptiveFaceCarrierInOpen U hU
      sourceTileCarrier_eq_faces := by
        intro t
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨i, j, z, hz⟩ :=
            T.toIntrinsic.exists_adaptiveFanFaceMap_eq_of_mem_adaptiveFaceCarrier
              U hU t hx
          let a : T.toIntrinsic.AdaptiveFanFace U hU := ⟨t, i, j⟩
          have ha : a ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t :=
            (T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a).2 rfl
          let a' : {f : Q.complex.Face //
              f ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t} := ⟨a, ha⟩
          apply Set.mem_iUnion.mpr
          refine ⟨a', ?_⟩
          let hxU : x ∈ U := T.toIntrinsic.adaptiveFaceCarrier_subset U t hx
          refine ⟨hxU, ?_⟩
          apply (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
            (eU ⟨x, hxU⟩)).2
          change ⟨x, hxU⟩ ∈ R.faceCarrier a
          change ⟨x, hxU⟩ ∈
            Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a)
          rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a]
          exact ⟨z, hz⟩
        · intro x hx
          obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
          obtain ⟨hxU, hxaQ⟩ := hxa
          have hxaR := (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a.1
            (eU ⟨x, hxU⟩)).1 hxaQ
          change ⟨x, hxU⟩ ∈
            Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a.1) at hxaR
          rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a.1] at hxaR
          have hxt :=
            T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a.1 hxaR
          change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1.1 at hxt
          rw [(T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a.1).1 a.2] at hxt
          exact hxt
      sourceFaceParent := sourceParent
      sourceFaceSet_subset_parent := by
        intro a x hx
        change T.toIntrinsic.AdaptiveFanFace U hU at a
        obtain ⟨hxU, hxaQ⟩ := hx
        have hxaR :=
          (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
            (eU ⟨x, hxU⟩)).1 hxaQ
        change ⟨x, hxU⟩ ∈
          Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a) at hxaR
        rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a] at hxaR
        have hxt :=
          T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a hxaR
        change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1 at hxt
        obtain ⟨z, hz, hzx⟩ := hxt
        let Rt := T.toIntrinsic.safeSubdivision a.1.1
        let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
        have hzParent :=
          (Classical.choose_spec h).2 z hz
        change x ∈ T.toIntrinsic.faceCarrier (sourceParent a).1
        change x ∈ T.toIntrinsic.faceCarrier (Classical.choose h)
        rw [← hzx]
        exact hzParent
      sourceFaceStandardAffine := by
        intro a
        change T.toIntrinsic.AdaptiveFanFace U hU at a
        obtain ⟨b, hb⟩ :=
          T.toIntrinsic.adaptiveGlobalFanFaceMap_standardAffine hU a
        refine ⟨b, ?_⟩
        intro x
        have hsource :
            q.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                (K := P) a x) =
              eU.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                (K := R) a x) := by
          change
            eU.symm
                ((R.polygonalReplacementHomeomorph H).symm
                  (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                    (K := P) a x)) =
              eU.symm
                (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
                  (K := R) a x)
          congr 1
          exact R.polygonalReplacementInverse_faceToSupport H a x
        change
          (q.symm
            (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
              (K := P) a x)).1.1 =
            b (P.facePlaneHomeomorph a x).1
        rw [hsource]
        change
          (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a x).1.1 =
            b ((T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex U hU
              ).facePlaneHomeomorph a x).1
        exact hb x
      commonLevel := T.toIntrinsic.adaptiveFaceCommonLevel U
      levelFaces := fun F ↦
        (Finset.univ : Finset
          (T.toIntrinsic.LevelFace (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
          fun u ↦ ∃ t ∈ F,
            T.toIntrinsic.levelFaceCarrier u ⊆
              T.toIntrinsic.adaptiveFaceCarrier U t
      sourceTiles_eq_levelFaces := by
        intro F
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
          rw [T.toIntrinsic.adaptiveFaceCarrier_eq_iUnion_commonLevel_descendants
            U F t.2] at hxt
          obtain ⟨u, hxt⟩ := Set.mem_iUnion.mp hxt
          obtain ⟨hut, hxu⟩ := Set.mem_iUnion.mp hxt
          let u' : {u : T.toIntrinsic.LevelFace
              (T.toIntrinsic.adaptiveFaceCommonLevel U F) //
              u ∈ (Finset.univ : Finset
                (T.toIntrinsic.LevelFace
                  (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
                (fun u ↦ ∃ t ∈ F,
                  T.toIntrinsic.levelFaceCarrier u ⊆
                    T.toIntrinsic.adaptiveFaceCarrier U t)} :=
            ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t.1, t.2, hut⟩⟩⟩
          exact Set.mem_iUnion.mpr ⟨u', hxu⟩
        · intro x hx
          obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hx
          obtain ⟨-, t, htF, hut⟩ := Finset.mem_filter.mp u.2
          let t' : {t : T.toIntrinsic.AdaptiveFace U // t ∈ F} := ⟨t, htF⟩
          exact Set.mem_iUnion.mpr ⟨t', hut hxu⟩ }
  have hqmodel : ∀ y : U, (q y).1.1 ∈ c.kind.modelRegion := by
    intro y
    cases hk : c.kind with
    | disk =>
        simpa [ChartKind.modelRegion, ChartKind.perturbationRegion, hk] using
          (q y).1.2
    | halfDisk =>
        have hfHalf : Set.range f ⊆ HalfPlaneSet := by
          rintro z ⟨x, rfl⟩
          have hx := (T.chartOverlapModelMap c x).2
          change f x ∈ c.kind.modelRegion at hx
          rw [hk] at hx
          simpa [ChartKind.modelRegion, HalfPlaneSet] using hx.2
        have hgraph : Set.range G'.graphReplacementMap ⊆ HalfPlaneSet := by
          apply IntrinsicTwoComplex.ControlledAdaptiveComplex.range_graphReplacementMap_subset_halfPlane
            T.toIntrinsic U hU f hf (regionSafeControl V f mu)
              (stronglyPositiveOn_regionSafeControl hV hf hmem hmu) G'
          · intro p
            rfl
          · exact hfHalf
        have hhalf : (q y).1.1 ∈ HalfPlaneSet := by
          exact LocallyFiniteTriangleComplex.polygonalReplacementHomeomorph_mem_halfPlane
            G' H hgraph (eU y)
        exact ⟨by
            simpa [V, ChartKind.perturbationRegion, hk] using (q y).1.2,
          by simpa [HalfPlaneSet] using hhalf⟩
  let g' : U → c.kind.modelRegion := fun y ↦ ⟨(q y).1.1, hqmodel y⟩
  let g : T.toIntrinsic.realization → S := fun x ↦
    if hx : x ∈ U then (c.chart.symm (g' ⟨x, hx⟩)).1 else T.embed x
  have hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1 := by
    intro y
    simp [g, y.2]
  have hgclose : ∀ y : U,
      dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y := by
    intro y
    change dist (q y).1.1 (f y) ≤ mu y
    have h := hclose (eU y)
    change dist (q y).1.1 (G.map (eU y)) ≤ mu y at h
    rw [hGmap] at h
    exact h
  have hgmatch : MatchesAtFrontier U g T.embed := by
    exact hmatch g' g hgval hgclose
  have hgcont : ContinuousOn g U := by
    have hg'cont : Continuous g' := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_subtype_val.comp q.continuous))
    have hcomp : Continuous (fun y : U ↦ (c.chart.symm (g' y)).1) :=
      continuous_subtype_val.comp (c.chart.symm.continuous.comp hg'cont)
    rw [continuousOn_iff_continuous_restrict]
    exact hcomp.congr fun y ↦ (hgval y).symm
  have hginj : Set.InjOn g U := by
    intro x hx y hy hxy
    let xU : U := ⟨x, hx⟩
    let yU : U := ⟨y, hy⟩
    have hchart : c.chart.symm (g' xU) = c.chart.symm (g' yU) := by
      apply Subtype.ext
      rw [← hgval xU, ← hgval yU]
      exact hxy
    have hg'eq : g' xU = g' yU := c.chart.symm.injective hchart
    have hqeq : q xU = q yU := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : c.kind.modelRegion => (z : Plane)) hg'eq
    exact congrArg Subtype.val (q.injective hqeq)
  have hcross : Disjoint (g '' U) (T.embed '' Uᶜ) := by
    apply T.disjoint_image_chartOverlap_embed_compl c
    intro x hx
    rw [hgval ⟨x, hx⟩]
    exact (c.chart.symm (g' ⟨x, hx⟩)).2
  have hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed) :=
    isEmbedding_frontierGlue_of_matches hU hgcont T.isEmbedding.continuous
      hgmatch hginj T.isEmbedding.injective hcross
  exact ⟨Q, A, g', g, fun _ ↦ rfl, hgval, hgmatch, hgcont, hginj, hcross, hembed⟩

open PartialTriangulation.PolygonalReplacementSourceAtlas

/-- **Theorem boundary** (Moise Ch. 8, Thm. 3, crossing-case preparation).

In the genuine crossing case (the chart core is not yet covered, and the absorbed region is not
inside the chart patch), the adjusted old complex and the chart patch admit a common welded
presentation: a common vertex type carrying both face families, with embeddings that agree
exactly on the shared realization, satisfy the combinatorial-surface bound jointly, and whose
united image contains `A ∪ c.core` in its topological interior.

The intended proof is the machinery already in place: straighten the old complex over the
chart overlap by the locally finite controlled polygonal replacement over
`adaptiveOverlapGraphRealization` with tolerance vanishing at the overlap frontier
(`replaceOnOpen`/`frontierGlue`), refine the straightened trace and the fixed patch complex to
a common plane subdivision (`CommonSubdivision`, Moise's conditions (e)-(h)), and read off the
welded presentation.  Per `docs/MOISE_ROUTE.md`, the finite compact-collar theorem must not be
silently substituted for the vanishing-tolerance construction. -/
theorem MoiseChart.exists_crossing_weld (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A)
    (hcore : ¬ c.core ⊆ interior T.support)
    (hA : ¬ A ⊆ interior c.patchPartialTriangulation.support) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
  classical
  letI : SecondCountableTopology S := moise_secondCountableTopology S
  -- Protect a genuine closed neighborhood of the old cores, not merely the cores pointwise.
  -- This makes the old half of the final coverage invariant tautological after straightening.
  obtain ⟨C, hCclosed, hAC, hCT⟩ := hT.exists_closedBuffer
  obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
      hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
      hembed⟩ :=
    T.exists_straightenedChartAway c C hCclosed
  let T₀ : PartialTriangulation S := T.replaceOnOpen U g hembed
  have hA₀ : A ⊆ interior T₀.support := by
    change A ⊆ interior (Set.range (frontierGlue U g T.embed))
    exact T.subset_interior_range_frontierGlue_of_fixedOn U g hAC
      (hCT.trans interior_subset) hgfix
  -- At an ambient-interior point of the protected trace, ordinary invariance of domain and
  -- pointwise fixation already retain the physical point in the new support.
  have hProtectedInteriorPoint :
      c.core ∩ C ∩
          (modelWithCornersEuclideanHalfSpace 2).interior S ⊆
        interior T₀.support := by
    rintro x ⟨⟨hxCore, hxC⟩, hxi⟩
    change x ∈ interior (Set.range (frontierGlue U g T.embed))
    apply
      T.subset_interior_range_frontierGlue_of_fixedOn_of_isInteriorPoint
        U g hembed (A := {x})
    · simpa only [Set.singleton_subset_iff] using hCT hxC
    · intro z hz
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact hxi
    · intro y hy
      apply hgfix y
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxC
    · exact Set.mem_singleton x
  -- This is the remaining bordered form of Moise conditions (a)--(c): the relative
  -- polygonal replacement must preserve the fixed manifold-boundary stratum.  The
  -- half-plane doubling theorem in `BoundaryInvariant.lean` proves the required relative
  -- invariance of domain once exact boundary-line preservation of the replacement has been
  -- extracted from the synchronized arrangement.
  have hBoundaryPreservation :
      ∀ y : T.toIntrinsic.realization,
        frontierGlue U g T.embed y ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          T.embed y ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S := by
    sorry
  have hProtectedBoundaryPoint :
      c.core ∩ C ∩
          (modelWithCornersEuclideanHalfSpace 2).boundary S ⊆
        interior T₀.support := by
    rintro x ⟨⟨hxCore, hxC⟩, hxBoundary⟩
    obtain ⟨y, hy⟩ := interior_subset (hCT hxC)
    change T.toIntrinsic.realization at y
    have hyFixed :
        frontierGlue U g T.embed y = T.embed y := by
      by_cases hyU : y ∈ U
      · rw [frontierGlue_of_mem hyU, hgfix y]
        simpa only [hy] using hxC
      · rw [frontierGlue_of_notMem hyU]
    cases hk : c.kind with
    | disk =>
        exact False.elim <|
          (hc.1 hk x (c.core_subset_domain hxCore)) hxBoundary
    | halfDisk =>
        have hmodel :
            c.kind.modelRegion = ChartKind.halfDisk.modelRegion := by
          rw [hk]
        let chartHalf :
            c.domain ≃ₜ ChartKind.halfDisk.modelRegion :=
          c.chart.trans (Homeomorph.setCongr hmodel)
        have hchartHalfBoundary :
            ∀ z (hz : z ∈ c.domain),
              z ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
                ((chartHalf ⟨z, hz⟩ : Plane) 0 = 0) := by
          intro z hz
          have h := hc.2 hk z hz
          have hcoord :
              (((Homeomorph.setCongr hmodel)
                (c.chart ⟨z, hz⟩) :
                  ChartKind.halfDisk.modelRegion) : Plane) =
                (c.chart ⟨z, hz⟩ : Plane) := by
            exact congrArg Subtype.val
              (Equiv.setCongr_apply hmodel (c.chart ⟨z, hz⟩))
          change
            z ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
              (((Homeomorph.setCongr hmodel)
                (c.chart ⟨z, hz⟩) :
                  ChartKind.halfDisk.modelRegion) : Plane) 0 = 0
          rw [hcoord]
          exact h
        change x ∈ interior
          (Set.range (frontierGlue U g T.embed))
        have hopen :=
          mem_interior_range_of_fixed_boundary_preserving_in_halfDiskChart
            c.domain c.isOpen_domain
            chartHalf hchartHalfBoundary
            T.isEmbedding hembed hBoundaryPreservation
            (x := y) (by
              change T.embed y ∈ interior (Set.range T.embed)
              rw [hy]
              exact hCT hxC)
            (by
              rw [hy]
              exact c.core_subset_domain hxCore)
            hyFixed
        rwa [hy] at hopen
  have hProtectedCore :
      c.core ∩ C ⊆ interior T₀.support := by
    rintro x ⟨hxCore, hxC⟩
    rcases
        (modelWithCornersEuclideanHalfSpace 2).isInteriorPoint_or_isBoundaryPoint x with
      hxi | hxb
    · exact hProtectedInteriorPoint ⟨⟨hxCore, hxC⟩, hxi⟩
    · exact hProtectedBoundaryPoint ⟨⟨hxCore, hxC⟩, hxb⟩
  -- Choose the target from the *actual* compact remainder after straightening.  This is the
  -- correct replacement for the false assertion that every point of the old physical
  -- interior remains in the physical interior after an arbitrary small re-embedding.
  let D : Set S := c.core \ interior T₀.support
  have hDcompact : IsCompact D :=
    c.isCompact_core.diff isOpen_interior
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
  let dToDomain : D → c.domain :=
    fun x ↦ ⟨x.1, c.core_subset_domain x.2.1⟩
  let dModel : D → c.kind.modelRegion :=
    fun x ↦ c.chart (dToDomain x)
  let dCoord : D → Plane :=
    fun x ↦ (dModel x : Plane)
  have hdCoord_cont : Continuous dCoord := by
    exact continuous_subtype_val.comp
      (c.chart.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
  let Dcoord : Set Plane := Set.range dCoord
  have hDcoordCompact : IsCompact Dcoord :=
    isCompact_range hdCoord_cont
  have hdModel_cont : Continuous dModel :=
    c.chart.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _)
  let Dmodel : Set c.kind.modelRegion := Set.range dModel
  have hDmodelCompact : IsCompact Dmodel :=
    isCompact_range hdModel_cont
  have hDcoordPatch :
      Dcoord ⊆ c.kind.patchComplex.support := by
    rintro p ⟨x, rfl⟩
    apply c.kind.modelCore_subset_patchComplex_support
    obtain ⟨hxDomain, hxCore⟩ := c.mem_core_iff.mp x.2.1
    have hdomain :
        (⟨x.1, hxDomain⟩ : c.domain) = dToDomain x :=
      Subtype.ext rfl
    simpa [dCoord, dModel, hdomain] using hxCore
  have hDcoordV : Dcoord ⊆ V := by
    rintro p ⟨x, rfl⟩
    by_contra hpV
    have hxC : (c.chart.symm (c.chart (dToDomain x))).1 ∈ C := by
      apply hVavoid (c.chart (dToDomain x))
      simpa [dCoord, dModel] using hpV
    have hxC' : x.1 ∈ C := by
      simpa only [c.chart.symm_apply_apply] using hxC
    exact x.2.2 (hProtectedCore ⟨x.2.1, hxC'⟩)
  -- Thicken the compact remainder inside the *model-region* topology.  This is the correct
  -- topology at the boundary line of a half-disk chart: such points are interior in the
  -- surface even though they are not interior in the ambient plane.
  let Vmodel : Set c.kind.modelRegion := {p | (p : Plane) ∈ V}
  let patchModel : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ c.kind.patchComplex.support}
  have hVmodelOpen : IsOpen Vmodel :=
    hV.preimage continuous_subtype_val
  have htargetOpen : IsOpen (Vmodel ∩ interior patchModel) :=
    hVmodelOpen.inter isOpen_interior
  have hDmodelTarget : Dmodel ⊆ Vmodel ∩ interior patchModel := by
    rintro p ⟨x, rfl⟩
    constructor
    · exact hDcoordV ⟨x, rfl⟩
    · apply c.kind.modelCore_subset_interior_patchInRegion
      obtain ⟨hxDomain, hxCore⟩ := c.mem_core_iff.mp x.2.1
      have hdomain :
          (⟨x.1, hxDomain⟩ : c.domain) = dToDomain x :=
        Subtype.ext rfl
      simpa [dModel, patchModel, hdomain] using hxCore
  letI : LocallyCompactSpace c.kind.modelRegion :=
    c.kind.modelRegionLocallyCompactSpace
  obtain ⟨E, hEcompact, hDmodelInteriorE, hEtarget⟩ :=
    exists_compact_between hDmodelCompact htargetOpen hDmodelTarget
  let Ecoord : Set Plane := Subtype.val '' E
  have hEcoordCompact : IsCompact Ecoord :=
    hEcompact.image continuous_subtype_val
  have hEcoordPatch : Ecoord ⊆ c.kind.patchComplex.support := by
    rintro p ⟨q, hqE, rfl⟩
    have hqPatch : q ∈ patchModel :=
      interior_subset (hEtarget hqE).2
    exact hqPatch
  have hEcoordV : Ecoord ⊆ V := by
    rintro p ⟨q, hqE, rfl⟩
    exact (hEtarget hqE).1
  let L : c.kind.patchComplex.OpenSubmesh Ecoord V :=
    Classical.choice
      (c.kind.patchComplex.exists_openSubmesh c.kind.patchComplex_pure
        hEcoordCompact hEcoordPatch hV hEcoordV)
  let N : TriangleMesh := L.mesh
  have hN_V : N.toPlaneComplex.support ⊆ V :=
    L.contained
  have hN_patch :
      N.toPlaneComplex.support ⊆ c.kind.patchComplex.support :=
    L.support_subset_original
  have hDmodelInteriorN :
      Dmodel ⊆ interior {p : c.kind.modelRegion |
        (p : Plane) ∈ N.toPlaneComplex.support} := by
    apply hDmodelInteriorE.trans
    apply interior_mono
    intro p hpE
    exact L.covers ⟨p, hpE, rfl⟩
  have hDcoordN : Dcoord ⊆ N.toPlaneComplex.support := by
    rintro p ⟨x, rfl⟩
    have hxSupport :
        dModel x ∈ {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support} :=
      interior_subset (hDmodelInteriorN ⟨x, rfl⟩)
    exact hxSupport
  -- Regard the whole selected target support as a compact subset of `V`; closing the
  -- replacement faces which meet it under adaptive tiles gives the finite old-side source
  -- subcomplex that the relative coning step must extend.
  let CN : Set V := {p | p.1 ∈ N.toPlaneComplex.support}
  have hCNcompact : IsCompact CN := by
    apply _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      N.toPlaneComplex.isCompact_support
    intro p hp
    exact ⟨⟨p, hN_V hp⟩, rfl⟩
  have hN_arrangement :
      N.toPlaneComplex.support ⊆
        (PolygonalFamily.arrangementMesh
          (Qatlas.tileFacePolygonMeeting CN hCNcompact)).toPlaneComplex.support :=
    hN_patch.trans
      (PartialTriangulation.SynchronizedPatch.patchComplex_support_subset_arrangementMesh
        c.kind (Qatlas.tileFacePolygonMeeting CN hCNcompact))
  have hN_model :
      N.toPlaneComplex.support ⊆ c.kind.modelRegion :=
    hN_patch.trans c.kind.patchComplex_support_subset_modelRegion
  let J := Qatlas.tileFacePolygonMeeting CN hCNcompact
  let n := Qatlas.commonLevel (Qatlas.tilesMeeting CN hCNcompact)
  let Rlevel := T.toIntrinsic.safeSubdivision n
  have hRlevelSurface : Rlevel.refined.HasSurfaceEdgeValence := by
    apply T.toIntrinsic.hasSurfaceEdgeValence_iteratedMidpointSubdivision
    intro e he
    exact hT.combSurface e he
  let selectedLevelFaces :=
    Qatlas.levelFaces (Qatlas.tilesMeeting CN hCNcompact)
  let edgeHalf : Set.Icc (0 : ℝ) 1 :=
    ⟨1 / 2, by constructor <;> norm_num⟩
  let LevelAnchor :=
    Σ u : {u : T.toIntrinsic.LevelFace n // u ∈ selectedLevelFaces},
      Sum {v // v ∈ u.1.1} (ZMod 3)
  let anchorLevelPoint : LevelAnchor → Rlevel.refined.realization :=
    fun a ↦
      match a.2 with
      | Sum.inl v => Rlevel.refined.facePoint a.1.1 v
      | Sum.inr i =>
          Rlevel.refined.edgePath
            (Rlevel.refined.faceEdge a.1.1 i) edgeHalf
  let anchorSourcePoint : LevelAnchor → T.toIntrinsic.realization :=
    fun a ↦ Rlevel.homeo (anchorLevelPoint a)
  have hAnchorSelected (a : LevelAnchor) :
      anchorSourcePoint a ∈
        ⋃ u : {u : T.toIntrinsic.LevelFace n // u ∈ selectedLevelFaces},
          T.toIntrinsic.levelFaceCarrier u.1 := by
    rcases a with ⟨s, v | i⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨s, Rlevel.refined.facePoint s.1 v, ?_, rfl⟩
      exact Rlevel.refined.facePoint_mem_faceCarrier s.1 v
    · have hedge :
          Rlevel.refined.edgePath
              (Rlevel.refined.faceEdge s.1 i) edgeHalf ∈
            Rlevel.refined.faceCarrier
              (Rlevel.refined.faceEdge s.1 i).1 := by
        rw [← Rlevel.refined.range_edgePath]
        exact ⟨edgeHalf, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨s,
        Rlevel.refined.edgePath
          (Rlevel.refined.faceEdge s.1 i) edgeHalf, ?_, rfl⟩
      intro v hv
      exact hedge v (fun hve ↦
        hv (Rlevel.refined.faceEdge_subset_face s.1 i hve))
  have hAnchorU (a : LevelAnchor) : anchorSourcePoint a ∈ U := by
    apply Qatlas.sourceTileFacesMeeting_subset_open CN hCNcompact
    rw [Qatlas.sourceTileFacesMeeting_eq_levelFaces CN hCNcompact]
    exact hAnchorSelected a
  let anchorCoordinate : LevelAnchor → Plane :=
    fun a ↦
      (Q.sourceHomeomorph
        ⟨anchorSourcePoint a, hAnchorU a⟩).1.1
  let anchorLines : List (Plane →ᵃ[ℝ] ℝ) :=
    PartialTriangulation.PolygonalReplacementSourceAtlas.coordinateAnchorLines
      anchorCoordinate
  let baseOldMesh :=
    Qatlas.tileFacesMeetingRelativeOldMesh CN hCNcompact N anchorLines
  let alignmentLines : List (Plane →ᵃ[ℝ] ℝ) :=
    Qatlas.relativeLevelAlignmentLines
      CN hCNcompact N anchorLines n
  let extraLines : List (Plane →ᵃ[ℝ] ℝ) :=
    anchorLines ++ baseOldMesh.coordinateLines ++ alignmentLines
  let lines := Qatlas.tileFaceMeetingLines CN hCNcompact N extraLines
  have hJmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion :=
    Qatlas.tileFacePolygonMeeting_closedRegion_subset_modelRegion
      c CN hCNcompact g' hgcoord
  let e₁local :=
    PartialTriangulation.RelativeSynchronizedTarget.oldSurfaceEmbed
      c J N lines hJmodel
  have he₁local : _root_.Topology.IsEmbedding e₁local :=
    PartialTriangulation.RelativeSynchronizedTarget.isEmbedding_oldSurfaceEmbed
      c J N lines hJmodel
  let source₁ :=
    Qatlas.tileFacesMeetingRelativeSourceEmbed CN hCNcompact N extraLines
  have hsource₁Embedding : _root_.Topology.IsEmbedding source₁ :=
    Qatlas.isEmbedding_tileFacesMeetingRelativeSourceEmbed
      CN hCNcompact N extraLines
  have hsource₁Range :
      Set.range source₁ =
        ⋃ u : {u : T.toIntrinsic.LevelFace
            (Qatlas.commonLevel (Qatlas.tilesMeeting CN hCNcompact)) //
            u ∈ Qatlas.levelFaces (Qatlas.tilesMeeting CN hCNcompact)},
          T.toIntrinsic.levelFaceCarrier u.1 :=
    Qatlas.range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces
      CN hCNcompact N extraLines
  let localSourceComplex :=
    Qatlas.tileFacesMeetingRelativeSourceComplex CN hCNcompact N extraLines
  let localOldMesh :=
    Qatlas.tileFacesMeetingRelativeOldMesh CN hCNcompact N extraLines
  have exists_baseTriangle_of_localOldTriangle
      (t : localOldMesh.Triangle) :
      ∃ u : baseOldMesh.Triangle,
        localOldMesh.triangleCarrier t.1 ⊆
          baseOldMesh.triangleCarrier u.1 := by
    let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
    have htR :
        t.1 ∈ R.triangles :=
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp t.2 |>.1
    let tR : R.Triangle := ⟨t.1, htR⟩
    have hBaseLines :
        ∀ a ∈ baseOldMesh.coordinateLines,
          a ∈ N.coordinateLines ++ lines := by
      intro a ha
      apply List.mem_append_right
      change a ∈
        Qatlas.tileFaceMeetingCertificateLines CN hCNcompact N ++
          extraLines
      apply List.mem_append_right
      change a ∈
        (anchorLines ++ baseOldMesh.coordinateLines) ++ alignmentLines
      exact List.mem_append_left _
        (List.mem_append_right _ ha)
    have hhit :
        (interior (R.triangleCarrier tR.1) ∩
          baseOldMesh.toPlaneComplex.support).Nonempty := by
      obtain ⟨p, hp⟩ := R.interior_triangleCarrier_nonempty tR
      refine ⟨p, hp, ?_⟩
      rw [Qatlas.tileFacesMeetingRelativeOldMesh_support
        CN hCNcompact N anchorLines,
        ← Qatlas.tileFacesMeetingRelativeOldMesh_support
          CN hCNcompact N extraLines]
      rw [localOldMesh.toPlaneComplex_support]
      exact Set.mem_iUnion.mpr
        ⟨t.1, Set.mem_iUnion.mpr ⟨t.2, interior_subset hp⟩⟩
    obtain ⟨u, hu⟩ :=
      (PolygonalFamily.arrangementMesh J
        ).exists_target_triangle_of_refineByLines_of_interior_inter_support
          baseOldMesh (N.coordinateLines ++ lines)
          hBaseLines tR hhit
    exact ⟨u, hu⟩
  have exists_levelFace_of_localOldTriangle
      (t : localOldMesh.Triangle) :
      ∃ s : {s : T.toIntrinsic.LevelFace n // s ∈ selectedLevelFaces},
        ∀ (p : Plane) (hp : p ∈ localOldMesh.triangleCarrier t.1),
          source₁
              (Qatlas.relativeOldTrianglePoint
                CN hCNcompact N extraLines t ⟨p, hp⟩) ∈
            T.toIntrinsic.levelFaceCarrier s.1 := by
    obtain ⟨u, htu⟩ := exists_baseTriangle_of_localOldTriangle t
    obtain ⟨p, hp⟩ := localOldMesh.interior_triangleCarrier_nonempty t
    have hpBase : p ∈ interior (baseOldMesh.triangleCarrier u.1) :=
      interior_mono htu hp
    let pLocal :
        {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} :=
      ⟨p, interior_subset hp⟩
    let pBase :
        {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
      ⟨p, interior_subset hpBase⟩
    let xLocal :=
      Qatlas.relativeOldTrianglePoint
        CN hCNcompact N extraLines t pLocal
    let xBase :=
      Qatlas.relativeOldTrianglePoint
        CN hCNcompact N anchorLines u pBase
    have hsourceEq :
        Qatlas.tileFacesMeetingRelativeSourceEmbed
            CN hCNcompact N anchorLines xBase =
          source₁ xLocal := by
      apply
        Qatlas.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq
          CN hCNcompact N xBase xLocal
      rw [Qatlas.relativeOldTrianglePoint_coordinateEmbed
          CN hCNcompact N anchorLines u pBase,
        Qatlas.relativeOldTrianglePoint_coordinateEmbed
          CN hCNcompact N extraLines t pLocal]
    have hxUnion :
        source₁ xLocal ∈
          ⋃ s : {s : T.toIntrinsic.LevelFace n // s ∈ selectedLevelFaces},
            T.toIntrinsic.levelFaceCarrier s.1 := by
      rw [← hsource₁Range]
      exact Set.mem_range_self xLocal
    obtain ⟨s, hsSource⟩ := Set.mem_iUnion.mp hxUnion
    obtain ⟨q, hqFace, hqSource⟩ := hsSource
    have hbaseMem :
        source₁ xLocal ∈
          T.toIntrinsic.faceCarrier
            (Qatlas.relativeOldTriangleParent
              CN hCNcompact N anchorLines u).1 := by
      rw [← hsourceEq]
      exact Qatlas.relativeOldTriangleParent_contains
        CN hCNcompact N anchorLines u xBase
        (Qatlas.relativeOldTrianglePoint_supported
          CN hCNcompact N anchorLines u pBase)
    have hlevelMem :
        source₁ xLocal ∈
          T.toIntrinsic.faceCarrier
            (levelFaceParent T.toIntrinsic s.1).1 := by
      have h :=
        levelFaceParent_contains T.toIntrinsic s.1 q hqFace
      rw [hqSource] at h
      exact h
    let F :=
      Qatlas.relativeOldTriangleParentPlaneAffine
        CN hCNcompact N anchorLines u
    have hFimage :
        F '' interior (baseOldMesh.triangleCarrier u.1) ⊆
          standardTrianglePlaneComplex.support := by
      rintro z ⟨r, hr, rfl⟩
      let rBase :
          {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
        ⟨r, interior_subset hr⟩
      rw [Qatlas.relativeOldTriangleParentPlaneAffine_eq
        CN hCNcompact N anchorLines u rBase]
      exact
        (T.toIntrinsic.facePlaneHomeomorph
          (Qatlas.relativeOldTriangleParent
            CN hCNcompact N anchorLines u) _).2
    have hFopen :
        IsOpen (F '' interior (baseOldMesh.triangleCarrier u.1)) :=
      (F.isOpenMap F.continuous_of_finiteDimensional
        (Qatlas.relativeOldTriangleParentPlaneAffine_surjective
          CN hCNcompact N anchorLines u))
        (interior (baseOldMesh.triangleCarrier u.1)) isOpen_interior
    have hpFint :
        F p ∈ interior standardTrianglePlaneComplex.support := by
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset
        (hFopen.mem_nhds ⟨p, hpBase, rfl⟩) hFimage
    have hpChartInt :
        (T.toIntrinsic.facePlaneHomeomorph
          (Qatlas.relativeOldTriangleParent
            CN hCNcompact N anchorLines u)
          ⟨source₁ xLocal, hbaseMem⟩).1 ∈
            interior standardTrianglePlaneComplex.support := by
      have heq :
          (T.toIntrinsic.facePlaneHomeomorph
            (Qatlas.relativeOldTriangleParent
              CN hCNcompact N anchorLines u)
            ⟨source₁ xLocal, hbaseMem⟩).1 = F p := by
        have hbaseMem' :
            Qatlas.tileFacesMeetingRelativeSourceEmbed
                CN hCNcompact N anchorLines xBase ∈
              T.toIntrinsic.faceCarrier
                (Qatlas.relativeOldTriangleParent
                  CN hCNcompact N anchorLines u).1 :=
          Qatlas.relativeOldTriangleParent_contains
            CN hCNcompact N anchorLines u xBase
            (Qatlas.relativeOldTrianglePoint_supported
              CN hCNcompact N anchorLines u pBase)
        have hclosed :
            (⟨Qatlas.tileFacesMeetingRelativeSourceEmbed
                  CN hCNcompact N anchorLines xBase, hbaseMem'⟩ :
                T.toIntrinsic.ClosedFace
                  (Qatlas.relativeOldTriangleParent
                    CN hCNcompact N anchorLines u)) =
              ⟨source₁ xLocal, hbaseMem⟩ :=
          Subtype.ext hsourceEq
        calc
          (T.toIntrinsic.facePlaneHomeomorph
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)
              ⟨source₁ xLocal, hbaseMem⟩).1 =
              (T.toIntrinsic.facePlaneHomeomorph
                (Qatlas.relativeOldTriangleParent
                  CN hCNcompact N anchorLines u)
                ⟨Qatlas.tileFacesMeetingRelativeSourceEmbed
                    CN hCNcompact N anchorLines xBase, hbaseMem'⟩).1 :=
            congrArg (fun w => w.1)
              (congrArg
                (T.toIntrinsic.facePlaneHomeomorph
                  (Qatlas.relativeOldTriangleParent
                    CN hCNcompact N anchorLines u)) hclosed.symm)
          _ = F p :=
            (Qatlas.relativeOldTriangleParentPlaneAffine_eq
              CN hCNcompact N anchorLines u pBase).symm
      rw [heq]
      exact hpFint
    have hparent :
        levelFaceParent T.toIntrinsic s.1 =
          Qatlas.relativeOldTriangleParent
            CN hCNcompact N anchorLines u := by
      symm
      exact face_eq_of_mem_faceCarriers_of_facePlane_mem_interior
        T.toIntrinsic
        (Qatlas.relativeOldTriangleParent
          CN hCNcompact N anchorLines u)
        (levelFaceParent T.toIntrinsic s.1)
        (source₁ xLocal) hbaseMem hlevelMem hpChartInt
    let z : standardTrianglePlaneComplex.support :=
      Rlevel.refined.facePlaneHomeomorph s.1 ⟨q, hqFace⟩
    have hplaneAtP :
        F p =
          levelFaceParentPlaneAffine T.toIntrinsic s.1 z.1 := by
      have hbase :=
        Qatlas.relativeOldTriangleParentPlaneAffine_eq
          CN hCNcompact N anchorLines u pBase
      have hlevel :=
        levelFaceParentPlaneAffine_eq T.toIntrinsic s.1 z
      rw [T.toIntrinsic.facePlaneHomeomorph_val_eq_forwardAffine] at hbase hlevel
      have hqback :
          ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1 = q := by
        change
          ((Rlevel.refined.facePlaneHomeomorph s.1).symm
              ((Rlevel.refined.facePlaneHomeomorph s.1) ⟨q, hqFace⟩)).1 =
            q
        exact congrArg Subtype.val
          ((Rlevel.refined.facePlaneHomeomorph s.1
            ).symm_apply_apply ⟨q, hqFace⟩)
      have hhomeoBack :
          (Rlevel.homeo
              ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1).1 =
            (Rlevel.homeo q).1 :=
        congrArg Subtype.val (congrArg Rlevel.homeo hqback)
      have hlevel' :
          levelFaceParentPlaneAffine T.toIntrinsic s.1 z.1 =
            T.toIntrinsic.facePlaneForwardAffine
              (levelFaceParent T.toIntrinsic s.1)
              (Rlevel.homeo q).1 := by
        calc
          levelFaceParentPlaneAffine T.toIntrinsic s.1 z.1 =
              T.toIntrinsic.facePlaneForwardAffine
                (levelFaceParent T.toIntrinsic s.1)
                (Rlevel.homeo
                  ((Rlevel.refined.facePlaneHomeomorph s.1).symm z).1).1 :=
            hlevel
          _ =
              T.toIntrinsic.facePlaneForwardAffine
                (levelFaceParent T.toIntrinsic s.1)
                (Rlevel.homeo q).1 :=
            congrArg
              (T.toIntrinsic.facePlaneForwardAffine
                (levelFaceParent T.toIntrinsic s.1)) hhomeoBack
      calc
        F p =
            T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)
              (Qatlas.tileFacesMeetingRelativeSourceEmbed
                CN hCNcompact N anchorLines xBase).1 :=
          hbase
        _ =
            T.toIntrinsic.facePlaneForwardAffine
              (levelFaceParent T.toIntrinsic s.1)
              (Rlevel.homeo q).1 := by
          rw [hparent]
          apply congrArg
            (T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u))
          exact congrArg Subtype.val
            (hsourceEq.trans hqSource.symm)
        _ = levelFaceParentPlaneAffine T.toIntrinsic s.1 z.1 :=
          hlevel'.symm
    have hmono (k : Fin 3) :
        localOldMesh.IsMonochromatic
          ((levelFaceParentCoord T.toIntrinsic s.1 k).comp F) := by
      have haAlign :
          (levelFaceParentCoord T.toIntrinsic s.1 k).comp F ∈
            alignmentLines := by
        exact Qatlas.relativeLevelAlignmentLine_mem
          CN hCNcompact N anchorLines n u s.1 hparent k
      have haExtra :
          (levelFaceParentCoord T.toIntrinsic s.1 k).comp F ∈
            extraLines :=
        List.mem_append_right _ haAlign
      have haLines :
          (levelFaceParentCoord T.toIntrinsic s.1 k).comp F ∈ lines :=
        List.mem_append_right _ haExtra
      have haAll :
          (levelFaceParentCoord T.toIntrinsic s.1 k).comp F ∈
            N.coordinateLines ++ lines :=
        List.mem_append_right _ haLines
      have hR :=
        (PolygonalFamily.arrangementMesh J
          ).refineByLines_isMonochromatic_of_mem
            (N.coordinateLines ++ lines) haAll
      intro w hw
      apply hR w
      exact
        (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
          J N lines (fun _ ↦ True)).mp hw |>.1
    have hcoordAtP (k : Fin 3) :
        0 <
          ((levelFaceParentCoord T.toIntrinsic s.1 k).comp F) p := by
      let a := (levelFaceParentCoord T.toIntrinsic s.1 k).comp F
      have hnonneg : 0 ≤ a p := by
        change 0 ≤ levelFaceParentCoord T.toIntrinsic s.1 k (F p)
        rw [hplaneAtP]
        exact levelFaceParentCoord_nonneg T.toIntrinsic s.1 k z
      rcases hmono k t.1 t.2 with hpos | hneg
      · have hsub :
            localOldMesh.triangleCarrier t.1 ⊆ {r | 0 ≤ a r} := by
          apply convexHull_min
          · rintro r ⟨v, hv, rfl⟩
            exact hpos v hv
          · exact ((convex_Ici (0 : ℝ)).affine_preimage a)
        have hpHalf := interior_mono hsub hp
        rw [TriangleMesh.interior_affine_nonneg_of_surjective a
          (Qatlas.relativeLevelAlignmentLine_surjective
            CN hCNcompact N anchorLines u s.1 k)] at hpHalf
        exact hpHalf
      · have hsub :
            localOldMesh.triangleCarrier t.1 ⊆ {r | a r ≤ 0} := by
          apply convexHull_min
          · rintro r ⟨v, hv, rfl⟩
            exact hneg v hv
          · exact ((convex_Iic (0 : ℝ)).affine_preimage a)
        have hpHalf := interior_mono hsub hp
        rw [TriangleMesh.interior_affine_nonpos_of_surjective a
          (Qatlas.relativeLevelAlignmentLine_surjective
            CN hCNcompact N anchorLines u s.1 k)] at hpHalf
        exact False.elim ((not_lt_of_ge hnonneg) hpHalf)
    refine ⟨s, ?_⟩
    intro r hr
    let a : Fin 3 → (Plane →ᵃ[ℝ] ℝ) :=
      fun k => (levelFaceParentCoord T.toIntrinsic s.1 k).comp F
    have hrcoord (k : Fin 3) : 0 ≤ a k r := by
      rcases hmono k t.1 t.2 with hpos | hneg
      · apply convexHull_min ?_
          ((convex_Ici (0 : ℝ)).affine_preimage (a k)) hr
        rintro z ⟨v, hv, rfl⟩
        exact hpos v hv
      · have hpNonpos : a k p ≤ 0 := by
          apply convexHull_min ?_
              ((convex_Iic (0 : ℝ)).affine_preimage (a k))
            (interior_subset hp)
          rintro z ⟨v, hv, rfl⟩
          exact hneg v hv
        exact False.elim ((not_lt_of_ge hpNonpos) (hcoordAtP k))
    let b := affineBasisOfTriangle
      (levelFaceParentPlaneAffine T.toIntrinsic s.1 ∘
        standardTriangleVertex)
      (affineIndependent_comp_of_injOn_convexHull
        standardTriangleVertex standardTriangleVertex_affineIndependent
        (levelFaceParentPlaneAffine T.toIntrinsic s.1) (by
          rw [← standardTrianglePlaneComplex_support]
          exact levelFaceParentPlaneAffine_injOn T.toIntrinsic s.1))
    have hFr :
        F r ∈ convexHull ℝ (Set.range b) := by
      rw [b.convexHull_eq_nonneg_coord]
      intro k
      change
        0 ≤
          levelFaceParentCoord T.toIntrinsic s.1 k (F r)
      exact hrcoord k
    have hb :
        (fun i => b i) =
          levelFaceParentPlaneAffine T.toIntrinsic s.1 ∘
            standardTriangleVertex := by
      funext i
      rfl
    have hFr' :
        F r ∈ convexHull ℝ
          (Set.range
            (levelFaceParentPlaneAffine T.toIntrinsic s.1 ∘
              standardTriangleVertex)) := by
      rwa [← congrArg Set.range hb]
    rw [Set.range_comp,
      ← (levelFaceParentPlaneAffine T.toIntrinsic s.1).image_convexHull,
      ← standardTrianglePlaneComplex_support] at hFr'
    obtain ⟨z', hz', hz'eq⟩ := hFr'
    let z'Support : standardTrianglePlaneComplex.support := ⟨z', hz'⟩
    let rLocal :
        {q : Plane // q ∈ localOldMesh.triangleCarrier t.1} := ⟨r, hr⟩
    let rBase :
        {q : Plane // q ∈ baseOldMesh.triangleCarrier u.1} :=
      ⟨r, htu hr⟩
    let q' : Rlevel.refined.ClosedFace s.1 :=
      (Rlevel.refined.facePlaneHomeomorph s.1).symm z'Support
    refine ⟨q'.1, q'.2, ?_⟩
    have hsourceR :
        Qatlas.tileFacesMeetingRelativeSourceEmbed
            CN hCNcompact N anchorLines
            (Qatlas.relativeOldTrianglePoint
              CN hCNcompact N anchorLines u rBase) =
          source₁
            (Qatlas.relativeOldTrianglePoint
              CN hCNcompact N extraLines t rLocal) := by
      apply
        Qatlas.tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq
          CN hCNcompact N
      rw [Qatlas.relativeOldTrianglePoint_coordinateEmbed
          CN hCNcompact N anchorLines u rBase,
        Qatlas.relativeOldTrianglePoint_coordinateEmbed
          CN hCNcompact N extraLines t rLocal]
    have hsourceRMem :
        source₁
            (Qatlas.relativeOldTrianglePoint
              CN hCNcompact N extraLines t rLocal) ∈
          T.toIntrinsic.faceCarrier
            (Qatlas.relativeOldTriangleParent
              CN hCNcompact N anchorLines u).1 := by
      rw [← hsourceR]
      exact Qatlas.relativeOldTriangleParent_contains
        CN hCNcompact N anchorLines u _
        (Qatlas.relativeOldTrianglePoint_supported
          CN hCNcompact N anchorLines u rBase)
    have hq'Parent :
        Rlevel.homeo q'.1 ∈
          T.toIntrinsic.faceCarrier
            (Qatlas.relativeOldTriangleParent
              CN hCNcompact N anchorLines u).1 := by
      rw [← hparent]
      exact levelFaceParent_contains
        T.toIntrinsic s.1 q'.1 q'.2
    have hclosed :
        (⟨Rlevel.homeo q'.1, hq'Parent⟩ :
            T.toIntrinsic.ClosedFace
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)) =
          ⟨source₁
              (Qatlas.relativeOldTrianglePoint
                CN hCNcompact N extraLines t rLocal),
            hsourceRMem⟩ := by
      apply
        (T.toIntrinsic.facePlaneHomeomorph
          (Qatlas.relativeOldTriangleParent
            CN hCNcompact N anchorLines u)).injective
      apply Subtype.ext
      have hlevel :=
        levelFaceParentPlaneAffine_eq
          T.toIntrinsic s.1 z'Support
      have hbase :=
        Qatlas.relativeOldTriangleParentPlaneAffine_eq
          CN hCNcompact N anchorLines u rBase
      rw [T.toIntrinsic.facePlaneHomeomorph_val_eq_forwardAffine] at hlevel hbase
      calc
        T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)
              (Rlevel.homeo q'.1).1 =
            T.toIntrinsic.facePlaneForwardAffine
              (levelFaceParent T.toIntrinsic s.1)
              (Rlevel.homeo q'.1).1 := by
          rw [hparent]
        _ = levelFaceParentPlaneAffine T.toIntrinsic s.1 z' :=
          hlevel.symm
        _ = F r := hz'eq
        _ =
            T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)
              (Qatlas.tileFacesMeetingRelativeSourceEmbed
                CN hCNcompact N anchorLines
                (Qatlas.relativeOldTrianglePoint
                  CN hCNcompact N anchorLines u rBase)).1 :=
          hbase
        _ =
            T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u)
              (source₁
                (Qatlas.relativeOldTrianglePoint
                  CN hCNcompact N extraLines t rLocal)).1 := by
          exact congrArg
            (T.toIntrinsic.facePlaneForwardAffine
              (Qatlas.relativeOldTriangleParent
                CN hCNcompact N anchorLines u))
            (congrArg Subtype.val hsourceR)
    exact congrArg Subtype.val hclosed
  let localFaceLevelFace
      (t : localSourceComplex.Face) :
      {s : T.toIntrinsic.LevelFace n // s ∈ selectedLevelFaces} :=
    Classical.choose
      (exists_levelFace_of_localOldTriangle
        (⟨t.1, t.2⟩ : localOldMesh.Triangle))
  have localFaceLevelFace_contains
      (t : localSourceComplex.Face) (p : Plane)
      (hp : p ∈ localOldMesh.triangleCarrier t.1) :
      source₁
          (Qatlas.relativeOldTrianglePoint
            CN hCNcompact N extraLines
              (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩) ∈
        T.toIntrinsic.levelFaceCarrier (localFaceLevelFace t).1 :=
    Classical.choose_spec
      (exists_levelFace_of_localOldTriangle
        (⟨t.1, t.2⟩ : localOldMesh.Triangle)) p hp
  have localFaceLevelFace_contains_realization
      (t : localSourceComplex.Face)
      (x : localSourceComplex.realization)
      (hx : ∀ v ∉ t.1, x.1 v = 0) :
      source₁ x ∈
        T.toIntrinsic.levelFaceCarrier (localFaceLevelFace t).1 := by
    let p : Plane := localOldMesh.coordinateEmbed x
    have hp : p ∈ localOldMesh.triangleCarrier t.1 := by
      apply localOldMesh.toPlaneComplex.baryEval_mem_cellCarrier
        hx x.2.1.1 x.2.1.2
    let y :=
      Qatlas.relativeOldTrianglePoint
        CN hCNcompact N extraLines
          (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩
    have hyx : y = x := by
      apply localOldMesh.isEmbedding_coordinateEmbed.injective
      rw [Qatlas.relativeOldTrianglePoint_coordinateEmbed
        CN hCNcompact N extraLines
          (⟨t.1, t.2⟩ : localOldMesh.Triangle) ⟨p, hp⟩]
    rw [← hyx]
    exact localFaceLevelFace_contains t p hp
  have hAnchorCoordinateSupport (a : LevelAnchor) :
      anchorCoordinate a ∈ localOldMesh.toPlaneComplex.support := by
    rw [Qatlas.tileFacesMeetingRelativeOldMesh_support
      CN hCNcompact N extraLines]
    have haSelected :
        anchorSourcePoint a ∈
          ⋃ f : Qatlas.TileFacesMeeting CN hCNcompact,
            Q.sourceFaceSet f.1 := by
      rw [Qatlas.sourceTileFacesMeeting_eq_levelFaces CN hCNcompact]
      exact hAnchorSelected a
    rw [Qatlas.sourceTileFacesMeeting_eq_coordinatePreimage
      CN hCNcompact] at haSelected
    simpa only [anchorCoordinate] using haSelected.2
  have hAnchorVerticalMono (a : LevelAnchor) :
      localOldMesh.IsMonochromatic
        (BrokenLineData.verticalLine (anchorCoordinate a)) := by
    have hExtra :
        BrokenLineData.verticalLine (anchorCoordinate a) ∈ extraLines := by
      apply List.mem_append_left
      apply List.mem_append_left
      exact
        PartialTriangulation.PolygonalReplacementSourceAtlas.verticalLine_mem_coordinateAnchorLines
          anchorCoordinate a
    have hLines :
        BrokenLineData.verticalLine (anchorCoordinate a) ∈ lines := by
      exact List.mem_append_right _ hExtra
    have hAll :
        BrokenLineData.verticalLine (anchorCoordinate a) ∈
          N.coordinateLines ++ lines :=
      List.mem_append_right _ hLines
    have hR :=
      (PolygonalFamily.arrangementMesh J).refineByLines_isMonochromatic_of_mem
        (N.coordinateLines ++ lines) hAll
    intro t ht
    apply hR t
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp ht |>.1
  have hAnchorHorizontalMono (a : LevelAnchor) :
      localOldMesh.IsMonochromatic
        (BrokenLineData.horizontalLine (anchorCoordinate a)) := by
    have hExtra :
        BrokenLineData.horizontalLine (anchorCoordinate a) ∈ extraLines := by
      apply List.mem_append_left
      apply List.mem_append_left
      exact
        PartialTriangulation.PolygonalReplacementSourceAtlas.horizontalLine_mem_coordinateAnchorLines
          anchorCoordinate a
    have hLines :
        BrokenLineData.horizontalLine (anchorCoordinate a) ∈ lines := by
      exact List.mem_append_right _ hExtra
    have hAll :
        BrokenLineData.horizontalLine (anchorCoordinate a) ∈
          N.coordinateLines ++ lines :=
      List.mem_append_right _ hLines
    have hR :=
      (PolygonalFamily.arrangementMesh J).refineByLines_isMonochromatic_of_mem
        (N.coordinateLines ++ lines) hAll
    intro t ht
    apply hR t
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp ht |>.1
  have exists_localSourceVertex_eq_anchor (a : LevelAnchor) :
      ∃ v : localSourceComplex.UsedVertex,
        Qatlas.tileFacesMeetingRelativeSourceVertexPoint
          CN hCNcompact N extraLines v = anchorSourcePoint a := by
    obtain ⟨v, hvPosition, hvSimplex⟩ :=
      localOldMesh.exists_vertex_position_eq_of_monochromatic_coordinates
        (anchorCoordinate a) (hAnchorCoordinateSupport a)
        (hAnchorVerticalMono a) (hAnchorHorizontalMono a)
    obtain ⟨-, t, ht, hvt⟩ :=
      localOldMesh.mem_faces_iff.mp hvSimplex
    have hvUsed : ∃ t ∈ localOldMesh.triangles, v ∈ t :=
      ⟨t, ht, hvt (by simp)⟩
    let v' : localSourceComplex.UsedVertex := ⟨v, hvUsed⟩
    refine ⟨v', ?_⟩
    let pLocal : U :=
      Qatlas.tileFacesMeetingRelativeSourceVertexPointInOpen
        CN hCNcompact N extraLines v'
    let pAnchor : U := ⟨anchorSourcePoint a, hAnchorU a⟩
    have hcoordLocal :
        (Q.sourceHomeomorph pLocal).1.1 =
          localOldMesh.position v := by
      exact
        Qatlas.sourceHomeomorph_relativeSourceVertexPointInOpen
          CN hCNcompact N extraLines v'
    have hq :
        Q.sourceHomeomorph pLocal = Q.sourceHomeomorph pAnchor := by
      apply Subtype.ext
      apply Subtype.ext
      exact hcoordLocal.trans hvPosition
    have hp : pLocal = pAnchor :=
      Q.sourceHomeomorph.injective hq
    exact congrArg Subtype.val hp
  let localVertexLevelPoint :
      localSourceComplex.UsedVertex → Rlevel.refined.realization :=
    fun v ↦ Rlevel.homeo.symm
      (Qatlas.tileFacesMeetingRelativeSourceVertexPoint
        CN hCNcompact N extraLines v)
  have localVertexLevelPoint_mem_face
      (t : localSourceComplex.Face) (v : {v // v ∈ t.1}) :
      localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1 := by
    let uv : localSourceComplex.UsedVertex :=
      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
    let xv : localSourceComplex.realization :=
      localSourceComplex.vertexPoint uv
    have hxv : ∀ w ∉ t.1, xv.1 w = 0 := by
      intro w hw
      change Pi.single v.1 1 w = 0
      have hwv : w ≠ v.1 := fun h => hw (h ▸ v.2)
      simp [hwv]
    have hsource :
        source₁ xv ∈
          T.toIntrinsic.levelFaceCarrier (localFaceLevelFace t).1 :=
      localFaceLevelFace_contains_realization t xv hxv
    obtain ⟨q, hq, hqeq⟩ := hsource
    have hlocal :
        Rlevel.homeo (localVertexLevelPoint uv) = source₁ xv := by
      exact Rlevel.homeo.apply_symm_apply _
    have heq :
        localVertexLevelPoint uv = q :=
      Rlevel.homeo.injective (hlocal.trans hqeq.symm)
    rwa [heq]
  have localFaceLevelMap_val
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1}) :
      (Rlevel.homeo.symm
          (source₁ (localSourceComplex.faceStandardMap t x))).1 =
        ∑ v : {v // v ∈ t.1}, x v •
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 := by
    let xg : localSourceComplex.realization :=
      localSourceComplex.faceStandardMap t x
    have hxg : ∀ v ∉ t.1, xg.1 v = 0 := by
      intro v hv
      rw [localSourceComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem t.1 x hv
    let s := (localFaceLevelFace t).1
    let y : Rlevel.refined.realization :=
      Rlevel.homeo.symm (source₁ xg)
    have hyFace : y ∈ Rlevel.refined.faceCarrier s.1 := by
      have hsource :=
        localFaceLevelFace_contains_realization t xg hxg
      obtain ⟨q, hq, hqeq⟩ := hsource
      have hyq : y = q := by
        apply Rlevel.homeo.injective
        rw [Rlevel.homeo.apply_symm_apply, hqeq]
      rwa [hyq]
    let point : {v // v ∈ t.1} →
        (Rlevel.refined.Vertex → ℝ) :=
      fun v ↦
        (localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1
    let weight : {v // v ∈ t.1} → ℝ := fun v ↦ x v
    have hweight : ∑ v, weight v = 1 := x.2.2
    let zfun : Rlevel.refined.Vertex → ℝ :=
      (Finset.univ : Finset {v // v ∈ t.1}).affineCombination
        ℝ point weight
    have hzlinear :
        zfun = ∑ v, weight v • point v := by
      exact Finset.affineCombination_eq_linear_combination
        Finset.univ point weight hweight
    have hznonneg : ∀ k, 0 ≤ zfun k := by
      intro k
      rw [hzlinear]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_nonneg
      intro v _
      have hk :
          0 ≤
            (localVertexLevelPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k :=
        (localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.1 k
      exact mul_nonneg (x.2.1 v) hk
    have hzsum : ∑ k, zfun k = 1 := by
      rw [hzlinear]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      calc
        (∑ v, ∑ k,
            weight v *
              (localVertexLevelPoint
                ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
            ∑ v, weight v *
              ∑ k,
                (localVertexLevelPoint
                  ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
        _ = ∑ v, weight v := by
          apply Finset.sum_congr rfl
          intro v _
          rw [(localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.2, mul_one]
        _ = 1 := hweight
    have hzsupport :
        ∀ k ∉ s.1, zfun k = 0 := by
      intro k hk
      rw [hzlinear]
      simp only [Finset.sum_apply, Pi.smul_apply]
      apply Finset.sum_eq_zero
      intro v _
      have hvFace :=
        localVertexLevelPoint_mem_face t v
      change weight v •
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k = 0
      rw [hvFace k hk, smul_zero]
    let z : Rlevel.refined.realization :=
      ⟨zfun, ⟨hznonneg, hzsum⟩, ⟨s.1, s.2, hzsupport⟩⟩
    obtain ⟨b, hb⟩ := Rlevel.affineOnFace s.1 s.2
    have hbz : (Rlevel.homeo z).1 = b z.1 :=
      hb z (by exact hzsupport)
    have hbcomb :
        b zfun =
          (Finset.univ : Finset {v // v ∈ t.1}
            ).affineCombination ℝ (b ∘ point) weight := by
      exact (Finset.univ : Finset {v // v ∈ t.1}
        ).map_affineCombination point weight hweight b
    have hvertex (v : {v // v ∈ t.1}) :
        b (point v) =
          (source₁
            (localSourceComplex.vertexPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
      have hbv :=
        hb (localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)
          (localVertexLevelPoint_mem_face t v)
      rw [← hbv]
      exact congrArg Subtype.val (Rlevel.homeo.apply_symm_apply _)
    have hzsource :
        (Rlevel.homeo z).1 = (source₁ xg).1 := by
      rw [hbz, hbcomb,
        Finset.affineCombination_eq_linear_combination
          Finset.univ (b ∘ point) weight hweight]
      simp only [Function.comp_apply]
      rw [show
          (∑ v, weight v • b (point v)) =
            ∑ v, x v •
              (source₁
                (localSourceComplex.vertexPoint
                  ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 by
        apply Finset.sum_congr rfl
        intro v _
        rw [hvertex v]
        ]
      rw [Qatlas.relativeSourceFaceMap_eq_vertex_sum
        CN hCNcompact N extraLines
        (⟨t.1, t.2⟩ : localOldMesh.Triangle) xg hxg]
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      change x v = xg.1 v.1
      rw [show xg.1 =
          extendFaceCoordinates t.1 x from
        localSourceComplex.faceStandardMap_val t x,
        extendFaceCoordinates_of_mem t.1 x v.2]
    have hyz : y = z := by
      apply Rlevel.homeo.injective
      apply Subtype.ext
      rw [Rlevel.homeo.apply_symm_apply]
      exact hzsource.symm
    change y.1 = _
    rw [hyz]
    exact hzlinear
  let localFaceSimplexLineMap
      (t : localSourceComplex.Face)
      (x y : stdSimplex ℝ {v // v ∈ t.1})
      (r : Set.Icc (0 : ℝ) 1) :
      stdSimplex ℝ {v // v ∈ t.1} :=
    ⟨AffineMap.lineMap x.1 y.1 r.1,
      (convex_stdSimplex ℝ _).lineMap_mem x.2 y.2 r.2⟩
  have localFaceLevelMap_simplexLineMap
      (t : localSourceComplex.Face)
      (x y : stdSimplex ℝ {v // v ∈ t.1})
      (r : Set.Icc (0 : ℝ) 1) :
      (Rlevel.homeo.symm
        (source₁
          (localSourceComplex.faceStandardMap t
            (localFaceSimplexLineMap t x y r)))).1 =
        AffineMap.lineMap
          (Rlevel.homeo.symm
            (source₁
              (localSourceComplex.faceStandardMap t x))).1
          (Rlevel.homeo.symm
            (source₁
              (localSourceComplex.faceStandardMap t y))).1 r.1 := by
    rw [localFaceLevelMap_val t (localFaceSimplexLineMap t x y r),
      localFaceLevelMap_val t x, localFaceLevelMap_val t y]
    funext k
    simp only [localFaceSimplexLineMap,
      AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
    change
      (∑ v, (((1 - r.1) • x.1 + r.1 • y.1) v) *
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
        (1 - r.1) *
            ∑ v, x v *
              (localVertexLevelPoint
                ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k +
          r.1 *
            ∑ v, y v *
              (localVertexLevelPoint
                ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ v, ((1 - r.1) * x v + r.1 * y v) *
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) =
          ∑ v,
            ((1 - r.1) *
                (x v *
                  (localVertexLevelPoint
                    ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k) +
              r.1 *
                (y v *
                  (localVertexLevelPoint
                    ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k)) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have localFaceLevelMap_vertex
      (t : localSourceComplex.Face) (v : {v // v ∈ t.1}) :
      Rlevel.homeo.symm
          (source₁
            (localSourceComplex.faceStandardMap t
              (stdSimplex.vertex v))) =
        localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ := by
    apply Subtype.ext
    rw [localFaceLevelMap_val]
    funext k
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [stdSimplex.vertex, Pi.single_apply, hw]
    · simp
  let localVertexLevelPoints : Finset Rlevel.refined.realization :=
    (Finset.univ : Finset localSourceComplex.UsedVertex).image
      localVertexLevelPoint
  have hAnchorLevelPoint_mem_localVertexLevelPoints (a : LevelAnchor) :
      anchorLevelPoint a ∈ localVertexLevelPoints := by
    obtain ⟨v, hv⟩ := exists_localSourceVertex_eq_anchor a
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_univ v, ?_⟩
    change Rlevel.homeo.symm
        (Qatlas.tileFacesMeetingRelativeSourceVertexPoint
          CN hCNcompact N extraLines v) =
      anchorLevelPoint a
    rw [hv]
    change Rlevel.homeo.symm
        (Rlevel.homeo (anchorLevelPoint a)) =
      anchorLevelPoint a
    exact Rlevel.homeo.symm_apply_apply _
  let edgeMidpointPoints : Finset Rlevel.refined.realization :=
    (Finset.univ : Finset Rlevel.refined.Edge).image
      (fun e ↦ Rlevel.refined.edgePath e edgeHalf)
  let boundaryMarking : Rlevel.refined.EdgeMarking :=
    IntrinsicTwoComplex.EdgeMarking.ofFinset
      (K := Rlevel.refined)
        (localVertexLevelPoints ∪ edgeMidpointPoints)
  let outsideFan := boundaryMarking.markedFanLocallyFiniteTriangleComplex
  have hboundaryFanSurface :
      outsideFan.compactIntrinsic.HasSurfaceEdgeValence :=
    boundaryMarking.markedFanCompactIntrinsic_hasSurfaceEdgeValence
      hRlevelSurface
  let OutsideFanFace :=
    {f : boundaryMarking.FanFace // f.1 ∉ selectedLevelFaces}
  let outsideFanFaceMap (f : OutsideFanFace) :
      stdSimplex ℝ
          {v // v ∈ boundaryMarking.globalFanFaceVertices f.1} →
        T.toIntrinsic.realization :=
    fun x ↦ Rlevel.homeo (boundaryMarking.globalFanFaceMap f.1 x)
  have localVertexLevelPoint_injective :
      Function.Injective localVertexLevelPoint := by
    intro v w hvw
    apply localSourceComplex.injective_vertexPoint
    apply hsource₁Embedding.injective
    change
      Qatlas.tileFacesMeetingRelativeSourceVertexPoint
          CN hCNcompact N extraLines v =
        Qatlas.tileFacesMeetingRelativeSourceVertexPoint
          CN hCNcompact N extraLines w
    have h := congrArg Rlevel.homeo hvw
    simpa only [localVertexLevelPoint,
      Rlevel.homeo.apply_symm_apply] using h
  let oldVertexPoints : Finset Rlevel.refined.realization :=
    localVertexLevelPoints ∪ boundaryMarking.fanVertices
  let OldVertex := {p : Rlevel.refined.realization // p ∈ oldVertexPoints}
  let localOldVertexEmbedding :
      localSourceComplex.UsedVertex ↪ OldVertex :=
    { toFun := fun v ↦ ⟨localVertexLevelPoint v, by
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
      inj' := by
        intro v w hvw
        exact localVertexLevelPoint_injective
          (congrArg (fun z : OldVertex ↦ z.1) hvw) }
  let fanOldVertexEmbedding :
      boundaryMarking.FanVertex ↪ OldVertex :=
    { toFun := fun v ↦ ⟨v.1, Finset.mem_union_right _ v.2⟩
      inj' := by
        intro v w hvw
        exact Subtype.ext
          (congrArg (fun z : OldVertex ↦ z.1) hvw) }
  let localFaceOldVertexEmbedding (t : localSourceComplex.Face) :
      {v // v ∈ t.1} ↪ OldVertex :=
    { toFun := fun v ↦ localOldVertexEmbedding
        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
      inj' := by
        intro v w hvw
        apply Subtype.ext
        have hp :
            localVertexLevelPoint
                ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ =
              localVertexLevelPoint
                ⟨w.1, ⟨t.1, t.2, w.2⟩⟩ :=
          congrArg (fun z : OldVertex ↦ z.1) hvw
        have huv :
            (⟨v.1, ⟨t.1, t.2, v.2⟩⟩ :
              localSourceComplex.UsedVertex) =
            ⟨w.1, ⟨t.1, t.2, w.2⟩⟩ :=
          localVertexLevelPoint_injective hp
        exact congrArg
          (fun z : localSourceComplex.UsedVertex ↦ z.1) huv }
  let MixedOldFace := Sum localSourceComplex.Face OutsideFanFace
  let mixedOldFaceVertices : MixedOldFace → Finset OldVertex
    | Sum.inl t =>
        (Finset.univ : Finset {v // v ∈ t.1}).map
          (localFaceOldVertexEmbedding t)
    | Sum.inr f =>
        (boundaryMarking.globalFanFaceVertices f.1).map
          fanOldVertexEmbedding
  let mixedOldFaceMap (f : MixedOldFace) :
      stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f} →
        Rlevel.refined.realization :=
    match f with
    | Sum.inl t => fun x ↦
        Rlevel.homeo.symm
          (source₁
            (localSourceComplex.faceStandardMap t
              (relabelUnivSimplex
                (localFaceOldVertexEmbedding t) x)))
    | Sum.inr f => fun x ↦
        boundaryMarking.globalFanFaceMap f.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1) x)
  have mixedOldFaceVertices_card (f : MixedOldFace) :
      (mixedOldFaceVertices f).card = 3 := by
    rcases f with t | f
    · change ((Finset.univ : Finset {v // v ∈ t.1}).map
          (localFaceOldVertexEmbedding t)).card = 3
      rw [Finset.card_map, Finset.card_univ, Fintype.card_coe,
        localSourceComplex.faces_card t.1 t.2]
    · change ((boundaryMarking.globalFanFaceVertices f.1).map
          fanOldVertexEmbedding).card = 3
      rw [Finset.card_map, IntrinsicTwoComplex.EdgeMarking.globalFanFaceVertices,
        Finset.card_map, Finset.card_attach,
        boundaryMarking.fanFaceVertices_card]
  have continuous_mixedOldFaceMap (f : MixedOldFace) :
      Continuous (mixedOldFaceMap f) := by
    rcases f with t | f
    · exact Rlevel.homeo.symm.continuous.comp
        (hsource₁Embedding.continuous.comp
          (localSourceComplex.continuous_faceStandardMap t |>.comp
            (stdSimplex.continuous_map
              (univMapSubtypeEquiv
                (localFaceOldVertexEmbedding t)))))
    · exact boundaryMarking.continuous_globalFanFaceMap f.1 |>.comp
        (stdSimplex.continuous_map
          (finsetMapSubtypeEquiv fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1)).symm)
  have localMixedExtended_apply
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)})
      (u : localSourceComplex.UsedVertex) :
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inl t)) x
          (localOldVertexEmbedding u) =
        extendFaceCoordinates t.1
          (relabelUnivSimplex
            (localFaceOldVertexEmbedding t) x) u.1 := by
    by_cases hut : u.1 ∈ t.1
    · let v : {v // v ∈ t.1} := ⟨u.1, hut⟩
      have huv :
          u = ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ := Subtype.ext rfl
      have hemb :
          localOldVertexEmbedding u =
            localFaceOldVertexEmbedding t v := by
        change localOldVertexEmbedding u =
          localOldVertexEmbedding
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩
        exact congrArg localOldVertexEmbedding huv
      have hmem :
          localFaceOldVertexEmbedding t v ∈
            mixedOldFaceVertices (Sum.inl t) := by
        change localFaceOldVertexEmbedding t v ∈
          (Finset.univ : Finset {v // v ∈ t.1}).map
            (localFaceOldVertexEmbedding t)
        exact Finset.mem_map.mpr
          ⟨v, Finset.mem_univ v, rfl⟩
      rw [hemb,
        extendFaceCoordinates_of_mem _ _ hmem,
        extendFaceCoordinates_of_mem _ _ hut]
      have hrel :=
        (relabelUnivSimplex_apply
          (localFaceOldVertexEmbedding t) x v).symm
      rw [extendFaceCoordinates_of_mem _ _ hmem] at hrel
      simpa only [v] using hrel
    · have hnot :
          localOldVertexEmbedding u ∉
            mixedOldFaceVertices (Sum.inl t) := by
        intro hu
        change localOldVertexEmbedding u ∈
          (Finset.univ : Finset {v // v ∈ t.1}).map
            (localFaceOldVertexEmbedding t) at hu
        obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hu
        have hused :
            u = ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ :=
          localOldVertexEmbedding.injective hv.symm
        exact hut (congrArg
          (fun z : localSourceComplex.UsedVertex ↦ z.1) hused ▸ v.2)
      rw [extendFaceCoordinates_of_notMem _ _ hnot,
        extendFaceCoordinates_of_notMem _ _ hut]
  have localMixedFaceMap_eq_iff
      {t u : localSourceComplex.Face}
      {x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl u)}} :
      mixedOldFaceMap (Sum.inl t) x =
          mixedOldFaceMap (Sum.inl u) y ↔
        extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl t)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl u)) y := by
    let x₀ := relabelUnivSimplex
      (localFaceOldVertexEmbedding t) x
    let y₀ := relabelUnivSimplex
      (localFaceOldVertexEmbedding u) y
    constructor
    · intro hxy
      have hsource :
          localSourceComplex.faceStandardMap t x₀ =
            localSourceComplex.faceStandardMap u y₀ := by
        apply hsource₁Embedding.injective
        apply Rlevel.homeo.symm.injective
        exact hxy
      have hcoords :
          extendFaceCoordinates t.1 x₀ =
            extendFaceCoordinates u.1 y₀ := by
        rw [← localSourceComplex.faceStandardMap_val t x₀,
          ← localSourceComplex.faceStandardMap_val u y₀]
        exact congrArg Subtype.val hsource
      funext p
      by_cases hp :
          p ∈ Set.range localOldVertexEmbedding
      · obtain ⟨v, hv⟩ := hp
        subst p
        rw [localMixedExtended_apply t x v,
          localMixedExtended_apply u y v,
          congrFun hcoords v.1]
      · have hpt :
            p ∉ mixedOldFaceVertices (Sum.inl t) := by
          intro hpt
          change p ∈
            (Finset.univ : Finset {v // v ∈ t.1}).map
              (localFaceOldVertexEmbedding t) at hpt
          obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpt
          apply hp
          refine
            ⟨(⟨v.1, ⟨t.1, t.2, v.2⟩⟩ :
              localSourceComplex.UsedVertex), ?_⟩
          exact hv
        have hpu :
            p ∉ mixedOldFaceVertices (Sum.inl u) := by
          intro hpu
          change p ∈
            (Finset.univ : Finset {v // v ∈ u.1}).map
              (localFaceOldVertexEmbedding u) at hpu
          obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpu
          apply hp
          refine
            ⟨(⟨v.1, ⟨u.1, u.2, v.2⟩⟩ :
              localSourceComplex.UsedVertex), ?_⟩
          exact hv
        rw [extendFaceCoordinates_of_notMem _ _ hpt,
          extendFaceCoordinates_of_notMem _ _ hpu]
    · intro hcoords
      have hlocal :
          extendFaceCoordinates t.1 x₀ =
            extendFaceCoordinates u.1 y₀ := by
        funext v
        by_cases hvUsed :
            ∃ q ∈ localSourceComplex.faces, v ∈ q
        · let w : localSourceComplex.UsedVertex :=
            ⟨v, hvUsed⟩
          have hw := congrFun hcoords
            (localOldVertexEmbedding w)
          rw [localMixedExtended_apply t x w,
            localMixedExtended_apply u y w] at hw
          exact hw
        · have hvt : v ∉ t.1 := by
            intro hvt
            exact hvUsed ⟨t.1, t.2, hvt⟩
          have hvu : v ∉ u.1 := by
            intro hvu
            exact hvUsed ⟨u.1, u.2, hvu⟩
          rw [extendFaceCoordinates_of_notMem _ _ hvt,
            extendFaceCoordinates_of_notMem _ _ hvu]
      change
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t x₀)) =
          Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap u y₀))
      apply congrArg Rlevel.homeo.symm
      apply congrArg source₁
      apply Subtype.ext
      simpa only [localSourceComplex.faceStandardMap_val] using hlocal
  have fanMixedFaceMap_eq_iff
      {f g : OutsideFanFace}
      {x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)}}
      {y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr g)}} :
      mixedOldFaceMap (Sum.inr f) x =
          mixedOldFaceMap (Sum.inr g) y ↔
        extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr f)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr g)) y := by
    change
      boundaryMarking.globalFanFaceMap f.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1) x) =
        boundaryMarking.globalFanFaceMap g.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices g.1) y) ↔ _
    rw [boundaryMarking.globalFanFaceMap_eq_iff]
    exact relabelFaceSimplex_extended_eq_iff
      fanOldVertexEmbedding
  have mixedOldFaceMap_val
      (f : MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f}) :
      (mixedOldFaceMap f x).1 =
        fun k ↦ ∑ v : OldVertex,
          extendFaceCoordinates (mixedOldFaceVertices f) x v *
            v.1.1 k := by
    rcases f with t | f
    · let x₀ := relabelUnivSimplex
        (localFaceOldVertexEmbedding t) x
      rw [localFaceLevelMap_val t x₀]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hsum :=
        sum_extendFaceCoordinates_relabelUnivSimplex
          (localFaceOldVertexEmbedding t) x
          (fun v : OldVertex ↦ v.1.1 k)
      exact hsum.symm
    · let y := relabelFaceSimplex fanOldVertexEmbedding
        (boundaryMarking.globalFanFaceVertices f.1) x
      rw [boundaryMarking.globalFanFaceMap_val_eq_fanBarycentricAffine]
      funext k
      rw [boundaryMarking.fanBarycentricAffine_apply]
      have hsum :=
        sum_extendFaceCoordinates_relabelFaceSimplex
          fanOldVertexEmbedding
          (boundaryMarking.globalFanFaceVertices f.1) x
          (fun v : OldVertex ↦ v.1.1 k)
      exact hsum.symm
  let mixedFaceSimplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f} :=
    ⟨AffineMap.lineMap x.1 y.1 r.1,
      (convex_stdSimplex ℝ _).lineMap_mem x.2 y.2 r.2⟩
  have extend_mixedFaceSimplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      extendFaceCoordinates (mixedOldFaceVertices f)
          (mixedFaceSimplexLineMap f x y r) =
        (1 - r.1) •
            extendFaceCoordinates (mixedOldFaceVertices f) x +
          r.1 •
            extendFaceCoordinates (mixedOldFaceVertices f) y := by
    funext v
    by_cases hv : v ∈ mixedOldFaceVertices f
    · rw [extendFaceCoordinates_of_mem _ _ hv]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [extendFaceCoordinates_of_mem _ _ hv,
        extendFaceCoordinates_of_mem _ _ hv]
      change
        (AffineMap.lineMap x.1 y.1 r.1) ⟨v, hv⟩ =
          (1 - r.1) * x ⟨v, hv⟩ + r.1 * y ⟨v, hv⟩
      rw [AffineMap.lineMap_apply_module]
      rfl
    · rw [extendFaceCoordinates_of_notMem _ _ hv]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [extendFaceCoordinates_of_notMem _ _ hv,
        extendFaceCoordinates_of_notMem _ _ hv]
      simp
  have mixedOldFaceMap_simplexLineMap
      (f : MixedOldFace)
      (x y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f})
      (r : Set.Icc (0 : ℝ) 1) :
      (mixedOldFaceMap f (mixedFaceSimplexLineMap f x y r)).1 =
        AffineMap.lineMap
          (mixedOldFaceMap f x).1 (mixedOldFaceMap f y).1 r.1 := by
    rw [mixedOldFaceMap_val,
      extend_mixedFaceSimplexLineMap,
      mixedOldFaceMap_val, mixedOldFaceMap_val]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      AffineMap.lineMap_apply_module]
    calc
      (∑ v,
          ((1 - r.1) *
                extendFaceCoordinates (mixedOldFaceVertices f) x v +
              r.1 *
                extendFaceCoordinates (mixedOldFaceVertices f) y v) *
            v.1.1 k) =
          ∑ v,
            ((1 - r.1) *
                (extendFaceCoordinates
                    (mixedOldFaceVertices f) x v * v.1.1 k) +
              r.1 *
                (extendFaceCoordinates
                    (mixedOldFaceVertices f) y v * v.1.1 k)) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have extend_mixedOldFace_vertex
      (f : MixedOldFace)
      (v : {v // v ∈ mixedOldFaceVertices f}) :
      extendFaceCoordinates (mixedOldFaceVertices f)
          (stdSimplex.vertex v) =
        Pi.single v.1 1 := by
    funext w
    by_cases hwv : w = v.1
    · subst w
      simp [extendFaceCoordinates, v.2]
    · by_cases hw : w ∈ mixedOldFaceVertices f
      · have hsub :
            (⟨w, hw⟩ : {w // w ∈ mixedOldFaceVertices f}) ≠ v := by
          exact fun h ↦ hwv (congrArg Subtype.val h)
        simp [extendFaceCoordinates, hw, hwv, hsub]
      · simp [extendFaceCoordinates, hw, hwv]
  have mixedOldFaceMap_vertex
      (f : MixedOldFace)
      (v : {v // v ∈ mixedOldFaceVertices f}) :
      mixedOldFaceMap f (stdSimplex.vertex v) = v.1.1 := by
    apply Subtype.ext
    rw [mixedOldFaceMap_val,
      extend_mixedOldFace_vertex]
    funext k
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro w _ hw
      simp [Pi.single_apply, hw]
    · simp
  have mixedLocalExtended_eq_single_of_map_eq_localVertex
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)})
      (u : localSourceComplex.UsedVertex)
      (hxu :
        mixedOldFaceMap (Sum.inl t) x =
          localVertexLevelPoint u) :
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inl t)) x =
        Pi.single (localOldVertexEmbedding u) 1 := by
    let tu : localSourceComplex.Face :=
      ⟨Classical.choose u.2, (Classical.choose_spec u.2).1⟩
    let uv : {v // v ∈ tu.1} :=
      ⟨u.1, (Classical.choose_spec u.2).2⟩
    have huv :
        localFaceOldVertexEmbedding tu uv =
          localOldVertexEmbedding u := by
      apply Subtype.ext
      rfl
    have huMem :
        localOldVertexEmbedding u ∈
          mixedOldFaceVertices (Sum.inl tu) := by
      change localOldVertexEmbedding u ∈
        (Finset.univ : Finset {v // v ∈ tu.1}).map
          (localFaceOldVertexEmbedding tu)
      exact Finset.mem_map.mpr
        ⟨uv, Finset.mem_univ uv, huv⟩
    let w :
        {v // v ∈ mixedOldFaceVertices (Sum.inl tu)} :=
      ⟨localOldVertexEmbedding u, huMem⟩
    have hmapw :
        mixedOldFaceMap (Sum.inl tu) (stdSimplex.vertex w) =
          localVertexLevelPoint u := by
      calc
        mixedOldFaceMap (Sum.inl tu) (stdSimplex.vertex w) =
            w.1.1 := mixedOldFaceMap_vertex (Sum.inl tu) w
        _ = localVertexLevelPoint u := rfl
    have hcoords :=
      localMixedFaceMap_eq_iff.mp (hxu.trans hmapw.symm)
    calc
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inl t)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl tu))
            (stdSimplex.vertex w) := hcoords
      _ = Pi.single w.1 1 :=
        extend_mixedOldFace_vertex (Sum.inl tu) w
      _ = Pi.single (localOldVertexEmbedding u) 1 := by rfl
  have mixedFanExtended_eq_single_of_map_eq_fanVertex
      (f : OutsideFanFace)
      (y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)})
      (v : {p // p ∈ boundaryMarking.fanFaceVertices f.1})
      (hyv : mixedOldFaceMap (Sum.inr f) y = v.1) :
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inr f)) y =
        Pi.single
          (fanOldVertexEmbedding
            (boundaryMarking.fanVertexEmbedding f.1 v)) 1 := by
    let gv : boundaryMarking.FanVertex :=
      boundaryMarking.fanVertexEmbedding f.1 v
    have hgvMem :
        gv ∈ boundaryMarking.globalFanFaceVertices f.1 :=
      (boundaryMarking.mem_globalFanFaceVertices_iff f.1 gv).mpr v.2
    have hOldMem :
        fanOldVertexEmbedding gv ∈
          mixedOldFaceVertices (Sum.inr f) := by
      change fanOldVertexEmbedding gv ∈
        (boundaryMarking.globalFanFaceVertices f.1).map
          fanOldVertexEmbedding
      exact Finset.mem_map.mpr ⟨gv, hgvMem, rfl⟩
    let w :
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
      ⟨fanOldVertexEmbedding gv, hOldMem⟩
    have hmapw :
        mixedOldFaceMap (Sum.inr f) (stdSimplex.vertex w) = v.1 := by
      calc
        mixedOldFaceMap (Sum.inr f) (stdSimplex.vertex w) =
            w.1.1 := mixedOldFaceMap_vertex (Sum.inr f) w
        _ = v.1 := rfl
    have hcoords :=
      fanMixedFaceMap_eq_iff.mp (hyv.trans hmapw.symm)
    calc
      extendFaceCoordinates
          (mixedOldFaceVertices (Sum.inr f)) y =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr f))
            (stdSimplex.vertex w) := hcoords
      _ = Pi.single w.1 1 :=
        extend_mixedOldFace_vertex (Sum.inr f) w
      _ = Pi.single
          (fanOldVertexEmbedding
            (boundaryMarking.fanVertexEmbedding f.1 v)) 1 := by rfl
  have edge_subset_face_of_midpoint_mem
      (d : Rlevel.refined.Edge) (s : Finset Rlevel.refined.Vertex)
      (hmid :
        Rlevel.refined.edgePath d edgeHalf ∈
          Rlevel.refined.faceCarrier s) :
      d.1 ⊆ s := by
    intro v hv
    by_contra hvs
    have hzero :
        (Rlevel.refined.edgePath d edgeHalf).1 v = 0 :=
      hmid v hvs
    have hpos :
        0 < (Rlevel.refined.edgePath d edgeHalf).1 v := by
      rw [Rlevel.refined.edge_eq_pair d] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [Rlevel.refined.edgePath_apply_first]
        change 0 < 1 - (1 / 2 : ℝ)
        norm_num
      · rw [Rlevel.refined.edgePath_apply_second]
        change 0 < (1 / 2 : ℝ)
        norm_num
    linarith
  have interfaceEdgeMarks_subset_local
      (s : {s : T.toIntrinsic.LevelFace n //
        s ∈ selectedLevelFaces})
      (e : Rlevel.refined.Edge) (hes : e.1 ⊆ s.1.1) :
      ∀ p ∈ boundaryMarking.edgeMarks e,
        p ∈ localVertexLevelPoints := by
    intro p hp
    have hpData := (boundaryMarking.mem_edgeMarks_iff e p).mp hp
    have hpPoints := hpData.1
    have hpEdge := hpData.2
    change p ∈ (localVertexLevelPoints ∪ edgeMidpointPoints) ∪
        (Finset.univ : Finset Rlevel.refined.Edge).image
            Rlevel.refined.edgeFirstPoint ∪
          (Finset.univ : Finset Rlevel.refined.Edge).image
            Rlevel.refined.edgeSecondPoint at hpPoints
    rcases Finset.mem_union.mp hpPoints with hpLeft | hpSecond
    · rcases Finset.mem_union.mp hpLeft with hpPrimary | hpFirst
      · rcases Finset.mem_union.mp hpPrimary with hpLocal | hpMid
        · exact hpLocal
        · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpMid
          have hdSubset :
              d.1 ⊆ e.1 := by
            apply edge_subset_face_of_midpoint_mem d e.1
            rw [hdp]
            exact hpEdge
          have hde : d = e := by
            apply Subtype.ext
            exact Finset.eq_of_subset_of_card_le hdSubset (by
              rw [Rlevel.refined.card_of_mem_edges d.2,
                Rlevel.refined.card_of_mem_edges e.2])
          subst d
          obtain ⟨i, hi⟩ :=
            Rlevel.refined.exists_faceEdge_eq_of_subset s.1 e hes
          let a : LevelAnchor := ⟨s, Sum.inr i⟩
          have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
          rw [← hdp]
          simpa only [a, anchorLevelPoint, hi] using ha
      · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpFirst
        have hfirstEdge :
            Rlevel.refined.edgeFirst d ∈ e.1 := by
          let w := Rlevel.refined.edgeFirstUsed d
          have hw :
              Rlevel.refined.vertexPoint w ∈
                Rlevel.refined.faceCarrier e.1 := by
            rw [Rlevel.refined.vertexPoint_edgeFirstUsed d,
              hdp]
            exact hpEdge
          exact
            (Rlevel.refined.vertexPoint_mem_faceCarrier_iff
              w e.1).mp hw
        let v : s.1.1 :=
          ⟨Rlevel.refined.edgeFirst d, hes hfirstEdge⟩
        let a : LevelAnchor := ⟨s, Sum.inl v⟩
        have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
        have heq :
            Rlevel.refined.edgeFirstPoint d =
              Rlevel.refined.facePoint s.1 v := by
          apply Subtype.ext
          rfl
        rw [← hdp, heq]
        exact ha
    · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpSecond
      have hsecondEdge :
          Rlevel.refined.edgeSecond d ∈ e.1 := by
        let w := Rlevel.refined.edgeSecondUsed d
        have hw :
            Rlevel.refined.vertexPoint w ∈
              Rlevel.refined.faceCarrier e.1 := by
          rw [Rlevel.refined.vertexPoint_edgeSecondUsed d,
            hdp]
          exact hpEdge
        exact
          (Rlevel.refined.vertexPoint_mem_faceCarrier_iff
            w e.1).mp hw
      let v : s.1.1 :=
        ⟨Rlevel.refined.edgeSecond d, hes hsecondEdge⟩
      let a : LevelAnchor := ⟨s, Sum.inl v⟩
      have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
      have heq :
          Rlevel.refined.edgeSecondPoint d =
            Rlevel.refined.facePoint s.1 v := by
        apply Subtype.ext
        rfl
      rw [← hdp, heq]
      exact ha
  have selectedFace_marking_subset_local
      (s : {s : T.toIntrinsic.LevelFace n //
        s ∈ selectedLevelFaces})
      (p : Rlevel.refined.realization)
      (hpMark : p ∈ boundaryMarking.points)
      (hpFace : p ∈ Rlevel.refined.faceCarrier s.1.1) :
      p ∈ localVertexLevelPoints := by
    change p ∈ (localVertexLevelPoints ∪ edgeMidpointPoints) ∪
        (Finset.univ : Finset Rlevel.refined.Edge).image
            Rlevel.refined.edgeFirstPoint ∪
          (Finset.univ : Finset Rlevel.refined.Edge).image
            Rlevel.refined.edgeSecondPoint at hpMark
    rcases Finset.mem_union.mp hpMark with hpLeft | hpSecond
    · rcases Finset.mem_union.mp hpLeft with hpPrimary | hpFirst
      · rcases Finset.mem_union.mp hpPrimary with hpLocal | hpMid
        · exact hpLocal
        · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpMid
          have hdSubset :
              d.1 ⊆ s.1.1 := by
            apply edge_subset_face_of_midpoint_mem d s.1.1
            rw [hdp]
            exact hpFace
          obtain ⟨i, hi⟩ :=
            Rlevel.refined.exists_faceEdge_eq_of_subset s.1 d hdSubset
          let a : LevelAnchor := ⟨s, Sum.inr i⟩
          have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
          rw [← hdp]
          simpa only [a, anchorLevelPoint, hi] using ha
      · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpFirst
        have hfirstFace :
            Rlevel.refined.edgeFirst d ∈ s.1.1 := by
          let w := Rlevel.refined.edgeFirstUsed d
          have hw :
              Rlevel.refined.vertexPoint w ∈
                Rlevel.refined.faceCarrier s.1.1 := by
            rw [Rlevel.refined.vertexPoint_edgeFirstUsed d,
              hdp]
            exact hpFace
          exact
            (Rlevel.refined.vertexPoint_mem_faceCarrier_iff
              w s.1.1).mp hw
        let v : s.1.1 :=
          ⟨Rlevel.refined.edgeFirst d, hfirstFace⟩
        let a : LevelAnchor := ⟨s, Sum.inl v⟩
        have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
        have heq :
            Rlevel.refined.edgeFirstPoint d =
              Rlevel.refined.facePoint s.1 v := by
          apply Subtype.ext
          rfl
        rw [← hdp, heq]
        exact ha
    · obtain ⟨d, -, hdp⟩ := Finset.mem_image.mp hpSecond
      have hsecondFace :
          Rlevel.refined.edgeSecond d ∈ s.1.1 := by
        let w := Rlevel.refined.edgeSecondUsed d
        have hw :
            Rlevel.refined.vertexPoint w ∈
              Rlevel.refined.faceCarrier s.1.1 := by
          rw [Rlevel.refined.vertexPoint_edgeSecondUsed d,
            hdp]
          exact hpFace
        exact
          (Rlevel.refined.vertexPoint_mem_faceCarrier_iff
            w s.1.1).mp hw
      let v : s.1.1 :=
        ⟨Rlevel.refined.edgeSecond d, hsecondFace⟩
      let a : LevelAnchor := ⟨s, Sum.inl v⟩
      have ha := hAnchorLevelPoint_mem_localVertexLevelPoints a
      have heq :
          Rlevel.refined.edgeSecondPoint d =
            Rlevel.refined.facePoint s.1 v := by
        apply Subtype.ext
        rfl
      rw [← hdp, heq]
      exact ha
  have edge_subset_selectedFace_of_openPoint
      (e : Rlevel.refined.Edge) (s : Rlevel.refined.Face)
      (q : Rlevel.refined.realization)
      (hqOpen :
        q ∈ Rlevel.refined.edgePath e ''
          {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1})
      (hqFace : q ∈ Rlevel.refined.faceCarrier s.1) :
      e.1 ⊆ s.1 := by
    rintro v hv
    obtain ⟨r, hr, hqr⟩ := hqOpen
    by_contra hvs
    have hzero : q.1 v = 0 := hqFace v hvs
    have hpositive :
        0 < (Rlevel.refined.edgePath e r).1 v := by
      rw [Rlevel.refined.edge_eq_pair e] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [Rlevel.refined.edgePath_apply_first]
        exact sub_pos.mpr hr.2
      · rw [Rlevel.refined.edgePath_apply_second]
        exact hr.1
    rw [hqr] at hpositive
    linarith
  have localMark_endpoint_or_selectedEdge
      (e : Rlevel.refined.Edge) (p : Rlevel.refined.realization)
      (hpEdge : p ∈ Rlevel.refined.faceCarrier e.1)
      (hpLocal : p ∈ localVertexLevelPoints) :
      (∃ s : {s : T.toIntrinsic.LevelFace n //
          s ∈ selectedLevelFaces}, e.1 ⊆ s.1.1) ∨
        p = Rlevel.refined.edgeFirstPoint e ∨
        p = Rlevel.refined.edgeSecondPoint e := by
    obtain ⟨u, -, hup⟩ := Finset.mem_image.mp hpLocal
    obtain ⟨t, ht, hut⟩ := u.2
    let tf : localSourceComplex.Face := ⟨t, ht⟩
    let uv : {v // v ∈ tf.1} := ⟨u.1, hut⟩
    have huFace :
        localVertexLevelPoint u ∈
          Rlevel.refined.faceCarrier
            (localFaceLevelFace tf).1.1 := by
      have huv :
          (⟨uv.1, ⟨tf.1, tf.2, uv.2⟩⟩ :
              localSourceComplex.UsedVertex) = u :=
        Subtype.ext rfl
      simpa only [huv] using localVertexLevelPoint_mem_face tf uv
    have hpFace :
        p ∈ Rlevel.refined.faceCarrier
          (localFaceLevelFace tf).1.1 := by
      rw [← hup]
      exact huFace
    by_cases hes : e.1 ⊆ (localFaceLevelFace tf).1.1
    · exact Or.inl ⟨localFaceLevelFace tf, hes⟩
    · let r := Rlevel.refined.edgeParameter e p hpEdge
      have hpath :
          Rlevel.refined.edgePath e r = p :=
        Rlevel.refined.edgePath_edgeParameter e p hpEdge
      by_cases hr0 : r.1 = 0
      · apply Or.inr
        apply Or.inl
        calc
          p = Rlevel.refined.edgePath e r := hpath.symm
          _ =
              Rlevel.refined.edgePath e
                ⟨0, by simp⟩ := by
            apply congrArg (Rlevel.refined.edgePath e)
            exact Subtype.ext hr0
          _ = Rlevel.refined.edgeFirstPoint e :=
            Rlevel.refined.edgePath_zero e
      · by_cases hr1 : r.1 = 1
        · apply Or.inr
          apply Or.inr
          calc
            p = Rlevel.refined.edgePath e r := hpath.symm
            _ =
                Rlevel.refined.edgePath e
                  ⟨1, by simp⟩ := by
              apply congrArg (Rlevel.refined.edgePath e)
              exact Subtype.ext hr1
            _ = Rlevel.refined.edgeSecondPoint e :=
              Rlevel.refined.edgePath_one e
        · have hrOpen : 0 < r.1 ∧ r.1 < 1 := by
            exact
              ⟨lt_of_le_of_ne r.2.1 (Ne.symm hr0),
                lt_of_le_of_ne r.2.2 hr1⟩
          have hes' :
              e.1 ⊆ (localFaceLevelFace tf).1.1 :=
            edge_subset_selectedFace_of_openPoint e
              (localFaceLevelFace tf).1 p
              ⟨r, hrOpen, hpath⟩ hpFace
          exact (hes hes').elim
  have selectedFace_of_fanInterval_endpoints_local
      (f : OutsideFanFace)
      (hp₀ :
        (boundaryMarking.fanFirstVertex f.1).1 ∈
          localVertexLevelPoints)
      (hp₁ :
        (boundaryMarking.fanSecondVertex f.1).1 ∈
          localVertexLevelPoints) :
      ∃ s : {s : T.toIntrinsic.LevelFace n //
          s ∈ selectedLevelFaces},
        (Rlevel.refined.faceEdge f.1.1 f.1.2.1).1 ⊆ s.1.1 := by
    let e := Rlevel.refined.faceEdge f.1.1 f.1.2.1
    let p₀ := (boundaryMarking.fanFirstVertex f.1).1
    let p₁ := (boundaryMarking.fanSecondVertex f.1).1
    have hp₀Edge : p₀ ∈ Rlevel.refined.faceCarrier e.1 :=
      ((boundaryMarking.mem_edgeMarks_iff e p₀).mp
        (boundaryMarking.edgeIntervalFirst_mem_edgeMarks
          e f.1.2.2)).2
    have hp₁Edge : p₁ ∈ Rlevel.refined.faceCarrier e.1 :=
      ((boundaryMarking.mem_edgeMarks_iff e p₁).mp
        (boundaryMarking.edgeIntervalSecond_mem_edgeMarks
          e f.1.2.2)).2
    rcases localMark_endpoint_or_selectedEdge e p₀ hp₀Edge hp₀ with hs | hp₀End
    · exact hs
    rcases localMark_endpoint_or_selectedEdge e p₁ hp₁Edge hp₁ with hs | hp₁End
    · exact hs
    have hparamPath (r : Set.Icc (0 : ℝ) 1) :
        boundaryMarking.edgeParameterValue e
            (Rlevel.refined.edgePath e r) = r.1 := by
      rw [boundaryMarking.edgeParameterValue_eq e (by
          rw [← Rlevel.refined.range_edgePath e]
          exact ⟨r, rfl⟩),
        Rlevel.refined.edgeParameter_eq_secondCoordinate,
        Rlevel.refined.edgePath_apply_second]
    have hfirstParam :
        boundaryMarking.edgeParameterValue e
            (Rlevel.refined.edgeFirstPoint e) = 0 := by
      rw [← Rlevel.refined.edgePath_zero e, hparamPath]
    have hsecondParam :
        boundaryMarking.edgeParameterValue e
            (Rlevel.refined.edgeSecondPoint e) = 1 := by
      rw [← Rlevel.refined.edgePath_one e, hparamPath]
    have hmidPoint :
        Rlevel.refined.edgePath e edgeHalf ∈
          boundaryMarking.points := by
      apply IntrinsicTwoComplex.EdgeMarking.subset_points_ofFinset
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    have hmidMark :
        Rlevel.refined.edgePath e edgeHalf ∈
          boundaryMarking.edgeMarks e := by
      rw [boundaryMarking.mem_edgeMarks_iff e]
      refine ⟨hmidPoint, ?_⟩
      rw [← Rlevel.refined.range_edgePath e]
      exact ⟨edgeHalf, rfl⟩
    have hmidParam :
        boundaryMarking.edgeParameterValue e
            (Rlevel.refined.edgePath e edgeHalf) = 1 / 2 := by
      rw [hparamPath]
    rcases hp₀End with hp₀First | hp₀Second <;>
      rcases hp₁End with hp₁First | hp₁Second
    · exact False.elim
        (boundaryMarking.edgeIntervalFirst_ne_second e f.1.2.2
          (hp₀First.trans hp₁First.symm))
    · exfalso
      apply boundaryMarking.not_edgeMark_parameter_mem_Ioo
        e f.1.2.2 hmidMark
      change
        boundaryMarking.edgeParameterValue e
              (Rlevel.refined.edgePath e edgeHalf) ∈
          Set.Ioo
            (boundaryMarking.edgeParameterValue e p₀)
            (boundaryMarking.edgeParameterValue e p₁)
      rw [hp₀First, hp₁Second, hfirstParam, hsecondParam, hmidParam]
      norm_num
    · have hlt :=
        boundaryMarking.edgeInterval_parameter_lt e f.1.2.2
      change
        boundaryMarking.edgeParameterValue e p₀ <
          boundaryMarking.edgeParameterValue e p₁ at hlt
      rw [hp₀Second, hp₁First, hsecondParam, hfirstParam] at hlt
      norm_num at hlt
    · exact False.elim
        (boundaryMarking.edgeIntervalFirst_ne_second e f.1.2.2
          (hp₀Second.trans hp₁Second.symm))
  have mixedOldFaceMap_eq_of_extendedCoordinates
      {f g : MixedOldFace}
      {x : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f}}
      {y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices g}}
      (hxy :
        extendFaceCoordinates (mixedOldFaceVertices f) x =
          extendFaceCoordinates (mixedOldFaceVertices g) y) :
      mixedOldFaceMap f x = mixedOldFaceMap g y := by
    apply Subtype.ext
    rw [mixedOldFaceMap_val f x, mixedOldFaceMap_val g y, hxy]
  have localMixedFaceMap_mem_parent
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)}) :
      mixedOldFaceMap (Sum.inl t) x ∈
        Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1 := by
    let x₀ := relabelUnivSimplex
      (localFaceOldVertexEmbedding t) x
    let z := localSourceComplex.faceStandardMap t x₀
    have hzSupport : ∀ v ∉ t.1, z.1 v = 0 := by
      intro v hv
      rw [localSourceComplex.faceStandardMap_val]
      exact extendFaceCoordinates_of_notMem t.1 x₀ hv
    have hsource :=
      localFaceLevelFace_contains_realization t z hzSupport
    obtain ⟨q, hqFace, hq⟩ := hsource
    change Rlevel.homeo.symm (source₁ z) ∈
      Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1
    have heq :
        Rlevel.homeo.symm (source₁ z) = q := by
      apply Rlevel.homeo.injective
      rw [Rlevel.homeo.apply_symm_apply]
      exact hq.symm
    rwa [heq]
  have localVertexLevelPoint_mem_marking
      (v : localSourceComplex.UsedVertex) :
      localVertexLevelPoint v ∈ boundaryMarking.points := by
    apply IntrinsicTwoComplex.EdgeMarking.subset_points_ofFinset
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have positive_localVertex_mem_edge
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : Rlevel.refined.Edge)
      (hqEdge :
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t x)) ∈
          Rlevel.refined.faceCarrier e.1)
      (v : {v // v ∈ t.1}) (hv : 0 < x v) :
      localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
        Rlevel.refined.faceCarrier e.1 := by
    intro k hk
    have hmap := congrFun (localFaceLevelMap_val t x) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hmap
    have hsumZero :
        (∑ w : {w // w ∈ t.1},
          x w *
            (localVertexLevelPoint
              ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k) = 0 := by
      rw [← hmap]
      exact hqEdge k hk
    have htermNonneg :
        0 ≤ x v *
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k :=
      mul_nonneg (x.2.1 v)
        ((localVertexLevelPoint
          ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).2.1.1 k)
    have htermLe :
        x v *
            (localVertexLevelPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k ≤
          ∑ w : {w // w ∈ t.1},
            x w *
              (localVertexLevelPoint
                ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k := by
      simpa only using (Finset.single_le_sum
        (s := (Finset.univ : Finset {w // w ∈ t.1}))
        (a := v)
        (f := fun w ↦ x w *
          (localVertexLevelPoint
            ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).1 k)
        (by
          intro w _
          exact mul_nonneg (x.2.1 w)
            ((localVertexLevelPoint
              ⟨w.1, ⟨t.1, t.2, w.2⟩⟩).2.1.1 k))
        (Finset.mem_univ v))
    have hprod :
        x v *
          (localVertexLevelPoint
            ⟨v.1, ⟨t.1, t.2, v.2⟩⟩).1 k = 0 := by
      apply le_antisymm
      · rw [hsumZero] at htermLe
        exact htermLe
      · exact htermNonneg
    exact (mul_eq_zero.mp hprod).resolve_left hv.ne'
  have localFace_edgeParameter_eq_sum
      (t : localSourceComplex.Face)
      (x : stdSimplex ℝ {v // v ∈ t.1})
      (e : Rlevel.refined.Edge)
      (hqEdge :
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t x)) ∈
          Rlevel.refined.faceCarrier e.1) :
      boundaryMarking.edgeParameterValue e
          (Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t x))) =
        ∑ v : {v // v ∈ t.1}, x v *
          boundaryMarking.edgeParameterValue e
            (localVertexLevelPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
    let q :=
      Rlevel.homeo.symm
        (source₁ (localSourceComplex.faceStandardMap t x))
    rw [boundaryMarking.edgeParameterValue_eq e hqEdge,
      Rlevel.refined.edgeParameter_eq_secondCoordinate]
    have hmap := congrFun (localFaceLevelMap_val t x)
      (Rlevel.refined.edgeSecond e)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hmap
    rw [hmap]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hvZero : x v = 0
    · rw [hvZero, zero_mul, zero_mul]
    · have hvPos : 0 < x v :=
        lt_of_le_of_ne (x.2.1 v) (Ne.symm hvZero)
      have hvEdge :=
        positive_localVertex_mem_edge t x e hqEdge v hvPos
      rw [boundaryMarking.edgeParameterValue_eq e hvEdge,
        Rlevel.refined.edgeParameter_eq_secondCoordinate]
  have edge_subset_face_of_openPoint
      (e : Rlevel.refined.Edge) (s : Rlevel.refined.Face)
      (q : Rlevel.refined.realization)
      (hqOpen :
        q ∈ Rlevel.refined.edgePath e ''
          {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1})
      (hqFace : q ∈ Rlevel.refined.faceCarrier s.1) :
      e.1 ⊆ s.1 := by
    rintro v hv
    obtain ⟨r, hr, hqr⟩ := hqOpen
    by_contra hvs
    have hzero : q.1 v = 0 := hqFace v hvs
    have hpositive :
        0 < (Rlevel.refined.edgePath e r).1 v := by
      rw [Rlevel.refined.edge_eq_pair e] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [Rlevel.refined.edgePath_apply_first]
        exact sub_pos.mpr hr.2
      · rw [Rlevel.refined.edgePath_apply_second]
        exact hr.1
    rw [hqr] at hpositive
    linarith
  have localUsedVertex_mem_face_of_map_eq
      (t : localSourceComplex.Face)
      (z : stdSimplex ℝ {v // v ∈ t.1})
      (u : localSourceComplex.UsedVertex)
      (hzu :
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t z)) =
          localVertexLevelPoint u) :
      u.1 ∈ t.1 := by
    have hsource :
        source₁ (localSourceComplex.faceStandardMap t z) =
          source₁ (localSourceComplex.vertexPoint u) := by
      apply Rlevel.homeo.symm.injective
      change
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t z)) =
          Rlevel.homeo.symm
            (source₁ (localSourceComplex.vertexPoint u))
      exact hzu
    have hlocal :
        localSourceComplex.faceStandardMap t z =
          localSourceComplex.vertexPoint u :=
      hsource₁Embedding.injective hsource
    by_contra hut
    have hcoord := congrArg
      (fun q : localSourceComplex.realization ↦ q.1 u.1) hlocal
    rw [localSourceComplex.faceStandardMap_val,
      extendFaceCoordinates_of_notMem t.1 z hut] at hcoord
    have hone :
        (localSourceComplex.vertexPoint u).1 u.1 = (1 : ℝ) := by
      simp [IntrinsicTwoComplex.vertexPoint]
    rw [hone] at hcoord
    exact zero_ne_one hcoord
  have exists_localFacePoint_eq_of_edgeParameter_between
      (t : localSourceComplex.Face)
      (e : Rlevel.refined.Edge)
      (a b : {v // v ∈ t.1})
      (p : Rlevel.refined.realization)
      (haEdge :
        localVertexLevelPoint
            ⟨a.1, ⟨t.1, t.2, a.2⟩⟩ ∈
          Rlevel.refined.faceCarrier e.1)
      (hbEdge :
        localVertexLevelPoint
            ⟨b.1, ⟨t.1, t.2, b.2⟩⟩ ∈
          Rlevel.refined.faceCarrier e.1)
      (hpEdge : p ∈ Rlevel.refined.faceCarrier e.1)
      (hap :
        boundaryMarking.edgeParameterValue e
            (localVertexLevelPoint
              ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) ≤
          boundaryMarking.edgeParameterValue e p)
      (hpb :
        boundaryMarking.edgeParameterValue e p ≤
          boundaryMarking.edgeParameterValue e
            (localVertexLevelPoint
              ⟨b.1, ⟨t.1, t.2, b.2⟩⟩))
      (hab :
        boundaryMarking.edgeParameterValue e
            (localVertexLevelPoint
              ⟨a.1, ⟨t.1, t.2, a.2⟩⟩) <
          boundaryMarking.edgeParameterValue e
            (localVertexLevelPoint
              ⟨b.1, ⟨t.1, t.2, b.2⟩⟩)) :
      ∃ z : stdSimplex ℝ {v // v ∈ t.1},
        Rlevel.homeo.symm
            (source₁ (localSourceComplex.faceStandardMap t z)) = p := by
    let A :=
      localVertexLevelPoint
        ⟨a.1, ⟨t.1, t.2, a.2⟩⟩
    let B :=
      localVertexLevelPoint
        ⟨b.1, ⟨t.1, t.2, b.2⟩⟩
    let ar := boundaryMarking.edgeParameterValue e A
    let br := boundaryMarking.edgeParameterValue e B
    let pr := boundaryMarking.edgeParameterValue e p
    have haEdge' : A ∈ Rlevel.refined.faceCarrier e.1 := haEdge
    have hbEdge' : B ∈ Rlevel.refined.faceCarrier e.1 := hbEdge
    have hden : 0 < br - ar := sub_pos.mpr hab
    let r₀ := (pr - ar) / (br - ar)
    have hr₀ : r₀ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hap) hden.le
      · rw [div_le_one hden]
        linarith
    let r : Set.Icc (0 : ℝ) 1 := ⟨r₀, hr₀⟩
    let z :=
      localFaceSimplexLineMap t
        (stdSimplex.vertex a) (stdSimplex.vertex b) r
    refine ⟨z, ?_⟩
    let q :=
      Rlevel.homeo.symm
        (source₁ (localSourceComplex.faceStandardMap t z))
    have hqLine :
        q.1 = AffineMap.lineMap A.1 B.1 r.1 := by
      change
        (Rlevel.homeo.symm
          (source₁
            (localSourceComplex.faceStandardMap t
              (localFaceSimplexLineMap t
                (stdSimplex.vertex a) (stdSimplex.vertex b) r)))).1 =
          AffineMap.lineMap A.1 B.1 r.1
      rw [localFaceLevelMap_simplexLineMap,
        localFaceLevelMap_vertex, localFaceLevelMap_vertex]
    have hqEdge : q ∈ Rlevel.refined.faceCarrier e.1 := by
      intro k hk
      rw [hqLine]
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [haEdge' k hk, hbEdge' k hk]
      ring
    have hqParameter :
        boundaryMarking.edgeParameterValue e q = pr := by
      rw [boundaryMarking.edgeParameterValue_eq e hqEdge,
        Rlevel.refined.edgeParameter_eq_secondCoordinate,
        hqLine, AffineMap.lineMap_apply_module]
      have haParameter :
          A.1 (Rlevel.refined.edgeSecond e) = ar := by
        change A.1 (Rlevel.refined.edgeSecond e) =
          boundaryMarking.edgeParameterValue e A
        rw [boundaryMarking.edgeParameterValue_eq e haEdge',
          Rlevel.refined.edgeParameter_eq_secondCoordinate]
      have hbParameter :
          B.1 (Rlevel.refined.edgeSecond e) = br := by
        change B.1 (Rlevel.refined.edgeSecond e) =
          boundaryMarking.edgeParameterValue e B
        rw [boundaryMarking.edgeParameterValue_eq e hbEdge',
          Rlevel.refined.edgeParameter_eq_secondCoordinate]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [haParameter, hbParameter]
      change (1 - r₀) * ar + r₀ * br = pr
      dsimp only [r₀]
      field_simp
      ring
    change q = p
    exact
      boundaryMarking.edgeParameterValue_injOn e hqEdge hpEdge
        (hqParameter.trans rfl)
  have localFanMixedFaceMap_eq_iff
      {t : localSourceComplex.Face} {f : OutsideFanFace}
      {x : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inl t)}}
      {y : stdSimplex ℝ
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)}} :
      mixedOldFaceMap (Sum.inl t) x =
          mixedOldFaceMap (Sum.inr f) y ↔
        extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inl t)) x =
          extendFaceCoordinates
            (mixedOldFaceVertices (Sum.inr f)) y := by
    let x₀ := relabelUnivSimplex
      (localFaceOldVertexEmbedding t) x
    let yG := relabelFaceSimplex fanOldVertexEmbedding
      (boundaryMarking.globalFanFaceVertices f.1) y
    let y₀ := boundaryMarking.fanRelabelSimplex f.1 yG
    constructor
    · intro hxy
      have hyParent :
          boundaryMarking.fanFaceMap f.1 y₀ ∈
            Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1 := by
        have hlocal := localMixedFaceMap_mem_parent t x
        have hfan :
            boundaryMarking.fanFaceMap f.1 y₀ =
              mixedOldFaceMap (Sum.inr f) y := rfl
        rw [hfan, ← hxy]
        exact hlocal
      have hparentNe :
          f.1.1 ≠ (localFaceLevelFace t).1 := by
        intro h
        apply f.2
        rw [h]
        exact (localFaceLevelFace t).2
      have hyCenter :
          y₀ (boundaryMarking.fanCenterVertex f.1) = 0 :=
        boundaryMarking.fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
          f.1 (localFaceLevelFace t).1 hparentNe y₀ hyParent
      by_cases hyPos :
          0 < y₀ (boundaryMarking.fanFirstVertex f.1) ∧
            0 < y₀ (boundaryMarking.fanSecondVertex f.1)
      · let e := Rlevel.refined.faceEdge f.1.1 f.1.2.1
        let q := mixedOldFaceMap (Sum.inl t) x
        let p₀ := (boundaryMarking.fanFirstVertex f.1).1
        let p₁ := (boundaryMarking.fanSecondVertex f.1).1
        let a₀ := boundaryMarking.edgeParameterValue e p₀
        let a₁ := boundaryMarking.edgeParameterValue e p₁
        let z₀ := boundaryMarking.edgeParameterValue e q
        have hfanEq :
            boundaryMarking.fanFaceMap f.1 y₀ = q := by
          exact hxy.symm
        have hqOpen :
            q ∈ Rlevel.refined.edgePath e ''
              {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} := by
          rw [← hfanEq]
          exact
            boundaryMarking.fanFaceMap_mem_edgePath_image_Ioo_of_center_zero_of_base_weights_pos
              f.1 y₀ hyCenter hyPos.1 hyPos.2
        have hqEdge : q ∈ Rlevel.refined.faceCarrier e.1 := by
          rw [← hfanEq]
          exact
            boundaryMarking.fanFaceMap_mem_baseEdge_of_center_eq_zero
              f.1 y₀ hyCenter
        have heSelected :
            e.1 ⊆ (localFaceLevelFace t).1.1 :=
          edge_subset_face_of_openPoint e (localFaceLevelFace t).1
            q hqOpen (localMixedFaceMap_mem_parent t x)
        have hzInterval : z₀ ∈ Set.Ioo a₀ a₁ := by
          change
            boundaryMarking.edgeParameterValue e q ∈
              Set.Ioo
                (boundaryMarking.edgeParameterValue e
                  (boundaryMarking.fanFirstVertex f.1).1)
                (boundaryMarking.edgeParameterValue e
                  (boundaryMarking.fanSecondVertex f.1).1)
          rw [← hfanEq]
          exact
            boundaryMarking.edgeParameterValue_fanFaceMap_mem_Ioo_of_center_eq_zero
              f.1 y₀ hyCenter hyPos.1 hyPos.2
        have hzAverage :
            z₀ =
              ∑ v : {v // v ∈ t.1}, x₀ v *
                boundaryMarking.edgeParameterValue e
                  (localVertexLevelPoint
                    ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
          exact localFace_edgeParameter_eq_sum t x₀ e hqEdge
        have existsLow :
            ∃ v : {v // v ∈ t.1},
              0 < x₀ v ∧
                boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ≤ a₀ := by
          by_contra hLow
          have hterm (v : {v // v ∈ t.1}) :
              x₀ v * a₁ ≤
                x₀ v *
                  boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
            by_cases hvZero : x₀ v = 0
            · simp [hvZero]
            · have hvPos : 0 < x₀ v :=
                lt_of_le_of_ne (x₀.2.1 v) (Ne.symm hvZero)
              have hvNotLow :
                  ¬boundaryMarking.edgeParameterValue e
                      (localVertexLevelPoint
                        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ≤ a₀ := by
                intro hv
                exact hLow ⟨v, hvPos, hv⟩
              have hvEdge :=
                positive_localVertex_mem_edge t x₀ e hqEdge v hvPos
              have hvMark :
                  localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
                    boundaryMarking.edgeMarks e :=
                (boundaryMarking.mem_edgeMarks_iff e _).mpr
                  ⟨localVertexLevelPoint_mem_marking
                    ⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hvEdge⟩
              have hvNotOpen :=
                boundaryMarking.not_edgeMark_parameter_mem_Ioo
                  e f.1.2.2 hvMark
              have hvAbove :
                  a₁ ≤
                    boundaryMarking.edgeParameterValue e
                      (localVertexLevelPoint
                        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
                apply le_of_not_gt
                intro hvBelow
                apply hvNotOpen
                exact ⟨lt_of_not_ge hvNotLow, hvBelow⟩
              exact mul_le_mul_of_nonneg_left hvAbove (x₀.2.1 v)
          have hsum :
              a₁ ≤
                ∑ v : {v // v ∈ t.1}, x₀ v *
                  boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
            calc
              a₁ = (∑ v : {v // v ∈ t.1}, x₀ v) * a₁ := by
                have hxSum :
                    ∑ v : {v // v ∈ t.1}, x₀ v = 1 := x₀.2.2
                rw [hxSum, one_mul]
              _ = ∑ v : {v // v ∈ t.1}, x₀ v * a₁ := by
                rw [Finset.sum_mul]
              _ ≤ _ := Finset.sum_le_sum fun v _ ↦ hterm v
          rw [← hzAverage] at hsum
          exact (not_le_of_gt hzInterval.2) hsum
        have existsHigh :
            ∃ v : {v // v ∈ t.1},
              0 < x₀ v ∧
                a₁ ≤
                  boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
          by_contra hHigh
          have hterm (v : {v // v ∈ t.1}) :
              x₀ v *
                  boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ≤
                x₀ v * a₀ := by
            by_cases hvZero : x₀ v = 0
            · simp [hvZero]
            · have hvPos : 0 < x₀ v :=
                lt_of_le_of_ne (x₀.2.1 v) (Ne.symm hvZero)
              have hvNotHigh :
                  ¬a₁ ≤
                    boundaryMarking.edgeParameterValue e
                      (localVertexLevelPoint
                        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) := by
                intro hv
                exact hHigh ⟨v, hvPos, hv⟩
              have hvEdge :=
                positive_localVertex_mem_edge t x₀ e hqEdge v hvPos
              have hvMark :
                  localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
                    boundaryMarking.edgeMarks e :=
                (boundaryMarking.mem_edgeMarks_iff e _).mpr
                  ⟨localVertexLevelPoint_mem_marking
                    ⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hvEdge⟩
              have hvNotOpen :=
                boundaryMarking.not_edgeMark_parameter_mem_Ioo
                  e f.1.2.2 hvMark
              have hvBelow :
                  boundaryMarking.edgeParameterValue e
                      (localVertexLevelPoint
                        ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ≤ a₀ := by
                apply le_of_not_gt
                intro hvAbove
                apply hvNotOpen
                exact ⟨hvAbove, lt_of_not_ge hvNotHigh⟩
              exact mul_le_mul_of_nonneg_left hvBelow (x₀.2.1 v)
          have hsum :
              (∑ v : {v // v ∈ t.1}, x₀ v *
                  boundaryMarking.edgeParameterValue e
                    (localVertexLevelPoint
                      ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)) ≤ a₀ := by
            calc
              _ ≤ ∑ v : {v // v ∈ t.1}, x₀ v * a₀ :=
                Finset.sum_le_sum fun v _ ↦ hterm v
              _ = (∑ v : {v // v ∈ t.1}, x₀ v) * a₀ := by
                rw [Finset.sum_mul]
              _ = a₀ := by
                have hxSum :
                    ∑ v : {v // v ∈ t.1}, x₀ v = 1 := x₀.2.2
                rw [hxSum, one_mul]
          rw [← hzAverage] at hsum
          exact (not_le_of_gt hzInterval.1) hsum
        obtain ⟨lo, hloPos, hlo⟩ := existsLow
        obtain ⟨hi, hhiPos, hhi⟩ := existsHigh
        have hloEdge :=
          positive_localVertex_mem_edge t x₀ e hqEdge lo hloPos
        have hhiEdge :=
          positive_localVertex_mem_edge t x₀ e hqEdge hi hhiPos
        have hp₀Mark :
            p₀ ∈ boundaryMarking.edgeMarks e := by
          exact
            boundaryMarking.edgeIntervalFirst_mem_edgeMarks
              e f.1.2.2
        have hp₁Mark :
            p₁ ∈ boundaryMarking.edgeMarks e := by
          exact
            boundaryMarking.edgeIntervalSecond_mem_edgeMarks
              e f.1.2.2
        have hp₀Edge :=
          ((boundaryMarking.mem_edgeMarks_iff e p₀).mp hp₀Mark).2
        have hp₁Edge :=
          ((boundaryMarking.mem_edgeMarks_iff e p₁).mp hp₁Mark).2
        have hp₀Local :=
          interfaceEdgeMarks_subset_local
            (localFaceLevelFace t) e heSelected p₀ hp₀Mark
        have hp₁Local :=
          interfaceEdgeMarks_subset_local
            (localFaceLevelFace t) e heSelected p₁ hp₁Mark
        obtain ⟨u₀, -, hu₀⟩ := Finset.mem_image.mp hp₀Local
        obtain ⟨u₁, -, hu₁⟩ := Finset.mem_image.mp hp₁Local
        have hlohi :
            boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) <
              boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) := by
          calc
            _ ≤ a₀ := hlo
            _ < a₁ := hzInterval.1.trans hzInterval.2
            _ ≤ _ := hhi
        have hp₀hi :
            boundaryMarking.edgeParameterValue e p₀ ≤
              boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨hi.1, ⟨t.1, t.2, hi.2⟩⟩) := by
          change a₀ ≤ _
          exact le_trans (hzInterval.1.trans hzInterval.2).le hhi
        have hloP₁ :
            boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨lo.1, ⟨t.1, t.2, lo.2⟩⟩) ≤
              boundaryMarking.edgeParameterValue e p₁ := by
          change _ ≤ a₁
          exact le_trans hlo (hzInterval.1.trans hzInterval.2).le
        obtain ⟨zAt, hzAt⟩ :=
          exists_localFacePoint_eq_of_edgeParameter_between
            t e lo hi p₀ hloEdge hhiEdge hp₀Edge hlo
              hp₀hi hlohi
        obtain ⟨zBt, hzBt⟩ :=
          exists_localFacePoint_eq_of_edgeParameter_between
            t e lo hi p₁ hloEdge hhiEdge hp₁Edge
              hloP₁ hhi hlohi
        have hu₀Face : u₀.1 ∈ t.1 :=
          localUsedVertex_mem_face_of_map_eq
            t zAt u₀ (hzAt.trans hu₀.symm)
        have hu₁Face : u₁.1 ∈ t.1 :=
          localUsedVertex_mem_face_of_map_eq
            t zBt u₁ (hzBt.trans hu₁.symm)
        let v₀t : {v // v ∈ t.1} := ⟨u₀.1, hu₀Face⟩
        let v₁t : {v // v ∈ t.1} := ⟨u₁.1, hu₁Face⟩
        have hv₀Local :
            localFaceOldVertexEmbedding t v₀t =
              localOldVertexEmbedding u₀ := by
          apply Subtype.ext
          rfl
        have hv₁Local :
            localFaceOldVertexEmbedding t v₁t =
              localOldVertexEmbedding u₁ := by
          apply Subtype.ext
          rfl
        have hw₀LocalMem :
            localOldVertexEmbedding u₀ ∈
              mixedOldFaceVertices (Sum.inl t) := by
          change localOldVertexEmbedding u₀ ∈
            (Finset.univ : Finset {v // v ∈ t.1}).map
              (localFaceOldVertexEmbedding t)
          exact Finset.mem_map.mpr
            ⟨v₀t, Finset.mem_univ v₀t, hv₀Local⟩
        have hw₁LocalMem :
            localOldVertexEmbedding u₁ ∈
              mixedOldFaceVertices (Sum.inl t) := by
          change localOldVertexEmbedding u₁ ∈
            (Finset.univ : Finset {v // v ∈ t.1}).map
              (localFaceOldVertexEmbedding t)
          exact Finset.mem_map.mpr
            ⟨v₁t, Finset.mem_univ v₁t, hv₁Local⟩
        let w₀Local :
            {v // v ∈ mixedOldFaceVertices (Sum.inl t)} :=
          ⟨localOldVertexEmbedding u₀, hw₀LocalMem⟩
        let w₁Local :
            {v // v ∈ mixedOldFaceVertices (Sum.inl t)} :=
          ⟨localOldVertexEmbedding u₁, hw₁LocalMem⟩
        let gv₀ : boundaryMarking.FanVertex :=
          boundaryMarking.fanVertexEmbedding f.1
            (boundaryMarking.fanFirstVertex f.1)
        let gv₁ : boundaryMarking.FanVertex :=
          boundaryMarking.fanVertexEmbedding f.1
            (boundaryMarking.fanSecondVertex f.1)
        have hgv₀Mem :
            gv₀ ∈ boundaryMarking.globalFanFaceVertices f.1 :=
          (boundaryMarking.mem_globalFanFaceVertices_iff f.1 gv₀).mpr
            (boundaryMarking.fanFirstVertex f.1).2
        have hgv₁Mem :
            gv₁ ∈ boundaryMarking.globalFanFaceVertices f.1 :=
          (boundaryMarking.mem_globalFanFaceVertices_iff f.1 gv₁).mpr
            (boundaryMarking.fanSecondVertex f.1).2
        have hw₀FanMem :
            fanOldVertexEmbedding gv₀ ∈
              mixedOldFaceVertices (Sum.inr f) := by
          change fanOldVertexEmbedding gv₀ ∈
            (boundaryMarking.globalFanFaceVertices f.1).map
              fanOldVertexEmbedding
          exact Finset.mem_map.mpr ⟨gv₀, hgv₀Mem, rfl⟩
        have hw₁FanMem :
            fanOldVertexEmbedding gv₁ ∈
              mixedOldFaceVertices (Sum.inr f) := by
          change fanOldVertexEmbedding gv₁ ∈
            (boundaryMarking.globalFanFaceVertices f.1).map
              fanOldVertexEmbedding
          exact Finset.mem_map.mpr ⟨gv₁, hgv₁Mem, rfl⟩
        let w₀Fan :
            {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
          ⟨fanOldVertexEmbedding gv₀, hw₀FanMem⟩
        let w₁Fan :
            {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
          ⟨fanOldVertexEmbedding gv₁, hw₁FanMem⟩
        have hw₀Eq : w₀Local.1 = w₀Fan.1 := by
          apply Subtype.ext
          exact hu₀
        have hw₁Eq : w₁Local.1 = w₁Fan.1 := by
          apply Subtype.ext
          exact hu₁
        let β := y₀ (boundaryMarking.fanSecondVertex f.1)
        have hβIcc : β ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨y₀.2.1 _, stdSimplex.le_one y₀ _⟩
        let r : Set.Icc (0 : ℝ) 1 := ⟨β, hβIcc⟩
        let xLine :=
          mixedFaceSimplexLineMap (Sum.inl t)
            (stdSimplex.vertex w₀Local)
            (stdSimplex.vertex w₁Local) r
        let yLine :=
          mixedFaceSimplexLineMap (Sum.inr f)
            (stdSimplex.vertex w₀Fan)
            (stdSimplex.vertex w₁Fan) r
        have hlineCoords :
            extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inl t)) xLine =
              extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f)) yLine := by
          dsimp only [xLine, yLine]
          calc
            extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inl t))
                (mixedFaceSimplexLineMap (Sum.inl t)
                  (stdSimplex.vertex w₀Local)
                  (stdSimplex.vertex w₁Local) r) =
                (1 - r.1) •
                    extendFaceCoordinates
                      (mixedOldFaceVertices (Sum.inl t))
                      (stdSimplex.vertex w₀Local) +
                  r.1 •
                    extendFaceCoordinates
                      (mixedOldFaceVertices (Sum.inl t))
                      (stdSimplex.vertex w₁Local) :=
              extend_mixedFaceSimplexLineMap
                (Sum.inl t) _ _ r
            _ = (1 - r.1) • Pi.single w₀Local.1 1 +
                  r.1 • Pi.single w₁Local.1 1 := by
              rw [extend_mixedOldFace_vertex
                  (Sum.inl t) w₀Local,
                extend_mixedOldFace_vertex
                  (Sum.inl t) w₁Local]
            _ = (1 - r.1) • Pi.single w₀Fan.1 1 +
                  r.1 • Pi.single w₁Fan.1 1 := by
              rw [hw₀Eq, hw₁Eq]
            _ = (1 - r.1) •
                    extendFaceCoordinates
                      (mixedOldFaceVertices (Sum.inr f))
                      (stdSimplex.vertex w₀Fan) +
                  r.1 •
                    extendFaceCoordinates
                      (mixedOldFaceVertices (Sum.inr f))
                      (stdSimplex.vertex w₁Fan) := by
              rw [extend_mixedOldFace_vertex
                  (Sum.inr f) w₀Fan,
                extend_mixedOldFace_vertex
                  (Sum.inr f) w₁Fan]
            _ = extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f))
                (mixedFaceSimplexLineMap (Sum.inr f)
                  (stdSimplex.vertex w₀Fan)
                  (stdSimplex.vertex w₁Fan) r) :=
              (extend_mixedFaceSimplexLineMap
                (Sum.inr f) _ _ r).symm
        have hyLineVal :
            (mixedOldFaceMap (Sum.inr f) yLine).1 =
              AffineMap.lineMap p₀.1 p₁.1 β := by
          dsimp only [yLine]
          calc
            (mixedOldFaceMap (Sum.inr f)
                (mixedFaceSimplexLineMap (Sum.inr f)
                  (stdSimplex.vertex w₀Fan)
                  (stdSimplex.vertex w₁Fan) r)).1 =
                AffineMap.lineMap
                  (mixedOldFaceMap (Sum.inr f)
                    (stdSimplex.vertex w₀Fan)).1
                  (mixedOldFaceMap (Sum.inr f)
                    (stdSimplex.vertex w₁Fan)).1 r.1 :=
              mixedOldFaceMap_simplexLineMap
                (Sum.inr f) _ _ r
            _ = AffineMap.lineMap w₀Fan.1.1.1
                  w₁Fan.1.1.1 r.1 := by
              rw [mixedOldFaceMap_vertex
                  (Sum.inr f) w₀Fan,
                mixedOldFaceMap_vertex
                  (Sum.inr f) w₁Fan]
            _ = AffineMap.lineMap p₀.1 p₁.1 β := by rfl
        have hyLineEdge :
            mixedOldFaceMap (Sum.inr f) yLine ∈
              Rlevel.refined.faceCarrier e.1 := by
          intro k hk
          rw [hyLineVal]
          simp only [AffineMap.lineMap_apply_module,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hp₀Edge k hk, hp₁Edge k hk]
          ring
        have hp₀Parameter :
            p₀.1 (Rlevel.refined.edgeSecond e) = a₀ := by
          change p₀.1 (Rlevel.refined.edgeSecond e) =
            boundaryMarking.edgeParameterValue e p₀
          rw [boundaryMarking.edgeParameterValue_eq e hp₀Edge,
            Rlevel.refined.edgeParameter_eq_secondCoordinate]
        have hp₁Parameter :
            p₁.1 (Rlevel.refined.edgeSecond e) = a₁ := by
          change p₁.1 (Rlevel.refined.edgeSecond e) =
            boundaryMarking.edgeParameterValue e p₁
          rw [boundaryMarking.edgeParameterValue_eq e hp₁Edge,
            Rlevel.refined.edgeParameter_eq_secondCoordinate]
        have hyLineParameter :
            boundaryMarking.edgeParameterValue e
                (mixedOldFaceMap (Sum.inr f) yLine) =
              (1 - β) * a₀ + β * a₁ := by
          rw [boundaryMarking.edgeParameterValue_eq e hyLineEdge,
            Rlevel.refined.edgeParameter_eq_secondCoordinate,
            hyLineVal, AffineMap.lineMap_apply_module]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hp₀Parameter, hp₁Parameter]
        have hqParameter :
            z₀ =
              y₀ (boundaryMarking.fanFirstVertex f.1) * a₀ +
                β * a₁ := by
          change boundaryMarking.edgeParameterValue e q =
            y₀ (boundaryMarking.fanFirstVertex f.1) *
                boundaryMarking.edgeParameterValue e
                  (boundaryMarking.fanFirstVertex f.1).1 +
              y₀ (boundaryMarking.fanSecondVertex f.1) *
                boundaryMarking.edgeParameterValue e
                  (boundaryMarking.fanSecondVertex f.1).1
          rw [← hfanEq]
          exact
            boundaryMarking.edgeParameterValue_fanFaceMap_of_center_eq_zero
              f.1 y₀ hyCenter
        have hbaseSum :=
          boundaryMarking.fanBaseWeights_sum_of_center_eq_zero
            f.1 y₀ hyCenter
        have hfirstCoeff :
            1 - β =
              y₀ (boundaryMarking.fanFirstVertex f.1) := by
          dsimp only [β]
          linarith
        have hyLineEq :
            mixedOldFaceMap (Sum.inr f) yLine = q := by
          apply
            boundaryMarking.edgeParameterValue_injOn e
              hyLineEdge hqEdge
          calc
            boundaryMarking.edgeParameterValue e
                (mixedOldFaceMap (Sum.inr f) yLine) =
                (1 - β) * a₀ + β * a₁ := hyLineParameter
            _ = y₀ (boundaryMarking.fanFirstVertex f.1) * a₀ +
                  β * a₁ := by rw [hfirstCoeff]
            _ = z₀ := hqParameter.symm
            _ = boundaryMarking.edgeParameterValue e q := rfl
        have hyMap :
            mixedOldFaceMap (Sum.inr f) y = q := hxy.symm
        have hyLineSame :
            mixedOldFaceMap (Sum.inr f) yLine =
              mixedOldFaceMap (Sum.inr f) y :=
          hyLineEq.trans hyMap.symm
        have hyLineCoords :
            extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f)) yLine =
              extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f)) y :=
          fanMixedFaceMap_eq_iff.mp hyLineSame
        have hcrossLine :
            mixedOldFaceMap (Sum.inl t) xLine =
              mixedOldFaceMap (Sum.inr f) yLine :=
          mixedOldFaceMap_eq_of_extendedCoordinates
            (f := Sum.inl t) (g := Sum.inr f)
            (x := xLine) (y := yLine) hlineCoords
        have hxLineSame :
            mixedOldFaceMap (Sum.inl t) x =
              mixedOldFaceMap (Sum.inl t) xLine :=
          hxy.trans (hyLineSame.symm.trans hcrossLine.symm)
        have hxLineCoords :
            extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inl t)) x =
              extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inl t)) xLine :=
          localMixedFaceMap_eq_iff.mp hxLineSame
        exact hxLineCoords.trans (hlineCoords.trans hyLineCoords)
      · have endpointCoordinates
            (v : {p // p ∈ boundaryMarking.fanFaceVertices f.1})
            (hvMark : v.1 ∈ boundaryMarking.points)
            (hyv :
              (boundaryMarking.fanFaceMap f.1 y₀).1 = v.1.1) :
            extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inl t)) x =
              extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f)) y := by
          have hyEndpoint :
              mixedOldFaceMap (Sum.inr f) y = v.1 := by
            apply Subtype.ext
            exact hyv
          have hvSelected :
              v.1 ∈
                Rlevel.refined.faceCarrier
                  (localFaceLevelFace t).1.1 := by
            rw [← hyEndpoint, ← hxy]
            exact localMixedFaceMap_mem_parent t x
          have hvLocal :=
            selectedFace_marking_subset_local
              (localFaceLevelFace t) v.1 hvMark hvSelected
          obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hvLocal
          have hxLocal :
              extendFaceCoordinates
                  (mixedOldFaceVertices (Sum.inl t)) x =
                Pi.single (localOldVertexEmbedding u) 1 :=
            mixedLocalExtended_eq_single_of_map_eq_localVertex
              t x u (hxy.trans (hyEndpoint.trans hu.symm))
          have hyFan :
              extendFaceCoordinates
                  (mixedOldFaceVertices (Sum.inr f)) y =
                Pi.single
                  (fanOldVertexEmbedding
                    (boundaryMarking.fanVertexEmbedding f.1 v)) 1 :=
            mixedFanExtended_eq_single_of_map_eq_fanVertex
              f y v hyEndpoint
          have hvertex :
              localOldVertexEmbedding u =
                fanOldVertexEmbedding
                  (boundaryMarking.fanVertexEmbedding f.1 v) := by
            apply Subtype.ext
            exact hu
          rw [hxLocal, hyFan, hvertex]
        rcases
            boundaryMarking.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
              f.1 y₀ hyCenter hyPos with hyFirst | hySecond
        · exact endpointCoordinates
            (boundaryMarking.fanFirstVertex f.1)
            (((boundaryMarking.mem_edgeMarks_iff
              (Rlevel.refined.faceEdge f.1.1 f.1.2.1) _).mp
                (boundaryMarking.edgeIntervalFirst_mem_edgeMarks
                  (Rlevel.refined.faceEdge f.1.1 f.1.2.1)
                  f.1.2.2)).1)
            hyFirst.1
        · exact endpointCoordinates
            (boundaryMarking.fanSecondVertex f.1)
            (((boundaryMarking.mem_edgeMarks_iff
              (Rlevel.refined.faceEdge f.1.1 f.1.2.1) _).mp
                (boundaryMarking.edgeIntervalSecond_mem_edgeMarks
                  (Rlevel.refined.faceEdge f.1.1 f.1.2.1)
                  f.1.2.2)).1)
            hySecond.1
    · intro hcoords
      exact mixedOldFaceMap_eq_of_extendedCoordinates
        (f := Sum.inl t) (g := Sum.inr f)
        (x := x) (y := y) hcoords
  have mixedOldFaceMap_eq_iff
      {f g : MixedOldFace}
      {x : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices f}}
      {y : stdSimplex ℝ {v // v ∈ mixedOldFaceVertices g}} :
      mixedOldFaceMap f x = mixedOldFaceMap g y ↔
        extendFaceCoordinates (mixedOldFaceVertices f) x =
          extendFaceCoordinates (mixedOldFaceVertices g) y := by
    rcases f with t | f <;> rcases g with u | g
    · exact localMixedFaceMap_eq_iff
    · exact localFanMixedFaceMap_eq_iff
    · constructor
      · intro hxy
        exact localFanMixedFaceMap_eq_iff.mp hxy.symm |>.symm
      · intro hcoords
        exact (localFanMixedFaceMap_eq_iff.mpr hcoords.symm).symm
    · exact fanMixedFaceMap_eq_iff
  let usedOldVertices : Finset OldVertex :=
    (Finset.univ : Finset MixedOldFace).biUnion mixedOldFaceVertices
  let UsedOldVertex := {v : OldVertex // v ∈ usedOldVertices}
  let mixedFaceUsedEmbedding (f : MixedOldFace) :
      {v // v ∈ mixedOldFaceVertices f} ↪ UsedOldVertex :=
    { toFun := fun v ↦ ⟨v.1, Finset.mem_biUnion.mpr
          ⟨f, Finset.mem_univ f, v.2⟩⟩
      inj' := by
        intro v w hvw
        exact Subtype.ext
          (congrArg (fun z : UsedOldVertex ↦ z.1) hvw) }
  let mixedUsedFaceVertices (f : MixedOldFace) :
      Finset UsedOldVertex :=
    (Finset.univ : Finset {v // v ∈ mixedOldFaceVertices f}).map
      (mixedFaceUsedEmbedding f)
  let mixedUsedFaceMap (f : MixedOldFace) :
      stdSimplex ℝ {v // v ∈ mixedUsedFaceVertices f} →
        Rlevel.refined.realization :=
    fun x ↦ mixedOldFaceMap f
      (relabelUnivSimplex (mixedFaceUsedEmbedding f) x)
  have mixedUsedFaceVertices_card (f : MixedOldFace) :
      (mixedUsedFaceVertices f).card = 3 := by
    change ((Finset.univ :
        Finset {v // v ∈ mixedOldFaceVertices f}).map
          (mixedFaceUsedEmbedding f)).card = 3
    rw [Finset.card_map, Finset.card_univ, Fintype.card_coe,
      mixedOldFaceVertices_card]
  have continuous_mixedUsedFaceMap (f : MixedOldFace) :
      Continuous (mixedUsedFaceMap f) := by
    exact (continuous_mixedOldFaceMap f).comp
      (stdSimplex.continuous_map
        (univMapSubtypeEquiv (mixedFaceUsedEmbedding f)))
  have mixedUsedExtended_apply
      (f : MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ mixedUsedFaceVertices f})
      (p : UsedOldVertex) :
      extendFaceCoordinates (mixedUsedFaceVertices f) x p =
        extendFaceCoordinates (mixedOldFaceVertices f)
          (relabelUnivSimplex (mixedFaceUsedEmbedding f) x) p.1 := by
    by_cases hp : p.1 ∈ mixedOldFaceVertices f
    · let v : {v // v ∈ mixedOldFaceVertices f} := ⟨p.1, hp⟩
      have hemb :
          mixedFaceUsedEmbedding f v = p := by
        apply Subtype.ext
        rfl
      have hmem :
          mixedFaceUsedEmbedding f v ∈
            mixedUsedFaceVertices f := by
        change mixedFaceUsedEmbedding f v ∈
          (Finset.univ :
            Finset {v // v ∈ mixedOldFaceVertices f}).map
              (mixedFaceUsedEmbedding f)
        exact Finset.mem_map.mpr
          ⟨v, Finset.mem_univ v, rfl⟩
      have hpMem : p ∈ mixedUsedFaceVertices f := by
        rw [← hemb]
        exact hmem
      rw [extendFaceCoordinates_of_mem _ _ hpMem,
        extendFaceCoordinates_of_mem _ _ hp]
      have hleft :
          (⟨p, hpMem⟩ :
              {q // q ∈ mixedUsedFaceVertices f}) =
            ⟨mixedFaceUsedEmbedding f v, hmem⟩ := by
        apply Subtype.ext
        exact hemb.symm
      have hright :
          (⟨p.1, hp⟩ :
              {q // q ∈ mixedOldFaceVertices f}) = v := by
        apply Subtype.ext
        rfl
      rw [hleft, hright]
      have hmapMem :
          mixedFaceUsedEmbedding f v ∈
            (Finset.univ :
              Finset {q // q ∈ mixedOldFaceVertices f}).map
                (mixedFaceUsedEmbedding f) :=
        Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
      have hrel :=
        (relabelUnivSimplex_apply
          (mixedFaceUsedEmbedding f) x v).symm
      rw [extendFaceCoordinates_of_mem _ _ hmapMem] at hrel
      exact hrel
    · have hpUsed :
          p ∉ mixedUsedFaceVertices f := by
        intro hpUsed
        change p ∈
          (Finset.univ :
            Finset {v // v ∈ mixedOldFaceVertices f}).map
              (mixedFaceUsedEmbedding f) at hpUsed
        obtain ⟨v, -, hv⟩ := Finset.mem_map.mp hpUsed
        exact hp (congrArg
          (fun z : UsedOldVertex ↦ z.1) hv ▸ v.2)
      rw [extendFaceCoordinates_of_notMem _ _ hpUsed,
        extendFaceCoordinates_of_notMem _ _ hp]
  have mixedUsedFaceMap_eq_iff
      {f g : MixedOldFace}
      {x : stdSimplex ℝ {v // v ∈ mixedUsedFaceVertices f}}
      {y : stdSimplex ℝ {v // v ∈ mixedUsedFaceVertices g}} :
      mixedUsedFaceMap f x = mixedUsedFaceMap g y ↔
        extendFaceCoordinates (mixedUsedFaceVertices f) x =
          extendFaceCoordinates (mixedUsedFaceVertices g) y := by
    rw [show mixedUsedFaceMap f x =
        mixedOldFaceMap f
          (relabelUnivSimplex (mixedFaceUsedEmbedding f) x) from rfl,
      show mixedUsedFaceMap g y =
        mixedOldFaceMap g
          (relabelUnivSimplex (mixedFaceUsedEmbedding g) y) from rfl,
      mixedOldFaceMap_eq_iff]
    constructor
    · intro hcoords
      funext p
      rw [mixedUsedExtended_apply f x p,
        mixedUsedExtended_apply g y p,
        congrFun hcoords p.1]
    · intro hcoords
      funext p
      by_cases hp : p ∈ usedOldVertices
      · let q : UsedOldVertex := ⟨p, hp⟩
        have hq := congrFun hcoords q
        rw [mixedUsedExtended_apply f x q,
          mixedUsedExtended_apply g y q] at hq
        exact hq
      · have hpf : p ∉ mixedOldFaceVertices f := by
          intro hpf
          exact hp (Finset.mem_biUnion.mpr
            ⟨f, Finset.mem_univ f, hpf⟩)
        have hpg : p ∉ mixedOldFaceVertices g := by
          intro hpg
          exact hp (Finset.mem_biUnion.mpr
            ⟨g, Finset.mem_univ g, hpg⟩)
        rw [extendFaceCoordinates_of_notMem _ _ hpf,
          extendFaceCoordinates_of_notMem _ _ hpg]
  let mixedOldComplex :
      LocallyFiniteTriangleComplex Rlevel.refined.realization :=
    { Vertex := UsedOldVertex
      Face := MixedOldFace
      faceVertices := mixedUsedFaceVertices
      faceVertices_card := mixedUsedFaceVertices_card
      vertex_used := by
        intro v
        obtain ⟨f, -, hvf⟩ := Finset.mem_biUnion.mp v.2
        have hvMem :
            mixedFaceUsedEmbedding f
                ⟨v.1, hvf⟩ ∈ mixedUsedFaceVertices f := by
          change mixedFaceUsedEmbedding f ⟨v.1, hvf⟩ ∈
            (Finset.univ :
              Finset {v // v ∈ mixedOldFaceVertices f}).map
                (mixedFaceUsedEmbedding f)
          exact Finset.mem_map.mpr
            ⟨⟨v.1, hvf⟩, Finset.mem_univ _, rfl⟩
        refine ⟨f, ?_⟩
        change v ∈ mixedUsedFaceVertices f
        convert hvMem using 1
        apply Subtype.ext
        rfl
      faceMap := mixedUsedFaceMap
      faceMap_continuous := continuous_mixedUsedFaceMap
      faceMap_eq_iff := mixedUsedFaceMap_eq_iff
      locallyFinite := locallyFinite_of_finite _ }
  have sourceRanges_cover :
      Set.range source₁ ∪
          ⋃ f : OutsideFanFace, Set.range (outsideFanFaceMap f) =
        Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    let q : Rlevel.refined.realization := Rlevel.homeo.symm p
    obtain ⟨t, ht, hqt⟩ := q.2.2
    let tf : Rlevel.refined.Face := ⟨t, ht⟩
    by_cases htSelected : tf ∈ selectedLevelFaces
    · apply Set.mem_union_left
      rw [hsource₁Range]
      apply Set.mem_iUnion.mpr
      let u :
          {u : T.toIntrinsic.LevelFace n // u ∈ selectedLevelFaces} :=
        ⟨tf, htSelected⟩
      refine ⟨u, ?_⟩
      exact ⟨q, hqt, Rlevel.homeo.apply_symm_apply p⟩
    · apply Set.mem_union_right
      obtain ⟨i, j, x, hx⟩ :=
        boundaryMarking.exists_fanFaceMap_eq_of_mem_faceCarrier tf hqt
      let f : boundaryMarking.FanFace := ⟨tf, i, j⟩
      have hqRange :
          q ∈ Set.range (boundaryMarking.globalFanFaceMap f) := by
        rw [boundaryMarking.range_globalFanFaceMap f]
        exact ⟨x, hx⟩
      obtain ⟨y, hy⟩ := hqRange
      let fo : OutsideFanFace := ⟨f, htSelected⟩
      apply Set.mem_iUnion.mpr
      refine ⟨fo, y, ?_⟩
      change Rlevel.homeo
          (boundaryMarking.globalFanFaceMap f y) = p
      rw [hy, Rlevel.homeo.apply_symm_apply]
  have mixedOldComplex_support :
      mixedOldComplex.support = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    have hpCover :
        Rlevel.homeo p ∈
          Set.range source₁ ∪
            ⋃ f : OutsideFanFace, Set.range (outsideFanFaceMap f) := by
      rw [sourceRanges_cover]
      exact Set.mem_univ _
    rcases hpCover with hpLocal | hpFan
    · obtain ⟨z, hz⟩ := hpLocal
      obtain ⟨t, ht, hzt⟩ := z.2.2
      let tf : localSourceComplex.Face := ⟨t, ht⟩
      let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
        localSourceComplex.restrictToFaceSimplex tf z hzt
      have hx₀ :
          localSourceComplex.faceStandardMap tf x₀ = z :=
        localSourceComplex.faceStandardMap_restrictToFaceSimplex
          tf z hzt
      obtain ⟨x₁, hx₁⟩ :=
        relabelUnivSimplex_surjective
          (localFaceOldVertexEmbedding tf) x₀
      obtain ⟨x₂, hx₂⟩ :=
        relabelUnivSimplex_surjective
          (mixedFaceUsedEmbedding (Sum.inl tf)) x₁
      change p ∈ ⋃ f, Set.range (mixedUsedFaceMap f)
      apply Set.mem_iUnion.mpr
      refine ⟨Sum.inl tf, x₂, ?_⟩
      change Rlevel.homeo.symm
          (source₁
            (localSourceComplex.faceStandardMap tf
              (relabelUnivSimplex (localFaceOldVertexEmbedding tf)
                (relabelUnivSimplex
                  (mixedFaceUsedEmbedding (Sum.inl tf)) x₂)))) = p
      rw [hx₂, hx₁, hx₀, hz, Rlevel.homeo.symm_apply_apply]
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hpFan
      obtain ⟨z, hz⟩ := hf
      have hz' :
          boundaryMarking.globalFanFaceMap f.1 z = p := by
        apply Rlevel.homeo.injective
        exact hz
      obtain ⟨x₁, hx₁⟩ :=
        relabelFaceSimplex_surjective fanOldVertexEmbedding
          (boundaryMarking.globalFanFaceVertices f.1) z
      obtain ⟨x₂, hx₂⟩ :=
        relabelUnivSimplex_surjective
          (mixedFaceUsedEmbedding (Sum.inr f)) x₁
      change p ∈ ⋃ f, Set.range (mixedUsedFaceMap f)
      apply Set.mem_iUnion.mpr
      refine ⟨Sum.inr f, x₂, ?_⟩
      change boundaryMarking.globalFanFaceMap f.1
          (relabelFaceSimplex fanOldVertexEmbedding
            (boundaryMarking.globalFanFaceVertices f.1)
            (relabelUnivSimplex
              (mixedFaceUsedEmbedding (Sum.inr f)) x₂)) = p
      rw [hx₂, hx₁, hz']
  have hsource₁U (z) : source₁ z ∈ U := by
    change
      (Q.sourceHomeomorph.symm
        (Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
          CN hCNcompact N extraLines z)).1 ∈ U
    exact
      (Q.sourceHomeomorph.symm
        (Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
          CN hCNcompact N extraLines z)).2
  have hlocalOldEq (z) : T₀.embed (source₁ z) = e₁local z := by
    change frontierGlue U g T.embed (source₁ z) = _
    rw [frontierGlue_of_mem (hsource₁U z)]
    let q : Q.complex.support :=
      Qatlas.tileFacesMeetingRelativeOldCoordinateSupport
        CN hCNcompact N extraLines z
    let zU : U := ⟨source₁ z, hsource₁U z⟩
    have hzU : zU = Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [hgval zU]
    unfold e₁local
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    apply Subtype.ext
    rw [hgcoord zU, hzU, Q.sourceHomeomorph.apply_symm_apply]
    rfl
  let e₂ :=
    PartialTriangulation.RelativeSynchronizedTarget.newSurfaceEmbed
      c J N lines hN_arrangement hN_model
  have he₂ : _root_.Topology.IsEmbedding e₂ :=
    PartialTriangulation.RelativeSynchronizedTarget.isEmbedding_newSurfaceEmbed
      c J N lines hN_arrangement hN_model
  have hDtarget : D ⊆ interior (Set.range e₂) := by
    intro x hx
    let xD : D := ⟨x, hx⟩
    have hpInterior :
        dModel xD ∈ interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support} :=
      hDmodelInteriorN ⟨xD, rfl⟩
    apply
      (PartialTriangulation.RelativeSynchronizedTarget.modelInterior_subset_interior_range_newSurfaceEmbed
        c J N lines hN_arrangement hN_model)
    refine ⟨c.chart.symm (dModel xD), ⟨dModel xD, hpInterior, rfl⟩, ?_⟩
    change (c.chart.symm (c.chart (dToDomain xD))).1 = x
    rw [c.chart.symm_apply_apply]
  let localUsedOldEmbedding :
      localSourceComplex.UsedVertex ↪ UsedOldVertex :=
    { toFun := fun u ↦
        ⟨localOldVertexEmbedding u, by
          obtain ⟨t, ht, hut⟩ := u.2
          apply Finset.mem_biUnion.mpr
          refine ⟨Sum.inl (⟨t, ht⟩ : localSourceComplex.Face),
            Finset.mem_univ _, ?_⟩
          change localOldVertexEmbedding u ∈
            (Finset.univ : Finset {v // v ∈ t}).map
              (localFaceOldVertexEmbedding ⟨t, ht⟩)
          apply Finset.mem_map.mpr
          refine ⟨⟨u.1, hut⟩, Finset.mem_univ _, ?_⟩
          apply Subtype.ext
          rfl⟩
      inj' := by
        intro u v huv
        apply localOldVertexEmbedding.injective
        exact congrArg Subtype.val huv }
  let OldExtra :=
    {v : UsedOldVertex //
      ¬ ∃ u : localSourceComplex.UsedVertex,
        localUsedOldEmbedding u = v}
  let CommonVertex := Sum OldExtra localSourceComplex.Vertex
  let oldToCommonFun : UsedOldVertex → CommonVertex :=
    fun v ↦ if hv : ∃ u : localSourceComplex.UsedVertex,
        localUsedOldEmbedding u = v then
      Sum.inr (Classical.choose hv).1
    else
      Sum.inl ⟨v, hv⟩
  have oldToCommonFun_injective :
      Function.Injective oldToCommonFun := by
    intro v w hvw
    by_cases hv : ∃ u : localSourceComplex.UsedVertex,
        localUsedOldEmbedding u = v
    · by_cases hw : ∃ u : localSourceComplex.UsedVertex,
          localUsedOldEmbedding u = w
      · have hraw :
            (Classical.choose hv).1 =
              (Classical.choose hw).1 := by
          have hs :
              (Sum.inr (Classical.choose hv).1 :
                  CommonVertex) =
                Sum.inr (Classical.choose hw).1 := by
            simpa only [oldToCommonFun, dif_pos hv,
              dif_pos hw] using hvw
          exact Sum.inr_injective hs
        have hused :
            Classical.choose hv = Classical.choose hw :=
          Subtype.ext hraw
        calc
          v = localUsedOldEmbedding (Classical.choose hv) :=
            (Classical.choose_spec hv).symm
          _ = localUsedOldEmbedding (Classical.choose hw) :=
            congrArg localUsedOldEmbedding hused
          _ = w := Classical.choose_spec hw
      · exfalso
        simpa only [oldToCommonFun, dif_pos hv,
          dif_neg hw, reduceCtorEq] using hvw
    · by_cases hw : ∃ u : localSourceComplex.UsedVertex,
          localUsedOldEmbedding u = w
      · exfalso
        simpa only [oldToCommonFun, dif_neg hv,
          dif_pos hw, reduceCtorEq] using hvw
      · have hextra :
            (⟨v, hv⟩ : OldExtra) = ⟨w, hw⟩ := by
          have hs :
              (Sum.inl (⟨v, hv⟩ : OldExtra) :
                  CommonVertex) =
                Sum.inl ⟨w, hw⟩ := by
            simpa only [oldToCommonFun, dif_neg hv,
              dif_neg hw] using hvw
          exact Sum.inl_injective hs
        exact congrArg Subtype.val hextra
  let oldToCommon : UsedOldVertex ↪ CommonVertex :=
    ⟨oldToCommonFun, oldToCommonFun_injective⟩
  let targetToCommon : localSourceComplex.Vertex ↪ CommonVertex :=
    ⟨Sum.inr, Sum.inr_injective⟩
  have oldToCommon_local
      (u : localSourceComplex.UsedVertex) :
      oldToCommon (localUsedOldEmbedding u) =
        targetToCommon u.1 := by
    have hlocal :
        ∃ q, localUsedOldEmbedding q =
          localUsedOldEmbedding u := ⟨u, rfl⟩
    change oldToCommonFun (localUsedOldEmbedding u) = Sum.inr u.1
    rw [show oldToCommonFun (localUsedOldEmbedding u) =
        Sum.inr (Classical.choose hlocal).1 by
      simp only [oldToCommonFun, dif_pos hlocal]]
    congr 1
    exact congrArg Subtype.val
      (localUsedOldEmbedding.injective
        (Classical.choose_spec hlocal))
  letI : Fintype UsedOldVertex :=
    mixedOldComplex.compactIntrinsic.vertexFintype
  let compactVertexEquiv :
      mixedOldComplex.compactIntrinsic.Vertex ≃ UsedOldVertex :=
    Equiv.refl _
  let oldCompactToCommon :
      mixedOldComplex.compactIntrinsic.Vertex ↪ CommonVertex :=
    ⟨fun v => oldToCommon (compactVertexEquiv v), by
      intro v w hvw
      exact compactVertexEquiv.injective (oldToCommon.injective hvw)⟩
  let eOld :
      mixedOldComplex.compactIntrinsic.realization → S :=
    fun x ↦ T₀.embed
      (Rlevel.homeo (mixedOldComplex.compactEval x))
  have heCompactEval :
      _root_.Topology.IsEmbedding mixedOldComplex.compactEval :=
    ((mixedOldComplex.continuous_compactEval).isClosedEmbedding
      mixedOldComplex.injective_compactEval).isEmbedding
  have heOld : _root_.Topology.IsEmbedding eOld :=
    T₀.isEmbedding.comp
      (Rlevel.homeo.isEmbedding.comp heCompactEval)
  let F₁ : Finset (Finset CommonVertex) :=
    relabelFaceFamily oldCompactToCommon
      mixedOldComplex.compactIntrinsic.faces
  let F₂ : Finset (Finset CommonVertex) :=
    relabelFaceFamily targetToCommon
      (PartialTriangulation.RelativeSynchronizedTarget.newMesh
        J N lines).triangles
  let e₁ : GeometricRealization CommonVertex F₁ → S :=
    fun x ↦
      eOld
        ((relabelGeometricRealizationHomeomorph oldCompactToCommon
          mixedOldComplex.compactIntrinsic.faces).symm
            (⟨x.1, by
              change x.1 ∈ GeometricRealization CommonVertex
                (relabelFaceFamily oldCompactToCommon
                  mixedOldComplex.compactIntrinsic.faces)
              exact x.2⟩))
  let e₂common : GeometricRealization CommonVertex F₂ → S :=
    e₂ ∘
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm
  have he₁ : _root_.Topology.IsEmbedding e₁ :=
    by
      have h := heOld.comp
        (relabelGeometricRealizationHomeomorph oldCompactToCommon
          mixedOldComplex.compactIntrinsic.faces).symm.isEmbedding
      convert h using 1
      funext x
      rfl
  have he₂common : _root_.Topology.IsEmbedding e₂common :=
    he₂.comp
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm.isEmbedding
  have hcard : ∀ t ∈ F₁ ∪ F₂, t.card = 3 := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · change t ∈ relabelFaceFamily oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.card_map]
      exact mixedOldComplex.compactIntrinsic.faces_card s hs
    · change t ∈ relabelFaceFamily targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.card_map]
      exact
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).card_triangle s hs
  have range_eOld : Set.range eOld = T₀.support := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨Rlevel.homeo (mixedOldComplex.compactEval x), rfl⟩
    · rintro y ⟨q, rfl⟩
      let p : Rlevel.refined.realization := Rlevel.homeo.symm q
      have hp : p ∈ mixedOldComplex.support := by
        rw [mixedOldComplex_support]
        exact Set.mem_univ _
      rw [← mixedOldComplex.range_compactEval] at hp
      obtain ⟨x, hx⟩ := hp
      refine ⟨x, ?_⟩
      change T₀.embed
          (Rlevel.homeo (mixedOldComplex.compactEval x)) =
        T₀.embed q
      rw [hx, Rlevel.homeo.apply_symm_apply]
  have range_e₁ : Set.range e₁ = T₀.support := by
    rw [← range_eOld]
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨(relabelGeometricRealizationHomeomorph oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces).symm
          ⟨x.1, by
            change x.1 ∈ GeometricRealization CommonVertex
              (relabelFaceFamily oldCompactToCommon
                mixedOldComplex.compactIntrinsic.faces)
            exact x.2⟩, rfl⟩
    · rintro y ⟨x, rfl⟩
      let z :=
        (relabelGeometricRealizationHomeomorph oldCompactToCommon
          mixedOldComplex.compactIntrinsic.faces) x
      have hz : z.1 ∈ GeometricRealization CommonVertex F₁ := by
        change z.1 ∈ GeometricRealization CommonVertex
          (relabelFaceFamily oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces)
        exact z.2
      refine ⟨⟨z.1, hz⟩, ?_⟩
      change eOld
          ((relabelGeometricRealizationHomeomorph oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces).symm z) =
        eOld x
      rw [Homeomorph.symm_apply_apply]
  have range_e₂common : Set.range e₂common = Set.range e₂ := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨(relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm x, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨(relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles) x, ?_⟩
      change e₂
          ((relabelGeometricRealizationHomeomorph targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles).symm
            ((relabelGeometricRealizationHomeomorph targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles) x)) = e₂ x
      rw [Homeomorph.symm_apply_apply]
  have oldTarget_eq_implies_local
      (x : mixedOldComplex.compactIntrinsic.realization)
      (y : GeometricRealization
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).Vertex
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles)
      (hxy : eOld x = e₂ y) :
      ∃ z : localSourceComplex.realization,
        source₁ z =
            Rlevel.homeo (mixedOldComplex.compactEval x) ∧
        (z : localSourceComplex.Vertex → ℝ) =
          (y :
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).Vertex → ℝ) := by
    let q : T.toIntrinsic.realization :=
      Rlevel.homeo (mixedOldComplex.compactEval x)
    let p : Plane :=
      (PartialTriangulation.RelativeSynchronizedTarget.newMesh
        J N lines).coordinateEmbed y
    have hpNew :
        p ∈
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).toPlaneComplex.support := by
      rw [← (PartialTriangulation.RelativeSynchronizedTarget.newMesh
        J N lines).range_coordinateEmbed]
      exact Set.mem_range_self y
    have hpN : p ∈ N.toPlaneComplex.support := by
      rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
        J N lines hN_arrangement] at hpNew
      exact hpNew
    have hpV : p ∈ V := hN_V hpN
    have hqSurface : T₀.embed q = e₂ y := hxy
    have hqU : q ∈ U := by
      by_contra hqU
      have hqOld : T.embed q = e₂ y := by
        calc
          T.embed q = T₀.embed q := by
            change T.embed q = frontierGlue U g T.embed q
            rw [frontierGlue_of_notMem hqU]
          _ = e₂ y := hqSurface
      have hqDomain : T.embed q ∈ c.domain := by
        rw [hqOld]
        unfold e₂
        exact (c.chart.symm
          ((PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).coordinateEmbedInto c.kind.modelRegion (by
              rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
                J N lines hN_arrangement]
              exact hN_model) y)).2
      let qChart : T.chartOverlap c := ⟨q, hqDomain⟩
      have hqC : T.embed q ∈ C :=
        hUprotected qChart hqU
      have hqNotV :
          T.chartOverlapMap c qChart ∉ V :=
        hVprotected qChart hqC
      apply hqNotV
      have hdomain :
          T.chartOverlapToDomain c qChart =
            c.chart.symm
              ((PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).coordinateEmbedInto c.kind.modelRegion (by
                  rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
                    J N lines hN_arrangement]
                  exact hN_model) y) := by
        apply Subtype.ext
        exact hqOld
      have hmodel := congrArg c.chart hdomain
      rw [c.chart.apply_symm_apply] at hmodel
      change T.chartOverlapMap c qChart ∈ V
      change
        ((c.chart (T.chartOverlapToDomain c qChart) :
          c.kind.modelRegion) : Plane) ∈ V
      rw [hmodel]
      exact hpV
    let qU : U := ⟨q, hqU⟩
    have hqTarget : g q = e₂ y := by
      calc
        g q = T₀.embed q := by
          change g q = frontierGlue U g T.embed q
          rw [frontierGlue_of_mem hqU]
        _ = e₂ y := hqSurface
    have hmodel :
        g' qU =
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).coordinateEmbedInto c.kind.modelRegion (by
              rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
                J N lines hN_arrangement]
              exact hN_model) y := by
      apply c.chart.symm.injective
      apply Subtype.ext
      change (c.chart.symm (g' qU)).1 = _
      rw [← hgval qU]
      exact hqTarget
    have hqCN :
        (Q.sourceHomeomorph qU).1 ∈ CN := by
      change (Q.sourceHomeomorph qU).1.1 ∈
        N.toPlaneComplex.support
      rw [← hgcoord qU]
      change (g' qU : Plane) ∈ N.toPlaneComplex.support
      rw [hmodel]
      exact hpN
    have hqSelected :
        q ∈ ⋃ f : Qatlas.TileFacesMeeting CN hCNcompact,
          Q.sourceFaceSet f.1 :=
      Qatlas.coordinatePreimage_subset_sourceTileFacesMeeting
        CN hCNcompact ⟨hqU, hqCN⟩
    rw [Qatlas.sourceTileFacesMeeting_eq_levelFaces
      CN hCNcompact] at hqSelected
    rw [← hsource₁Range] at hqSelected
    obtain ⟨z, hz⟩ := hqSelected
    refine ⟨z, hz, ?_⟩
    apply
      (PartialTriangulation.RelativeSynchronizedTarget.surfaceEmbed_eq_iff
        c J N lines hN_arrangement hJmodel hN_model z y).mp
    change e₁local z = e₂ y
    rw [← hlocalOldEq z, hz]
    exact hqSurface
  have localMixedUsedVertex_isLocal
      (t : localSourceComplex.Face) (v : UsedOldVertex)
      (hv : v ∈ mixedUsedFaceVertices (Sum.inl t)) :
      ∃ u : localSourceComplex.UsedVertex,
        localUsedOldEmbedding u = v := by
    change v ∈
      (Finset.univ :
        Finset {w // w ∈ mixedOldFaceVertices (Sum.inl t)}).map
          (mixedFaceUsedEmbedding (Sum.inl t)) at hv
    obtain ⟨w, -, hwv⟩ := Finset.mem_map.mp hv
    have hwOld : w.1 ∈ mixedOldFaceVertices (Sum.inl t) := w.2
    change w.1 ∈
      (Finset.univ : Finset {a // a ∈ t.1}).map
        (localFaceOldVertexEmbedding t) at hwOld
    obtain ⟨a, -, haw⟩ := Finset.mem_map.mp hwOld
    let u : localSourceComplex.UsedVertex :=
      ⟨a.1, t.1, t.2, a.2⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    calc
      (localUsedOldEmbedding u).1 =
          localFaceOldVertexEmbedding t a := rfl
      _ = w.1 := haw
      _ = v.1 := congrArg Subtype.val hwv
  have exists_oldPoint_of_local
      (z : localSourceComplex.realization) :
      ∃ x : mixedOldComplex.compactIntrinsic.realization,
        mixedOldComplex.compactEval x =
            Rlevel.homeo.symm (source₁ z) ∧
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces x).1 =
          (pushGeometricRealization targetToCommon
            localSourceComplex.faces z).1 := by
    obtain ⟨t, ht, hzt⟩ := z.2.2
    let tf : localSourceComplex.Face := ⟨t, ht⟩
    let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
      localSourceComplex.restrictToFaceSimplex tf z hzt
    have hx₀ :
        localSourceComplex.faceStandardMap tf x₀ = z :=
      localSourceComplex.faceStandardMap_restrictToFaceSimplex
        tf z hzt
    have hExt₀ :
        extendFaceCoordinates tf.1 x₀ = z.1 := by
      rw [← localSourceComplex.faceStandardMap_val tf x₀, hx₀]
    obtain ⟨x₁, hx₁⟩ :=
      relabelUnivSimplex_surjective
        (localFaceOldVertexEmbedding tf) x₀
    obtain ⟨x₂, hx₂⟩ :=
      relabelUnivSimplex_surjective
        (mixedFaceUsedEmbedding (Sum.inl tf)) x₁
    have hface :
        mixedUsedFaceVertices (Sum.inl tf) ∈
          mixedOldComplex.compactIntrinsic.faces := by
      exact
        mixedOldComplex.compactIntrinsic_face_mem
          (Sum.inl tf : MixedOldFace)
    let cf : mixedOldComplex.compactIntrinsic.Face :=
      ⟨mixedUsedFaceVertices (Sum.inl tf), hface⟩
    let x :
        mixedOldComplex.compactIntrinsic.realization :=
      mixedOldComplex.compactIntrinsic.faceStandardMap cf x₂
    have hxVal :
        x.1 =
          extendFaceCoordinates
            (mixedUsedFaceVertices (Sum.inl tf)) x₂ := by
      exact
        mixedOldComplex.compactIntrinsic.faceStandardMap_val
          cf x₂
    have hxSupp :
        ∀ v ∉ mixedUsedFaceVertices (Sum.inl tf),
          x.1 v = 0 := by
      intro v hv
      rw [hxVal]
      exact extendFaceCoordinates_of_notMem _ _ hv
    refine ⟨x, ?_, ?_⟩
    · rw [mixedOldComplex.compactEval_eq_faceMap
        (Sum.inl tf) x hxSupp]
      change mixedUsedFaceMap (Sum.inl tf)
          (mixedOldComplex.restrictToFace
            (mixedUsedFaceVertices (Sum.inl tf))
            ⟨x.1, x.2.1⟩ hxSupp) =
        Rlevel.homeo.symm (source₁ z)
      calc
        _ = mixedUsedFaceMap (Sum.inl tf) x₂ := by
          exact
            (mixedUsedFaceMap_eq_iff
              (f := Sum.inl tf) (g := Sum.inl tf)
              (x := mixedOldComplex.restrictToFace
                (mixedUsedFaceVertices (Sum.inl tf))
                ⟨x.1, x.2.1⟩ hxSupp)
              (y := x₂)).mpr (by
                rw [mixedOldComplex.extendFaceCoordinates_restrictToFace]
                exact
                  mixedOldComplex.compactIntrinsic.faceStandardMap_val
                    cf x₂)
        _ = Rlevel.homeo.symm (source₁ z) := by
          change
            Rlevel.homeo.symm
                (source₁
                  (localSourceComplex.faceStandardMap tf
                    (relabelUnivSimplex
                      (localFaceOldVertexEmbedding tf)
                      (relabelUnivSimplex
                        (mixedFaceUsedEmbedding (Sum.inl tf)) x₂)))) =
              Rlevel.homeo.symm (source₁ z)
          rw [hx₂, hx₁, hx₀]
    · funext b
      cases b with
      | inl v =>
          have hcompact :
              oldCompactToCommon (compactVertexEquiv.symm v.1) =
                Sum.inl v := by
            change
              oldToCommon
                  (compactVertexEquiv
                    (compactVertexEquiv.symm v.1)) =
                Sum.inl v
            rw [compactVertexEquiv.apply_symm_apply]
            change oldToCommonFun v.1 = Sum.inl v
            rw [show oldToCommonFun v.1 =
                Sum.inl ⟨v.1, v.2⟩ by
              simp only [oldToCommonFun, dif_neg v.2]]
          rw [← hcompact,
            pushGeometricRealization_apply_embedding]
          change x.1 v.1 = _
          rw [show x.1 =
              extendFaceCoordinates
                (mixedUsedFaceVertices (Sum.inl tf)) x₂ by
            exact mixedOldComplex.compactIntrinsic.faceStandardMap_val
              cf x₂]
          have hvNot :
              v.1 ∉ mixedUsedFaceVertices (Sum.inl tf) := by
            intro hv
            exact v.2 (localMixedUsedVertex_isLocal tf v.1 hv)
          rw [extendFaceCoordinates_of_notMem _ _ hvNot]
          apply Eq.symm
          apply pushGeometricRealization_apply_of_notMem_range
          intro hvRange
          obtain ⟨a, ha⟩ := hvRange
          have hcontra :
              (Sum.inr a : CommonVertex) = Sum.inl v :=
            ha.trans hcompact
          simp at hcontra
      | inr a =>
          have htarget :
              (pushGeometricRealization targetToCommon
                  localSourceComplex.faces z).1 (Sum.inr a) =
                z.1 a := by
            change
              (pushGeometricRealization targetToCommon
                  localSourceComplex.faces z).1
                  (targetToCommon a) =
                z.1 a
            exact
              pushGeometricRealization_apply_embedding
                targetToCommon localSourceComplex.faces z a
          rw [htarget]
          by_cases haUsed :
              ∃ s ∈ localSourceComplex.faces, a ∈ s
          · let u : localSourceComplex.UsedVertex := ⟨a, haUsed⟩
            have hcommon :
                oldCompactToCommon
                    (compactVertexEquiv.symm
                      (localUsedOldEmbedding u)) =
                  Sum.inr a := oldToCommon_local u
            rw [← hcommon,
              pushGeometricRealization_apply_embedding]
            change x.1 (localUsedOldEmbedding u) = _
            calc
              x.1 (localUsedOldEmbedding u) =
                  extendFaceCoordinates
                    (mixedUsedFaceVertices (Sum.inl tf)) x₂
                    (localUsedOldEmbedding u) := by
                exact congrFun hxVal (localUsedOldEmbedding u)
              _ =
                  extendFaceCoordinates
                    (mixedOldFaceVertices (Sum.inl tf))
                    (relabelUnivSimplex
                      (mixedFaceUsedEmbedding (Sum.inl tf)) x₂)
                    (localOldVertexEmbedding u) :=
                mixedUsedExtended_apply
                  (Sum.inl tf) x₂ (localUsedOldEmbedding u)
              _ =
                  extendFaceCoordinates
                    (mixedOldFaceVertices (Sum.inl tf)) x₁
                    (localOldVertexEmbedding u) := by
                rw [hx₂]
              _ =
                  extendFaceCoordinates tf.1 x₀ u.1 := by
                rw [localMixedExtended_apply, hx₁]
              _ = z.1 a := congrFun hExt₀ a
          · have haZero : z.1 a = 0 := by
              apply hzt a
              intro hat
              exact haUsed ⟨t, ht, hat⟩
            rw [haZero]
            apply pushGeometricRealization_apply_of_notMem_range
            intro haRange
            obtain ⟨v, hv⟩ := haRange
            let vOld : UsedOldVertex := compactVertexEquiv v
            have hvOld :
                oldToCommon vOld = Sum.inr a := by
              exact hv
            have hvLocal :
                ∃ u : localSourceComplex.UsedVertex,
                  localUsedOldEmbedding u = vOld := by
              by_cases hlocal :
                  ∃ u : localSourceComplex.UsedVertex,
                    localUsedOldEmbedding u = vOld
              · exact hlocal
              · change oldToCommonFun vOld = Sum.inr a at hvOld
                simp only [oldToCommonFun, dif_neg hlocal,
                  reduceCtorEq] at hvOld
            obtain ⟨u, huv⟩ := hvLocal
            have hraw :
                (Sum.inr u.1 : CommonVertex) = Sum.inr a := by
              calc
                (Sum.inr u.1 : CommonVertex) =
                    oldToCommon (localUsedOldEmbedding u) :=
                  (oldToCommon_local u).symm
                _ = oldToCommon vOld :=
                  congrArg oldToCommon huv
                _ = Sum.inr a := hvOld
            have hua : u.1 = a := Sum.inr_injective hraw
            exact haUsed (hua ▸ u.2)
  have hsep :
      ∀ (x : GeometricRealization CommonVertex F₁)
        (y : GeometricRealization CommonVertex F₂),
        e₁ x = e₂common y → x.1 = y.1 := by
    intro x y hxy
    let xb : mixedOldComplex.compactIntrinsic.realization :=
      (relabelGeometricRealizationHomeomorph oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces).symm x
    let yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles :=
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm y
    have hbase : eOld xb = e₂ yb := by
      change eOld xb = e₂ yb
      exact hxy
    obtain ⟨z, hz, hzy⟩ :=
      oldTarget_eq_implies_local xb yb hbase
    obtain ⟨xz, hxzEval, hxzCoord⟩ :=
      exists_oldPoint_of_local z
    have hxzxb : xz = xb := by
      apply heCompactEval.injective
      calc
        mixedOldComplex.compactEval xz =
            Rlevel.homeo.symm (source₁ z) := hxzEval
        _ =
            Rlevel.homeo.symm
              (Rlevel.homeo
                (mixedOldComplex.compactEval xb)) := by
          rw [hz]
        _ = mixedOldComplex.compactEval xb :=
          Rlevel.homeo.symm_apply_apply _
    subst xz
    have htargetCoord :
        (pushGeometricRealization targetToCommon
            localSourceComplex.faces z).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1 :=
      pushGeometricRealization_val_eq_of_val_eq targetToCommon
        localSourceComplex.faces
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles z yb hzy
    have hxback :
        (relabelGeometricRealizationHomeomorph oldCompactToCommon
          mixedOldComplex.compactIntrinsic.faces) xb = x :=
      (relabelGeometricRealizationHomeomorph oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces).apply_symm_apply x
    have hyback :
        (relabelGeometricRealizationHomeomorph targetToCommon
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles) yb = y :=
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).apply_symm_apply y
    calc
      x.1 =
          ((relabelGeometricRealizationHomeomorph oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces) xb).1 :=
        congrArg Subtype.val hxback.symm
      _ =
          (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 := rfl
      _ =
          (pushGeometricRealization targetToCommon
            localSourceComplex.faces z).1 := hxzCoord
      _ =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1 := htargetCoord
      _ =
          ((relabelGeometricRealizationHomeomorph targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles) yb).1 := rfl
      _ = y.1 := congrArg Subtype.val hyback
  have fanCenter_not_local
      (f : OutsideFanFace) :
      ¬ ∃ u : localSourceComplex.UsedVertex,
          localOldVertexEmbedding u =
            fanOldVertexEmbedding
              (boundaryMarking.fanVertexEmbedding f.1
                (boundaryMarking.fanCenterVertex f.1)) := by
    rintro ⟨u, hu⟩
    obtain ⟨t, ht, hut⟩ := u.2
    let tf : localSourceComplex.Face := ⟨t, ht⟩
    let uv : {v // v ∈ tf.1} := ⟨u.1, hut⟩
    have hlocal :
        localVertexLevelPoint u ∈
          Rlevel.refined.faceCarrier
            (localFaceLevelFace tf).1.1 := by
      have huv :
          (⟨uv.1, ⟨tf.1, tf.2, uv.2⟩⟩ :
              localSourceComplex.UsedVertex) = u :=
        Subtype.ext rfl
      simpa only [huv] using localVertexLevelPoint_mem_face tf uv
    have hcenterEq :
        localVertexLevelPoint u =
          Rlevel.refined.faceCenter f.1.1 := by
      exact congrArg (fun z : OldVertex ↦ z.1) hu
    have hcenterMem :
        Rlevel.refined.faceCenter f.1.1 ∈
          Rlevel.refined.faceCarrier
            (localFaceLevelFace tf).1.1 := by
      rw [← hcenterEq]
      exact hlocal
    have hparentNe :
        f.1.1 ≠ (localFaceLevelFace tf).1 := by
      intro h
      apply f.2
      rw [h]
      exact (localFaceLevelFace tf).2
    let xc :
        stdSimplex ℝ
          {p // p ∈ boundaryMarking.fanFaceVertices f.1} :=
      stdSimplex.vertex (boundaryMarking.fanCenterVertex f.1)
    have hxcCarrier :
        boundaryMarking.fanFaceMap f.1 xc ∈
          Rlevel.refined.faceCarrier
            (localFaceLevelFace tf).1.1 := by
      rw [boundaryMarking.fanFaceMap_vertex f.1
        (boundaryMarking.fanCenterVertex f.1)]
      exact hcenterMem
    have hzero :=
      boundaryMarking.fanCenterWeight_eq_zero_of_mem_faceCarrier_of_parent_ne
        f.1 (localFaceLevelFace tf).1 hparentNe xc hxcCarrier
    have hone :
        xc (boundaryMarking.fanCenterVertex f.1) = 1 := by
      simp [xc, stdSimplex.vertex]
    rw [hone] at hzero
    exact one_ne_zero hzero
  have fanFace_oldPoint_mem_baseEdge_of_common
      (f : OutsideFanFace)
      (xb : mixedOldComplex.compactIntrinsic.realization)
      (yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
      (hxb :
        ∀ v ∉ mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
      (hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1) :
      mixedOldComplex.compactEval xb ∈
        Rlevel.refined.faceCarrier
          (Rlevel.refined.faceEdge f.1.1 f.1.2.1).1 := by
    let fc :=
      boundaryMarking.fanCenterVertex f.1
    let gc : boundaryMarking.FanVertex :=
      boundaryMarking.fanVertexEmbedding f.1 fc
    have hgc :
        gc ∈ boundaryMarking.globalFanFaceVertices f.1 :=
      (boundaryMarking.mem_globalFanFaceVertices_iff f.1 gc).mpr fc.2
    have hoc :
        fanOldVertexEmbedding gc ∈
          mixedOldFaceVertices (Sum.inr f) := by
      change fanOldVertexEmbedding gc ∈
        (boundaryMarking.globalFanFaceVertices f.1).map
          fanOldVertexEmbedding
      exact Finset.mem_map.mpr ⟨gc, hgc, rfl⟩
    let oc :
        {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
      ⟨fanOldVertexEmbedding gc, hoc⟩
    let uc : UsedOldVertex :=
      mixedFaceUsedEmbedding (Sum.inr f) oc
    have huc :
        uc ∈ mixedUsedFaceVertices (Sum.inr f) := by
      change mixedFaceUsedEmbedding (Sum.inr f) oc ∈
        (Finset.univ :
          Finset {v // v ∈ mixedOldFaceVertices (Sum.inr f)}).map
            (mixedFaceUsedEmbedding (Sum.inr f))
      exact Finset.mem_map.mpr ⟨oc, Finset.mem_univ oc, rfl⟩
    let wc :
        {v // v ∈ mixedUsedFaceVertices (Sum.inr f)} :=
      ⟨uc, huc⟩
    have hnotLocal :
        ¬ ∃ u : localSourceComplex.UsedVertex,
            localUsedOldEmbedding u = uc := by
      rintro ⟨u, hu⟩
      apply fanCenter_not_local f
      refine ⟨u, ?_⟩
      exact congrArg (fun z : UsedOldVertex ↦ z.1) hu
    have hucCommon :
        oldToCommon uc = Sum.inl ⟨uc, hnotLocal⟩ := by
      change oldToCommonFun uc = Sum.inl ⟨uc, hnotLocal⟩
      simp only [oldToCommonFun, dif_neg hnotLocal]
    let vc :
        mixedOldComplex.compactIntrinsic.Vertex :=
      compactVertexEquiv.symm uc
    have hvcCommon :
        oldCompactToCommon vc = Sum.inl ⟨uc, hnotLocal⟩ := by
      change
        oldToCommon (compactVertexEquiv vc) =
          Sum.inl ⟨uc, hnotLocal⟩
      rw [compactVertexEquiv.apply_symm_apply]
      exact hucCommon
    have htargetZero :
        (pushGeometricRealization targetToCommon
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles yb).1
            (Sum.inl ⟨uc, hnotLocal⟩) = 0 := by
      apply pushGeometricRealization_apply_of_notMem_range
      rintro ⟨a, ha⟩
      have hcontra :
          (Sum.inr a : CommonVertex) =
            Sum.inl ⟨uc, hnotLocal⟩ := ha
      simp at hcontra
    have hxbCenter : xb.1 vc = 0 := by
      calc
        xb.1 vc =
            (pushGeometricRealization oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces xb).1
                (oldCompactToCommon vc) :=
          (pushGeometricRealization_apply_embedding
            oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb vc).symm
        _ =
            (pushGeometricRealization oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces xb).1
                (Sum.inl ⟨uc, hnotLocal⟩) := by rw [hvcCommon]
        _ =
            (pushGeometricRealization targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles yb).1
                (Sum.inl ⟨uc, hnotLocal⟩) :=
          congrFun hcoords (Sum.inl ⟨uc, hnotLocal⟩)
        _ = 0 := htargetZero
    let x₂ :
        stdSimplex ℝ
          {v // v ∈ mixedUsedFaceVertices (Sum.inr f)} :=
      mixedOldComplex.restrictToFace
        (mixedUsedFaceVertices (Sum.inr f))
        ⟨xb.1, xb.2.1⟩ hxb
    let x₁ :
        stdSimplex ℝ
          {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
      relabelUnivSimplex
        (mixedFaceUsedEmbedding (Sum.inr f)) x₂
    let xG :
        stdSimplex ℝ
          {v // v ∈ boundaryMarking.globalFanFaceVertices f.1} :=
      relabelFaceSimplex fanOldVertexEmbedding
        (boundaryMarking.globalFanFaceVertices f.1) x₁
    let x₀ :
        stdSimplex ℝ
          {p // p ∈ boundaryMarking.fanFaceVertices f.1} :=
      boundaryMarking.fanRelabelSimplex f.1 xG
    have hcenter : x₀ fc = 0 := by
      calc
        x₀ fc =
            extendFaceCoordinates
              (boundaryMarking.fanFaceVertices f.1) x₀ gc.1 := by
          change x₀ fc =
            extendFaceCoordinates
              (boundaryMarking.fanFaceVertices f.1) x₀ fc.1
          rw [extendFaceCoordinates_of_mem _ _ fc.2]
        _ =
            extendFaceCoordinates
              (boundaryMarking.globalFanFaceVertices f.1) xG gc :=
          boundaryMarking.fanRelabel_extended_apply f.1 xG gc
        _ =
            extendFaceCoordinates
              (mixedOldFaceVertices (Sum.inr f)) x₁
                (fanOldVertexEmbedding gc) := by
          exact
            relabelFaceSimplex_extended_apply fanOldVertexEmbedding
              (boundaryMarking.globalFanFaceVertices f.1) x₁ gc
        _ = x₁ oc := by
          rw [extendFaceCoordinates_of_mem _ _ hoc]
        _ =
            extendFaceCoordinates
              (mixedUsedFaceVertices (Sum.inr f)) x₂ uc :=
          relabelUnivSimplex_apply
            (mixedFaceUsedEmbedding (Sum.inr f)) x₂ oc
        _ = x₂ wc := by
          rw [extendFaceCoordinates_of_mem _ _ huc]
        _ = xb.1 vc := by rfl
        _ = 0 := hxbCenter
    rw [mixedOldComplex.compactEval_eq_faceMap
      (Sum.inr f) xb hxb]
    change boundaryMarking.fanFaceMap f.1 x₀ ∈
      Rlevel.refined.faceCarrier
        (Rlevel.refined.faceEdge f.1.1 f.1.2.1).1
    exact
      boundaryMarking.fanFaceMap_mem_baseEdge_of_center_eq_zero
        f.1 x₀ hcenter
  have positive_usedOld_isLocal_of_common
      (xb : mixedOldComplex.compactIntrinsic.realization)
      (yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
      (hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1)
      (v : UsedOldVertex)
      (hv : 0 < xb.1 (compactVertexEquiv.symm v)) :
      ∃ u : localSourceComplex.UsedVertex,
        localUsedOldEmbedding u = v := by
    by_contra hlocal
    have hvCommon :
        oldCompactToCommon (compactVertexEquiv.symm v) =
          Sum.inl ⟨v, hlocal⟩ := by
      change
        oldToCommon
            (compactVertexEquiv (compactVertexEquiv.symm v)) =
          Sum.inl ⟨v, hlocal⟩
      rw [compactVertexEquiv.apply_symm_apply]
      change oldToCommonFun v = Sum.inl ⟨v, hlocal⟩
      simp only [oldToCommonFun, dif_neg hlocal]
    have htargetZero :
        (pushGeometricRealization targetToCommon
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles yb).1 (Sum.inl ⟨v, hlocal⟩) = 0 := by
      apply pushGeometricRealization_apply_of_notMem_range
      rintro ⟨a, ha⟩
      have hcontra :
          (Sum.inr a : CommonVertex) = Sum.inl ⟨v, hlocal⟩ := ha
      simp at hcontra
    have hzero :
        xb.1 (compactVertexEquiv.symm v) = 0 := by
      calc
        xb.1 (compactVertexEquiv.symm v) =
            (pushGeometricRealization oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces xb).1
                (oldCompactToCommon (compactVertexEquiv.symm v)) :=
          (pushGeometricRealization_apply_embedding
            oldCompactToCommon mixedOldComplex.compactIntrinsic.faces
            xb (compactVertexEquiv.symm v)).symm
        _ =
            (pushGeometricRealization oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces xb).1
                (Sum.inl ⟨v, hlocal⟩) := by rw [hvCommon]
        _ =
            (pushGeometricRealization targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles yb).1
                (Sum.inl ⟨v, hlocal⟩) :=
          congrFun hcoords (Sum.inl ⟨v, hlocal⟩)
        _ = 0 := htargetZero
    linarith
  have fanFace_oldPoint_mem_selected_of_common
      (f : OutsideFanFace)
      (xb : mixedOldComplex.compactIntrinsic.realization)
      (yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
      (hxb :
        ∀ v ∉ mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
      (hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1) :
      Rlevel.homeo (mixedOldComplex.compactEval xb) ∈
        ⋃ s : {s : T.toIntrinsic.LevelFace n //
            s ∈ selectedLevelFaces},
          T.toIntrinsic.levelFaceCarrier s.1 := by
    let x₂ :
        stdSimplex ℝ
          {v // v ∈ mixedUsedFaceVertices (Sum.inr f)} :=
      mixedOldComplex.restrictToFace
        (mixedUsedFaceVertices (Sum.inr f))
        ⟨xb.1, xb.2.1⟩ hxb
    let x₁ :
        stdSimplex ℝ
          {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
      relabelUnivSimplex
        (mixedFaceUsedEmbedding (Sum.inr f)) x₂
    let xG :
        stdSimplex ℝ
          {v // v ∈ boundaryMarking.globalFanFaceVertices f.1} :=
      relabelFaceSimplex fanOldVertexEmbedding
        (boundaryMarking.globalFanFaceVertices f.1) x₁
    let x₀ :
        stdSimplex ℝ
          {p // p ∈ boundaryMarking.fanFaceVertices f.1} :=
      boundaryMarking.fanRelabelSimplex f.1 xG
    have hmap :
        mixedOldComplex.compactEval xb =
          boundaryMarking.fanFaceMap f.1 x₀ := by
      rw [mixedOldComplex.compactEval_eq_faceMap
        (Sum.inr f) xb hxb]
      rfl
    have hbase :=
      fanFace_oldPoint_mem_baseEdge_of_common f xb yb hxb hcoords
    have hcenter :
        x₀ (boundaryMarking.fanCenterVertex f.1) = 0 := by
      apply boundaryMarking.fanCenterWeight_eq_zero_of_mem_baseEdge
      rwa [← hmap]
    have hpositiveLocal
        (p : {p // p ∈ boundaryMarking.fanFaceVertices f.1})
        (hp : 0 < x₀ p) :
        p.1 ∈ localVertexLevelPoints := by
      let gp : boundaryMarking.FanVertex :=
        boundaryMarking.fanVertexEmbedding f.1 p
      have hgp :
          gp ∈ boundaryMarking.globalFanFaceVertices f.1 :=
        (boundaryMarking.mem_globalFanFaceVertices_iff f.1 gp).mpr p.2
      have hop :
          fanOldVertexEmbedding gp ∈
            mixedOldFaceVertices (Sum.inr f) := by
        change fanOldVertexEmbedding gp ∈
          (boundaryMarking.globalFanFaceVertices f.1).map
            fanOldVertexEmbedding
        exact Finset.mem_map.mpr ⟨gp, hgp, rfl⟩
      let op :
          {v // v ∈ mixedOldFaceVertices (Sum.inr f)} :=
        ⟨fanOldVertexEmbedding gp, hop⟩
      let uv : UsedOldVertex :=
        mixedFaceUsedEmbedding (Sum.inr f) op
      have huv :
          uv ∈ mixedUsedFaceVertices (Sum.inr f) := by
        change mixedFaceUsedEmbedding (Sum.inr f) op ∈
          (Finset.univ :
            Finset {v // v ∈ mixedOldFaceVertices (Sum.inr f)}).map
              (mixedFaceUsedEmbedding (Sum.inr f))
        exact Finset.mem_map.mpr ⟨op, Finset.mem_univ op, rfl⟩
      let wv :
          {v // v ∈ mixedUsedFaceVertices (Sum.inr f)} :=
        ⟨uv, huv⟩
      let cv : mixedOldComplex.compactIntrinsic.Vertex :=
        compactVertexEquiv.symm uv
      have hweight : x₀ p = xb.1 cv := by
        calc
          x₀ p =
              extendFaceCoordinates
                (boundaryMarking.fanFaceVertices f.1) x₀ gp.1 := by
            change x₀ p =
              extendFaceCoordinates
                (boundaryMarking.fanFaceVertices f.1) x₀ p.1
            rw [extendFaceCoordinates_of_mem _ _ p.2]
          _ =
              extendFaceCoordinates
                (boundaryMarking.globalFanFaceVertices f.1) xG gp :=
            boundaryMarking.fanRelabel_extended_apply f.1 xG gp
          _ =
              extendFaceCoordinates
                (mixedOldFaceVertices (Sum.inr f)) x₁
                  (fanOldVertexEmbedding gp) :=
            relabelFaceSimplex_extended_apply fanOldVertexEmbedding
              (boundaryMarking.globalFanFaceVertices f.1) x₁ gp
          _ = x₁ op := by
            rw [extendFaceCoordinates_of_mem _ _ hop]
          _ =
              extendFaceCoordinates
                (mixedUsedFaceVertices (Sum.inr f)) x₂ uv :=
            relabelUnivSimplex_apply
              (mixedFaceUsedEmbedding (Sum.inr f)) x₂ op
          _ = x₂ wv := by
            rw [extendFaceCoordinates_of_mem _ _ huv]
          _ = xb.1 cv := by rfl
      have hcv : 0 < xb.1 cv := by
        rw [← hweight]
        exact hp
      obtain ⟨u, hu⟩ :=
        positive_usedOld_isLocal_of_common xb yb hcoords uv hcv
      have hup :
          localVertexLevelPoint u = p.1 := by
        have huOld :
            localOldVertexEmbedding u =
              fanOldVertexEmbedding gp :=
          congrArg (fun z : UsedOldVertex ↦ z.1) hu
        exact congrArg (fun z : OldVertex ↦ z.1) huOld
      rw [← hup]
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
    have hlocalPointSelected
        (p : Rlevel.refined.realization)
        (hp : p ∈ localVertexLevelPoints) :
        Rlevel.homeo p ∈
          ⋃ s : {s : T.toIntrinsic.LevelFace n //
              s ∈ selectedLevelFaces},
            T.toIntrinsic.levelFaceCarrier s.1 := by
      rw [← hsource₁Range]
      obtain ⟨u, -, hup⟩ := Finset.mem_image.mp hp
      refine ⟨localSourceComplex.vertexPoint u, ?_⟩
      change source₁ (localSourceComplex.vertexPoint u) =
        Rlevel.homeo p
      rw [← hup]
      exact (Rlevel.homeo.apply_symm_apply _).symm
    by_cases hpos :
        0 < x₀ (boundaryMarking.fanFirstVertex f.1) ∧
          0 < x₀ (boundaryMarking.fanSecondVertex f.1)
    · obtain ⟨s, hes⟩ :=
        selectedFace_of_fanInterval_endpoints_local f
          (hpositiveLocal (boundaryMarking.fanFirstVertex f.1) hpos.1)
          (hpositiveLocal (boundaryMarking.fanSecondVertex f.1) hpos.2)
      apply Set.mem_iUnion.mpr
      refine ⟨s, mixedOldComplex.compactEval xb, ?_, rfl⟩
      intro v hv
      exact hbase v (fun hve ↦ hv (hes hve))
    · rcases
          boundaryMarking.fanEndpointData_of_center_eq_zero_of_not_base_weights_pos
            f.1 x₀ hcenter hpos with hfirst | hsecond
      · have hfirstOne :
            x₀ (boundaryMarking.fanFirstVertex f.1) = 1 := by
          have hone := congrFun hfirst.2
            (boundaryMarking.fanFirstVertex f.1).1
          rw [extendFaceCoordinates_of_mem _ _
            (boundaryMarking.fanFirstVertex f.1).2] at hone
          simpa only [Pi.single_eq_same] using hone
        have hlocal :=
          hpositiveLocal (boundaryMarking.fanFirstVertex f.1)
            (by rw [hfirstOne]; norm_num)
        have heq :
            mixedOldComplex.compactEval xb =
              (boundaryMarking.fanFirstVertex f.1).1 := by
          apply Subtype.ext
          rw [hmap]
          exact hfirst.1
        rw [heq]
        exact hlocalPointSelected _ hlocal
      · have hsecondOne :
            x₀ (boundaryMarking.fanSecondVertex f.1) = 1 := by
          have hone := congrFun hsecond.2
            (boundaryMarking.fanSecondVertex f.1).1
          rw [extendFaceCoordinates_of_mem _ _
            (boundaryMarking.fanSecondVertex f.1).2] at hone
          simpa only [Pi.single_eq_same] using hone
        have hlocal :=
          hpositiveLocal (boundaryMarking.fanSecondVertex f.1)
            (by rw [hsecondOne]; norm_num)
        have heq :
            mixedOldComplex.compactEval xb =
              (boundaryMarking.fanSecondVertex f.1).1 := by
          apply Subtype.ext
          rw [hmap]
          exact hsecond.1
        rw [heq]
        exact hlocalPointSelected _ hlocal
  have localFace_oldTarget_agree
      (tf : localSourceComplex.Face)
      (xb : mixedOldComplex.compactIntrinsic.realization)
      (yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
      (hxb :
        ∀ v ∉ mixedUsedFaceVertices (Sum.inl tf), xb.1 v = 0)
      (hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1) :
      eOld xb = e₂ yb := by
    let x₂ :
        stdSimplex ℝ
          {v // v ∈ mixedUsedFaceVertices (Sum.inl tf)} :=
      mixedOldComplex.restrictToFace
        (mixedUsedFaceVertices (Sum.inl tf))
        ⟨xb.1, xb.2.1⟩ hxb
    let x₁ :
        stdSimplex ℝ
          {v // v ∈ mixedOldFaceVertices (Sum.inl tf)} :=
      relabelUnivSimplex
        (mixedFaceUsedEmbedding (Sum.inl tf)) x₂
    let x₀ : stdSimplex ℝ {v // v ∈ tf.1} :=
      relabelUnivSimplex (localFaceOldVertexEmbedding tf) x₁
    let z : localSourceComplex.realization :=
      localSourceComplex.faceStandardMap tf x₀
    have hxbEval :
        mixedOldComplex.compactEval xb =
          Rlevel.homeo.symm (source₁ z) := by
      rw [mixedOldComplex.compactEval_eq_faceMap
        (Sum.inl tf) xb hxb]
      change mixedUsedFaceMap (Sum.inl tf) x₂ =
        Rlevel.homeo.symm (source₁ z)
      rfl
    obtain ⟨xz, hxzEval, hxzCoord⟩ :=
      exists_oldPoint_of_local z
    have hxzxb : xz = xb := by
      apply heCompactEval.injective
      exact hxzEval.trans hxbEval.symm
    subst xz
    have hpush :
        (pushGeometricRealization targetToCommon
            localSourceComplex.faces z).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1 :=
      hxzCoord.symm.trans hcoords
    have hzy : z.1 = yb.1 := by
      funext a
      calc
        z.1 a =
            (pushGeometricRealization targetToCommon
              localSourceComplex.faces z).1 (targetToCommon a) :=
          (pushGeometricRealization_apply_embedding
            targetToCommon localSourceComplex.faces z a).symm
        _ =
            (pushGeometricRealization targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles yb).1 (targetToCommon a) :=
          congrFun hpush (targetToCommon a)
        _ = yb.1 a :=
          pushGeometricRealization_apply_embedding
            targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb a
    have hsurface : e₁local z = e₂ yb :=
      (PartialTriangulation.RelativeSynchronizedTarget.surfaceEmbed_eq_iff
        c J N lines hN_arrangement hJmodel hN_model z yb).mpr hzy
    calc
      eOld xb =
          T₀.embed
            (Rlevel.homeo
              (Rlevel.homeo.symm (source₁ z))) := by
        change
          T₀.embed
              (Rlevel.homeo
                (mixedOldComplex.compactEval xb)) =
            T₀.embed
              (Rlevel.homeo
                (Rlevel.homeo.symm (source₁ z)))
        rw [hxbEval]
      _ = T₀.embed (source₁ z) := by
        rw [Rlevel.homeo.apply_symm_apply]
      _ = e₁local z := hlocalOldEq z
      _ = e₂ yb := hsurface
  have fanFace_oldTarget_agree
      (f : OutsideFanFace)
      (xb : mixedOldComplex.compactIntrinsic.realization)
      (yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
      (hxb :
        ∀ v ∉ mixedUsedFaceVertices (Sum.inr f), xb.1 v = 0)
      (hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1) :
      eOld xb = e₂ yb := by
    have hselected :=
      fanFace_oldPoint_mem_selected_of_common f xb yb hxb hcoords
    rw [← hsource₁Range] at hselected
    obtain ⟨z, hz⟩ := hselected
    obtain ⟨xz, hxzEval, hxzCoord⟩ :=
      exists_oldPoint_of_local z
    have hxzxb : xz = xb := by
      apply heCompactEval.injective
      calc
        mixedOldComplex.compactEval xz =
            Rlevel.homeo.symm (source₁ z) := hxzEval
        _ =
            Rlevel.homeo.symm
              (Rlevel.homeo
                (mixedOldComplex.compactEval xb)) :=
          congrArg Rlevel.homeo.symm hz
        _ = mixedOldComplex.compactEval xb :=
          Rlevel.homeo.symm_apply_apply _
    subst xz
    have hpush :
        (pushGeometricRealization targetToCommon
            localSourceComplex.faces z).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1 :=
      hxzCoord.symm.trans hcoords
    have hzy : z.1 = yb.1 := by
      funext a
      calc
        z.1 a =
            (pushGeometricRealization targetToCommon
              localSourceComplex.faces z).1 (targetToCommon a) :=
          (pushGeometricRealization_apply_embedding
            targetToCommon localSourceComplex.faces z a).symm
        _ =
            (pushGeometricRealization targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles yb).1 (targetToCommon a) :=
          congrFun hpush (targetToCommon a)
        _ = yb.1 a :=
          pushGeometricRealization_apply_embedding
            targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb a
    have hsurface : e₁local z = e₂ yb :=
      (PartialTriangulation.RelativeSynchronizedTarget.surfaceEmbed_eq_iff
        c J N lines hN_arrangement hJmodel hN_model z yb).mpr hzy
    calc
      eOld xb =
          T₀.embed
            (Rlevel.homeo
              (Rlevel.homeo.symm (source₁ z))) := by
        change
          T₀.embed
              (Rlevel.homeo
                (mixedOldComplex.compactEval xb)) =
            T₀.embed
              (Rlevel.homeo
                (Rlevel.homeo.symm (source₁ z)))
        rw [hz, Rlevel.homeo.symm_apply_apply]
      _ = T₀.embed (source₁ z) := by
        rw [Rlevel.homeo.apply_symm_apply]
      _ = e₁local z := hlocalOldEq z
      _ = e₂ yb := hsurface
  have hagree :
      ∀ (x : GeometricRealization CommonVertex F₁)
        (y : GeometricRealization CommonVertex F₂),
        x.1 = y.1 → e₁ x = e₂common y := by
    intro x y hxy
    let xb : mixedOldComplex.compactIntrinsic.realization :=
      (relabelGeometricRealizationHomeomorph oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces).symm x
    let yb :
        GeometricRealization
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).Vertex
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles :=
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm y
    have hxback :
        (relabelGeometricRealizationHomeomorph oldCompactToCommon
          mixedOldComplex.compactIntrinsic.faces) xb = x :=
      (relabelGeometricRealizationHomeomorph oldCompactToCommon
        mixedOldComplex.compactIntrinsic.faces).apply_symm_apply x
    have hyback :
        (relabelGeometricRealizationHomeomorph targetToCommon
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles) yb = y :=
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).apply_symm_apply y
    have hcoords :
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
          (pushGeometricRealization targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles yb).1 := by
      calc
        (pushGeometricRealization oldCompactToCommon
            mixedOldComplex.compactIntrinsic.faces xb).1 =
            ((relabelGeometricRealizationHomeomorph oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces) xb).1 := rfl
        _ = x.1 := congrArg Subtype.val hxback
        _ = y.1 := hxy
        _ =
            ((relabelGeometricRealizationHomeomorph targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles) yb).1 :=
          congrArg Subtype.val hyback.symm
        _ =
            (pushGeometricRealization targetToCommon
              (PartialTriangulation.RelativeSynchronizedTarget.newMesh
                J N lines).triangles yb).1 := rfl
    obtain ⟨f, hxb⟩ :=
      mixedOldComplex.exists_containingFace xb
    change eOld xb = e₂ yb
    rcases f with tf | f
    · exact localFace_oldTarget_agree tf xb yb hxb hcoords
    · exact fanFace_oldTarget_agree f xb yb hxb hcoords
  refine ⟨CommonVertex, inferInstance, inferInstance,
    F₁, F₂, e₁, e₂common, hcard, he₁, he₂common, hagree, hsep, ?_⟩
  · rw [range_e₁, range_e₂common]
    intro x hx
    rcases hx with hxA | hxCore
    · exact interior_mono (Set.subset_union_left) (hA₀ hxA)
    · by_cases hxOld : x ∈ interior T₀.support
      · exact interior_mono Set.subset_union_left
          hxOld
      · apply interior_mono Set.subset_union_right
        exact hDtarget ⟨hxCore, hxOld⟩

/-- **Theorem boundary** (Moise Ch. 8, Thm. 3, the induction step; bordered version).

Given a partial triangulation satisfying the Radó invariant for the absorbed region `A`, and one
more boundary-faithful chart, the chart's core can be absorbed: there is a partial triangulation
satisfying the invariant for `A ∪ c.core`.

Moise's proof of the step: work in the chart's model coordinates; take a polyhedral neighborhood
of the part of the built complex meeting the chart (Thm. 8.2); adjust it by a PL approximation of
the chart-transition homeomorphism (Thm. 6.3, `pl_approximation_two_manifold`) so that it meets a
fine complex containing the model core simplicially (conditions (a)-(h)); glue (Thm. 7.6).  The
polygonal Jordan and Schoenflies theorems enter through Thm. 6.3.

Hypothesis refinement is expected here (see `RadoInvariant`); conclusion weakening is not. -/
theorem moise_induction_step (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core) := by
  classical
  by_cases hcore : c.core ⊆ interior T.support
  · exact ⟨T, hT.absorb_of_subset c.isCompact_core hcore⟩
  by_cases hA : A ⊆ interior c.patchPartialTriangulation.support
  · exact ⟨c.patchPartialTriangulation,
      radoInvariant_chartPatch_absorb c hT.coresCompact hA⟩
  · -- the crossing case: weld the adjusted old complex and the chart patch, then glue
    obtain ⟨V, _, _, F₁, F₂, e₁, e₂, hcard, he₁, he₂, hagree, hsep, hcover⟩ :=
      MoiseChart.exists_crossing_weld S c hc hT hcore hA
    obtain ⟨T', hsupport, hsurf'⟩ :=
      PartialTriangulation.exists_glued V F₁ F₂ hcard e₁ e₂ he₁ he₂ hagree hsep
    refine ⟨T', ?_, hsurf', ?_⟩
    · exact (hT.coresCompact.union c.isCompact_core)
    · rw [hsupport]
      exact hcover

/-- The Radó induction assembled: a compact Eval surface admits a geometric triangulation.

This is a genuine proof from the two theorem boundaries above: starting from the empty complex,
absorb the finitely many chart cores one at a time by `moise_induction_step`; when all cores are
absorbed the invariant forces the support to be everything, and a fully covering partial
triangulation is a geometric triangulation. -/
theorem moise_triangulation_of_boundaries :
    Nonempty (GeometricTriangulation S) := by
  classical
  obtain ⟨m, charts, hcover, hbd⟩ := moise_finite_chart_cover S
  -- Absorb the first `k` cores.
  have Hrec : ∀ k : ℕ,
      ∃ T : PartialTriangulation S,
        RadoInvariant T (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
    intro k
    induction k with
    | zero =>
        refine ⟨PartialTriangulation.empty S, ?_⟩
        have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < 0), (charts i).core) = (∅ : Set S) := by
          simp
        rw [hA]
        exact radoInvariant_empty S
    | succ k ih =>
        rcases ih with ⟨T, hT⟩
        by_cases hk : k < m
        · obtain ⟨T', hT'⟩ :=
            moise_induction_step S (charts ⟨k, hk⟩) (hbd ⟨k, hk⟩) hT
          refine ⟨T', ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) ∪
                (charts ⟨k, hk⟩).core := by
            ext x
            simp only [Set.mem_iUnion, Set.mem_union]
            constructor
            · rintro ⟨i, hik, hx⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hik' | hik'
              · exact Or.inl ⟨i, hik', hx⟩
              · refine Or.inr ?_
                have : i = ⟨k, hk⟩ := Fin.ext hik'
                rwa [← this]
            · rintro (⟨i, hik, hx⟩ | hx)
              · exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
              · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
          rw [hA]
          exact hT'
        · refine ⟨T, ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
            ext x
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨i, hik, hx⟩
              have : (i : ℕ) < k := by
                have := i.isLt
                omega
              exact ⟨i, this, hx⟩
            · rintro ⟨i, hik, hx⟩
              exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
          rw [hA]
          exact hT
  obtain ⟨T, hT⟩ := Hrec m
  have hall : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < m), (charts i).core) = Set.univ := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i, i.isLt, hx⟩
  have hsupport : T.support = Set.univ := by
    have huniv : (Set.univ : Set S) ⊆ T.support := by
      rw [← hall]
      exact hT.coresCovered
    exact Set.eq_univ_of_univ_subset huniv
  exact ⟨T.toGeometricTriangulation hsupport⟩

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
