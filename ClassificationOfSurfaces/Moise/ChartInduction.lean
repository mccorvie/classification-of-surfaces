/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.ChartPatch
import ClassificationOfSurfaces.Moise.IntrinsicComplex
import ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision
import ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension
import ClassificationOfSurfaces.Moise.PLApproximation
import ClassificationOfSurfaces.Moise.AdaptiveTriangulation
import ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation
import ClassificationOfSurfaces.Moise.FrontierGlue

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

theorem isOpen_perturbationRegion (k : ChartKind) : IsOpen k.perturbationRegion :=
  Metric.isOpen_ball

theorem modelRegion_subset_perturbationRegion (k : ChartKind) :
    k.modelRegion ⊆ k.perturbationRegion := by
  cases k <;> intro p hp
  · exact hp
  · exact hp.1

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
    (V : Type) [Fintype V] [DecidableEq V]
    (F₁ F₂ : Finset (Finset V))
    (hcard : ∀ t ∈ F₁ ∪ F₂, t.card = 3)
    (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S)
    (he₁ : _root_.Topology.IsEmbedding e₁) (he₂ : _root_.Topology.IsEmbedding e₂)
    (hagree : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y)
    (hsep : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ))
    (hsurf : ∀ e ∈ (F₁ ∪ F₂).biUnion fun t => t.powersetCard 2,
      ((F₁ ∪ F₂).filter fun t => e ⊆ t).card ≤ 2) :
    ∃ T' : PartialTriangulation S,
      T'.support = Set.range e₁ ∪ Set.range e₂ ∧
      ∀ e ∈ T'.edges, (T'.faces.filter fun t => e ⊆ t).card ≤ 2 := by
  sorry

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
variable [ChartBoundaryInvariant S]

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
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t => t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t => e ⊆ t).card ≤ 2) ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
  sorry

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
    obtain ⟨V, _, _, F₁, F₂, e₁, e₂, hcard, he₁, he₂, hagree, hsep, hsurf, hcover⟩ :=
      MoiseChart.exists_crossing_weld S c hc hT hcore hA
    obtain ⟨T', hsupport, hsurf'⟩ :=
      PartialTriangulation.exists_glued V F₁ F₂ hcard e₁ e₂ he₁ he₂ hagree hsep hsurf
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
