/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.ChartInductionCore

/-!
# The Radó crossing weld and chart induction

This file completes the chart-induction framework developed in `ChartInductionCore`. It constructs
the crossing weld, packages the one-chart induction step, and assembles the final triangulation.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

open PartialTriangulation.PolygonalReplacementSourceAtlas
open PartialTriangulation.RelativeSynchronizedTarget

-- This large assembly includes the boundary-regular subdivision certificate as well as the
-- crossing weld; keep one explicit cumulative budget for the whole construction.
set_option maxHeartbeats 2500000 in
-- The proof assembles the certified straightening, subdivision, and weld in one dependent term.
/-- Shared implementation of the Moise crossing weld once the chart straightening is certified
to preserve the ambient manifold-boundary stratum.

In the genuine crossing case (the chart core is not yet covered, and the absorbed region is not
inside the chart patch), the adjusted old complex and the chart patch admit a common welded
presentation: a common vertex type carrying both face families, with embeddings that agree
exactly on the shared realization, satisfy the combinatorial-surface bound jointly, and whose
united image contains `A ∪ c.core` in its topological interior.

The proof straightens the old complex over the
chart overlap by the locally finite controlled polygonal replacement over
`adaptiveOverlapGraphRealization` with tolerance vanishing at the overlap frontier
(`replaceOnOpen`/`frontierGlue`), refine the straightened trace and the fixed patch complex to
a common plane subdivision (`CommonSubdivision`, Moise's conditions (e)-(h)), and read off the
welded presentation. The finite compact-collar theorem cannot replace this vanishing-tolerance
construction, because continuity across the overlap frontier depends on the error tending to
zero there. -/
theorem MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening
    (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A)
    (hstraight :
      PartialTriangulation.BoundaryPreservingStraightening S T c) :
    let _ := (inferInstance : ConnectedSpace S)
    let _ := (inferInstance : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S)
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
  dsimp
  classical
  letI : SecondCountableTopology S := moise_secondCountableTopology S
  -- Protect a genuine closed neighborhood of the old cores, not merely the cores pointwise.
  -- This makes the old half of the final coverage invariant tautological after straightening.
  obtain ⟨C, hCclosed, hAC, hCT⟩ := hT.exists_closedBuffer
  obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
      hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
      hembed, hBoundaryPreservation⟩ :=
    hstraight C hCclosed
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
        horizontalLine_mem_coordinateAnchorLines anchorCoordinate a
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
      simp [stdSimplex.vertex, hw]
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
      simp [hw]
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
        boundaryMarking.edgeIntervalFirst
            (Rlevel.refined.faceEdge f.1.1 f.1.2.1) f.1.2.2 ∈
          localVertexLevelPoints)
      (hp₁ :
        boundaryMarking.edgeIntervalSecond
            (Rlevel.refined.faceEdge f.1.1 f.1.2.1) f.1.2.2 ∈
          localVertexLevelPoints) :
      ∃ s : {s : T.toIntrinsic.LevelFace n //
          s ∈ selectedLevelFaces},
        (Rlevel.refined.faceEdge f.1.1 f.1.2.1).1 ⊆ s.1.1 := by
    let e := Rlevel.refined.faceEdge f.1.1 f.1.2.1
    let p₀ :=
      boundaryMarking.edgeIntervalFirst e f.1.2.2
    let p₁ :=
      boundaryMarking.edgeIntervalSecond e f.1.2.2
    have hp₀Edge : p₀ ∈ Rlevel.refined.faceCarrier e.1 :=
      boundaryMarking.edgeIntervalFirst_mem_faceCarrier e f.1.2.2
    have hp₁Edge : p₁ ∈ Rlevel.refined.faceCarrier e.1 :=
      boundaryMarking.edgeIntervalSecond_mem_faceCarrier e f.1.2.2
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
        let p₀ := boundaryMarking.edgeIntervalFirst e f.1.2.2
        let p₁ := boundaryMarking.edgeIntervalSecond e f.1.2.2
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
        have hgap (v : {v // v ∈ t.1}) (hvPos : 0 < x₀ v) :
            ¬boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨v.1, ⟨t.1, t.2, v.2⟩⟩) ∈ Set.Ioo a₀ a₁ := by
          have hvEdge :=
            positive_localVertex_mem_edge t x₀ e hqEdge v hvPos
          have hvMark :
              localVertexLevelPoint
                  ⟨v.1, ⟨t.1, t.2, v.2⟩⟩ ∈
                boundaryMarking.edgeMarks e :=
            (boundaryMarking.mem_edgeMarks_iff e _).mpr
              ⟨localVertexLevelPoint_mem_marking
                ⟨v.1, ⟨t.1, t.2, v.2⟩⟩, hvEdge⟩
          exact boundaryMarking.not_edgeMark_parameter_mem_Ioo
            e f.1.2.2 hvMark
        obtain ⟨existsLow, existsHigh⟩ :=
          exists_positive_weight_on_both_sides_of_gap
            (weight := fun v : {v // v ∈ t.1} ↦ x₀ v)
            (value := fun v ↦
              boundaryMarking.edgeParameterValue e
                (localVertexLevelPoint
                  ⟨v.1, ⟨t.1, t.2, v.2⟩⟩))
            a₀ a₁ z₀ x₀.2.1 x₀.2.2 hzAverage hgap hzInterval
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
  have mixedUsedFaceMap_val
      (f : MixedOldFace)
      (x : stdSimplex ℝ {v // v ∈ mixedUsedFaceVertices f}) :
      (mixedUsedFaceMap f x).1 =
        fun k ↦ ∑ v : UsedOldVertex,
          extendFaceCoordinates (mixedUsedFaceVertices f) x v *
            v.1.1.1 k := by
    rw [show mixedUsedFaceMap f x =
        mixedOldFaceMap f
          (relabelUnivSimplex (mixedFaceUsedEmbedding f) x) by rfl,
      mixedOldFaceMap_val]
    funext k
    have hused :=
      sum_extendFaceCoordinates_relabelUnivSimplex
        (mixedFaceUsedEmbedding f) x
          (fun v : UsedOldVertex ↦ v.1.1.1 k)
    have hold :
        (∑ v : OldVertex,
            extendFaceCoordinates (mixedOldFaceVertices f)
                (relabelUnivSimplex (mixedFaceUsedEmbedding f) x) v *
              v.1.1 k) =
          ∑ v ∈ mixedOldFaceVertices f,
            extendFaceCoordinates (mixedOldFaceVertices f)
                (relabelUnivSimplex (mixedFaceUsedEmbedding f) x) v *
              v.1.1 k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      rw [extendFaceCoordinates_of_notMem _ _ hv, zero_mul]
    rw [hused, hold,
      ← sum_attach_mul_eq_sum_extendFaceCoordinates
        (mixedOldFaceVertices f)
        (relabelUnivSimplex (mixedFaceUsedEmbedding f) x)
        (fun v : OldVertex ↦ v.1.1 k)]
    rfl
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
  let mixedOldHomeomorph :
      mixedOldComplex.compactIntrinsic.realization ≃ₜ
        Rlevel.refined.realization := by
    let e :
        mixedOldComplex.compactIntrinsic.realization ≃
          Rlevel.refined.realization :=
      Equiv.ofBijective mixedOldComplex.compactEval
        ⟨mixedOldComplex.injective_compactEval, by
          intro y
          have hy : y ∈ mixedOldComplex.support := by
            rw [mixedOldComplex_support]
            exact Set.mem_univ y
          rw [← mixedOldComplex.range_compactEval] at hy
          exact hy⟩
    exact Continuous.homeoOfEquivCompactToT2
      (f := e) mixedOldComplex.continuous_compactEval
  let mixedUsedBarycentricAffine :
      (UsedOldVertex → ℝ) →ᵃ[ℝ]
        (Rlevel.refined.Vertex → ℝ) :=
    (∑ v : UsedOldVertex,
      (LinearMap.proj v).smulRight
        (v.1.1.1 : Rlevel.refined.Vertex → ℝ)).toAffineMap
  have mixedUsedBarycentricAffine_apply
      (z : UsedOldVertex → ℝ) :
      mixedUsedBarycentricAffine z =
        fun k ↦ ∑ v : UsedOldVertex, z v * v.1.1.1 k := by
    funext k
    simp [mixedUsedBarycentricAffine, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  let mixedSubdivision : Rlevel.refined.Subdivision := by
    letI : Fintype mixedOldComplex.Vertex :=
      mixedOldComplex.compactIntrinsic.vertexFintype
    exact
      { refined := mixedOldComplex.compactIntrinsic
        homeo := mixedOldHomeomorph
        affineOnFace := by
          intro s hs
          change s ∈ mixedOldComplex.compactIntrinsic.faces at hs
          rw [mixedOldComplex.compactIntrinsic_faces] at hs
          obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
          refine ⟨mixedUsedBarycentricAffine, ?_⟩
          intro x hx
          have heval :=
            mixedOldComplex.compactEval_eq_faceMap f x hx
          have hhomeo :
              (mixedOldHomeomorph x).1 =
                (mixedOldComplex.compactEval x).1 :=
            congrArg Subtype.val (show
              mixedOldHomeomorph x =
                mixedOldComplex.compactEval x by rfl)
          rw [hhomeo, heval]
          change
            (mixedUsedFaceMap f
                (mixedOldComplex.restrictToFace
                  (mixedUsedFaceVertices f) ⟨x.1, x.2.1⟩ hx)).1 =
              mixedUsedBarycentricAffine x.1
          rw [mixedUsedFaceMap_val,
            mixedUsedBarycentricAffine_apply,
            mixedOldComplex.extendFaceCoordinates_restrictToFace]
          funext k
          apply Finset.sum_congr rfl
          intro v hv
          rfl
        subordinate := by
          intro s hs
          change s ∈ mixedOldComplex.compactIntrinsic.faces at hs
          rw [mixedOldComplex.compactIntrinsic_faces] at hs
          obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hs
          rcases f with t | f
          · refine ⟨(localFaceLevelFace t).1.1,
                (localFaceLevelFace t).1.2, ?_⟩
            intro x hx
            have heval :=
              mixedOldComplex.compactEval_eq_faceMap
                (Sum.inl t) x hx
            change mixedOldHomeomorph x ∈
              Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1
            rw [show mixedOldHomeomorph x =
                mixedOldComplex.compactEval x by rfl, heval]
            change mixedUsedFaceMap (Sum.inl t)
                (mixedOldComplex.restrictToFace
                  (mixedUsedFaceVertices (Sum.inl t))
                  ⟨x.1, x.2.1⟩ hx) ∈
              Rlevel.refined.faceCarrier (localFaceLevelFace t).1.1
            exact localMixedFaceMap_mem_parent t _
          · refine ⟨f.1.1.1, f.1.1.2, ?_⟩
            intro x hx
            have heval :=
              mixedOldComplex.compactEval_eq_faceMap
                (Sum.inr f) x hx
            change mixedOldHomeomorph x ∈
              Rlevel.refined.faceCarrier f.1.1.1
            rw [show mixedOldHomeomorph x =
                mixedOldComplex.compactEval x by rfl, heval]
            change mixedUsedFaceMap (Sum.inr f)
                (mixedOldComplex.restrictToFace
                  (mixedUsedFaceVertices (Sum.inr f))
                  ⟨x.1, x.2.1⟩ hx) ∈
              Rlevel.refined.faceCarrier f.1.1.1
            exact boundaryMarking.globalFanFaceMap_mem_faceCarrier
              f.1 _ }
  have hRlevelBoundary :
      (T.refine Rlevel).BoundaryFacewiseRegular :=
    PartialTriangulation.boundaryFacewiseRegular_refine
      T hT.boundaryFacewiseRegular Rlevel
  have hMixedBoundaryForT :
      ((T.refine Rlevel).refine mixedSubdivision).BoundaryFacewiseRegular :=
    PartialTriangulation.boundaryFacewiseRegular_refine
      (T.refine Rlevel) hRlevelBoundary mixedSubdivision
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
  have he₂Boundary :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles e₂ := by
    have hmeshModel :
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).toPlaneComplex.support ⊆ c.kind.modelRegion := by
      rw [PartialTriangulation.RelativeSynchronizedTarget.newMesh_support
        J N lines hN_arrangement]
      exact hN_model
    apply PartialTriangulation.boundaryFacewiseRegularEmbedding_congr
      (PartialTriangulation.TriangleMesh.boundaryFacewiseRegularEmbedding_chart
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh J N lines)
        c hc hmeshModel)
    intro x
    have heq :
        e₂ x =
          (c.chart.symm
            ((PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).coordinateEmbedInto
                c.kind.modelRegion hmeshModel x)).1 := by
      rfl
    rw [heq]
  have hDtarget : D ⊆ interior (Set.range e₂) := by
    intro x hx
    let xD : D := ⟨x, hx⟩
    have hpInterior :
        dModel xD ∈ interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support} :=
      hDmodelInteriorN ⟨xD, rfl⟩
    apply
      (modelInterior_subset_interior_range_newSurfaceEmbed c J N lines
        hN_arrangement hN_model)
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
        simp only [oldToCommonFun, dif_pos hv,
          dif_neg hw, reduceCtorEq] at hvw
    · by_cases hw : ∃ u : localSourceComplex.UsedVertex,
          localUsedOldEmbedding u = w
      · exfalso
        simp only [oldToCommonFun, dif_neg hv,
          dif_pos hw, reduceCtorEq] at hvw
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
  have hMixedBoundaryEmbedding :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        mixedOldComplex.compactIntrinsic.faces
        (fun x ↦
          T.embed
            (Rlevel.homeo (mixedOldComplex.compactEval x))) := by
    change
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        mixedOldComplex.compactIntrinsic.faces
        (fun x ↦
          T.embed
            (Rlevel.homeo (mixedOldHomeomorph x)))
        at hMixedBoundaryForT
    convert hMixedBoundaryForT using 1
    funext x
    rfl
  have heOldBoundary :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        mixedOldComplex.compactIntrinsic.faces eOld := by
    apply PartialTriangulation.boundaryFacewiseRegularEmbedding_congr
      hMixedBoundaryEmbedding
    intro x
    change
      T₀.embed
          (Rlevel.homeo (mixedOldComplex.compactEval x)) ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        T.embed
          (Rlevel.homeo (mixedOldComplex.compactEval x)) ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S
    exact hBoundaryPreservation
      (Rlevel.homeo (mixedOldComplex.compactEval x))
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
  have he₁Boundary :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ := by
    apply PartialTriangulation.boundaryFacewiseRegularEmbedding_congr
      (PartialTriangulation.boundaryFacewiseRegularEmbedding_relabel
        oldCompactToCommon mixedOldComplex.compactIntrinsic.faces
          eOld heOldBoundary)
    intro x
    have heq :
        e₁ x =
          (eOld ∘
            (relabelGeometricRealizationHomeomorph oldCompactToCommon
              mixedOldComplex.compactIntrinsic.faces).symm) x := by
      rfl
    rw [heq]
  have he₂common : _root_.Topology.IsEmbedding e₂common :=
    he₂.comp
      (relabelGeometricRealizationHomeomorph targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles).symm.isEmbedding
  have he₂commonBoundary :
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂common := by
    change
      PartialTriangulation.BoundaryFacewiseRegularEmbedding
        (relabelFaceFamily targetToCommon
          (PartialTriangulation.RelativeSynchronizedTarget.newMesh
            J N lines).triangles)
        (e₂ ∘
          (relabelGeometricRealizationHomeomorph targetToCommon
            (PartialTriangulation.RelativeSynchronizedTarget.newMesh
              J N lines).triangles).symm)
    exact
      PartialTriangulation.boundaryFacewiseRegularEmbedding_relabel
        targetToCommon
        (PartialTriangulation.RelativeSynchronizedTarget.newMesh
          J N lines).triangles e₂ he₂Boundary
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
      rw [← hgval qU]
      exact hqTarget
    have hqCN :
        (Q.sourceHomeomorph qU).1 ∈ CN := by
      change (Q.sourceHomeomorph qU).1.1 ∈
        N.toPlaneComplex.support
      rw [← hgcoord qU]
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
    F₁, F₂, e₁, e₂common, hcard, he₁, he₂common, hagree, hsep,
      he₁Boundary, he₂commonBoundary, ?_⟩
  · rw [range_e₁, range_e₂common]
    intro x hx
    rcases hx with hxA | hxCore
    · exact interior_mono (Set.subset_union_left) (hA₀ hxA)
    · by_cases hxOld : x ∈ interior T₀.support
      · exact interior_mono Set.subset_union_left
          hxOld
      · apply interior_mono Set.subset_union_right
        exact hDtarget ⟨hxCore, hxOld⟩

/-- The bordered crossing weld.  The relative straightening preserves the ambient boundary
stratum, and the synchronized source/target presentations retain it as a simplicial face. -/
theorem MoiseChart.exists_crossing_weld (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
      PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
      A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) :=
  MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening
    S c hc hT
      (PartialTriangulation.exists_boundaryPreservingStraightening S T c hc
        hT.boundaryFacewiseRegular)

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
      radoInvariant_chartPatch_absorb c hc hT.coresCompact hA⟩
  · -- the crossing case: weld the adjusted old complex and the chart patch, then glue
    obtain ⟨V, _, _, F₁, F₂, e₁, e₂, hcard, he₁, he₂, hagree, hsep,
        hboundary₁, hboundary₂, hcover⟩ :=
      MoiseChart.exists_crossing_weld S c hc hT
    obtain ⟨T', _vertexEquiv, _hfaces, hsupport, hsurf', hboundary'⟩ :=
      PartialTriangulation.exists_glued V F₁ F₂ hcard e₁ e₂ he₁ he₂
        hagree hsep hboundary₁ hboundary₂
    refine ⟨T', ?_, hsurf', hboundary', ?_⟩
    · exact (hT.coresCompact.union c.isCompact_core)
    · rw [hsupport]
      exact hcover

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- Shared finite Radó induction assembler.  It turns any clean one-chart absorption step with the
full `RadoInvariant` conclusion into an end-to-end geometric triangulation. -/
theorem moise_triangulation_of_induction
    (hstep : ∀ (c : MoiseChart S), c.BoundaryFaithful →
      ∀ {T : PartialTriangulation S} {A : Set S}, RadoInvariant T A →
        ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core)) :
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
            hstep (charts ⟨k, hk⟩) (hbd ⟨k, hk⟩) hT
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

/-- The bordered Radó induction assembled from its boundary-preserving one-chart step. -/
theorem moise_triangulation_of_boundaries :
    Nonempty (GeometricTriangulation S) :=
  moise_triangulation_of_induction S (moise_induction_step S)

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
