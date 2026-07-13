/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.HalfPlanePolygon
import ClassificationOfSurfaces.Moise.LocallyFiniteSidePreservation

/-!
# Controlled locally finite PL replacement

This file packages the completed cellwise part of Moise Chapter 6, Theorem 3.  The graph-level
construction supplies quantitative face control and separation.  Polygonal Schoenflies then
fills every face, and local finiteness glues the fillings into a homeomorphism of supports.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

open PlaneGraphRealization

variable {S : Type*} [TopologicalSpace S] [T2Space S]
variable {K : LocallyFiniteTriangleComplex S}

/-- The closed metric controls used for a replacement are contained in the permitted open
region. -/
def PlaneGraphRealization.ControlsStayInRegion (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  ∀ p, Metric.closedBall (G.map p) (phi p) ⊆ G.region

/-- A global bound and a frontier-relative bound sufficient to control a locally finite
family of polygonal face fillings. -/
def PlaneGraphRealization.UniformFrontierControl (G : K.PlaneGraphRealization)
    (phi : K.support → ℝ) : Prop :=
  (∀ p, phi p ≤ 1) ∧
    ∀ (_ : G.regionᶜ.Nonempty) (p : K.support),
      phi p ≤ Metric.infDist (G.map p) G.regionᶜ / 4

/-- Frontier control keeps each selected polygonal disk inside the permitted open region. -/
theorem closedRegions_mem_region_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region := by
  by_cases hcomp : G.regionᶜ.Nonempty
  · obtain ⟨z, hz⟩ := K.faceCarrier_nonempty f
    obtain ⟨x, rfl⟩ := hz
    let p : K.support := faceToSupport (K := K) f x
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self x
    have hball := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp
    intro q hq
    have hdist : dist (G.map p) q ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hball hq
    have hinfPos : 0 < Metric.infDist (G.map p) G.regionᶜ := by
      exact (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
        (by simpa only [Set.mem_compl_iff, not_not] using G.map_mem_region p)
    have hlt : dist (G.map p) q < Metric.infDist (G.map p) G.regionᶜ := by
      calc
        dist (G.map p) q ≤ phi p := hdist
        _ ≤ Metric.infDist (G.map p) G.regionᶜ / 4 := hfrontier.2 hcomp p
        _ < Metric.infDist (G.map p) G.regionᶜ := by linarith
    have hnot := Metric.notMem_of_dist_lt_infDist hlt
    simpa only [Set.mem_compl_iff, not_not] using hnot
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    rw [hregion]
    exact Set.subset_univ _

/-- The filled polygonal disks of a uniformly frontier-controlled replacement are locally
finite in the open perturbation region.  The proof confines any disk meeting a small ball to
an original face meeting a fixed compact ball, then uses relative closed-embedding transport. -/
theorem locallyFinite_closedRegions_of_uniformFrontierControl
    (G : K.PlaneGraphRealization) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi) :
    LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion} := by
  intro x
  by_cases hcomp : G.regionᶜ.Nonempty
  · let d := Metric.infDist x.1 G.regionᶜ
    have hd : 0 < d := by
      apply (G.regionOpen.isClosed_compl.notMem_iff_infDist_pos hcomp).mp
      show x.1 ∉ G.regionᶜ
      simpa only [Set.mem_compl_iff, not_not] using x.2
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 (d / 8)}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (div_pos hd (by norm_num))), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 (d / 2)
    have hCV : C ⊆ G.region := by
      intro q hq
      by_contra hqRegion
      have hinf := Metric.infDist_le_dist_of_mem (x := x.1)
        (show q ∈ G.regionᶜ from hqRegion)
      have hdist : dist x.1 q ≤ d / 2 := by
        simpa only [C, Metric.mem_closedBall, dist_comm] using hq
      dsimp only [d] at hd hinf hdist
      linarith
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < d / 8 := Metric.mem_ball.mp hzU
    have hinf : Metric.infDist (G.map p) G.regionᶜ ≤
        d + dist (G.map p) x.1 :=
      Metric.infDist_le_infDist_add_dist
    have hmain : dist (G.map p) x.1 <
        (d + dist (G.map p) x.1) / 4 + d / 8 := calc
      dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
        dist_triangle _ _ _
      _ < phi p + d / 8 := add_lt_add_of_le_of_lt hcenterZ hzX
      _ ≤ (d + dist (G.map p) x.1) / 4 + d / 8 := by
        gcongr
        exact (hfrontier.2 hcomp p).trans
          (div_le_div_of_nonneg_right hinf (by norm_num))
    have hpCenter : dist (G.map p) x.1 ≤ d / 2 := by linarith
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter
  · have hregion : G.region = Set.univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      exact hcomp ⟨q, hq⟩
    let U : Set G.region := {q | q.1 ∈ Metric.ball x.1 1}
    refine ⟨U, continuous_subtype_val.continuousAt
      (Metric.ball_mem_nhds x.1 (by norm_num)), ?_⟩
    let C : Set Plane := Metric.closedBall x.1 2
    have hCV : C ⊆ G.region := by rw [hregion]; exact Set.subset_univ _
    have hCcompact : IsCompact ((↑) ⁻¹' C : Set G.region) :=
      PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        (isCompact_closedBall _ _) hCV
    have hfinite :=
      G.locallyFinite_faceImagesInRegion.finite_nonempty_inter_compact hCcompact
    apply hfinite.subset
    intro f hf
    obtain ⟨z, hzClosed, hzU⟩ := hf
    obtain ⟨w, hw⟩ := K.faceCarrier_nonempty f
    obtain ⟨y, rfl⟩ := hw
    let p : K.support := faceToSupport (K := K) f y
    let c : G.region := ⟨G.map p, G.map_mem_region p⟩
    have hp : p ∈ faceInSupport (K := K) f := Set.mem_range_self y
    have hzBall := facePolygonalCircle_closedRegion_subset_closedBall
      hcontrol f p hp hzClosed
    have hcenterZ : dist (G.map p) z.1 ≤ phi p := by
      simpa only [Metric.mem_closedBall, dist_comm] using hzBall
    have hzX : dist z.1 x.1 < 1 := Metric.mem_ball.mp hzU
    have hpCenter : dist (G.map p) x.1 ≤ 2 := by
      apply le_of_lt
      calc
        dist (G.map p) x.1 ≤ dist (G.map p) z.1 + dist z.1 x.1 :=
          dist_triangle _ _ _
        _ < phi p + 1 := add_lt_add_of_le_of_lt hcenterZ hzX
        _ ≤ 2 := by linarith [hfrontier.1 p]
    refine ⟨c, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact hpCenter

/-- Convex target regions are preserved by the simultaneous polygonal replacement of the
one-skeleton.  The construction chooses each central broken line in the convex hull of its
original embedded edge. -/
theorem range_graphReplacementMap_subset_of_convex
    (G : K.PlaneGraphRealization) {C : Set Plane} (hC : Convex ℝ C)
    (hmap : Set.range G.map ⊆ C) :
    Set.range G.graphReplacementMap ⊆ C := by
  rw [G.range_graphReplacementMap]
  intro y hy
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
  apply convexHull_min _ hC <|
    (G.replacementArc e).completeCarrier_subset_edgeConvexHull hye
  rintro z ⟨p, -, rfl⟩
  exact hmap (Set.mem_range_self p)

/-- A source realization in the model half-plane has a replacement graph in that half-plane. -/
theorem range_graphReplacementMap_subset_halfPlane
    (G : K.PlaneGraphRealization) (hmap : Set.range G.map ⊆ HalfPlaneSet) :
    Set.range G.graphReplacementMap ⊆ HalfPlaneSet :=
  range_graphReplacementMap_subset_of_convex G convex_halfPlaneSet hmap

/-- A controlled compatible cellwise replacement lands in the permitted perturbation region. -/
theorem polygonalReplacementMap_mem_region (G : K.PlaneGraphRealization)
    (H : K.CellwiseCompatibility G) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hregion : G.ControlsStayInRegion phi) (p : K.support) :
    (K.polygonalReplacementMap H p).1.1 ∈ G.region :=
  (K.polygonalReplacementMap H p).1.2

/-- The full locally finite Chapter 6 output from its quantitative graph hypotheses. -/
theorem exists_controlled_polygonalReplacement (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hsep : SeparatesVerticesFromFaces G phi)
    (hregion : ∀ f : K.Face,
      (K.facePolygonalCircle (G := G) f).closedRegion ⊆ G.region)
    (hloc : LocallyFinite fun f : K.Face ↦
      {q : G.region | q.1 ∈
        (K.facePolygonalCircle (G := G) f).closedRegion}) :
    ∃ H : K.CellwiseCompatibility G,
      (∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p) := by
  let H := cellwiseCompatibility_of_control (G := G) hfaces hcontrol hsep hregion hloc
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The complete locally finite Chapter 6 output in Moise's facewise side-control form.
Uniform frontier control supplies target containment and local finiteness automatically. -/
theorem exists_controlled_polygonalReplacement_of_facewise_close
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hclose : FaceBoundariesClose G (faceVertexSeparationRadius G)) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  let H := cellwiseCompatibility_of_facewise_close (G := G) hfaces hclose
    (closedRegions_mem_region_of_uniformFrontierControl G hcontrol hfrontier)
    (locallyFinite_closedRegions_of_uniformFrontierControl G hcontrol hfrontier)
  exact ⟨H, fun p ↦ polygonalReplacementMap_dist_le H hcontrol p⟩

/-- The Chapter 6 cellwise approximation from the exact edge-mesh condition supplied by an
internal edge subdivision.  No independent side hypothesis remains: the incident-face minimum
turns edgewise diameter control into the required facewise closeness. -/
theorem exists_controlled_polygonalReplacement_of_edgeMesh
    (G : K.PlaneGraphRealization)
    (hfaces : Function.Injective K.faceVertices) {phi : K.support → ℝ}
    (hcontrol : FaceBoundariesControlled G phi)
    (hfrontier : G.UniformFrontierControl phi)
    (hmesh : ∀ e : K.Edge,
      2 * Metric.diam (G.edgeImage e) < edgeFaceSeparationRadius G e) :
    ∃ H : K.CellwiseCompatibility G,
      ∀ p : K.support,
        dist (K.polygonalReplacementHomeomorph H p).1.1 (G.map p) ≤ phi p := by
  exact exists_controlled_polygonalReplacement_of_facewise_close G hfaces hcontrol hfrontier
    (faceBoundariesClose_of_edgeFaceSeparation_control (G := G) hmesh)

/-- If the replacement graph lies in the closed right half-plane, every selected polygonal face
disk lies there too. -/
theorem facePolygonalCircle_closedRegion_subset_halfPlane
    (G : K.PlaneGraphRealization)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (f : K.Face) :
    (K.facePolygonalCircle (G := G) f).closedRegion ⊆ HalfPlaneSet := by
  apply (K.facePolygonalCircle (G := G) f).closedRegion_subset_halfPlane
  exact (K.facePolygonalCircle_carrier_subset_graphReplacement (G := G) f).trans hgraph

/-- Consequently the entire assembled locally finite replacement complex stays in the closed
right half-plane. -/
theorem polygonalReplacementComplex_support_subset_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet) :
    Subtype.val '' (K.polygonalReplacementComplex H).support ⊆ HalfPlaneSet := by
  rintro p ⟨q, hq, rfl⟩
  have hpSupport : q ∈ (K.polygonalReplacementComplex H).support := hq
  obtain ⟨f, hpf⟩ := Set.mem_iUnion.mp hpSupport
  rw [K.polygonalReplacementComplex_faceCarrier H f] at hpf
  exact facePolygonalCircle_closedRegion_subset_halfPlane G hgraph f hpf

/-- Pointwise half-plane preservation for the assembled replacement homeomorphism. -/
theorem polygonalReplacementHomeomorph_mem_halfPlane
    (G : K.PlaneGraphRealization) (H : K.CellwiseCompatibility G)
    (hgraph : Set.range G.graphReplacementMap ⊆ HalfPlaneSet)
    (p : K.support) :
    (K.polygonalReplacementHomeomorph H p).1.1 ∈ HalfPlaneSet :=
  polygonalReplacementComplex_support_subset_halfPlane G H hgraph
    ⟨(K.polygonalReplacementHomeomorph H p).1,
      (K.polygonalReplacementHomeomorph H p).2, rfl⟩

end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
