import Schoenflies.OddWalkEdgeGraph

/-!
# Paths for individual segments in a common arrangement

`BrokenLineData.segmentFamilyChain` builds one line arrangement for an
arbitrary finite family of segments.  This file exposes the corresponding
path for each individual segment in the ambient arrangement graph and proves
that its geometric realization has exactly the original segment as range.
These declarations let the Chapter 9 collar-band construction concatenate
independently built polygonal arcs after resolving all of their overlaps in a
single finite plane complex.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData

namespace BrokenLineData

variable {U : Set Plane} (B : BrokenLineData U)

/-- The one-skeleton of a segment restriction maps into the one-skeleton of
the ambient common arrangement. -/
theorem segmentVertexGraph_le_arrangementVertexGraph (i : Fin B.n) :
    (B.segmentComplex i).vertexGraph ≤
      B.arrangementMesh.toPlaneComplex.vertexGraph :=
  (B.segmentVertexGraph_le_inSetGraph i).trans
    B.inSetGraph_le_arrangementVertexGraph

/-- A simple graph path along one source segment, viewed in the common
ambient arrangement. -/
noncomputable def arrangementSegmentPath (i : Fin B.n) :
    B.arrangementMesh.toPlaneComplex.vertexGraph.Path
      (B.arrangementVertex i.castSucc) (B.arrangementVertex i.succ) := by
  let q := Classical.choice (B.exists_path_on_segment i)
  let hle := segmentVertexGraph_le_arrangementVertexGraph B i
  exact ⟨(q : (B.segmentComplex i).vertexGraph.Walk _ _).mapLe hle,
    q.property.mapLe hle⟩

/-- The topological path obtained by drawing `arrangementSegmentPath` with
straight arrangement edges. -/
noncomputable def arrangementSegmentGeometricPath (i : Fin B.n) :
    Path (B.vertex i.castSucc) (B.vertex i.succ) :=
  Path.copy
    (B.arrangementMesh.toPlaneComplex.walkGeometricPath
      (arrangementSegmentPath B i :
        B.arrangementMesh.toPlaneComplex.vertexGraph.Walk _ _))
    (B.arrangementVertex_position i.castSucc)
    (B.arrangementVertex_position i.succ)

theorem range_arrangementSegmentGeometricPath_subset (i : Fin B.n) :
    range (arrangementSegmentGeometricPath B i) ⊆
      segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  let q := Classical.choice (B.exists_path_on_segment i)
  let hle := segmentVertexGraph_le_arrangementVertexGraph B i
  have hrange :
      range (B.arrangementMesh.toPlaneComplex.walkGeometricPath
        ((q : (B.segmentComplex i).vertexGraph.Walk
          (B.arrangementVertex i.castSucc)
          (B.arrangementVertex i.succ)).mapLe hle)) =
      range ((B.segmentComplex i).walkGeometricPath
        (q : (B.segmentComplex i).vertexGraph.Walk
          (B.arrangementVertex i.castSucc)
          (B.arrangementVertex i.succ))) := by
    exact B.arrangementMesh.toPlaneComplex
      |>.range_walkGeometricPath_mapLe_restrictedTo
        (segment ℝ (B.vertex i.castSucc) (B.vertex i.succ))
        (q : (B.segmentComplex i).vertexGraph.Walk
          (B.arrangementVertex i.castSucc)
          (B.arrangementVertex i.succ)) hle
  rw [arrangementSegmentGeometricPath, Path.copy_range]
  change range (B.arrangementMesh.toPlaneComplex.walkGeometricPath
      ((q : (B.segmentComplex i).vertexGraph.Walk
        (B.arrangementVertex i.castSucc)
        (B.arrangementVertex i.succ)).mapLe hle)) ⊆ _
  rw [hrange, ← B.segmentComplex_support i]
  exact (B.segmentComplex i).range_walkGeometricPath_subset_support
    (q : (B.segmentComplex i).vertexGraph.Walk
      (B.arrangementVertex i.castSucc)
      (B.arrangementVertex i.succ))
    (B.arrangementVertex_mem_segmentComplex_right i)

/-- For a nondegenerate source segment, its common-arrangement path draws
the whole segment, not merely a connected subarc of it. -/
theorem range_arrangementSegmentGeometricPath (i : Fin B.n)
    (hne : B.vertex i.castSucc ≠ B.vertex i.succ) :
    range (arrangementSegmentGeometricPath B i) =
      segment ℝ (B.vertex i.castSucc) (B.vertex i.succ) := by
  rw [← Path.range_segment]
  exact Path.range_eq_of_subset_of_injective
    (Path.segment (B.vertex i.castSucc) (B.vertex i.succ))
    (arrangementSegmentGeometricPath B i)
    (Path.segment_injective_of_ne hne)
    (by simpa only [Path.range_segment] using
      range_arrangementSegmentGeometricPath_subset B i)

/-- The common-arrangement vertex at the left endpoint of a labelled
segment. -/
noncomputable def segmentFamilyLeftVertex
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.Vertex :=
  let B := segmentFamilyChain left right
  let j := segmentFamilyIndex left right i
  B.arrangementVertex j.castSucc

/-- The common-arrangement vertex at the right endpoint of a labelled
segment. -/
noncomputable def segmentFamilyRightVertex
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.Vertex :=
  let B := segmentFamilyChain left right
  let j := segmentFamilyIndex left right i
  B.arrangementVertex j.succ

theorem segmentFamilyLeftVertex_position
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
        (segmentFamilyLeftVertex left right i) = left i := by
  exact segmentFamily_arrangementVertex_position_left left right i

theorem segmentFamilyRightVertex_position
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.position
        (segmentFamilyRightVertex left right i) = right i := by
  exact segmentFamily_arrangementVertex_position_right left right i

/-- The graph path along one labelled segment in the common arrangement. -/
noncomputable def segmentFamilyPath
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.vertexGraph.Path
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i) :=
  arrangementSegmentPath (segmentFamilyChain left right)
    (segmentFamilyIndex left right i)

/-- Drawing the canonical graph path for one label stays on that label's
source segment.  This walk-level form is convenient when comparing an edge
that occurs in two different labelled paths. -/
theorem range_walkGeometricPath_segmentFamilyPath_subset
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    range ((segmentFamilyChain left right).arrangementMesh.toPlaneComplex
      |>.walkGeometricPath
        (segmentFamilyPath left right i :
          (segmentFamilyChain left right).arrangementMesh.toPlaneComplex
            |>.vertexGraph.Walk
              (segmentFamilyLeftVertex left right i)
              (segmentFamilyRightVertex left right i))) ⊆
      segment ℝ (left i) (right i) := by
  have h := range_arrangementSegmentGeometricPath_subset
    (segmentFamilyChain left right) (segmentFamilyIndex left right i)
  rw [arrangementSegmentGeometricPath, Path.copy_range] at h
  rw [segmentFamilyChain_segment left right i] at h
  intro x hx
  apply h
  unfold segmentFamilyPath at hx
  exact hx

/-- Two labelled source segments whose intersection has at most one point
cannot contribute a common nondegenerate arrangement edge. -/
theorem segmentFamilyPath_edge_not_mem_of_inter_subsingleton
    {I : Type*} [Fintype I] (left right : I → Plane)
    (i j : I)
    (hinter : (segment ℝ (left i) (right i) ∩
      segment ℝ (left j) (right j)).Subsingleton)
    (e : Sym2
      (segmentFamilyChain left right).arrangementMesh.toPlaneComplex.Vertex)
    (hei : e ∈ (segmentFamilyPath left right i :
      (segmentFamilyChain left right).arrangementMesh.toPlaneComplex
        |>.vertexGraph.Walk
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i)).edges) :
    e ∉ (segmentFamilyPath left right j :
      (segmentFamilyChain left right).arrangementMesh.toPlaneComplex
        |>.vertexGraph.Walk
        (segmentFamilyLeftVertex left right j)
        (segmentFamilyRightVertex left right j)).edges := by
  intro hej
  induction e using Sym2.ind with
  | _ v w =>
      let K :=
        (segmentFamilyChain left right).arrangementMesh.toPlaneComplex
      let pi : K.vertexGraph.Walk
          (segmentFamilyLeftVertex left right i)
          (segmentFamilyRightVertex left right i) :=
        segmentFamilyPath left right i
      let pj : K.vertexGraph.Walk
          (segmentFamilyLeftVertex left right j)
          (segmentFamilyRightVertex left right j) :=
        segmentFamilyPath left right j
      have hiRange : segment ℝ (K.position v) (K.position w) ⊆
          range (K.walkGeometricPath pi) :=
        Schoenflies.TriangleMesh.PlaneComplex.segment_subset_range_walkGeometricPath_of_mem_edges
          K pi hei
      have hjRange : segment ℝ (K.position v) (K.position w) ⊆
          range (K.walkGeometricPath pj) :=
        Schoenflies.TriangleMesh.PlaneComplex.segment_subset_range_walkGeometricPath_of_mem_edges
          K pj hej
      have hiSource := range_walkGeometricPath_segmentFamilyPath_subset
        left right i
      have hjSource := range_walkGeometricPath_segmentFamilyPath_subset
        left right j
      have hv : K.position v ∈ segment ℝ (left i) (right i) ∩
          segment ℝ (left j) (right j) := by
        constructor
        · exact hiSource (hiRange (left_mem_segment ℝ _ _))
        · exact hjSource (hjRange (left_mem_segment ℝ _ _))
      have hw : K.position w ∈ segment ℝ (left i) (right i) ∩
          segment ℝ (left j) (right j) := by
        constructor
        · exact hiSource (hiRange (right_mem_segment ℝ _ _))
        · exact hjSource (hjRange (right_mem_segment ℝ _ _))
      have hvw : v = w := K.position_injective (hinter hv hw)
      exact (pi.adj_of_mem_edges hei).ne hvw

/-- If the initial vertex and every traversed straight edge lie in `U`, so
does the whole geometric realization of a graph walk. -/
theorem range_walkGeometricPath_subset_of_start_of_edges
    (K : PlaneComplex) {u z : K.Vertex}
    (p : K.vertexGraph.Walk u z) {U : Set Plane}
    (hstart : K.position u ∈ U)
    (hedges : ∀ v w, s(v, w) ∈ p.edges →
      segment ℝ (K.position v) (K.position w) ⊆ U) :
    range (K.walkGeometricPath p) ⊆ U := by
  induction p with
  | nil =>
      rw [K.walkGeometricPath_nil, Path.refl_range]
      exact Set.singleton_subset_iff.mpr hstart
  | @cons v w z hvw p ih =>
      rw [K.walkGeometricPath_cons, Path.trans_range]
      apply Set.union_subset
      · rw [Path.range_segment]
        exact hedges v w (by simp)
      · apply ih
        · exact hedges v w (by simp) (right_mem_segment ℝ _ _)
        · intro x y hxy
          exact hedges x y (by simp [hxy])

/-- Equal geometric endpoints are represented by the same canonical vertex
of the common arrangement. -/
theorem segmentFamilyRightVertex_eq_leftVertex_of_eq
    {I : Type*} [Fintype I] (left right : I → Plane) {i j : I}
    (h : right i = left j) :
    segmentFamilyRightVertex left right i =
      segmentFamilyLeftVertex left right j := by
  let B := segmentFamilyChain left right
  apply B.arrangementMesh.toPlaneComplex.position_injective
  rw [segmentFamilyRightVertex_position, segmentFamilyLeftVertex_position, h]

/-- Specialization to a labelled finite family: the canonical arrangement
path for label `i` has the prescribed endpoints. -/
noncomputable def segmentFamilyGeometricPath
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I) :
    Path (left i) (right i) := by
  let B := segmentFamilyChain left right
  let q := arrangementSegmentGeometricPath B
    (segmentFamilyIndex left right i)
  exact Path.copy q
    (segmentFamilyChain_vertex_even left right i)
    (segmentFamilyChain_vertex_odd left right i)

theorem range_segmentFamilyGeometricPath
    {I : Type*} [Fintype I] (left right : I → Plane) (i : I)
    (hne : left i ≠ right i) :
    range (segmentFamilyGeometricPath left right i) =
      segment ℝ (left i) (right i) := by
  let B := segmentFamilyChain left right
  let j := segmentFamilyIndex left right i
  have hleft : B.vertex j.castSucc = left i :=
    segmentFamilyChain_vertex_even left right i
  have hright : B.vertex j.succ = right i :=
    segmentFamilyChain_vertex_odd left right i
  have hne' : B.vertex j.castSucc ≠ B.vertex j.succ := by
    simpa [hleft, hright] using hne
  rw [segmentFamilyGeometricPath, Path.copy_range,
    range_arrangementSegmentGeometricPath B j hne', hleft, hright]

end BrokenLineData

end Schoenflies
