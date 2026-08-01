import Schoenflies.ArcNeighborhoods
import Schoenflies.PolygonalJordanCircle

/-!
# Polygonal disk neighborhoods of connected compact sets

The synchronized-collar construction naturally produces polygonal circles,
but selecting their bounded side requires a global winding argument.  For the
recursive disk exhaustion it is cleaner to select the bounded side first.

This file extracts the exterior-facing boundary component of a finite
polyhedral neighborhood of an arbitrary compact connected set.  Applied
inside a Jordan domain, the result is a polygonal disk which contains the
prescribed compact set in its open interior and whose entire closed region
remains in the Jordan inside.

All finite-complex input is reused from `ArcNeighborhoods` and
`FiniteBoundaryGraph`; no declaration in the Moise namespace is changed.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle

/-- A compact subset of the Jordan inside can be enlarged to a compact
connected subset of the inside.  Compactness reduces the construction to
finitely many paths from one base point and finitely many small closed balls.

This elementary hull lemma is what lets the polygonal disk neighborhoods
below absorb an arbitrary compact exhaustion core as well as the preceding
polygonal disk. -/
theorem exists_compactConnected_superset_inside
    (J : JordanCircle) {K : Set Plane}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKinside : K ⊆ J.inside) :
    ∃ C : Set Plane,
      K ⊆ C ∧ IsCompact C ∧ IsConnected C ∧ C ⊆ J.inside := by
  classical
  obtain ⟨delta, hdelta, hthick⟩ :=
    hKcompact.exists_cthickening_subset_open J.inside_isOpen hKinside
  obtain ⟨centers, hcentersK, hcentersFinite, hcover⟩ :=
    hKcompact.finite_cover_balls (show 0 < delta / 4 by positivity)
  letI : Fintype centers := hcentersFinite.fintype
  let a : Plane := hKnonempty.some
  have haK : a ∈ K := hKnonempty.some_mem
  have haInside : a ∈ J.inside := hKinside haK
  have hpathConnected : IsPathConnected J.inside :=
    J.inside_isOpen.isConnected_iff_isPathConnected.mp J.inside_isConnected
  let path (x : centers) : Path a x :=
    (hpathConnected.joinedIn a haInside x
      (hKinside (hcentersK x.2))).somePath
  let piece : Option centers → Set Plane
    | none => {a}
    | some x => range (path x) ∪ Metric.closedBall x (delta / 2)
  let C : Set Plane := ⋃ i : Option centers, piece i
  have hpieceCompact : ∀ i, IsCompact (piece i) := by
    intro i
    cases i with
    | none => exact isCompact_singleton
    | some x =>
        exact (isCompact_range (path x).continuous).union
          (isCompact_closedBall (x : Plane) (delta / 2))
  have hpieceConnected : ∀ i, IsConnected (piece i) := by
    intro i
    cases i with
    | none => exact isConnected_singleton
    | some x =>
        have hrange : IsConnected (range (path x)) :=
          isConnected_range (path x).continuous
        have hball : IsConnected (Metric.closedBall (x : Plane) (delta / 2)) :=
          (convex_closedBall (x : Plane) (delta / 2)).isConnected
            ⟨x, Metric.mem_closedBall_self (by positivity)⟩
        apply IsConnected.union
          (s := range (path x)) (t := Metric.closedBall x (delta / 2))
          (Hs := hrange) (Ht := hball)
        exact ⟨x, Path.target_mem_range (path x),
          Metric.mem_closedBall_self (by positivity)⟩
  have haPiece : ∀ i, a ∈ piece i := by
    intro i
    cases i with
    | none => exact Set.mem_singleton a
    | some x => exact Or.inl (Path.source_mem_range (path x))
  have hCcompact : IsCompact C := by
    exact isCompact_iUnion hpieceCompact
  have hCconnected : IsConnected C := by
    refine ⟨⟨a, Set.mem_iUnion.mpr ⟨none, haPiece none⟩⟩, ?_⟩
    apply isPreconnected_iUnion
    · exact ⟨a, Set.mem_iInter.mpr haPiece⟩
    · exact fun i => (hpieceConnected i).isPreconnected
  have hCinside : C ⊆ J.inside := by
    intro y hy
    obtain ⟨i, hyPiece⟩ := Set.mem_iUnion.mp hy
    cases i with
    | none =>
        have hya : y = a := by simpa [piece] using hyPiece
        simpa [hya] using haInside
    | some x =>
        rcases hyPiece with hyPath | hyBall
        · obtain ⟨t, rfl⟩ := hyPath
          exact (hpathConnected.joinedIn a haInside x
            (hKinside (hcentersK x.2))).somePath_mem t
        · apply hthick
          apply Metric.closedBall_subset_cthickening (hcentersK x.2) delta
          exact Metric.closedBall_subset_closedBall (by nlinarith) hyBall
  have hKC : K ⊆ C := by
    intro x hxK
    have hxCover := hcover hxK
    obtain ⟨c, hcCenters, hxc⟩ := Set.mem_iUnion₂.mp hxCover
    let c' : centers := ⟨c, hcCenters⟩
    apply Set.mem_iUnion.mpr
    refine ⟨some c', ?_⟩
    apply Or.inr
    rw [Metric.mem_closedBall]
    have hdist := Metric.mem_ball.mp hxc
    nlinarith
  exact ⟨C, hKC, hCcompact, hCconnected, hCinside⟩

namespace FinitePolyhedralNeighborhood

variable {J : JordanCircle} {C U : Set Plane}

/-- The open support component containing a connected compact core. -/
noncomputable def coreComponent (N : FinitePolyhedralNeighborhood C U)
    (hC : IsConnected C) : Set Plane :=
  connectedComponentIn (interior N.mesh.toPlaneComplex.support) hC.1.some

theorem core_subset_coreComponent
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    C ⊆ N.coreComponent hC := by
  intro x hx
  exact hC.isPreconnected.subset_connectedComponentIn hC.1.some_mem
    N.coversInterior hx

theorem isOpen_coreComponent
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    IsOpen (N.coreComponent hC) :=
  isOpen_interior.connectedComponentIn

theorem isConnected_coreComponent
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    IsConnected (N.coreComponent hC) := by
  rw [coreComponent, isConnected_connectedComponentIn_iff]
  exact N.coversInterior hC.1.some_mem

theorem coreComponent_subset_ambient
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    N.coreComponent hC ⊆ U :=
  (connectedComponentIn_subset _ _).trans (interior_subset.trans N.contained)

/-- The regular-closed finite polyhedral core belonging to the component
which contains `C`. -/
noncomputable def connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) : Set Plane :=
  closure (N.coreComponent hC)

theorem core_subset_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    C ⊆ N.connectedFrameCore hC :=
  (N.core_subset_coreComponent hC).trans subset_closure

theorem connectedFrameCore_subset_support
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    N.connectedFrameCore hC ⊆ N.mesh.toPlaneComplex.support := by
  apply closure_minimal
  · exact (connectedComponentIn_subset _ _).trans interior_subset
  · exact N.mesh.toPlaneComplex.isCompact_support.isClosed

theorem connectedFrameCore_subset_ambient
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    N.connectedFrameCore hC ⊆ U :=
  (N.connectedFrameCore_subset_support hC).trans N.contained

theorem isCompact_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    IsCompact (N.connectedFrameCore hC) :=
  N.mesh.toPlaneComplex.isCompact_support.of_isClosed_subset
    isClosed_closure (N.connectedFrameCore_subset_support hC)

theorem isConnected_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    IsConnected (N.connectedFrameCore hC) :=
  (N.isConnected_coreComponent hC).closure

theorem coreComponent_subset_interior_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    N.coreComponent hC ⊆ interior (N.connectedFrameCore hC) := by
  intro x hx
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset
    (N.isOpen_coreComponent hC |>.mem_nhds hx) subset_closure

theorem core_subset_interior_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    C ⊆ interior (N.connectedFrameCore hC) :=
  (N.core_subset_coreComponent hC).trans
    (N.coreComponent_subset_interior_connectedFrameCore hC)

theorem closure_interior_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    closure (interior (N.connectedFrameCore hC)) =
      N.connectedFrameCore hC := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · change closure (N.coreComponent hC) ⊆ _
    exact closure_mono
      (N.coreComponent_subset_interior_connectedFrameCore hC)

/-- Retain exactly the triangles whose open two-cells meet the selected
support component. -/
noncomputable def connectedComponentMesh
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    TriangleMesh := by
  classical
  exact N.mesh.restrictTriangles fun t =>
    (interior (N.mesh.triangleCarrier t) ∩ N.coreComponent hC).Nonempty

@[simp] theorem mem_connectedComponentMesh_triangles_iff
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C)
    {t : Finset (N.connectedComponentMesh hC).Vertex} :
    t ∈ (N.connectedComponentMesh hC).triangles ↔
      t ∈ N.mesh.triangles ∧
        (interior (N.mesh.triangleCarrier t) ∩
          N.coreComponent hC).Nonempty := by
  classical
  change t ∈ N.mesh.triangles.filter (fun t =>
      (interior (N.mesh.triangleCarrier t) ∩
        N.coreComponent hC).Nonempty) ↔ _
  exact Finset.mem_filter

theorem interior_triangleCarrier_subset_coreComponent_of_mem
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C)
    {t : Finset (N.connectedComponentMesh hC).Vertex}
    (ht : t ∈ (N.connectedComponentMesh hC).triangles) :
    interior ((N.connectedComponentMesh hC).triangleCarrier t) ⊆
      N.coreComponent hC := by
  classical
  have htN : t ∈ N.mesh.triangles :=
    (N.mem_connectedComponentMesh_triangles_iff hC).mp ht |>.1
  obtain ⟨y, hytri, hycomponent⟩ :=
    (N.mem_connectedComponentMesh_triangles_iff hC).mp ht |>.2
  have hconvex : Convex ℝ (interior (N.mesh.triangleCarrier t)) :=
    (convex_convexHull ℝ _).interior
  have hsubSupport : interior (N.mesh.triangleCarrier t) ⊆
      interior N.mesh.toPlaneComplex.support := by
    apply interior_mono
    rw [N.mesh.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset t
      (Set.subset_iUnion_of_subset htN (by rfl))
  have hsubAtY : interior (N.mesh.triangleCarrier t) ⊆
      connectedComponentIn (interior N.mesh.toPlaneComplex.support) y :=
    hconvex.isPreconnected.subset_connectedComponentIn hytri hsubSupport
  change interior (N.mesh.triangleCarrier t) ⊆
    connectedComponentIn (interior N.mesh.toPlaneComplex.support) hC.1.some
  rw [connectedComponentIn_eq hycomponent]
  exact hsubAtY

theorem coreComponent_subset_connectedComponentMesh_support
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    N.coreComponent hC ⊆
      (N.connectedComponentMesh hC).toPlaneComplex.support := by
  classical
  intro x hx
  have hxSupport : x ∈ N.mesh.toPlaneComplex.support :=
    interior_subset ((connectedComponentIn_subset _ _) hx)
  rw [N.mesh.toPlaneComplex_support] at hxSupport
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxSupport
  let T : N.mesh.Triangle := ⟨t, ht⟩
  have hxClosure : x ∈ closure (interior (N.mesh.triangleCarrier t)) := by
    rw [N.mesh.closure_interior_triangleCarrier T]
    exact hxt
  have hmeet :
      (interior (N.mesh.triangleCarrier t) ∩ N.coreComponent hC).Nonempty := by
    obtain ⟨y, hycomponent, hytri⟩ :=
      (_root_.mem_closure_iff.1 hxClosure) (N.coreComponent hC)
        (N.isOpen_coreComponent hC) hx
    exact ⟨y, hytri, hycomponent⟩
  have htSelected : t ∈ (N.connectedComponentMesh hC).triangles :=
    (N.mem_connectedComponentMesh_triangles_iff hC).mpr ⟨ht, hmeet⟩
  rw [(N.connectedComponentMesh hC).toPlaneComplex_support]
  exact Set.mem_iUnion₂.mpr ⟨t, htSelected, hxt⟩

theorem connectedComponentMesh_support_eq_connectedFrameCore
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    (N.connectedComponentMesh hC).toPlaneComplex.support =
      N.connectedFrameCore hC := by
  classical
  apply Set.Subset.antisymm
  · rw [(N.connectedComponentMesh hC).toPlaneComplex_support]
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have hinteriorSub :=
      N.interior_triangleCarrier_subset_coreComponent_of_mem hC ht
    have hxClosure : x ∈
        closure (interior ((N.connectedComponentMesh hC).triangleCarrier t)) := by
      let T : (N.connectedComponentMesh hC).Triangle := ⟨t, ht⟩
      rw [(N.connectedComponentMesh hC).closure_interior_triangleCarrier T]
      exact hxt
    exact closure_mono hinteriorSub hxClosure
  · apply closure_minimal
      (N.coreComponent_subset_connectedComponentMesh_support hC)
    exact (N.connectedComponentMesh hC).toPlaneComplex.isCompact_support.isClosed

theorem connectedComponentMesh_support_subset_mesh_support
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    (N.connectedComponentMesh hC).toPlaneComplex.support ⊆
      N.mesh.toPlaneComplex.support := by
  classical
  rw [(N.connectedComponentMesh hC).toPlaneComplex_support,
    N.mesh.toPlaneComplex_support]
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr
    ⟨t, (N.mem_connectedComponentMesh_triangles_iff hC).mp ht |>.1, hxt⟩

theorem interior_connectedComponentMesh_support_eq_coreComponent
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    interior (N.connectedComponentMesh hC).toPlaneComplex.support =
      N.coreComponent hC := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hxOriginal : x ∈ interior N.mesh.toPlaneComplex.support :=
      interior_mono
        (N.connectedComponentMesh_support_subset_mesh_support hC) hx
    have hxSupport : x ∈
        (N.connectedComponentMesh hC).toPlaneComplex.support :=
      interior_subset hx
    rw [(N.connectedComponentMesh hC).toPlaneComplex_support] at hxSupport
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxSupport
    let T : (N.connectedComponentMesh hC).Triangle := ⟨t, ht⟩
    obtain ⟨y, hyInterior⟩ :=
      (N.connectedComponentMesh hC).interior_triangleCarrier_nonempty T
    have hyComponent : y ∈ N.coreComponent hC :=
      N.interior_triangleCarrier_subset_coreComponent_of_mem hC ht hyInterior
    have hsegmentSubset : segment ℝ x y ⊆
        interior N.mesh.toPlaneComplex.support := by
      intro z hz
      rcases eq_or_ne z x with rfl | hzx
      · exact hxOriginal
      rcases eq_or_ne z y with rfl | hzy
      · exact (connectedComponentIn_subset _ _) hyComponent
      have hzOpen : z ∈ openSegment ℝ x y :=
        mem_openSegment_of_ne_left_right hzx.symm hzy.symm hz
      have hzTriangle : z ∈
          interior ((N.connectedComponentMesh hC).triangleCarrier t) :=
        (convex_convexHull ℝ _).openSegment_self_interior_subset_interior
          hxt hyInterior hzOpen
      exact (connectedComponentIn_subset _ _)
        (N.interior_triangleCarrier_subset_coreComponent_of_mem
          hC ht hzTriangle)
    have hsegToY : segment ℝ x y ⊆
        connectedComponentIn (interior N.mesh.toPlaneComplex.support) y :=
      (convex_segment x y).isPreconnected.subset_connectedComponentIn
        (right_mem_segment ℝ x y) hsegmentSubset
    change x ∈ connectedComponentIn
      (interior N.mesh.toPlaneComplex.support) hC.1.some
    rw [connectedComponentIn_eq hyComponent]
    exact hsegToY (left_mem_segment ℝ x y)
  · have h := N.coreComponent_subset_interior_connectedFrameCore hC
    rw [← N.connectedComponentMesh_support_eq_connectedFrameCore hC] at h
    exact h

theorem closure_interior_connectedComponentMesh_support
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    closure (interior
      (N.connectedComponentMesh hC).toPlaneComplex.support) =
      (N.connectedComponentMesh hC).toPlaneComplex.support := by
  rw [N.interior_connectedComponentMesh_support_eq_coreComponent hC,
    N.connectedComponentMesh_support_eq_connectedFrameCore hC]
  rfl

theorem connectedComponentMesh_boundaryCarrier_eq_frontier
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    (N.connectedComponentMesh hC).boundaryCarrier =
      frontier (N.connectedComponentMesh hC).toPlaneComplex.support := by
  let M := N.connectedComponentMesh hC
  apply Set.Subset.antisymm M.boundaryCarrier_subset_frontier
  have hdense : frontier M.toPlaneComplex.support ⊆
      closure (frontier M.toPlaneComplex.support \ Set.range M.position) :=
    frontier_subset_closure_sdiff_finite_of_regularClosed
      M.toPlaneComplex.isCompact_support.isClosed
      (N.closure_interior_connectedComponentMesh_support hC)
      (Set.finite_range M.position)
  have hnonvertex : frontier M.toPlaneComplex.support \ Set.range M.position ⊆
      M.boundaryCarrier := by
    rintro x ⟨hxFrontier, hxNotVertex⟩
    have hxv : ∀ v : M.Vertex, x ≠ M.position v := by
      intro v hx
      exact hxNotVertex ⟨v, hx.symm⟩
    obtain ⟨e, he, hxe⟩ :=
      (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hxv).mp hxFrontier
    rw [TriangleMesh.boundaryCarrier]
    exact Set.mem_iUnion₂.mpr
      ⟨e, M.mem_allBoundaryEdges_iff.mpr he, hxe⟩
  exact hdense.trans <| by
    have h := closure_mono hnonvertex
    rwa [M.isCompact_boundaryCarrier.isClosed.closure_eq] at h

theorem connectedComponentMesh_triangles_nonempty
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    (N.connectedComponentMesh hC).triangles.Nonempty := by
  have hxComponent : hC.1.some ∈ N.coreComponent hC :=
    N.core_subset_coreComponent hC hC.1.some_mem
  have hxSupport :=
    N.coreComponent_subset_connectedComponentMesh_support hC hxComponent
  rw [(N.connectedComponentMesh hC).toPlaneComplex_support] at hxSupport
  obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.mp hxSupport
  exact ⟨t, ht⟩

/-- The exterior-facing boundary cycle of the selected component.  Besides
containing the regular-closed frame, its open bounded side contains the whole
selected support component. -/
theorem exists_outerBoundaryPolygonalCircle_of_connected
    (N : FinitePolyhedralNeighborhood C U) (hC : IsConnected C) :
    ∃ P : PolygonalCircle,
      P.carrier ⊆ frontier (N.connectedFrameCore hC) ∧
        P.carrier ⊆ U ∧
        N.coreComponent hC ⊆ P.interiorRegion ∧
        N.connectedFrameCore hC ⊆ P.closedRegion := by
  let M := N.connectedComponentMesh hC
  obtain ⟨P, hPboundary, x, hxInside, hxMeshInterior⟩ :=
    Schoenflies.TriangleMesh.exists_boundaryPolygonalCircle_meeting_interiorRegion
      M (N.connectedComponentMesh_triangles_nonempty hC)
  have hPfrontier : P.carrier ⊆ frontier (N.connectedFrameCore hC) := by
    rw [← N.connectedComponentMesh_support_eq_connectedFrameCore hC,
      ← N.connectedComponentMesh_boundaryCarrier_eq_frontier hC]
    exact hPboundary
  have hPambient : P.carrier ⊆ U :=
    hPfrontier.trans
      ((N.isCompact_connectedFrameCore hC).isClosed.frontier_subset.trans
        (N.connectedFrameCore_subset_ambient hC))
  have hPdisjoint : Disjoint P.carrier (N.coreComponent hC) := by
    rw [← N.interior_connectedComponentMesh_support_eq_coreComponent hC]
    exact Set.disjoint_of_subset_left hPboundary <|
      Set.disjoint_of_subset_left
        (N.connectedComponentMesh hC).boundaryCarrier_subset_frontier
          disjoint_interior_frontier.symm
  have hxComponent : x ∈ N.coreComponent hC := by
    rw [← N.interior_connectedComponentMesh_support_eq_coreComponent hC]
    exact hxMeshInterior
  have hcomponentCompl : N.coreComponent hC ⊆ P.carrierᶜ := by
    intro y hy hyCarrier
    exact Set.disjoint_left.mp hPdisjoint hyCarrier hy
  have hregions : N.coreComponent hC ⊆
      P.interiorRegion ∪ P.exteriorRegion := by
    rw [P.interior_union_exterior]
    exact hcomponentCompl
  have hcomponentInside : N.coreComponent hC ⊆ P.interiorRegion :=
    (N.isConnected_coreComponent hC).isPreconnected.subset_left_of_subset_union
      P.isOpen_interiorRegion P.isOpen_exteriorRegion
      P.disjoint_interior_exterior hregions ⟨x, hxComponent, hxInside⟩
  have hframeClosed : N.connectedFrameCore hC ⊆ P.closedRegion := by
    change closure (N.coreComponent hC) ⊆ closure P.interiorRegion
    exact closure_mono hcomponentInside
  exact ⟨P, hPfrontier, hPambient, hcomponentInside, hframeClosed⟩

end FinitePolyhedralNeighborhood

/-- Every compact connected subset of the bounded Jordan component is
strictly contained in a polygonal disk which remains in that component.  The
polygonal boundary is disjoint from the prescribed core. -/
theorem exists_polygonalDiskNeighborhood_with_boundary_avoidance
    (J : JordanCircle) {C : Set Plane}
    (hCcompact : IsCompact C) (hCconnected : IsConnected C)
    (hCinside : C ⊆ J.inside) :
    ∃ P : PolygonalCircle,
      C ⊆ P.interiorRegion ∧ P.closedRegion ⊆ J.inside ∧
        Disjoint P.carrier C := by
  let N : FinitePolyhedralNeighborhood C J.inside :=
    Classical.choice
      (JordanCircle.exists_finitePolyhedralNeighborhood
        hCcompact J.inside_isOpen hCinside)
  obtain ⟨P, _hfrontier, hPinside, hcomponentInside, _hframe⟩ :=
    N.exists_outerBoundaryPolygonalCircle_of_connected hCconnected
  have hCInterior : C ⊆ P.interiorRegion :=
    (N.core_subset_coreComponent hCconnected).trans hcomponentInside
  have hcarrier : P.toJordanCircle.carrier ⊆ J.inside ∪ J.carrier := by
    rw [P.carrier_toJordanCircle]
    exact hPinside.trans Set.subset_union_left
  have hinterior : P.interiorRegion ⊆ J.inside := by
    rw [← P.inside_toJordanCircle]
    exact J.inside_subset_inside_of_carrier_subset P.toJordanCircle hcarrier
  have hclosed : P.closedRegion ⊆ J.inside := by
    rw [P.closedRegion_eq_union]
    exact Set.union_subset hinterior hPinside
  have hdisjoint : Disjoint P.carrier C := by
    rw [Set.disjoint_left]
    intro x hxCarrier hxC
    have hxCompl : x ∈ P.carrierᶜ := by
      rw [← P.interior_union_exterior]
      exact Or.inl (hCInterior hxC)
    exact hxCompl hxCarrier
  exact ⟨P, hCInterior, hclosed, hdisjoint⟩

/-- Boundary-avoidance-free form of
`exists_polygonalDiskNeighborhood_with_boundary_avoidance`. -/
theorem exists_polygonalDiskNeighborhood
    (J : JordanCircle) {C : Set Plane}
    (hCcompact : IsCompact C) (hCconnected : IsConnected C)
    (hCinside : C ⊆ J.inside) :
    ∃ P : PolygonalCircle,
      C ⊆ P.interiorRegion ∧ P.closedRegion ⊆ J.inside := by
  obtain ⟨P, hC, hP, _⟩ :=
    J.exists_polygonalDiskNeighborhood_with_boundary_avoidance
      hCcompact hCconnected hCinside
  exact ⟨P, hC, hP⟩

end JordanCircle
end Schoenflies
