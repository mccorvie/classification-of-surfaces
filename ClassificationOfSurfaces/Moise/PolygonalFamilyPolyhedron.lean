/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PolygonalPolyhedron

/-!
# Finite unions of polygonal disks

The cellwise intrinsic approximation produces finitely many polygonal closed disks whose
interiors are compatible.  Independently chosen disk triangulations need not agree on their
common boundary segments.  This file instead cuts one enclosing triangle by every edge line in
the family and retains precisely the chambers lying inside at least one polygon.  The resulting
single triangle mesh has support equal to the union.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalFamily

variable {ι : Type*} [Fintype ι] (J : ι → PolygonalCircle)

/-- The union of the finitely many closed polygonal disks. -/
def closedRegion : Set Plane :=
  ⋃ i, (J i).closedRegion

theorem isCompact_closedRegion : IsCompact (closedRegion J) :=
  isCompact_iUnion fun i ↦ (J i).isCompact_closedRegion

/-- A positive radius of a ball containing every disk in the family. -/
noncomputable def enclosingRadius : ℝ :=
  max ((isCompact_closedRegion J).isBounded.subset_closedBall (0 : Plane)).choose 1

theorem enclosingRadius_pos : 0 < enclosingRadius J :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem closedRegion_subset_enclosingBall :
    closedRegion J ⊆ Metric.closedBall (0 : Plane) (enclosingRadius J) := by
  intro x hx
  have h := ((isCompact_closedRegion J).isBounded.subset_closedBall
    (0 : Plane)).choose_spec hx
  exact Metric.closedBall_subset_closedBall (le_max_left _ _) h

/-- The common enclosing triangle. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (PolygonalCircle.enclosingTriangleVertices (enclosingRadius J))
    (PolygonalCircle.enclosingTriangleVertices_affineIndependent (enclosingRadius_pos J))

theorem closedRegion_subset_enclosingMesh_support :
    closedRegion J ⊆ (enclosingMesh J).toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact (closedRegion_subset_enclosingBall J).trans
    (PolygonalCircle.closedBall_subset_enclosingTriangle (enclosingRadius_pos J))

/-- Every supporting line of every polygon in the family. -/
noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset ι).toList.flatMap fun i ↦ (J i).edgeLines

theorem edgeLine_mem_edgeLines (i : ι) (k : ZMod (J i).n) :
    (J i).edgeLine k ∈ edgeLines J := by
  rw [edgeLines, List.mem_flatMap]
  exact ⟨i, by simp, (J i).edgeLine_mem_edgeLines k⟩

/-- The common supporting-line arrangement. -/
noncomputable def arrangementMesh : TriangleMesh :=
  (enclosingMesh J).refineByLines (edgeLines J)

theorem arrangementMesh_support :
    (arrangementMesh J).toPlaneComplex.support =
      (enclosingMesh J).toPlaneComplex.support :=
  (enclosingMesh J).refineByLines_support (edgeLines J)

theorem closedRegion_subset_arrangementMesh_support :
    closedRegion J ⊆ (arrangementMesh J).toPlaneComplex.support := by
  rw [arrangementMesh_support]
  exact closedRegion_subset_enclosingMesh_support J

theorem arrangementMesh_isMonochromatic (i : ι) (k : ZMod (J i).n) :
    (arrangementMesh J).IsMonochromatic ((J i).edgeLine k) :=
  (enclosingMesh J).refineByLines_isMonochromatic_of_mem
    (edgeLines J) (edgeLine_mem_edgeLines J i k)

/-- Carrier of one maximal chamber of the common arrangement. -/
def arrangementTriangleCarrier (t : Finset (arrangementMesh J).Vertex) : Set Plane :=
  convexHull ℝ ((arrangementMesh J).position '' (t : Set _))

theorem convex_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    Convex ℝ (arrangementTriangleCarrier J t) :=
  convex_convexHull ℝ _

theorem isClosed_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    IsClosed (arrangementTriangleCarrier J t) :=
  (t.finite_toSet.image (arrangementMesh J).position).isClosed_convexHull ℝ

theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    (interior (arrangementTriangleCarrier J t)).Nonempty := by
  apply (convex_arrangementTriangleCarrier J t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t ↦ (arrangementMesh J).position v) =
      (arrangementMesh J).position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  apply ((arrangementMesh J).affineIndependent_triangle t ht).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, (arrangementMesh J).card_triangle t ht]
  simp [Plane]

theorem closure_interior_arrangementTriangleCarrier
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    closure (interior (arrangementTriangleCarrier J t)) =
      arrangementTriangleCarrier J t := by
  calc
    closure (interior (arrangementTriangleCarrier J t)) =
        closure (arrangementTriangleCarrier J t) :=
      (convex_arrangementTriangleCarrier J t).closure_interior_eq_closure_of_nonempty_interior
        (arrangementTriangleCarrier_interior_nonempty J ht)
    _ = arrangementTriangleCarrier J t :=
      (isClosed_arrangementTriangleCarrier J t).closure_eq

/-- Every open arrangement chamber misses every polygon boundary in the family. -/
theorem arrangementTriangle_interior_disjoint_carrier
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    Disjoint (interior (arrangementTriangleCarrier J t)) (J i).carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : (J i).edgeLine k x = 0 :=
    (J i).edgeLine_eq_zero_of_mem_edgeSegment k hxk
  rcases arrangementMesh_isMonochromatic J i k t ht with hpos | hneg
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | 0 ≤ (J i).edgeLine k y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonneg k] at hxstrict
    change 0 < (J i).edgeLine k x at hxstrict
    linarith
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | (J i).edgeLine k y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonpos k] at hxstrict
    change (J i).edgeLine k x < 0 at hxstrict
    linarith

theorem arrangementTriangle_interior_side
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion ∨
      interior (arrangementTriangleCarrier J t) ⊆ (J i).exteriorRegion := by
  let s := interior (arrangementTriangleCarrier J t)
  have hsconn : IsPreconnected s :=
    (convex_arrangementTriangleCarrier J t).interior.isPreconnected
  have hsoff : s ⊆ (J i).carrierᶜ := by
    intro x hx
    exact fun hxcarrier ↦ Set.disjoint_left.mp
      (arrangementTriangle_interior_disjoint_carrier J i ht) hx hxcarrier
  have hsunion : s ⊆ (J i).interiorRegion ∪ (J i).exteriorRegion := by
    rw [(J i).interior_union_exterior]
    exact hsoff
  obtain ⟨x, hx⟩ := arrangementTriangleCarrier_interior_nonempty J ht
  rcases hsunion hx with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxout⟩

/-- A chamber is retained when it lies on the bounded side of at least one polygon. -/
def IsInteriorArrangementTriangle
    (t : Finset (arrangementMesh J).Vertex) : Prop :=
  ∃ i, interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion

/-- The common finite mesh of the union of all closed regions. -/
noncomputable def closedRegionMesh : TriangleMesh := by
  classical
  exact (arrangementMesh J).restrictTriangles (IsInteriorArrangementTriangle J)

theorem closedRegionMesh_triangle_mem
    {t : Finset (closedRegionMesh J).Vertex} :
    t ∈ (closedRegionMesh J).triangles ↔
      t ∈ (arrangementMesh J).triangles ∧ IsInteriorArrangementTriangle J t := by
  classical
  exact (arrangementMesh J).mem_restrictTriangles_triangles
    (IsInteriorArrangementTriangle J)

theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles)
    (hinside : IsInteriorArrangementTriangle J t) :
    arrangementTriangleCarrier J t ⊆ closedRegion J := by
  obtain ⟨i, hi⟩ := hinside
  rw [← closure_interior_arrangementTriangleCarrier J ht]
  exact (closure_mono hi).trans fun x hx ↦ Set.mem_iUnion.mpr
    ⟨i, by simpa only [PolygonalCircle.closedRegion] using hx⟩

theorem closedRegionMesh_support_subset :
    (closedRegionMesh J).toPlaneComplex.support ⊆ closedRegion J := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := (closedRegionMesh_triangle_mem J).mp ht
  exact arrangementTriangleCarrier_subset_closedRegion J htarr htinside hxt

theorem interiorRegion_subset_closedRegionMesh_support (i : ι) :
    (J i).interiorRegion ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ closedRegion J := Set.mem_iUnion.mpr
    ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hxinside⟩
  have hxsupport := closedRegion_subset_arrangementMesh_support J hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (arrangementTriangleCarrier J t)) := by
    rw [closure_interior_arrangementTriangleCarrier J ht]
    exact hxt
  have hxclosureInter : x ∈ closure
      ((J i).interiorRegion ∩ interior (arrangementTriangleCarrier J t)) :=
    (J i).isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  obtain ⟨y, hyinside, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have htinside : interior (arrangementTriangleCarrier J t) ⊆
      (J i).interiorRegion := by
    rcases arrangementTriangle_interior_side J i ht with hin | hout
    · exact hin
    · exact False.elim <| Set.disjoint_left.mp (J i).disjoint_interior_exterior
        hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, (closedRegionMesh_triangle_mem J).mpr
    ⟨ht, ⟨i, htinside⟩⟩, hxt⟩

theorem closedRegion_subset_closedRegionMesh_support :
    closedRegion J ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rw [PolygonalCircle.closedRegion] at hxi
  exact closure_minimal (interiorRegion_subset_closedRegionMesh_support J i)
    (closedRegionMesh J).toPlaneComplex.isCompact_support.isClosed hxi

/-- Exact support of the common family mesh. -/
theorem closedRegionMesh_support :
    (closedRegionMesh J).toPlaneComplex.support = closedRegion J :=
  Set.Subset.antisymm (closedRegionMesh_support_subset J)
    (closedRegion_subset_closedRegionMesh_support J)

/-- A finite union of polygonal closed disks is a finite pure plane polyhedron. -/
theorem closedRegion_is_polyhedron :
    ∃ K : PlaneComplex, K.support = closedRegion J ∧ K.IsPure2 :=
  ⟨(closedRegionMesh J).toPlaneComplex, closedRegionMesh_support J,
    (closedRegionMesh J).toPlaneComplex_isPure2⟩

end PolygonalFamily

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
