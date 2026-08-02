import Schoenflies.PolygonalAnnularCellDecomposition
import Schoenflies.TopologicalDiskAttachment

/-!
# Annular separator cells as relative disk attachments

One of the two separator disks contains the old inner polygonal disk.  The
other separator disk is the collar cell to be attached.  This file presents
that collar cell with the inner boundary arc as its shared arc, so it can be
consumed by `PolygonalDiskAttachment.homeomorph` without changing the map on
the old disk.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.AnnularCellDecomposition

variable {P Q : PolygonalCircle}
  (D : AnnularCellDecomposition P Q)

private abbrev A := D.first
private abbrev B := D.second

/-- The rest of a separator-cell boundary, traversed from the second inner
endpoint back to the first inner endpoint. -/
def exposedPath (outer : Path D.second.outerPoint D.first.outerPoint) :
    Path D.second.innerPoint D.first.innerPoint :=
  D.second.path.symm.trans (outer.trans D.first.path)

theorem range_exposedPath
    (outer : Path D.second.outerPoint D.first.outerPoint) :
    range (D.exposedPath outer) =
      range D.second.path ∪ (range outer ∪ range D.first.path) := by
  simp only [exposedPath, Path.trans_range, Path.symm_range]

private theorem outer_inter_firstPath
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (houter : range outer ⊆ Q.carrier) :
    range outer ∩ range D.first.path = {D.first.outerPoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxOuter, hxFirst⟩
    have hx : x ∈ range D.first.path ∩ Q.carrier :=
      ⟨hxFirst, houter hxOuter⟩
    rw [D.first.range_inter_outer] at hx
    exact hx
  · intro x hx
    have hxEq := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range outer,
      Path.source_mem_range D.first.path⟩

private theorem secondPath_inter_outer
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (houter : range outer ⊆ Q.carrier) :
    range D.second.path ∩ range outer = {D.second.outerPoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSecond, hxOuter⟩
    have hx : x ∈ range D.second.path ∩ Q.carrier :=
      ⟨hxSecond, houter hxOuter⟩
    rw [D.second.range_inter_outer] at hx
    exact hx
  · intro x hx
    have hxEq := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.source_mem_range D.second.path,
      Path.source_mem_range outer⟩

theorem exposedPath_injective
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (houterInj : Injective outer)
    (houter : range outer ⊆ Q.carrier) :
    Injective (D.exposedPath outer) := by
  have hOuterFirst : range outer ∩ range D.first.path =
      {D.first.outerPoint} := D.outer_inter_firstPath outer houter
  have hTail : Injective (outer.trans D.first.path) :=
    Path.trans_injective_of_range_inter outer D.first.path
      houterInj D.first.path_injective hOuterFirst
  have hSecondTail :
      range D.second.path ∩ range (outer.trans D.first.path) =
        {D.second.outerPoint} := by
    rw [Path.trans_range, inter_union_distrib_left,
      D.secondPath_inter_outer outer houter,
      Set.disjoint_iff_inter_eq_empty.mp D.disjoint.symm, union_empty]
  exact Path.trans_injective_of_range_inter D.second.path.symm
    (outer.trans D.first.path)
    (D.second.path_injective.comp unitInterval.symm_bijective.injective)
    hTail (by simpa only [Path.symm_range] using hSecondTail)

private theorem innerFirst_inter_secondPath :
    range D.separator.innerSplit.first ∩ range D.second.path =
      {D.second.innerPoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxInner, hxSecond⟩
    have hx : x ∈ range D.second.path ∩ P.carrier :=
      ⟨hxSecond, D.separator.innerFirst_range_subset hxInner⟩
    rw [D.second.range_inter_inner] at hx
    exact hx
  · intro x hx
    have hxEq := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range D.separator.innerSplit.first,
      Path.target_mem_range D.second.path⟩

private theorem innerFirst_inter_firstPath :
    range D.separator.innerSplit.first ∩ range D.first.path =
      {D.first.innerPoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxInner, hxFirst⟩
    have hx : x ∈ range D.first.path ∩ P.carrier :=
      ⟨hxFirst, D.separator.innerFirst_range_subset hxInner⟩
    rw [D.first.range_inter_inner] at hx
    exact hx
  · intro x hx
    have hxEq := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.source_mem_range D.separator.innerSplit.first,
      Path.target_mem_range D.first.path⟩

private theorem innerFirst_disjoint_outer
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (houter : range outer ⊆ Q.carrier) :
    Disjoint (range D.separator.innerSplit.first) (range outer) :=
  (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
      D.nested).mono
    D.separator.innerFirst_range_subset houter

theorem innerFirst_inter_exposedPath
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (houter : range outer ⊆ Q.carrier) :
    range D.separator.innerSplit.first ∩ range (D.exposedPath outer) =
      {D.first.innerPoint, D.second.innerPoint} := by
  rw [D.range_exposedPath outer, inter_union_distrib_left,
    inter_union_distrib_left, D.innerFirst_inter_secondPath,
    Set.disjoint_iff_inter_eq_empty.mp
      (D.innerFirst_disjoint_outer outer houter),
    D.innerFirst_inter_firstPath]
  ext x
  simp only [mem_union, mem_insert_iff, mem_singleton_iff,
    mem_empty_iff_false, false_or]
  tauto

private theorem cell_carrier_eq_innerFirst_union_exposedPath
    (outer : Path D.second.outerPoint D.first.outerPoint)
    (hcell : D.cell₀.carrier =
      range D.separator.commonBridge ∪ range outer) :
    D.cell₀.carrier =
      range D.separator.innerSplit.first ∪ range (D.exposedPath outer) := by
  rw [hcell, D.range_exposedPath outer,
    PolygonalCircle.AnnularCrosscut.SeparatorPair.commonBridge,
    PolygonalCircle.AnnularCrosscut.range_bridgePath]
  ext x
  simp only [mem_union]
  tauto

private theorem cell₀_carrier_eq_innerFirst_union_exposedPath :
    D.cell₀.carrier = range D.separator.innerSplit.first ∪
      range (D.exposedPath D.separator.outerArc₀) := by
  apply D.cell_carrier_eq_innerFirst_union_exposedPath
  exact D.cell₀_carrier.trans
    (D.separator.carrier_circle₀ D.nested D.disjoint)

private theorem cell₁_carrier_eq_innerFirst_union_exposedPath :
    D.cell₁.carrier = range D.separator.innerSplit.first ∪
      range (D.exposedPath D.separator.outerArc₁) := by
  have hcarrier : D.cell₁.carrier =
      range D.separator.commonBridge ∪ range D.separator.outerArc₁ :=
    D.cell₁_carrier.trans
      (D.separator.carrier_circle₁ D.nested D.disjoint)
  rw [hcarrier, D.range_exposedPath D.separator.outerArc₁,
    PolygonalCircle.AnnularCrosscut.SeparatorPair.commonBridge,
    PolygonalCircle.AnnularCrosscut.range_bridgePath]
  ext x
  simp only [mem_union]
  tauto

theorem commonBridge_inter_innerClosedRegion :
    range D.separator.commonBridge ∩ P.closedRegion =
      range D.separator.innerSplit.first := by
  rw [PolygonalCircle.AnnularCrosscut.SeparatorPair.commonBridge,
    PolygonalCircle.AnnularCrosscut.range_bridgePath]
  apply Set.Subset.antisymm
  · rintro x ⟨(hxFirst | hxInner) | hxSecond, hxP⟩
    · rw [P.closedRegion_eq_union] at hxP
      rcases hxP with hxInterior | hxCarrier
      · exact False.elim ((D.first.range_subset_closedShell hxFirst).2 hxInterior)
      · have hx : x ∈ range D.first.path ∩ P.carrier :=
          ⟨hxFirst, hxCarrier⟩
        rw [D.first.range_inter_inner] at hx
        rw [Set.mem_singleton_iff.mp hx]
        exact Path.source_mem_range D.separator.innerSplit.first
    · exact hxInner
    · rw [P.closedRegion_eq_union] at hxP
      rcases hxP with hxInterior | hxCarrier
      · exact False.elim ((D.second.range_subset_closedShell hxSecond).2 hxInterior)
      · have hx : x ∈ range D.second.path ∩ P.carrier :=
          ⟨hxSecond, hxCarrier⟩
        rw [D.second.range_inter_inner] at hx
        rw [Set.mem_singleton_iff.mp hx]
        exact Path.target_mem_range D.separator.innerSplit.first
  · intro x hxInner
    constructor
    · exact Or.inl (Or.inr hxInner)
    · rw [P.closedRegion_eq_union]
      exact Or.inr (D.separator.innerFirst_range_subset hxInner)

private theorem innerClosedRegion_subset_cell₀
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₀ D.nested D.disjoint).inside) :
    P.closedRegion ⊆ D.cell₀.closedRegion := by
  rw [D.cell₀_closedRegion]
  intro x hx
  rw [P.closedRegion_eq_union] at hx
  rw [(D.separator.circle₀ D.nested D.disjoint).closure_inside]
  rcases hx with hxInterior | hxCarrier
  · exact Or.inl (hinside hxInterior)
  · by_cases hxCircle : x ∈
        (D.separator.circle₀ D.nested D.disjoint).carrier
    · exact Or.inr hxCircle
    · exact Or.inl <|
        innerCarrier_sdiff_subset_inside_of_interior_subset_inside
          hinside ⟨hxCarrier, hxCircle⟩

private theorem innerClosedRegion_subset_cell₁
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₁ D.nested D.disjoint).inside) :
    P.closedRegion ⊆ D.cell₁.closedRegion := by
  rw [D.cell₁_closedRegion]
  intro x hx
  rw [P.closedRegion_eq_union] at hx
  rw [(D.separator.circle₁ D.nested D.disjoint).closure_inside]
  rcases hx with hxInterior | hxCarrier
  · exact Or.inl (hinside hxInterior)
  · by_cases hxCircle : x ∈
        (D.separator.circle₁ D.nested D.disjoint).carrier
    · exact Or.inr hxCircle
    · exact Or.inl <|
        innerCarrier_sdiff_subset_inside_of_interior_subset_inside
          hinside ⟨hxCarrier, hxCircle⟩

theorem innerClosedRegion_inter_cell₁
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₀ D.nested D.disjoint).inside) :
    P.closedRegion ∩ D.cell₁.closedRegion =
      range D.separator.innerSplit.first := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxBoth : x ∈ D.cell₀.closedRegion ∩ D.cell₁.closedRegion :=
      ⟨D.innerClosedRegion_subset_cell₀ hinside hx.1, hx.2⟩
    have hxBridge : x ∈ range D.separator.commonBridge := by
      rw [← D.separator.closure_separatorInteriors_inter
        D.nested D.disjoint]
      rwa [← D.cell₀_closedRegion, ← D.cell₁_closedRegion]
    rw [← D.commonBridge_inter_innerClosedRegion]
    exact ⟨hxBridge, hx.1⟩
  · intro x hxInner
    have hxBridge : x ∈ range D.separator.commonBridge := by
      rw [PolygonalCircle.AnnularCrosscut.SeparatorPair.commonBridge,
        PolygonalCircle.AnnularCrosscut.range_bridgePath]
      exact Or.inl (Or.inr hxInner)
    constructor
    · rw [P.closedRegion_eq_union]
      exact Or.inr (D.separator.innerFirst_range_subset hxInner)
    · rw [D.cell₁.closedRegion_eq_union]
      right
      rw [D.cell₁_carrier,
        D.separator.carrier_circle₁ D.nested D.disjoint]
      exact Or.inl hxBridge

theorem innerClosedRegion_inter_cell₀
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₁ D.nested D.disjoint).inside) :
    P.closedRegion ∩ D.cell₀.closedRegion =
      range D.separator.innerSplit.first := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxBoth : x ∈ D.cell₀.closedRegion ∩ D.cell₁.closedRegion :=
      ⟨hx.2, D.innerClosedRegion_subset_cell₁ hinside hx.1⟩
    have hxBridge : x ∈ range D.separator.commonBridge := by
      rw [← D.separator.closure_separatorInteriors_inter
        D.nested D.disjoint]
      rwa [← D.cell₀_closedRegion, ← D.cell₁_closedRegion]
    rw [← D.commonBridge_inter_innerClosedRegion]
    exact ⟨hxBridge, hx.1⟩
  · intro x hxInner
    have hxBridge : x ∈ range D.separator.commonBridge := by
      rw [PolygonalCircle.AnnularCrosscut.SeparatorPair.commonBridge,
        PolygonalCircle.AnnularCrosscut.range_bridgePath]
      exact Or.inl (Or.inr hxInner)
    constructor
    · rw [P.closedRegion_eq_union]
      exact Or.inr (D.separator.innerFirst_range_subset hxInner)
    · rw [D.cell₀.closedRegion_eq_union]
      right
      rw [D.cell₀_carrier,
        D.separator.carrier_circle₀ D.nested D.disjoint]
      exact Or.inl hxBridge

/-- If the first separator contains the inner disk, the second separator
disk is an attachment along the selected inner boundary arc. -/
def attachmentPresentation₁
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₀ D.nested D.disjoint).inside) :
    PolygonalDiskAttachment.Presentation P.closedRegion where
  disk := D.cell₁
  startPoint := D.first.innerPoint
  endPoint := D.second.innerPoint
  shared := D.separator.innerSplit.first
  exposed := D.exposedPath D.separator.outerArc₁
  shared_injective := D.separator.innerSplit.first_injective
  exposed_injective := D.exposedPath_injective D.separator.outerArc₁
    (D.separator.outerSplit.first_injective.comp
      unitInterval.symm_bijective.injective)
    D.separator.outerArc₁_range_subset
  boundary_overlap := D.innerFirst_inter_exposedPath
    D.separator.outerArc₁ D.separator.outerArc₁_range_subset
  carrier_eq := D.cell₁_carrier_eq_innerFirst_union_exposedPath
  base_closed := P.isCompact_closedRegion.isClosed
  base_inter_disk := D.innerClosedRegion_inter_cell₁ hinside

/-- If the second separator contains the inner disk, the first separator
disk is the corresponding attachment. -/
def attachmentPresentation₀
    (hinside : P.interiorRegion ⊆
      (D.separator.circle₁ D.nested D.disjoint).inside) :
    PolygonalDiskAttachment.Presentation P.closedRegion where
  disk := D.cell₀
  startPoint := D.first.innerPoint
  endPoint := D.second.innerPoint
  shared := D.separator.innerSplit.first
  exposed := D.exposedPath D.separator.outerArc₀
  shared_injective := D.separator.innerSplit.first_injective
  exposed_injective := D.exposedPath_injective D.separator.outerArc₀
    D.separator.outerSplit.second_injective
    D.separator.outerArc₀_range_subset
  boundary_overlap := D.innerFirst_inter_exposedPath
    D.separator.outerArc₀ D.separator.outerArc₀_range_subset
  carrier_eq := D.cell₀_carrier_eq_innerFirst_union_exposedPath
  base_closed := P.isCompact_closedRegion.isClosed
  base_inter_disk := D.innerClosedRegion_inter_cell₀ hinside

end PolygonalCircle.AnnularCellDecomposition

end

end Schoenflies
