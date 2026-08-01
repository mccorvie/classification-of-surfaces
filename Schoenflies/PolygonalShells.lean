import Schoenflies.LocalizedPolygonalDiskExhaustion

/-!
# Closed shells between strictly nested polygonal disks

The finite stage of the inside Schoenflies construction is the compact
region between two polygonal disks.  This file fixes that region as an exact
set and records the decomposition identities needed for cellwise pasting.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace PolygonalCircle

/-- The compact shell bounded by an inner polygon `P` and an outer polygon
`Q`.  The inner boundary is retained and only the open inner disk is
removed. -/
def closedShell (P Q : PolygonalCircle) : Set Plane :=
  Q.closedRegion \ P.interiorRegion

/-- The open stratum of the polygonal shell. -/
def openShell (P Q : PolygonalCircle) : Set Plane :=
  Q.interiorRegion \ P.closedRegion

theorem closedRegion_subset_closedRegion_of_strictlyNested
    (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    P.closedRegion ⊆ Q.closedRegion := by
  intro x hx
  rw [Q.closedRegion_eq_union]
  exact Or.inl (hPQ hx)

theorem carrier_disjoint_interiorRegion (P : PolygonalCircle) :
    Disjoint P.carrier P.interiorRegion := by
  rw [Set.disjoint_left]
  intro x hxCarrier hxInterior
  have hxCompl : x ∈ P.carrierᶜ := by
    rw [← P.interior_union_exterior]
    exact Or.inl hxInterior
  exact hxCompl hxCarrier

theorem innerCarrier_subset_closedShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    P.carrier ⊆ closedShell P Q := by
  intro x hx
  refine ⟨?_, ?_⟩
  · exact closedRegion_subset_closedRegion_of_strictlyNested P Q hPQ <| by
      rw [P.closedRegion_eq_union]
      exact Or.inr hx
  · exact fun hxInterior =>
      Set.disjoint_left.mp (carrier_disjoint_interiorRegion P) hx hxInterior

theorem outerCarrier_subset_closedShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    Q.carrier ⊆ closedShell P Q := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [Q.closedRegion_eq_union]
    exact Or.inr hx
  · intro hxPInterior
    have hxQInterior : x ∈ Q.interiorRegion := hPQ <| by
      rw [P.closedRegion_eq_union]
      exact Or.inl hxPInterior
    exact Set.disjoint_left.mp (carrier_disjoint_interiorRegion Q) hx hxQInterior

theorem isCompact_closedShell (P Q : PolygonalCircle) :
    IsCompact (closedShell P Q) :=
  Q.isCompact_closedRegion.diff P.isOpen_interiorRegion

theorem isOpen_openShell (P Q : PolygonalCircle) :
    IsOpen (openShell P Q) :=
  Q.isOpen_interiorRegion.sdiff P.isCompact_closedRegion.isClosed

theorem openShell_subset_closedShell (P Q : PolygonalCircle) :
    openShell P Q ⊆ closedShell P Q := by
  rintro x ⟨hxQ, hxP⟩
  refine ⟨?_, fun hxPInterior => hxP ?_⟩
  · rw [Q.closedRegion_eq_union]
    exact Or.inl hxQ
  · rw [P.closedRegion_eq_union]
    exact Or.inl hxPInterior

/-- Strict nesting makes the compact shell the closure of its open stratum.
This is the density fact used when an arrangement chamber contains a point
on either boundary polygon. -/
theorem closure_openShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    closure (openShell P Q) = closedShell P Q := by
  apply Set.Subset.antisymm
  · exact closure_minimal (openShell_subset_closedShell P Q)
      (isCompact_closedShell P Q).isClosed
  · rintro x ⟨hxQ, hxNotPInterior⟩
    rw [Q.closedRegion_eq_union] at hxQ
    rcases hxQ with hxQInterior | hxQCarrier
    · by_cases hxPClosed : x ∈ P.closedRegion
      · have hxPCarrier : x ∈ P.carrier := by
          rw [P.closedRegion_eq_union] at hxPClosed
          exact hxPClosed.resolve_left hxNotPInterior
        have hxClosureExterior : x ∈ closure P.exteriorRegion :=
          frontier_subset_closure <| by
            rw [P.frontier_exteriorRegion]
            exact hxPCarrier
        have hsub : Q.interiorRegion ∩ P.exteriorRegion ⊆
            openShell P Q := by
          rintro y ⟨hyQ, hyPExterior⟩
          refine ⟨hyQ, ?_⟩
          intro hyPClosed
          exact Set.disjoint_left.mp P.disjoint_closedRegion_exteriorRegion
            hyPClosed hyPExterior
        exact closure_mono hsub <|
          Q.isOpen_interiorRegion.inter_closure
            ⟨hxQInterior, hxClosureExterior⟩
      · exact subset_closure ⟨hxQInterior, hxPClosed⟩
    · have hxNotPClosed : x ∉ P.closedRegion := by
        intro hxPClosed
        have hxQInterior : x ∈ Q.interiorRegion := hPQ hxPClosed
        exact Set.disjoint_left.mp (carrier_disjoint_interiorRegion Q)
          hxQCarrier hxQInterior
      have hxClosureQInterior : x ∈ closure Q.interiorRegion :=
        frontier_subset_closure <| by
          rw [Q.frontier_interiorRegion]
          exact hxQCarrier
      have hxClosure := P.isCompact_closedRegion.isClosed.isOpen_compl.inter_closure
        ⟨hxNotPClosed, hxClosureQInterior⟩
      simpa only [openShell, Set.sdiff_eq, Set.inter_comm] using hxClosure

/-- The old disk together with the closed shell is exactly the new disk. -/
theorem closedRegion_union_closedShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    P.closedRegion ∪ closedShell P Q = Q.closedRegion := by
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (closedRegion_subset_closedRegion_of_strictlyNested P Q hPQ)
      Set.sdiff_subset
  · intro x hxQ
    by_cases hxP : x ∈ P.interiorRegion
    · left
      rw [P.closedRegion_eq_union]
      exact Or.inl hxP
    · exact Or.inr ⟨hxQ, hxP⟩

/-- The overlap in the preceding decomposition is precisely the inner
polygonal boundary. -/
theorem closedRegion_inter_closedShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    P.closedRegion ∩ closedShell P Q = P.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxP, _hxQ, hxNotInterior⟩
    rw [P.closedRegion_eq_union] at hxP
    exact hxP.resolve_left hxNotInterior
  · intro x hxCarrier
    refine ⟨?_, innerCarrier_subset_closedShell P Q hPQ hxCarrier⟩
    rw [P.closedRegion_eq_union]
    exact Or.inr hxCarrier

/-- Both boundary polygons are contained in the finite shell. -/
theorem boundary_union_subset_closedShell (P Q : PolygonalCircle)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion) :
    P.carrier ∪ Q.carrier ⊆ closedShell P Q :=
  Set.union_subset (innerCarrier_subset_closedShell P Q hPQ)
    (outerCarrier_subset_closedShell P Q hPQ)

end PolygonalCircle

end Schoenflies
