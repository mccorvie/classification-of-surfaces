import Schoenflies.AnnularCrosscutSeparators

/-!
# Sides of a Jordan separator contained in a polygonal shell

A Jordan circle contained in the closed shell between two polygonal circles
cannot enclose the unbounded side of the outer polygon.  The open inner disk
is disjoint from the separator and hence lies wholly on one of its two sides;
the corresponding inner boundary points lie on the same side.  These facts
are the side-theoretic input to the finite cyclic-order argument.
-/

namespace Schoenflies

open Set Function Bornology
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle

/-- If the carrier of `K` lies in the closed inside of `J`, then the unbounded
side of `J` lies in the unbounded side of `K`. -/
theorem outside_subset_outside_of_carrier_subset (J K : JordanCircle)
    (hcarrier : K.carrier ⊆ J.inside ∪ J.carrier) :
    J.outside ⊆ K.outside := by
  have houtsideCarrier : Disjoint J.outside K.carrier := by
    rw [Set.disjoint_left]
    intro x hxOutside hxK
    rcases hcarrier hxK with hxInside | hxCarrier
    · exact Set.disjoint_left.mp J.inside_disjoint_outside
        hxInside hxOutside
    · exact J.outside_subset_compl hxOutside hxCarrier
  have houtsideRegions : J.outside ⊆ K.inside ∪ K.outside := by
    rw [K.inside_union_outside]
    intro x hxOutside hxCarrier
    exact Set.disjoint_left.mp houtsideCarrier hxOutside hxCarrier
  rcases J.outside_isConnected.isPreconnected.subset_or_subset
      K.inside_isOpen K.outside_isOpen K.inside_disjoint_outside
      houtsideRegions with hInside | hOutside
  · exact False.elim
      (J.outside_unbounded (K.inside_bounded.subset hInside))
  · exact hOutside

end JordanCircle

namespace PolygonalCircle

variable {P Q : PolygonalCircle} {K : JordanCircle}

/-- A Jordan separator contained in the closed shell has the whole exterior
of the outer polygon on its unbounded side. -/
theorem exteriorRegion_subset_separatorOutside
    (hK : K.carrier ⊆ closedShell P Q) :
    Q.exteriorRegion ⊆ K.outside := by
  rw [← Q.outside_toJordanCircle]
  apply JordanCircle.outside_subset_outside_of_carrier_subset
  intro x hxK
  have hxClosed : x ∈ Q.closedRegion := (hK hxK).1
  rw [Q.closedRegion_eq_union] at hxClosed
  simpa only [Q.inside_toJordanCircle, Q.carrier_toJordanCircle]
    using hxClosed

/-- Outer-boundary points not used by a shell separator are also on its
unbounded side. -/
theorem outerCarrier_sdiff_separatorCarrier_subset_outside
    (hK : K.carrier ⊆ closedShell P Q) :
    Q.carrier \ K.carrier ⊆ K.outside := by
  have hExterior := exteriorRegion_subset_separatorOutside
    (P := P) (Q := Q) (K := K) hK
  rintro x ⟨hxQ, hxNotK⟩
  rcases K.mem_inside_or_outside hxNotK with hxInside | hxOutside
  · have hxClosure : x ∈ closure Q.exteriorRegion := by
      apply frontier_subset_closure
      rw [Q.frontier_exteriorRegion]
      exact hxQ
    have hxInterClosure :
        x ∈ closure (K.inside ∩ Q.exteriorRegion) :=
      K.inside_isOpen.inter_closure ⟨hxInside, hxClosure⟩
    obtain ⟨y, hyInside, hyExterior⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      hyInside (hExterior hyExterior)
  · exact hxOutside

/-- The inner polygonal interior is connected and misses every separator
contained in the shell, so it is entirely on one separator side. -/
theorem interiorRegion_subset_separatorSide
    (hK : K.carrier ⊆ closedShell P Q) :
    P.interiorRegion ⊆ K.inside ∨
      P.interiorRegion ⊆ K.outside := by
  have hregions : P.interiorRegion ⊆ K.inside ∪ K.outside := by
    rw [K.inside_union_outside]
    intro x hxInterior hxK
    exact (hK hxK).2 hxInterior
  exact P.isConnected_interiorRegion.isPreconnected.subset_or_subset
    K.inside_isOpen K.outside_isOpen K.inside_disjoint_outside hregions

/-- If the inner polygonal interior is on the bounded separator side, all
unused points of its boundary are on that side as well. -/
theorem innerCarrier_sdiff_subset_inside_of_interior_subset_inside
    (hInside : P.interiorRegion ⊆ K.inside) :
    P.carrier \ K.carrier ⊆ K.inside := by
  rintro x ⟨hxP, hxNotK⟩
  rcases K.mem_inside_or_outside hxNotK with hxInside | hxOutside
  · exact hxInside
  · have hxClosure : x ∈ closure P.interiorRegion := by
      apply frontier_subset_closure
      rw [P.frontier_interiorRegion]
      exact hxP
    have hxInterClosure :
        x ∈ closure (K.outside ∩ P.interiorRegion) :=
      K.outside_isOpen.inter_closure ⟨hxOutside, hxClosure⟩
    obtain ⟨y, hyOutside, hyInterior⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      (hInside hyInterior) hyOutside

/-- The analogous boundary propagation when the inner polygonal interior is
on the unbounded separator side. -/
theorem innerCarrier_sdiff_subset_outside_of_interior_subset_outside
    (hOutside : P.interiorRegion ⊆ K.outside) :
    P.carrier \ K.carrier ⊆ K.outside := by
  rintro x ⟨hxP, hxNotK⟩
  rcases K.mem_inside_or_outside hxNotK with hxInside | hxOutside
  · have hxClosure : x ∈ closure P.interiorRegion := by
      apply frontier_subset_closure
      rw [P.frontier_interiorRegion]
      exact hxP
    have hxInterClosure :
        x ∈ closure (K.inside ∩ P.interiorRegion) :=
      K.inside_isOpen.inter_closure ⟨hxInside, hxClosure⟩
    obtain ⟨y, hyInside, hyInterior⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      hyInside (hOutside hyInterior)
  · exact hxOutside

/-- Complete boundary-side classification for a Jordan circle contained in a
closed polygonal shell.  The outer exterior and unused outer boundary always
lie outside; the inner interior and unused inner boundary lie together on one
of the two sides. -/
theorem boundary_sides_of_carrier_subset_closedShell
    (hK : K.carrier ⊆ closedShell P Q) :
    Q.exteriorRegion ⊆ K.outside ∧
      Q.carrier \ K.carrier ⊆ K.outside ∧
      ((P.interiorRegion ⊆ K.inside ∧
          P.carrier \ K.carrier ⊆ K.inside) ∨
        (P.interiorRegion ⊆ K.outside ∧
          P.carrier \ K.carrier ⊆ K.outside)) := by
  refine ⟨exteriorRegion_subset_separatorOutside hK,
    outerCarrier_sdiff_separatorCarrier_subset_outside hK, ?_⟩
  rcases interiorRegion_subset_separatorSide hK with hInside | hOutside
  · exact Or.inl ⟨hInside,
      innerCarrier_sdiff_subset_inside_of_interior_subset_inside hInside⟩
  · exact Or.inr ⟨hOutside,
      innerCarrier_sdiff_subset_outside_of_interior_subset_outside hOutside⟩

end PolygonalCircle

end

end Schoenflies
