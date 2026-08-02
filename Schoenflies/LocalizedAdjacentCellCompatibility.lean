import Schoenflies.LocalizedCellHomeomorphisms

/-!
# Compatibility of adjacent localized collar cells

The cell fillings are constructed independently.  Their boundary
parameter control nevertheless makes them agree exactly on the radial cut
shared by a cell and its cyclic successor.  The statements allow arbitrary
membership proofs so they can be applied directly inside a closed-cover
gluing argument.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {k : ℕ} {a b : LevelAddress k}

/-- A point common to two distinct source cell closures lies on both cell
boundaries.  Pairwise interior disjointness and boundary avoidance exclude
all other cases. -/
theorem localizedCells_mem_carriers_of_mem_closedRegions
    (hk : 1 ≤ k) (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b) (hab : a ≠ b) {x : Plane}
    (hxC : x ∈ C.disk.closedRegion) (hxD : x ∈ D.disk.closedRegion) :
    x ∈ C.disk.carrier ∧ x ∈ D.disk.carrier := by
  have hinteriors := C.disjoint_diskInterior hk D hab
  constructor
  · rw [C.disk.closedRegion_eq_union] at hxC
    rcases hxC with hxCInterior | hxCCarrier
    · rw [D.disk.closedRegion_eq_union] at hxD
      rcases hxD with hxDInterior | hxDCarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxCInterior hxDInterior
      · exact False.elim <|
          Set.disjoint_left.mp (C.diskCarrier_disjoint_diskInterior D)
            hxDCarrier hxCInterior
    · exact hxCCarrier
  · rw [D.disk.closedRegion_eq_union] at hxD
    rcases hxD with hxDInterior | hxDCarrier
    · rw [C.disk.closedRegion_eq_union] at hxC
      rcases hxC with hxCInterior | hxCCarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxCInterior hxDInterior
      · exact False.elim <|
          Set.disjoint_left.mp (D.diskCarrier_disjoint_diskInterior C)
            hxCCarrier hxDInterior
    · exact hxDCarrier

/-- Forward cell maps agree pointwise on a common radial cut whenever the
second cell begins at the first cell's successor label. -/
theorem localizedCellHomeomorph_agree_on_commonCut
    (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b)
    (hnext : C.next = b) (t : unitInterval)
    (hC : (I.levelLocalizedAnnularCrosscut k b).path t ∈
      C.disk.closedRegion)
    (hD : (I.levelLocalizedAnnularCrosscut k b).path t ∈
      D.disk.closedRegion) :
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k b).path t, hC⟩ : Plane) =
      (D.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k b).path t, hD⟩ : Plane) := by
  subst b
  calc
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k C.next).path t, hC⟩ : Plane) =
        (I.levelTargetAnnularCrosscut k C.next).path t := by
      simpa only [] using C.cellHomeomorph_apply_successorCut t
    _ = (D.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k C.next).path t, hD⟩ :
          Plane) := by
      symm
      simpa only [] using D.cellHomeomorph_apply_initialCut t

/-- The inverse cell maps likewise agree on the corresponding target radial
cut. -/
theorem localizedCellHomeomorph_symm_agree_on_commonCut
    (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b)
    (hnext : C.next = b) (t : unitInterval)
    (hC : (I.levelTargetAnnularCrosscut k b).path t ∈
      C.targetAttachmentPresentation.disk.closedRegion)
    (hD : (I.levelTargetAnnularCrosscut k b).path t ∈
      D.targetAttachmentPresentation.disk.closedRegion) :
    (C.cellHomeomorph.symm
        ⟨(I.levelTargetAnnularCrosscut k b).path t, hC⟩ : Plane) =
      (D.cellHomeomorph.symm
        ⟨(I.levelTargetAnnularCrosscut k b).path t, hD⟩ : Plane) := by
  subst b
  let x := (I.levelLocalizedAnnularCrosscut k C.next).path t
  have hxC : x ∈ C.disk.closedRegion := by
    exact C.decomposition_secondPath_mem_disk_closedRegion t
  have hxD : x ∈ D.disk.closedRegion := by
    exact D.decomposition_firstPath_mem_disk_closedRegion t
  have hmapC : C.cellHomeomorph ⟨x, hxC⟩ =
      ⟨(I.levelTargetAnnularCrosscut k C.next).path t, hC⟩ := by
    apply Subtype.ext
    exact C.cellHomeomorph_apply_successorCut t
  have hmapD : D.cellHomeomorph ⟨x, hxD⟩ =
      ⟨(I.levelTargetAnnularCrosscut k C.next).path t, hD⟩ := by
    apply Subtype.ext
    exact D.cellHomeomorph_apply_initialCut t
  rw [← hmapC, ← hmapD,
    C.cellHomeomorph.symm_apply_apply,
    D.cellHomeomorph.symm_apply_apply]

/-- Distinct canonical source cells can overlap only when their labels are
cyclically adjacent, and then every common point lies on their common radial
cut. -/
theorem canonicalLocalizedCells_closedRegion_overlap_cases
    (k : ℕ) (hk : 1 ≤ k) {a b : LevelAddress k} (hab : a ≠ b)
    {x : Plane}
    (hxC : x ∈ (I.localizedCutFreeCellData k a).disk.closedRegion)
    (hxD : x ∈ (I.localizedCutFreeCellData k b).disk.closedRegion) :
    (b = I.levelLocalizedSuccessor k a ∧
        x ∈ range (I.levelLocalizedAnnularCrosscut k b).path) ∨
      (a = I.levelLocalizedSuccessor k b ∧
        x ∈ range (I.levelLocalizedAnnularCrosscut k a).path) := by
  let C := I.localizedCutFreeCellData k a
  let D := I.localizedCutFreeCellData k b
  have hxCarriers := localizedCells_mem_carriers_of_mem_closedRegions
    hk C D hab hxC hxD
  have hxCCarrier := hxCarriers.1
  have hxDCarrier := hxCarriers.2
  have hxCCarrierRaw : x ∈ C.disk.carrier := hxCarriers.1
  have hxDCarrierRaw : x ∈ D.disk.carrier := hxCarriers.2
  change x ∈ C.attachmentPresentation.disk.carrier at hxCCarrier
  change x ∈ D.attachmentPresentation.disk.carrier at hxDCarrier
  rw [C.attachmentPresentation.carrier_eq,
    C.range_attachmentPresentation_exposed] at hxCCarrier
  rw [D.attachmentPresentation.carrier_eq,
    D.range_attachmentPresentation_exposed] at hxDCarrier
  have classifyCcut (c : LevelAddress k)
      (hc : c = a ∨ c = I.levelLocalizedSuccessor k a)
      (hxc : x ∈ range (I.levelLocalizedAnnularCrosscut k c).path) :
      (b = I.levelLocalizedSuccessor k a ∧
          x ∈ range (I.levelLocalizedAnnularCrosscut k b).path) ∨
        (a = I.levelLocalizedSuccessor k b ∧
          x ∈ range (I.levelLocalizedAnnularCrosscut k a).path) := by
    by_cases hcb : c = b
    · rcases hc with hca | hcsuccessor
      · exact False.elim (hab (hca.symm.trans hcb))
      · left
        exact ⟨hcb.symm.trans hcsuccessor, hcb ▸ hxc⟩
    by_cases hcnext : c = D.next
    · rcases hc with hca | hcsuccessor
      · right
        exact ⟨hca.symm.trans (hcnext.trans D.next_eq), hca ▸ hxc⟩
      · exact False.elim <| hab <|
          (I.levelLocalizedSuccessor_bijective k).injective <| by
            rw [← hcsuccessor, hcnext, D.next_eq]
    exact False.elim <| Set.disjoint_left.mp
      (D.other_crosscut_disjoint_diskCarrier c hcb hcnext)
      hxc hxDCarrierRaw
  have classifyDcut (c : LevelAddress k)
      (hc : c = b ∨ c = I.levelLocalizedSuccessor k b)
      (hxc : x ∈ range (I.levelLocalizedAnnularCrosscut k c).path) :
      (b = I.levelLocalizedSuccessor k a ∧
          x ∈ range (I.levelLocalizedAnnularCrosscut k b).path) ∨
        (a = I.levelLocalizedSuccessor k b ∧
          x ∈ range (I.levelLocalizedAnnularCrosscut k a).path) := by
    by_cases hca : c = a
    · rcases hc with hcb | hcsuccessor
      · exact False.elim (hab (hca.symm.trans hcb))
      · right
        exact ⟨hca.symm.trans hcsuccessor, hca ▸ hxc⟩
    by_cases hcnext : c = C.next
    · rcases hc with hcb | hcsuccessor
      · left
        exact ⟨hcb.symm.trans (hcnext.trans C.next_eq), hcb ▸ hxc⟩
      · exact False.elim <| hab <|
          (I.levelLocalizedSuccessor_bijective k).injective <| by
            rw [← C.next_eq, ← hcnext, hcsuccessor]
    exact False.elim <| Set.disjoint_left.mp
      (C.other_crosscut_disjoint_diskCarrier c hca hcnext)
      hxc hxCCarrierRaw
  rcases hxCCarrier with hxCShared | hxCSecond | hxCOuter | hxCFirst
  · rcases hxDCarrier with hxDShared | hxDSecond | hxDOuter | hxDFirst
    · have hxEnds := I.localizedCutFreeCell_shared_inter_subset_endpoints
        k hk hab ⟨hxCShared, hxDShared⟩
      rcases hxEnds with hxa | hxsuccessor
      · subst x
        rcases (I.levelLocalizedInnerPoint_mem_canonicalCellShared_iff
          k hk b a).mp hxDShared with hab' | hasuccessor
        · exact False.elim (hab hab')
        · right
          exact ⟨hasuccessor,
            Path.target_mem_range
              (I.levelLocalizedAnnularCrosscut k a).path⟩
      · rw [Set.mem_singleton_iff] at hxsuccessor
        subst x
        rcases (I.levelLocalizedInnerPoint_mem_canonicalCellShared_iff
          k hk b (I.levelLocalizedSuccessor k a)).mp hxDShared with
          hsuccessorb | hsuccessors
        · left
          exact ⟨hsuccessorb.symm, by
            rw [← hsuccessorb]
            exact Path.target_mem_range
              (I.levelLocalizedAnnularCrosscut k
                (I.levelLocalizedSuccessor k a)).path⟩
        · exact False.elim <| hab <|
            (I.levelLocalizedSuccessor_bijective k).injective hsuccessors
    · exact classifyDcut D.next (Or.inr D.next_eq) hxDSecond
    · have hxInner : x ∈
          (I.localizedMarkedPolygonalDisk (k + 1)).carrier := by
        rw [C.range_attachmentPresentation_shared] at hxCShared
        exact C.separator.innerFirst_range_subset hxCShared
      have hxOuter : x ∈
          (I.localizedMarkedPolygonalDisk (k + 2)).carrier :=
        D.exposedOuterArc_subset_outerCarrier hxDOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)))
        hxInner hxOuter
    · exact classifyDcut b (Or.inl rfl) hxDFirst
  · exact classifyCcut C.next (Or.inr C.next_eq) hxCSecond
  · rcases hxDCarrier with hxDShared | hxDSecond | hxDOuter | hxDFirst
    · have hxInner : x ∈
          (I.localizedMarkedPolygonalDisk (k + 1)).carrier := by
        rw [D.range_attachmentPresentation_shared] at hxDShared
        exact D.separator.innerFirst_range_subset hxDShared
      have hxOuter : x ∈
          (I.localizedMarkedPolygonalDisk (k + 2)).carrier :=
        C.exposedOuterArc_subset_outerCarrier hxCOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)))
        hxInner hxOuter
    · exact classifyDcut D.next (Or.inr D.next_eq) hxDSecond
    · have hxEnds := I.localizedCutFreeCell_exposedOuterArc_inter_subset_endpoints
        k hk hab ⟨hxCOuter, hxDOuter⟩
      rcases hxEnds with hxa | hxsuccessor
      · subst x
        rcases (I.levelLocalizedOuterPoint_mem_canonicalCellExposed_iff
          k b a).mp hxDOuter with hab' | hasuccessor
        · exact False.elim (hab hab')
        · right
          exact ⟨hasuccessor,
            Path.source_mem_range
              (I.levelLocalizedAnnularCrosscut k a).path⟩
      · rw [Set.mem_singleton_iff] at hxsuccessor
        subst x
        rcases (I.levelLocalizedOuterPoint_mem_canonicalCellExposed_iff
          k b (I.levelLocalizedSuccessor k a)).mp hxDOuter with
          hsuccessorb | hsuccessors
        · left
          exact ⟨hsuccessorb.symm, by
            rw [← hsuccessorb]
            exact Path.source_mem_range
              (I.levelLocalizedAnnularCrosscut k
                (I.levelLocalizedSuccessor k a)).path⟩
        · exact False.elim <| hab <|
            (I.levelLocalizedSuccessor_bijective k).injective hsuccessors
    · exact classifyDcut b (Or.inl rfl) hxDFirst
  · exact classifyCcut a (Or.inl rfl) hxCFirst

/-- The canonical source cell fillings agree on every pairwise overlap, not
only when adjacency has already been supplied by the caller. -/
theorem canonicalLocalizedCellHomeomorph_agree
    (k : ℕ) (hk : 1 ≤ k) (a b : LevelAddress k) {x : Plane}
    (hxC : x ∈ (I.localizedCutFreeCellData k a).disk.closedRegion)
    (hxD : x ∈ (I.localizedCutFreeCellData k b).disk.closedRegion) :
    ((I.localizedCutFreeCellData k a).cellHomeomorph ⟨x, hxC⟩ : Plane) =
      ((I.localizedCutFreeCellData k b).cellHomeomorph ⟨x, hxD⟩ : Plane) := by
  let C := I.localizedCutFreeCellData k a
  let D := I.localizedCutFreeCellData k b
  by_cases hab : a = b
  · subst b
    rfl
  rcases I.canonicalLocalizedCells_closedRegion_overlap_cases
      k hk hab hxC hxD with hforward | hbackward
  · obtain ⟨t, ht⟩ := hforward.2
    subst x
    exact I.localizedCellHomeomorph_agree_on_commonCut C D
      (C.next_eq.trans hforward.1.symm) t hxC hxD
  · obtain ⟨t, ht⟩ := hbackward.2
    subst x
    symm
    exact I.localizedCellHomeomorph_agree_on_commonCut D C
      (D.next_eq.trans hbackward.1.symm) t hxD hxC

/-- A point common to two distinct target cell closures lies on both target
cell boundaries. -/
theorem localizedTargetCells_mem_carriers_of_mem_closedRegions
    (hk : 1 ≤ k) (C : I.LocalizedCutFreeCellData k a)
    (D : I.LocalizedCutFreeCellData k b) (hab : a ≠ b) {x : Plane}
    (hxC : x ∈ C.targetAttachmentPresentation.disk.closedRegion)
    (hxD : x ∈ D.targetAttachmentPresentation.disk.closedRegion) :
    x ∈ C.targetAttachmentPresentation.disk.carrier ∧
      x ∈ D.targetAttachmentPresentation.disk.carrier := by
  have hinteriors := C.disjoint_targetDiskInterior hk D hab
  constructor
  · rw [C.targetAttachmentPresentation.disk.closedRegion_eq_union] at hxC
    rcases hxC with hxCInterior | hxCCarrier
    · rw [D.targetAttachmentPresentation.disk.closedRegion_eq_union] at hxD
      rcases hxD with hxDInterior | hxDCarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxCInterior hxDInterior
      · exact False.elim <| Set.disjoint_left.mp
          (C.targetDiskCarrier_disjoint_targetDiskInterior hk D)
          hxDCarrier hxCInterior
    · exact hxCCarrier
  · rw [D.targetAttachmentPresentation.disk.closedRegion_eq_union] at hxD
    rcases hxD with hxDInterior | hxDCarrier
    · rw [C.targetAttachmentPresentation.disk.closedRegion_eq_union] at hxC
      rcases hxC with hxCInterior | hxCCarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxCInterior hxDInterior
      · exact False.elim <| Set.disjoint_left.mp
          (D.targetDiskCarrier_disjoint_targetDiskInterior hk C)
          hxCCarrier hxDInterior
    · exact hxDCarrier

/-- Distinct canonical target cells overlap only along the radial cut
corresponding to one of the two cyclic adjacency relations. -/
theorem canonicalLocalizedTargetCells_closedRegion_overlap_cases
    (k : ℕ) (hk : 1 ≤ k) {a b : LevelAddress k} (hab : a ≠ b)
    {x : Plane}
    (hxC : x ∈ (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion)
    (hxD : x ∈ (I.localizedCutFreeCellData k b).targetAttachmentPresentation.disk.closedRegion) :
    (b = (I.localizedCutFreeCellData k a).next ∧
        x ∈ range (I.levelTargetAnnularCrosscut k b).path) ∨
      (a = (I.localizedCutFreeCellData k b).next ∧
        x ∈ range (I.levelTargetAnnularCrosscut k a).path) := by
  let C := I.localizedCutFreeCellData k a
  let D := I.localizedCutFreeCellData k b
  have hxCarriers :=
    I.localizedTargetCells_mem_carriers_of_mem_closedRegions
      hk C D hab hxC hxD
  have hxCCarrier := hxCarriers.1
  have hxDCarrier := hxCarriers.2
  have hxCCarrierRaw :
      x ∈ C.targetAttachmentPresentation.disk.carrier := hxCarriers.1
  have hxDCarrierRaw :
      x ∈ D.targetAttachmentPresentation.disk.carrier := hxCarriers.2
  rw [C.targetAttachmentPresentation.carrier_eq,
    C.range_targetAttachmentPresentation_shared,
    C.range_targetAttachmentPresentation_exposed hk] at hxCCarrier
  rw [D.targetAttachmentPresentation.carrier_eq,
    D.range_targetAttachmentPresentation_shared,
    D.range_targetAttachmentPresentation_exposed hk] at hxDCarrier
  have classifyCcut (c : LevelAddress k)
      (hc : c = a ∨ c = C.next)
      (hxc : x ∈ range (I.levelTargetAnnularCrosscut k c).path) :
      (b = C.next ∧
          x ∈ range (I.levelTargetAnnularCrosscut k b).path) ∨
        (a = D.next ∧
          x ∈ range (I.levelTargetAnnularCrosscut k a).path) := by
    by_cases hcb : c = b
    · rcases hc with hca | hcnext
      · exact False.elim (hab (hca.symm.trans hcb))
      · left
        exact ⟨hcb.symm.trans hcnext, hcb ▸ hxc⟩
    by_cases hcDnext : c = D.next
    · rcases hc with hca | hcnext
      · right
        exact ⟨hca.symm.trans hcDnext, hca ▸ hxc⟩
      · exact False.elim <| hab <|
          (I.localizedCutFreeCellData_next_bijective k).injective <|
            hcnext.symm.trans hcDnext
    exact False.elim <| Set.disjoint_left.mp
      (D.other_targetCrosscut_disjoint_targetDiskCarrier
        hk c hcb hcDnext) hxc hxDCarrierRaw
  have classifyDcut (c : LevelAddress k)
      (hc : c = b ∨ c = D.next)
      (hxc : x ∈ range (I.levelTargetAnnularCrosscut k c).path) :
      (b = C.next ∧
          x ∈ range (I.levelTargetAnnularCrosscut k b).path) ∨
        (a = D.next ∧
          x ∈ range (I.levelTargetAnnularCrosscut k a).path) := by
    by_cases hca : c = a
    · rcases hc with hcb | hcnext
      · exact False.elim (hab (hca.symm.trans hcb))
      · right
        exact ⟨hca.symm.trans hcnext, hca ▸ hxc⟩
    by_cases hcCnext : c = C.next
    · rcases hc with hcb | hcnext
      · left
        exact ⟨hcb.symm.trans hcCnext, hcb ▸ hxc⟩
      · exact False.elim <| hab <|
          (I.localizedCutFreeCellData_next_bijective k).injective <|
            hcCnext.symm.trans hcnext
    exact False.elim <| Set.disjoint_left.mp
      (C.other_targetCrosscut_disjoint_targetDiskCarrier
        hk c hca hcCnext) hxc hxCCarrierRaw
  rcases hxCCarrier with hxCShared | hxCSecond | hxCOuter | hxCFirst
  · rcases hxDCarrier with hxDShared | hxDSecond | hxDOuter | hxDFirst
    · have hxEnds :=
        I.canonicalTargetBoundarySplit_first_inter_subset_endpoints
          k (k + 1) hk hab ⟨hxCShared, hxDShared⟩
      rcases hxEnds with hxa | hxnext
      · subst x
        rcases (I.levelTargetPoint_mem_canonicalBoundarySplit_first_iff
          k (k + 1) b a).mp hxDShared with hab' | haDnext
        · exact False.elim (hab hab')
        · right
          exact ⟨haDnext, by
            simpa only [JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
              JordanCircle.InitialAngularArcs.levelTargetInnerMark] using
                Path.target_mem_range
                  (I.levelTargetAnnularCrosscut k a).path⟩
      · rw [Set.mem_singleton_iff] at hxnext
        subst x
        rcases (I.levelTargetPoint_mem_canonicalBoundarySplit_first_iff
          k (k + 1) b C.next).mp hxDShared with hCnextb | hnexts
        · left
          exact ⟨hCnextb.symm, by
            rw [← hCnextb]
            simpa only [JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
              JordanCircle.InitialAngularArcs.levelTargetInnerMark] using
                Path.target_mem_range
                  (I.levelTargetAnnularCrosscut k C.next).path⟩
        · exact False.elim <| hab <|
            (I.localizedCutFreeCellData_next_bijective k).injective hnexts
    · exact classifyDcut D.next (Or.inr rfl) hxDSecond
    · have hxInner : x ∈
          (StandardPolygonalCollars.disk (k + 1)).carrier :=
        C.targetSeparator.innerFirst_range_subset hxCShared
      have hxOuter : x ∈
          (StandardPolygonalCollars.disk (k + 2)).carrier := by
        rw [← (StandardPolygonalCollars.disk (k + 2)).carrier_toJordanCircle,
          ← (D.targetBoundarySplit (k + 2)).cover]
        exact Or.inl hxDOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (StandardPolygonalCollars.disk_strictlyNested (k + 1)))
        hxInner hxOuter
    · exact classifyDcut b (Or.inl rfl) hxDFirst
  · exact classifyCcut C.next (Or.inr rfl) hxCSecond
  · rcases hxDCarrier with hxDShared | hxDSecond | hxDOuter | hxDFirst
    · have hxInner : x ∈
          (StandardPolygonalCollars.disk (k + 1)).carrier :=
        D.targetSeparator.innerFirst_range_subset hxDShared
      have hxOuter : x ∈
          (StandardPolygonalCollars.disk (k + 2)).carrier := by
        rw [← (StandardPolygonalCollars.disk (k + 2)).carrier_toJordanCircle,
          ← (C.targetBoundarySplit (k + 2)).cover]
        exact Or.inl hxCOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (StandardPolygonalCollars.disk_strictlyNested (k + 1)))
        hxInner hxOuter
    · exact classifyDcut D.next (Or.inr rfl) hxDSecond
    · have hxEnds :=
        I.canonicalTargetBoundarySplit_first_inter_subset_endpoints
          k (k + 2) hk hab ⟨hxCOuter, hxDOuter⟩
      rcases hxEnds with hxa | hxnext
      · subst x
        rcases (I.levelTargetPoint_mem_canonicalBoundarySplit_first_iff
          k (k + 2) b a).mp hxDOuter with hab' | haDnext
        · exact False.elim (hab hab')
        · right
          exact ⟨haDnext, by
            simpa only [JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
              JordanCircle.InitialAngularArcs.levelTargetOuterMark] using
                Path.source_mem_range
                  (I.levelTargetAnnularCrosscut k a).path⟩
      · rw [Set.mem_singleton_iff] at hxnext
        subst x
        rcases (I.levelTargetPoint_mem_canonicalBoundarySplit_first_iff
          k (k + 2) b C.next).mp hxDOuter with hCnextb | hnexts
        · left
          exact ⟨hCnextb.symm, by
            rw [← hCnextb]
            simpa only [JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
              JordanCircle.InitialAngularArcs.levelTargetOuterMark] using
                Path.source_mem_range
                  (I.levelTargetAnnularCrosscut k C.next).path⟩
        · exact False.elim <| hab <|
            (I.localizedCutFreeCellData_next_bijective k).injective hnexts
    · exact classifyDcut b (Or.inl rfl) hxDFirst
  · exact classifyCcut a (Or.inl rfl) hxCFirst

/-- The inverses of the canonical cell fillings agree on every pairwise
target-cell overlap. -/
theorem canonicalLocalizedCellHomeomorph_symm_agree
    (k : ℕ) (hk : 1 ≤ k) (a b : LevelAddress k) {y : Plane}
    (hyC : y ∈ (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion)
    (hyD : y ∈ (I.localizedCutFreeCellData k b).targetAttachmentPresentation.disk.closedRegion) :
    ((I.localizedCutFreeCellData k a).cellHomeomorph.symm ⟨y, hyC⟩ :
        Plane) =
      ((I.localizedCutFreeCellData k b).cellHomeomorph.symm ⟨y, hyD⟩ :
        Plane) := by
  let C := I.localizedCutFreeCellData k a
  let D := I.localizedCutFreeCellData k b
  by_cases hab : a = b
  · subst b
    rfl
  rcases I.canonicalLocalizedTargetCells_closedRegion_overlap_cases
      k hk hab hyC hyD with hforward | hbackward
  · obtain ⟨t, ht⟩ := hforward.2
    subst y
    exact I.localizedCellHomeomorph_symm_agree_on_commonCut C D
      hforward.1.symm t hyC hyD
  · obtain ⟨t, ht⟩ := hbackward.2
    subst y
    symm
    exact I.localizedCellHomeomorph_symm_agree_on_commonCut D C
      hbackward.1.symm t hyD hyC

end JordanCircle.InitialAngularArcs

end

end Schoenflies
