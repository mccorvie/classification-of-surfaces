import Schoenflies.CyclicTargetCellGeometry

/-!
# Pairwise compatibility of canonical cyclic target cells

Distinct target cells meet only on the radial side corresponding to one of
the two cyclic adjacency relations.  This is the target-side compatibility
input for finite closed-cover gluing.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- A point common to two distinct target cell closures lies on both cell
boundaries. -/
theorem cyclicTargetCells_mem_carriers_of_mem_closedRegions
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) {a b : LevelAddress n}
    (hab : a ≠ b) {x : Plane}
    (hxA : x ∈ (I.cyclicTargetAttachmentPresentation m a).disk.closedRegion)
    (hxB : x ∈ (I.cyclicTargetAttachmentPresentation m b).disk.closedRegion) :
    x ∈ (I.cyclicTargetAttachmentPresentation m a).disk.carrier ∧
      x ∈ (I.cyclicTargetAttachmentPresentation m b).disk.carrier := by
  have hinteriors := I.disjoint_cyclicTargetCellInterior m hn a b hab
  constructor
  · rw [(I.cyclicTargetAttachmentPresentation m a).disk.closedRegion_eq_union]
      at hxA
    rcases hxA with hxAInterior | hxACarrier
    · rw [(I.cyclicTargetAttachmentPresentation m b).disk.closedRegion_eq_union]
        at hxB
      rcases hxB with hxBInterior | hxBCarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxAInterior hxBInterior
      · exact False.elim <| Set.disjoint_left.mp
          (I.cyclicTargetCellCarrier_disjoint_cellInterior m hn a b)
          hxBCarrier hxAInterior
    · exact hxACarrier
  · rw [(I.cyclicTargetAttachmentPresentation m b).disk.closedRegion_eq_union]
      at hxB
    rcases hxB with hxBInterior | hxBCarrier
    · rw [(I.cyclicTargetAttachmentPresentation m a).disk.closedRegion_eq_union]
        at hxA
      rcases hxA with hxAInterior | hxACarrier
      · exact False.elim <|
          Set.disjoint_left.mp hinteriors hxAInterior hxBInterior
      · exact False.elim <| Set.disjoint_left.mp
          (I.cyclicTargetCellCarrier_disjoint_cellInterior m hn b a)
          hxACarrier hxBInterior
    · exact hxBCarrier

set_option maxHeartbeats 800000 in
-- Expanding all four boundary decompositions is elaboration-intensive.
/-! Distinct canonical target cells overlap only along the radial cut for
one of the two cyclic adjacency relations. -/
theorem cyclicTargetCells_closedRegion_overlap_cases
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) {a b : LevelAddress n}
    (hab : a ≠ b) {x : Plane}
    (hxA : x ∈ (I.cyclicTargetAttachmentPresentation m a).disk.closedRegion)
    (hxB : x ∈ (I.cyclicTargetAttachmentPresentation m b).disk.closedRegion) :
    (b = nextLevelAddress n a ∧
        x ∈ range (I.indexedTargetAnnularCrosscut m b).path) ∨
      (a = nextLevelAddress n b ∧
        x ∈ range (I.indexedTargetAnnularCrosscut m a).path) := by
  have hxCarriers := I.cyclicTargetCells_mem_carriers_of_mem_closedRegions
    m hn hab hxA hxB
  have hxACarrier := hxCarriers.1
  have hxBCarrier := hxCarriers.2
  have hxACarrierRaw := hxCarriers.1
  have hxBCarrierRaw := hxCarriers.2
  rw [(I.cyclicTargetAttachmentPresentation m a).carrier_eq,
    I.range_cyclicTargetAttachmentPresentation_shared,
    I.range_cyclicTargetAttachmentPresentation_exposed m hn] at hxACarrier
  rw [(I.cyclicTargetAttachmentPresentation m b).carrier_eq,
    I.range_cyclicTargetAttachmentPresentation_shared,
    I.range_cyclicTargetAttachmentPresentation_exposed m hn] at hxBCarrier
  have classifyAcut (c : LevelAddress n)
      (hc : c = a ∨ c = nextLevelAddress n a)
      (hxc : x ∈ range (I.indexedTargetAnnularCrosscut m c).path) :
      (b = nextLevelAddress n a ∧
          x ∈ range (I.indexedTargetAnnularCrosscut m b).path) ∨
        (a = nextLevelAddress n b ∧
          x ∈ range (I.indexedTargetAnnularCrosscut m a).path) := by
    by_cases hcb : c = b
    · rcases hc with hca | hcnext
      · exact False.elim (hab (hca.symm.trans hcb))
      · left
        exact ⟨hcb.symm.trans hcnext, hcb ▸ hxc⟩
    by_cases hcBnext : c = nextLevelAddress n b
    · rcases hc with hca | hcnext
      · right
        exact ⟨hca.symm.trans hcBnext, hca ▸ hxc⟩
      · exact False.elim <| hab <| nextLevelAddress_injective n <|
          hcnext.symm.trans hcBnext
    exact False.elim <| Set.disjoint_left.mp
      (I.other_indexedTargetCrosscut_disjoint_cellCarrier
        m hn b c hcb hcBnext) hxc hxBCarrierRaw
  have classifyBcut (c : LevelAddress n)
      (hc : c = b ∨ c = nextLevelAddress n b)
      (hxc : x ∈ range (I.indexedTargetAnnularCrosscut m c).path) :
      (b = nextLevelAddress n a ∧
          x ∈ range (I.indexedTargetAnnularCrosscut m b).path) ∨
        (a = nextLevelAddress n b ∧
          x ∈ range (I.indexedTargetAnnularCrosscut m a).path) := by
    by_cases hca : c = a
    · rcases hc with hcb | hcnext
      · exact False.elim (hab (hca.symm.trans hcb))
      · right
        exact ⟨hca.symm.trans hcnext, hca ▸ hxc⟩
    by_cases hcAnext : c = nextLevelAddress n a
    · rcases hc with hcb | hcnext
      · left
        exact ⟨hcb.symm.trans hcAnext, hcb ▸ hxc⟩
      · exact False.elim <| hab <| nextLevelAddress_injective n <|
          hcAnext.symm.trans hcnext
    exact False.elim <| Set.disjoint_left.mp
      (I.other_indexedTargetCrosscut_disjoint_cellCarrier
        m hn a c hca hcAnext) hxc hxACarrierRaw
  rcases hxACarrier with hxAInner | hxASecond | hxAOuter | hxAFirst
  · rcases hxBCarrier with hxBInner | hxBSecond | hxBOuter | hxBFirst
    · have hxEnds :=
        I.indexedTargetBoundarySplit_first_inter_subset_endpoints
          m hn hab ⟨hxAInner, hxBInner⟩
      rcases hxEnds with hxa | hxnext
      · subst x
        rcases (I.indexedTargetMark_mem_boundarySplit_first_iff
          m b a).mp hxBInner with hab' | haBnext
        · exact False.elim (hab hab')
        · right
          exact ⟨haBnext, Path.target_mem_range
            (I.indexedTargetAnnularCrosscut m a).path⟩
      · rw [Set.mem_singleton_iff] at hxnext
        subst x
        rcases (I.indexedTargetMark_mem_boundarySplit_first_iff
          m b (nextLevelAddress n a)).mp hxBInner with hnextb | hnextnext
        · left
          refine ⟨hnextb.symm, ?_⟩
          rw [← hnextb]
          exact Path.target_mem_range
            (I.indexedTargetAnnularCrosscut m
              (nextLevelAddress n a)).path
        · exact False.elim <| hab <| nextLevelAddress_injective n hnextnext
    · exact classifyBcut (nextLevelAddress n b) (Or.inr rfl) hxBSecond
    · have hxInnerCarrier : x ∈ (disk m).carrier := by
        simpa only [(disk m).carrier_toJordanCircle] using
          (I.indexedTargetBoundarySplit m a).first_range_subset_carrier hxAInner
      have hxOuterCarrier : x ∈ (disk (m + 1)).carrier := by
        rw [← (disk (m + 1)).carrier_toJordanCircle,
          ← (I.indexedTargetBoundarySplit (m + 1) b).cover]
        exact Or.inl hxBOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (disk_strictlyNested m)) hxInnerCarrier hxOuterCarrier
    · exact classifyBcut b (Or.inl rfl) hxBFirst
  · exact classifyAcut (nextLevelAddress n a) (Or.inr rfl) hxASecond
  · rcases hxBCarrier with hxBInner | hxBSecond | hxBOuter | hxBFirst
    · have hxInnerCarrier : x ∈ (disk m).carrier := by
        simpa only [(disk m).carrier_toJordanCircle] using
          (I.indexedTargetBoundarySplit m b).first_range_subset_carrier hxBInner
      have hxOuterCarrier : x ∈ (disk (m + 1)).carrier := by
        rw [← (disk (m + 1)).carrier_toJordanCircle,
          ← (I.indexedTargetBoundarySplit (m + 1) a).cover]
        exact Or.inl hxAOuter
      exact False.elim <| Set.disjoint_left.mp
        (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
          (disk_strictlyNested m)) hxInnerCarrier hxOuterCarrier
    · exact classifyBcut (nextLevelAddress n b) (Or.inr rfl) hxBSecond
    · have hxEnds :=
        I.indexedTargetBoundarySplit_first_inter_subset_endpoints
          (m + 1) hn hab ⟨hxAOuter, hxBOuter⟩
      rcases hxEnds with hxa | hxnext
      · subst x
        rcases (I.indexedTargetMark_mem_boundarySplit_first_iff
          (m + 1) b a).mp hxBOuter with hab' | haBnext
        · exact False.elim (hab hab')
        · right
          exact ⟨haBnext, Path.source_mem_range
            (I.indexedTargetAnnularCrosscut m a).path⟩
      · rw [Set.mem_singleton_iff] at hxnext
        subst x
        rcases (I.indexedTargetMark_mem_boundarySplit_first_iff
          (m + 1) b (nextLevelAddress n a)).mp hxBOuter with
          hnextb | hnextnext
        · left
          refine ⟨hnextb.symm, ?_⟩
          rw [← hnextb]
          exact Path.source_mem_range
            (I.indexedTargetAnnularCrosscut m
              (nextLevelAddress n a)).path
        · exact False.elim <| hab <| nextLevelAddress_injective n hnextnext
    · exact classifyBcut b (Or.inl rfl) hxBFirst
  · exact classifyAcut a (Or.inl rfl) hxAFirst

end JordanCircle.InitialAngularArcs

end

end Schoenflies
