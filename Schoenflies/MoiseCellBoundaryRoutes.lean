import Schoenflies.MoiseBandCellSeams
import Schoenflies.CyclicTargetCells
import Schoenflies.TwoBoundaryArcRigidity

/-!
# Marked boundary routes for recursive Moise cells

The boundary of a corrected Moise cell has three distinguished consecutive
arcs: its incoming adjacent-cell seam, its old synchronized crosscut, and its
outgoing adjacent-cell seam.  Their concatenation is an embedded arc.  The
matching standard target route consists of the initial radial cut, the inner
elementary boundary arc, and the successor radial cut.

Using the same nested concatenation on both sides is the key compatibility
device: the eventual disk homeomorphism will carry both adjacent seams, as
well as the old boundary arc, pointwise with their native parameters.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace ThreePiecePath

/-- Parameter on `(p.trans q).trans r` corresponding to `p`. -/
def firstCoordinate (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 4, by constructor <;> nlinarith [t.2.1, t.2.2]⟩

/-- Parameter on `(p.trans q).trans r` corresponding to `q`. -/
def middleCoordinate (t : unitInterval) : unitInterval :=
  ⟨1 / 4 + (t : ℝ) / 4, by
    constructor <;> nlinarith [t.2.1, t.2.2]⟩

/-- Parameter on `(p.trans q).trans r` corresponding to `r`. -/
def thirdCoordinate (t : unitInterval) : unitInterval :=
  ⟨1 / 2 + (t : ℝ) / 2, by
    constructor <;> nlinarith [t.2.1, t.2.2]⟩

theorem trans_trans_firstCoordinate
    {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (t : unitInterval) :
    ((p.trans q).trans r) (firstCoordinate t) = p t := by
  rw [Path.trans_apply]
  simp only [firstCoordinate]
  rw [dif_pos (by nlinarith [t.2.2]), Path.trans_apply]
  rw [dif_pos (by nlinarith [t.2.2])]
  congr 1
  apply Subtype.ext
  dsimp
  ring

theorem trans_trans_middleCoordinate
    {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (t : unitInterval) :
    ((p.trans q).trans r) (middleCoordinate t) = q t := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = 0 := Subtype.ext ht
    subst t
    rw [Path.trans_apply]
    simp only [middleCoordinate]
    rw [dif_pos (by norm_num), Path.trans_apply]
    rw [dif_pos (by norm_num)]
    have hendpoint : p 1 = q 0 := p.target.trans q.source.symm
    rw [← hendpoint]
    congr 1
    apply Subtype.ext
    norm_num
  · have htpos : 0 < (t : ℝ) :=
      lt_of_le_of_ne t.2.1 (Ne.symm ht)
    rw [Path.trans_apply]
    simp only [middleCoordinate]
    rw [dif_pos (by nlinarith [t.2.2]), Path.trans_apply]
    rw [dif_neg (by nlinarith)]
    congr 1
    apply Subtype.ext
    dsimp
    ring

theorem trans_trans_thirdCoordinate
    {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d)
    (t : unitInterval) :
    ((p.trans q).trans r) (thirdCoordinate t) = r t := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = 0 := Subtype.ext ht
    subst t
    rw [Path.trans_apply]
    simp only [thirdCoordinate]
    rw [dif_pos (by norm_num)]
    have hendpoint : (p.trans q) 1 = r 0 :=
      (p.trans q).target.trans r.source.symm
    rw [← hendpoint]
    congr 1
    apply Subtype.ext
    norm_num
  · have htpos : 0 < (t : ℝ) :=
      lt_of_le_of_ne t.2.1 (Ne.symm ht)
    rw [Path.trans_apply]
    simp only [thirdCoordinate]
    rw [dif_neg (by nlinarith)]
    congr 1
    apply Subtype.ext
    dsimp
    ring

end ThreePiecePath

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

/-- The seam inherited from the cyclic predecessor, with its target endpoint
written as the current cell's left synchronized point. -/
noncomputable def incomingMoiseBandSideSeamPath (a : LevelAddress n) :
    Path
      (L.adjacentMoiseBandInnerSeamPoint (prevLevelAddress n a) : Plane)
      (F.leftSynchronizedPoint a) :=
  (L.adjacentMoiseBandSideSeamPath (prevLevelAddress n a)).cast rfl (by
    simpa only [coe_adjacentMoiseBandParentPoint,
      nextLevelAddress_prevLevelAddress] using
      (F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint
        (prevLevelAddress n a)).symm)

theorem range_incomingMoiseBandSideSeamPath (a : LevelAddress n) :
    range (L.incomingMoiseBandSideSeamPath a) =
      L.adjacentMoiseBandSideSeam (prevLevelAddress n a) := by
  change range (L.adjacentMoiseBandSideSeamPath
    (prevLevelAddress n a)) = _
  exact L.range_adjacentMoiseBandSideSeamPath (prevLevelAddress n a)

theorem incomingMoiseBandSideSeamPath_injective
    (a : LevelAddress n) :
    Injective (L.incomingMoiseBandSideSeamPath a) := by
  simpa only [incomingMoiseBandSideSeamPath, Path.cast_coe] using
    L.adjacentMoiseBandSideSeamPath_injective (prevLevelAddress n a)

private theorem incomingSeam_subset_leftSide (a : LevelAddress n) :
    range (L.incomingMoiseBandSideSeamPath a) ⊆
      L.moiseBandLeftSideCarrier a := by
  rw [L.range_incomingMoiseBandSideSeamPath]
  intro x hx
  have := hx.2
  simpa only [nextLevelAddress_prevLevelAddress] using this

private theorem outgoingSeam_subset_rightSide (a : LevelAddress n) :
    range (L.adjacentMoiseBandSideSeamPath a) ⊆
      L.moiseBandRightSideCarrier a := by
  rw [L.range_adjacentMoiseBandSideSeamPath]
  exact Set.inter_subset_left

private theorem incomingSeam_inter_parent (a : LevelAddress n) :
    range (L.incomingMoiseBandSideSeamPath a) ∩
        range (F.synchronizedCrosscutPath a) =
      {F.leftSynchronizedPoint a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxIncoming, hxParent⟩
    have hx : x ∈ L.parentMoiseCarrier a ∩
        L.moiseBandLeftSideCarrier a := ⟨by
      rwa [L.parentMoiseCarrier_eq_crosscutRange],
      L.incomingSeam_subset_leftSide a hxIncoming⟩
    exact L.parentMoiseCarrier_inter_leftSideCarrier_subset a a hx
  · intro x hx
    have hxEq : x = F.leftSynchronizedPoint a :=
      Set.mem_singleton_iff.mp hx
    subst x
    constructor
    · rw [L.range_incomingMoiseBandSideSeamPath]
      have h := L.rightSynchronizedPoint_mem_adjacentMoiseBandSideSeam
        (prevLevelAddress n a)
      simpa only [nextLevelAddress_prevLevelAddress,
        F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint] using h
    · exact Path.source_mem_range (F.synchronizedCrosscutPath a)

private theorem parent_inter_outgoingSeam (a : LevelAddress n) :
    range (F.synchronizedCrosscutPath a) ∩
        range (L.adjacentMoiseBandSideSeamPath a) =
      {F.rightSynchronizedPoint a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxParent, hxOutgoing⟩
    have hx : x ∈ L.parentMoiseCarrier a ∩
        L.moiseBandRightSideCarrier a := ⟨by
      rwa [L.parentMoiseCarrier_eq_crosscutRange],
      L.outgoingSeam_subset_rightSide a hxOutgoing⟩
    exact L.parentMoiseCarrier_inter_rightSideCarrier_subset a a hx
  · intro x hx
    have hxEq : x = F.rightSynchronizedPoint a :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range (F.synchronizedCrosscutPath a), by
      rw [L.range_adjacentMoiseBandSideSeamPath]
      exact L.rightSynchronizedPoint_mem_adjacentMoiseBandSideSeam a⟩

private theorem disjoint_incomingSeam_outgoingSeam
    (a : LevelAddress n) :
    Disjoint (range (L.incomingMoiseBandSideSeamPath a))
      (range (L.adjacentMoiseBandSideSeamPath a)) := by
  exact (L.rawLeftSide_disjoint_rawRightSide a).mono
    (L.incomingSeam_subset_leftSide a)
    (L.outgoingSeam_subset_rightSide a)

/-- The marked source route, from the predecessor seam's inner endpoint to
the outgoing seam's inner endpoint. -/
noncomputable def moiseCellInnerBoundaryPath (a : LevelAddress n) :
    Path
      (L.adjacentMoiseBandInnerSeamPoint (prevLevelAddress n a) : Plane)
      (L.adjacentMoiseBandInnerSeamPoint a : Plane) :=
  ((L.incomingMoiseBandSideSeamPath a).trans
      (F.synchronizedCrosscutPath a)).trans
    (L.adjacentMoiseBandSideSeamPath a).symm

theorem range_moiseCellInnerBoundaryPath (a : LevelAddress n) :
    range (L.moiseCellInnerBoundaryPath a) =
      range (L.incomingMoiseBandSideSeamPath a) ∪
        (range (F.synchronizedCrosscutPath a) ∪
          range (L.adjacentMoiseBandSideSeamPath a).symm) := by
  rw [moiseCellInnerBoundaryPath, Path.trans_range, Path.trans_range]
  exact Set.union_assoc _ _ _

theorem moiseCellInnerBoundaryPath_firstCoordinate
    (a : LevelAddress n) (t : unitInterval) :
    L.moiseCellInnerBoundaryPath a (ThreePiecePath.firstCoordinate t) =
      L.incomingMoiseBandSideSeamPath a t := by
  exact ThreePiecePath.trans_trans_firstCoordinate _ _ _ t

theorem moiseCellInnerBoundaryPath_middleCoordinate
    (a : LevelAddress n) (t : unitInterval) :
    L.moiseCellInnerBoundaryPath a (ThreePiecePath.middleCoordinate t) =
      F.synchronizedCrosscutPath a t := by
  exact ThreePiecePath.trans_trans_middleCoordinate _ _ _ t

theorem moiseCellInnerBoundaryPath_thirdCoordinate
    (a : LevelAddress n) (t : unitInterval) :
    L.moiseCellInnerBoundaryPath a (ThreePiecePath.thirdCoordinate t) =
      (L.adjacentMoiseBandSideSeamPath a).symm t := by
  exact ThreePiecePath.trans_trans_thirdCoordinate _ _ _ t

theorem moiseCellInnerBoundaryPath_injective (a : LevelAddress n) :
    Injective (L.moiseCellInnerBoundaryPath a) := by
  have hfirst : Injective ((L.incomingMoiseBandSideSeamPath a).trans
      (F.synchronizedCrosscutPath a)) :=
    Path.trans_injective_of_range_inter
      (L.incomingMoiseBandSideSeamPath a)
      (F.synchronizedCrosscutPath a)
      (L.incomingMoiseBandSideSeamPath_injective a)
      (F.synchronizedCrosscutPath_injective a)
      (L.incomingSeam_inter_parent a)
  have hinter :
      range ((L.incomingMoiseBandSideSeamPath a).trans
          (F.synchronizedCrosscutPath a)) ∩
          range (L.adjacentMoiseBandSideSeamPath a).symm =
        {F.rightSynchronizedPoint a} := by
    rw [Path.trans_range, Path.symm_range,
      union_inter_distrib_right,
      Set.disjoint_iff_inter_eq_empty.mp
        (L.disjoint_incomingSeam_outgoingSeam a),
      L.parent_inter_outgoingSeam a, empty_union]
  exact Path.trans_injective_of_range_inter
    ((L.incomingMoiseBandSideSeamPath a).trans
      (F.synchronizedCrosscutPath a))
    (L.adjacentMoiseBandSideSeamPath a).symm
    hfirst
    ((L.adjacentMoiseBandSideSeamPath_injective a).comp
      unitInterval.symm_bijective.injective)
    hinter

theorem range_moiseCellInnerBoundaryPath_subset_carrier
    (a : LevelAddress n) :
    range (L.moiseCellInnerBoundaryPath a) ⊆
      (L.moiseBandPolygonalCircle a).carrier := by
  rw [L.moiseBandPolygonalCircle_carrier,
    L.range_moiseCellInnerBoundaryPath]
  apply Set.union_subset
  · exact (L.incomingSeam_subset_leftSide a).trans
      (L.moiseBandLeftSideCarrier_subset a)
  apply Set.union_subset
  · exact L.parentCrosscutRange_subset_moiseBandCarrier a
  · rintro x ⟨t, rfl⟩
    apply L.adjacentMoiseBandSideSeam_subset_left a
    rw [← L.range_adjacentMoiseBandSideSeamPath]
    exact ⟨unitInterval.symm t, rfl⟩

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The matching three-piece route in the standard radial target cell. -/
noncomputable def indexedTargetCellInnerBoundaryPath
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    Path (I.indexedTargetMark (m + 1) a)
      (I.indexedTargetMark (m + 1) (nextLevelAddress n a)) :=
  let D := I.cyclicTargetDecomposition m a
  (D.first.path.trans D.separator.innerSplit.first).trans
    D.second.path.symm

private theorem firstTargetCrosscut_inter_innerArc
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    let D := I.cyclicTargetDecomposition m a
    range D.first.path ∩ range D.separator.innerSplit.first =
      {D.first.innerPoint} := by
  let D := I.cyclicTargetDecomposition m a
  apply Set.Subset.antisymm
  · rintro x ⟨hxCut, hxArc⟩
    have hx : x ∈ range D.first.path ∩
        (StandardPolygonalCollars.disk m).carrier := ⟨hxCut, by
      simpa only [(StandardPolygonalCollars.disk m).carrier_toJordanCircle]
        using D.separator.innerFirst_range_subset hxArc⟩
    exact D.first.range_inter_inner ▸ hx
  · intro x hx
    have hxEq : x = D.first.innerPoint :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range _, Path.source_mem_range _⟩

private theorem innerArc_inter_secondTargetCrosscut
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    let D := I.cyclicTargetDecomposition m a
    range D.separator.innerSplit.first ∩ range D.second.path =
      {D.second.innerPoint} := by
  let D := I.cyclicTargetDecomposition m a
  apply Set.Subset.antisymm
  · rintro x ⟨hxArc, hxCut⟩
    have hx : x ∈ range D.second.path ∩
        (StandardPolygonalCollars.disk m).carrier := ⟨hxCut, by
      simpa only [(StandardPolygonalCollars.disk m).carrier_toJordanCircle]
        using D.separator.innerFirst_range_subset hxArc⟩
    exact D.second.range_inter_inner ▸ hx
  · intro x hx
    have hxEq : x = D.second.innerPoint :=
      Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Path.target_mem_range _, Path.target_mem_range _⟩

theorem indexedTargetCellInnerBoundaryPath_injective
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    Injective (I.indexedTargetCellInnerBoundaryPath m a) := by
  let D := I.cyclicTargetDecomposition m a
  have hfirst : Injective
      (D.first.path.trans D.separator.innerSplit.first) :=
    Path.trans_injective_of_range_inter
      D.first.path D.separator.innerSplit.first
      D.first.path_injective D.separator.innerSplit.first_injective
      (I.firstTargetCrosscut_inter_innerArc m a)
  have hcuts : Disjoint
      (range D.first.path) (range D.second.path) :=
    I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
      (nextLevelAddress_ne n a).symm
  have hinter :
      range (D.first.path.trans D.separator.innerSplit.first) ∩
          range D.second.path.symm = {D.second.innerPoint} := by
    rw [Path.trans_range, Path.symm_range,
      union_inter_distrib_right,
      Set.disjoint_iff_inter_eq_empty.mp hcuts,
      I.innerArc_inter_secondTargetCrosscut m a, empty_union]
  exact Path.trans_injective_of_range_inter
    (D.first.path.trans D.separator.innerSplit.first)
    D.second.path.symm
    hfirst
    (D.second.path_injective.comp unitInterval.symm_bijective.injective)
    hinter

theorem indexedTargetCellInnerBoundaryPath_firstCoordinate
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (t : unitInterval) :
    I.indexedTargetCellInnerBoundaryPath m a
        (ThreePiecePath.firstCoordinate t) =
      (I.indexedTargetAnnularCrosscut m a).path t := by
  let D := I.cyclicTargetDecomposition m a
  change ((D.first.path.trans D.separator.innerSplit.first).trans
    D.second.path.symm) (ThreePiecePath.firstCoordinate t) = _
  exact ThreePiecePath.trans_trans_firstCoordinate _ _ _ t

theorem indexedTargetCellInnerBoundaryPath_middleCoordinate
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (t : unitInterval) :
    I.indexedTargetCellInnerBoundaryPath m a
        (ThreePiecePath.middleCoordinate t) =
      (I.indexedTargetBoundarySplit m a).first t := by
  let D := I.cyclicTargetDecomposition m a
  change ((D.first.path.trans D.separator.innerSplit.first).trans
    D.second.path.symm) (ThreePiecePath.middleCoordinate t) = _
  exact ThreePiecePath.trans_trans_middleCoordinate _ _ _ t

theorem indexedTargetCellInnerBoundaryPath_thirdCoordinate
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (t : unitInterval) :
    I.indexedTargetCellInnerBoundaryPath m a
        (ThreePiecePath.thirdCoordinate t) =
      (I.indexedTargetAnnularCrosscut m
        (nextLevelAddress n a)).path.symm t := by
  let D := I.cyclicTargetDecomposition m a
  change ((D.first.path.trans D.separator.innerSplit.first).trans
    D.second.path.symm) (ThreePiecePath.thirdCoordinate t) = _
  exact ThreePiecePath.trans_trans_thirdCoordinate _ _ _ t

theorem range_indexedTargetCellInnerBoundaryPath_subset_carrier
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    range (I.indexedTargetCellInnerBoundaryPath m a) ⊆
      (I.cyclicTargetAttachmentPresentation m a).disk.carrier := by
  let D := I.cyclicTargetDecomposition m a
  change range ((D.first.path.trans
    D.separator.innerSplit.first).trans D.second.path.symm) ⊆ _
  rw [Path.trans_range, Path.trans_range]
  apply Set.union_subset
  · apply Set.union_subset
    · rintro x ⟨t, rfl⟩
      rw [← I.cyclicTargetAttachmentPresentation_exposedFirstCoordinate
        m a t]
      rw [(I.cyclicTargetAttachmentPresentation m a).carrier_eq]
      exact Or.inr ⟨_, rfl⟩
    · intro x hx
      change x ∈ range (I.indexedTargetBoundarySplit m a).first at hx
      rw [← I.range_cyclicTargetAttachmentPresentation_shared m a] at hx
      obtain ⟨t, rfl⟩ := hx
      exact (I.cyclicTargetAttachmentPresentation m a).shared_mem_carrier t
  · rintro x ⟨t, rfl⟩
    rw [← I.cyclicTargetAttachmentPresentation_exposedSecondCoordinate
      m a t]
    rw [(I.cyclicTargetAttachmentPresentation m a).carrier_eq]
    exact Or.inr ⟨_, rfl⟩

end JordanCircle.InitialAngularArcs

end

end Schoenflies
