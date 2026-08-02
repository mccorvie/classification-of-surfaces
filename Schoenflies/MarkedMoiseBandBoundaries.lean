import Schoenflies.MarkedMoiseBandGluing
import Schoenflies.MarkedMoiseCellOuterBoundaries
import Schoenflies.StandardRadialCollars

/-!
# Boundary restrictions of marked Moise band maps

The glued band homeomorphism has a canonically controlled restriction to its
parent polygon: the synchronized parent crosscuts are sent, with their native
parameters, to the elementary arcs of the inner standard polygon.  Packaging
that restriction as a homeomorphism makes it possible to prescribe the map on
a boundary shared with the preceding disk stage.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private abbrev parentDisk
    (_L : RecursiveInsideCollarStep.Later F hn) : PolygonalCircle :=
  F.synchronizedPolygonalCircle hn

private abbrev childDisk : PolygonalCircle :=
  L.next.family.forgetObstacle.synchronizedPolygonalCircle
    L.next.one_le_level

/-- Regard the parent carrier as a subtype of the actual source shell. -/
def markedMoiseParentCarrierInShell
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.parentDisk.carrier) :
    PolygonalCircle.closedShell L.parentDisk L.childDisk :=
  ⟨x, PolygonalCircle.innerCarrier_subset_closedShell _ _
    (L.parentClosedRegion_subset_childInteriorRegion houtward) x.2⟩

@[simp] theorem markedMoiseParentCarrierInShell_val
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.parentDisk.carrier) :
    (L.markedMoiseParentCarrierInShell houtward x : Plane) = x := by
  rfl

/-- The marked band map restricted to the parent carrier, with its codomain
tightened to the inner standard carrier. -/
def markedMoiseRawInnerBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    L.parentDisk.carrier → (disk m).carrier := fun x => by
  let y : Plane := L.markedMoiseBandHomeomorph m houtward
    (L.markedMoiseParentCarrierInShell houtward x)
  refine ⟨y, ?_⟩
  have hxUnion : (x : Plane) ∈
      ⋃ a : LevelAddress n, range (F.synchronizedCrosscutPath a) := by
    rw [← F.carrier_synchronizedPolygonalCircle hn]
    exact x.2
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨t, ht⟩ := Set.mem_range.mp hxa
  have hxBoth : (x : Plane) ∈ L.parentDisk.closedRegion ∩
      (L.moiseBandPolygonalCircle a).closedRegion := by
    rw [houtward a]
    exact ⟨t, ht⟩
  have hxCell : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).closedRegion := hxBoth.2
  have hmap := L.markedMoiseBandHomeomorph_apply m houtward a
    (L.markedMoiseParentCarrierInShell houtward x).2 hxCell
  have hcell := L.markedMoiseCellHomeomorph_apply_parentCrosscut m a t
  have hxEq : (x : Plane) = F.synchronizedCrosscutPath a t := ht.symm
  have harg :
      (⟨(L.markedMoiseParentCarrierInShell houtward x : Plane), hxCell⟩ :
        (L.moiseBandPolygonalCircle a).closedRegion) =
      ⟨F.synchronizedCrosscutPath a t, by simpa only [hxEq] using hxCell⟩ := by
    apply Subtype.ext
    exact hxEq
  have hyEq : y = (I.indexedTargetBoundarySplit m a).first t := by
    calc
      y = (L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseParentCarrierInShell houtward x) : Plane) := rfl
      _ = (L.markedMoiseCellHomeomorph m a
          ⟨(L.markedMoiseParentCarrierInShell houtward x : Plane),
            hxCell⟩ : Plane) := hmap
      _ = (L.markedMoiseCellHomeomorph m a
          ⟨F.synchronizedCrosscutPath a t,
            by simpa only [hxEq] using hxCell⟩ : Plane) := by rw [harg]
      _ = (I.indexedTargetBoundarySplit m a).first t := hcell
  rw [hyEq]
  simpa only [(disk m).carrier_toJordanCircle] using
    (I.indexedTargetBoundarySplit m a).first_range_subset_carrier
      ⟨t, rfl⟩

@[simp] theorem markedMoiseRawInnerBoundaryMap_val
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.parentDisk.carrier) :
    (L.markedMoiseRawInnerBoundaryMap m houtward x : Plane) =
      (L.markedMoiseBandHomeomorph m houtward
        (L.markedMoiseParentCarrierInShell houtward x) : Plane) := by
  simp only [markedMoiseRawInnerBoundaryMap]

theorem continuous_markedMoiseRawInnerBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Continuous (L.markedMoiseRawInnerBoundaryMap m houtward) := by
  apply continuous_induced_rng.mpr
  let inclusion : L.parentDisk.carrier →
      PolygonalCircle.closedShell L.parentDisk L.childDisk :=
    L.markedMoiseParentCarrierInShell houtward
  have hinclusion : Continuous inclusion :=
    continuous_subtype_val.subtype_mk _
  exact continuous_subtype_val.comp
    ((L.markedMoiseBandHomeomorph m houtward).continuous.comp hinclusion)
    |>.congr fun x => L.markedMoiseRawInnerBoundaryMap_val m houtward x |>.symm

theorem injective_markedMoiseRawInnerBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Injective (L.markedMoiseRawInnerBoundaryMap m houtward) := by
  intro x y hxy
  have hxyPlane := congrArg Subtype.val hxy
  have hE :
      L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseParentCarrierInShell houtward x) =
        L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseParentCarrierInShell houtward y) := by
    apply Subtype.ext
    simpa only [L.markedMoiseRawInnerBoundaryMap_val] using hxyPlane
  have hxyShell := (L.markedMoiseBandHomeomorph m houtward).injective hE
  apply Subtype.ext
  exact congrArg
    (fun z : PolygonalCircle.closedShell L.parentDisk L.childDisk =>
      (z : Plane)) hxyShell

theorem surjective_markedMoiseRawInnerBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Surjective (L.markedMoiseRawInnerBoundaryMap m houtward) := by
  intro y
  have hyUnion :=
    I.targetInnerCarrier_subset_iUnion_cyclicTargetCellShared m n y.2
  obtain ⟨a, hya⟩ := Set.mem_iUnion.mp hyUnion
  rw [I.range_cyclicTargetAttachmentPresentation_shared] at hya
  obtain ⟨t, ht⟩ := Set.mem_range.mp hya
  let x : L.parentDisk.carrier :=
    ⟨F.synchronizedCrosscutPath a t, by
      rw [F.carrier_synchronizedPolygonalCircle hn]
      exact Set.mem_iUnion.mpr ⟨a, ⟨t, rfl⟩⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  have hxBoth : (x : Plane) ∈ L.parentDisk.closedRegion ∩
      (L.moiseBandPolygonalCircle a).closedRegion := by
    rw [houtward a]
    exact ⟨t, rfl⟩
  have hxCell : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).closedRegion := hxBoth.2
  have harg :
      (⟨(L.markedMoiseParentCarrierInShell houtward x : Plane), hxCell⟩ :
        (L.moiseBandPolygonalCircle a).closedRegion) =
      ⟨F.synchronizedCrosscutPath a t, hxCell⟩ := by
    apply Subtype.ext
    rfl
  rw [L.markedMoiseRawInnerBoundaryMap_val]
  rw [L.markedMoiseBandHomeomorph_apply m houtward a
    (L.markedMoiseParentCarrierInShell houtward x).2 hxCell]
  rw [harg]
  exact (L.markedMoiseCellHomeomorph_apply_parentCrosscut m a t).trans ht

/-- The exact parent-boundary restriction of a marked Moise band map. -/
def markedMoiseRawInnerBoundaryHomeomorph
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    L.parentDisk.carrier ≃ₜ (disk m).carrier := by
  letI : CompactSpace L.parentDisk.carrier :=
    isCompact_iff_compactSpace.mp L.parentDisk.isCompact_carrier
  let e : L.parentDisk.carrier ≃ (disk m).carrier :=
    Equiv.ofBijective (L.markedMoiseRawInnerBoundaryMap m houtward)
      ⟨L.injective_markedMoiseRawInnerBoundaryMap m houtward,
        L.surjective_markedMoiseRawInnerBoundaryMap m houtward⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) (L.continuous_markedMoiseRawInnerBoundaryMap m houtward)

@[simp] theorem markedMoiseRawInnerBoundaryHomeomorph_apply
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.parentDisk.carrier) :
    (L.markedMoiseRawInnerBoundaryHomeomorph m houtward x : Plane) =
      (L.markedMoiseBandHomeomorph m houtward
        (L.markedMoiseParentCarrierInShell houtward x) : Plane) := by
  change (L.markedMoiseRawInnerBoundaryMap m houtward x : Plane) = _
  exact L.markedMoiseRawInnerBoundaryMap_val m houtward x

/-- Correct the marked band map so that it realizes an arbitrary prescribed
homeomorphism on the shared parent boundary. -/
def compatibleMarkedMoiseBandHomeomorph
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (b : L.parentDisk.carrier ≃ₜ (disk m).carrier) :
    PolygonalCircle.closedShell L.parentDisk L.childDisk ≃ₜ
      PolygonalCircle.closedShell (disk m) (disk (m + 1)) :=
  (L.markedMoiseBandHomeomorph m houtward).trans <|
    standardShellBoundaryAdjustment m
      ((L.markedMoiseRawInnerBoundaryHomeomorph m houtward).symm.trans b)

theorem compatibleMarkedMoiseBandHomeomorph_apply_innerCarrier
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (b : L.parentDisk.carrier ≃ₜ (disk m).carrier)
    (x : L.parentDisk.carrier) :
    (L.compatibleMarkedMoiseBandHomeomorph m houtward b
        (L.markedMoiseParentCarrierInShell houtward x) : Plane) = b x := by
  rw [compatibleMarkedMoiseBandHomeomorph, Homeomorph.trans_apply]
  have hraw :
      L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseParentCarrierInShell houtward x) =
        innerCarrierInClosedShell m
          (L.markedMoiseRawInnerBoundaryHomeomorph m houtward x) := by
    apply Subtype.ext
    exact (L.markedMoiseRawInnerBoundaryHomeomorph_apply m houtward x).symm
  rw [hraw, standardShellBoundaryAdjustment_apply_innerCarrier]
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

/-- Regard the child carrier as a subtype of the actual source shell. -/
def markedMoiseChildCarrierInShell
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.childDisk.carrier) :
    PolygonalCircle.closedShell L.parentDisk L.childDisk :=
  ⟨x, PolygonalCircle.outerCarrier_subset_closedShell _ _
    (L.parentClosedRegion_subset_childInteriorRegion houtward) x.2⟩

@[simp] theorem markedMoiseChildCarrierInShell_val
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.childDisk.carrier) :
    (L.markedMoiseChildCarrierInShell houtward x : Plane) = x := by
  rfl

/-- The raw marked band map restricted to the child carrier. -/
def markedMoiseRawOuterBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    L.childDisk.carrier → (disk (m + 1)).carrier := fun x => by
  let y : Plane := L.markedMoiseBandHomeomorph m houtward
    (L.markedMoiseChildCarrierInShell houtward x)
  refine ⟨y, ?_⟩
  have hxCells := L.childCircle_carrier_subset_iUnion_moiseBandCarrier x.2
  obtain ⟨a, hxaCarrier⟩ := Set.mem_iUnion.mp hxCells
  have hxCellCarrier : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).carrier := by
    rw [L.moiseBandPolygonalCircle_carrier]
    exact hxaCarrier
  have hxSecond :=
    L.childCarrier_inter_moiseBandCellCarrier_subset_boundarySplitSecond
      houtward a ⟨x.2, hxCellCarrier⟩
  obtain ⟨t, ht⟩ := Set.mem_range.mp hxSecond
  have hxCellClosed : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).closedRegion := by
    rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
    exact Or.inr hxCellCarrier
  have hmap := L.markedMoiseBandHomeomorph_apply m houtward a
    (L.markedMoiseChildCarrierInShell houtward x).2 hxCellClosed
  have harg :
      (⟨(L.markedMoiseChildCarrierInShell houtward x : Plane), hxCellClosed⟩ :
        (L.moiseBandPolygonalCircle a).closedRegion) =
      ⟨(L.moiseCellBoundarySplit a).second t, by
        simpa only [← ht] using hxCellClosed⟩ := by
    apply Subtype.ext
    exact ht.symm
  have hyEq : y = (I.indexedTargetCellBoundarySplit m a).second t := by
    calc
      y = (L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseChildCarrierInShell houtward x) : Plane) := rfl
      _ = (L.markedMoiseCellHomeomorph m a
          ⟨(L.markedMoiseChildCarrierInShell houtward x : Plane),
            hxCellClosed⟩ : Plane) := hmap
      _ = (L.markedMoiseCellHomeomorph m a
          ⟨(L.moiseCellBoundarySplit a).second t,
            by simpa only [← ht] using hxCellClosed⟩ : Plane) := by rw [harg]
      _ = (I.indexedTargetCellBoundarySplit m a).second t :=
        L.markedMoiseCellHomeomorph_apply_outerBoundaryPath m a t
  rw [hyEq]
  exact I.range_indexedTargetCellBoundarySplit_second_subset_outerCarrier
    m hn a ⟨t, rfl⟩

@[simp] theorem markedMoiseRawOuterBoundaryMap_val
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.childDisk.carrier) :
    (L.markedMoiseRawOuterBoundaryMap m houtward x : Plane) =
      (L.markedMoiseBandHomeomorph m houtward
        (L.markedMoiseChildCarrierInShell houtward x) : Plane) := by
  simp only [markedMoiseRawOuterBoundaryMap]

theorem continuous_markedMoiseRawOuterBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Continuous (L.markedMoiseRawOuterBoundaryMap m houtward) := by
  apply continuous_induced_rng.mpr
  let inclusion : L.childDisk.carrier →
      PolygonalCircle.closedShell L.parentDisk L.childDisk :=
    L.markedMoiseChildCarrierInShell houtward
  have hinclusion : Continuous inclusion :=
    continuous_subtype_val.subtype_mk _
  exact continuous_subtype_val.comp
    ((L.markedMoiseBandHomeomorph m houtward).continuous.comp hinclusion)
    |>.congr fun x => L.markedMoiseRawOuterBoundaryMap_val m houtward x |>.symm

theorem injective_markedMoiseRawOuterBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Injective (L.markedMoiseRawOuterBoundaryMap m houtward) := by
  intro x y hxy
  have hxyPlane := congrArg Subtype.val hxy
  have hE :
      L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseChildCarrierInShell houtward x) =
        L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseChildCarrierInShell houtward y) := by
    apply Subtype.ext
    simpa only [L.markedMoiseRawOuterBoundaryMap_val] using hxyPlane
  have hxyShell := (L.markedMoiseBandHomeomorph m houtward).injective hE
  apply Subtype.ext
  exact congrArg
    (fun z : PolygonalCircle.closedShell L.parentDisk L.childDisk =>
      (z : Plane)) hxyShell

theorem surjective_markedMoiseRawOuterBoundaryMap
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    Surjective (L.markedMoiseRawOuterBoundaryMap m houtward) := by
  intro y
  have hyUnion :=
    I.targetInnerCarrier_subset_iUnion_cyclicTargetCellShared (m + 1) n y.2
  obtain ⟨a, hya⟩ := Set.mem_iUnion.mp hyUnion
  rw [I.range_cyclicTargetAttachmentPresentation_shared,
    ← I.range_indexedTargetCellBoundarySplit_second m hn a] at hya
  obtain ⟨t, ht⟩ := Set.mem_range.mp hya
  have hxChild :=
    L.range_moiseCellBoundarySplit_second_subset_childCarrier
      houtward a ⟨t, rfl⟩
  let x : L.childDisk.carrier :=
    ⟨(L.moiseCellBoundarySplit a).second t, hxChild⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  rw [L.markedMoiseRawOuterBoundaryMap_val]
  have hxCellCarrier : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).carrier := by
    simpa only [← (L.moiseBandPolygonalCircle a).carrier_toJordanCircle]
      using (L.moiseCellBoundarySplit a).second_range_subset_carrier
        ⟨t, rfl⟩
  have hxCellClosed : (x : Plane) ∈
      (L.moiseBandPolygonalCircle a).closedRegion := by
    rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
    exact Or.inr hxCellCarrier
  rw [L.markedMoiseBandHomeomorph_apply m houtward a
    (L.markedMoiseChildCarrierInShell houtward x).2 hxCellClosed]
  have harg :
      (⟨(L.markedMoiseChildCarrierInShell houtward x : Plane), hxCellClosed⟩ :
        (L.moiseBandPolygonalCircle a).closedRegion) =
      ⟨(L.moiseCellBoundarySplit a).second t, hxCellClosed⟩ := by
    apply Subtype.ext
    rfl
  rw [harg]
  exact (L.markedMoiseCellHomeomorph_apply_outerBoundaryPath m a t).trans ht

/-- The outer-boundary restriction of the raw marked band map. -/
def markedMoiseRawOuterBoundaryHomeomorph
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c)) :
    L.childDisk.carrier ≃ₜ (disk (m + 1)).carrier := by
  letI : CompactSpace L.childDisk.carrier :=
    isCompact_iff_compactSpace.mp L.childDisk.isCompact_carrier
  let e : L.childDisk.carrier ≃ (disk (m + 1)).carrier :=
    Equiv.ofBijective (L.markedMoiseRawOuterBoundaryMap m houtward)
      ⟨L.injective_markedMoiseRawOuterBoundaryMap m houtward,
        L.surjective_markedMoiseRawOuterBoundaryMap m houtward⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) (L.continuous_markedMoiseRawOuterBoundaryMap m houtward)

@[simp] theorem markedMoiseRawOuterBoundaryHomeomorph_apply
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (x : L.childDisk.carrier) :
    (L.markedMoiseRawOuterBoundaryHomeomorph m houtward x : Plane) =
      (L.markedMoiseBandHomeomorph m houtward
        (L.markedMoiseChildCarrierInShell houtward x) : Plane) := by
  change (L.markedMoiseRawOuterBoundaryMap m houtward x : Plane) = _
  exact L.markedMoiseRawOuterBoundaryMap_val m houtward x

/-- The boundary homeomorphism induced on the child edge of a compatible
marked Moise band. -/
def compatibleMarkedMoiseOuterBoundaryHomeomorph
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (b : L.parentDisk.carrier ≃ₜ (disk m).carrier) :
    L.childDisk.carrier ≃ₜ (disk (m + 1)).carrier :=
  (L.markedMoiseRawOuterBoundaryHomeomorph m houtward).trans <|
    standardShellOuterBoundaryAdjustment m
      ((L.markedMoiseRawInnerBoundaryHomeomorph m houtward).symm.trans b)

theorem compatibleMarkedMoiseBandHomeomorph_apply_outerCarrier
    (m : ℕ)
    (houtward : ∀ c : LevelAddress n,
      L.parentDisk.closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (b : L.parentDisk.carrier ≃ₜ (disk m).carrier)
    (x : L.childDisk.carrier) :
    (L.compatibleMarkedMoiseBandHomeomorph m houtward b
        (L.markedMoiseChildCarrierInShell houtward x) : Plane) =
      L.compatibleMarkedMoiseOuterBoundaryHomeomorph m houtward b x := by
  rw [compatibleMarkedMoiseBandHomeomorph, Homeomorph.trans_apply]
  have hraw :
      L.markedMoiseBandHomeomorph m houtward
          (L.markedMoiseChildCarrierInShell houtward x) =
        outerCarrierInClosedShell m
          (L.markedMoiseRawOuterBoundaryHomeomorph m houtward x) := by
    apply Subtype.ext
    exact (L.markedMoiseRawOuterBoundaryHomeomorph_apply m houtward x).symm
  rw [hraw, standardShellBoundaryAdjustment_apply_outerCarrier]
  rfl

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
