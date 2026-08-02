import Schoenflies.LocalizedCellGluing

/-!
# Coverage by the standard target collar cells

The glued localized-cell map initially lands in the finite union of its
standard target cells.  This file proves that the finite union is the entire
standard polygonal shell.  The argument mirrors source-cell coverage: after
adjoining the inner standard disk, every non-exceptional shared or radial seam
is locally swallowed, so Jordan-region recognition identifies the result with
the outer standard disk.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev targetInnerDisk (_I : J.InitialAngularArcs)
    (k : ℕ) : PolygonalCircle :=
  StandardPolygonalCollars.disk (k + 1)

private abbrev targetOuterDisk (_I : J.InitialAngularArcs)
    (k : ℕ) : PolygonalCircle :=
  StandardPolygonalCollars.disk (k + 2)

private abbrev targetCell (k : ℕ) (a : LevelAddress k) : Set Plane :=
  (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion

/-- The inner standard disk together with all standard target cells. -/
def localizedTargetFilledDisk (k : ℕ) : Set Plane :=
  (I.targetInnerDisk k).closedRegion ∪
    ⋃ a : LevelAddress k, I.targetCell k a

theorem isCompact_localizedTargetFilledDisk (k : ℕ) :
    IsCompact (I.localizedTargetFilledDisk k) := by
  exact (I.targetInnerDisk k).isCompact_closedRegion.union <|
    isCompact_iUnion fun a =>
      (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.isCompact_closedRegion

theorem localizedTargetFilledDisk_subset_outerClosedRegion
    (k : ℕ) (hk : 1 ≤ k) :
    I.localizedTargetFilledDisk k ⊆ (I.targetOuterDisk k).closedRegion := by
  apply Set.union_subset
  · exact PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
      (I.targetInnerDisk k) (I.targetOuterDisk k)
      (StandardPolygonalCollars.disk_strictlyNested (k + 1))
  · exact Set.iUnion_subset fun a =>
      (I.localizedCutFreeCellData k a).targetDisk_closedRegion_subset_outerDisk hk

theorem closure_interior_localizedTargetFilledDisk (k : ℕ) :
    closure (interior (I.localizedTargetFilledDisk k)) =
      I.localizedTargetFilledDisk k := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset
      (I.isCompact_localizedTargetFilledDisk k).isClosed
  · intro x hx
    rcases hx with hxInner | hxCells
    · change x ∈ closure (I.targetInnerDisk k).interiorRegion at hxInner
      apply closure_mono _ hxInner
      apply interior_maximal
      · intro y hy
        left
        rw [(I.targetInnerDisk k).closedRegion_eq_union]
        exact Or.inl hy
      · exact (I.targetInnerDisk k).isOpen_interiorRegion
    · obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxCells
      change x ∈ closure
        (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.interiorRegion at hxa
      apply closure_mono _ hxa
      apply interior_maximal
      · intro y hy
        right
        apply Set.mem_iUnion.mpr
        refine ⟨a, ?_⟩
        change y ∈
          (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion
        rw [(I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion_eq_union]
        exact Or.inl hy
      · exact (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.isOpen_interiorRegion

/-- Surjectivity of the glued inner-boundary map transports source shared-arc
coverage to the shared arcs of the standard target cells. -/
theorem targetInnerCarrier_subset_iUnion_targetCellShared
    (k : ℕ) (hk : 1 ≤ k) :
    (I.targetInnerDisk k).carrier ⊆
      ⋃ a : LevelAddress k,
        range (I.localizedCutFreeCellData k a).targetAttachmentPresentation.shared := by
  intro y hy
  have hyRange : y ∈ Set.range (I.localizedInnerBoundaryEmbedding k hk) := by
    rw [I.range_localizedInnerBoundaryEmbedding k hk]
    exact hy
  obtain ⟨x, rfl⟩ := hyRange
  have hxInner : (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk (k + 1)).carrier := by
    simpa only
      [(I.localizedMarkedPolygonalDisk (k + 1)).carrier_toJordanCircle] using x.2
  obtain ⟨a, hxShared⟩ := Set.mem_iUnion.mp <|
    I.innerCarrier_subset_iUnion_localizedCellShared k hk hxInner
  obtain ⟨t, ht⟩ := hxShared
  apply Set.mem_iUnion.mpr
  refine ⟨a, t, ?_⟩
  have hxShell : (x : Plane) ∈ PolygonalCircle.closedShell
      (I.localizedMarkedPolygonalDisk (k + 1))
      (I.localizedMarkedPolygonalDisk (k + 2)) :=
    PolygonalCircle.innerCarrier_subset_closedShell _ _
      (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)) hxInner
  have hxCell : (x : Plane) ∈
      (I.localizedCutFreeCellData k a).disk.closedRegion := by
    rw [← ht]
    exact (I.localizedCutFreeCellData k a).attachmentPresentation.shared_mem_closedRegion t
  rw [localizedInnerBoundaryEmbedding]
  rw [I.localizedShellToTargetCellUnionHomeomorph_apply
    k hk a hxShell hxCell]
  symm
  calc
    ((I.localizedCutFreeCellData k a).cellHomeomorph
        ⟨(x : Plane), hxCell⟩ : Plane) =
        ((I.localizedCutFreeCellData k a).cellHomeomorph
          ⟨(I.localizedCutFreeCellData k a).attachmentPresentation.shared t,
            (I.localizedCutFreeCellData k a).attachmentPresentation.shared_mem_closedRegion t⟩ :
              Plane) := by
          apply congrArg (fun z =>
            ((I.localizedCutFreeCellData k a).cellHomeomorph z : Plane))
          exact Subtype.ext ht.symm
    _ = (I.localizedCutFreeCellData k a).targetAttachmentPresentation.shared t :=
      (I.localizedCutFreeCellData k a).cellHomeomorph_apply_shared t

/-- The finite set where a target seam meets an inner polygon vertex or a
radial-cut endpoint. -/
def localizedTargetCellExceptionalSet (k : ℕ) : Set Plane :=
  range (I.targetInnerDisk k).vertex ∪
    ⋃ a : LevelAddress k,
      ({(I.levelTargetAnnularCrosscut k a).innerPoint,
        (I.levelTargetAnnularCrosscut k a).outerPoint} : Set Plane)

theorem localizedTargetCellExceptionalSet_finite (k : ℕ) :
    (I.localizedTargetCellExceptionalSet k).Finite := by
  have hcuts : (⋃ a : LevelAddress k,
      ({(I.levelTargetAnnularCrosscut k a).innerPoint,
        (I.levelTargetAnnularCrosscut k a).outerPoint} : Set Plane)).Finite :=
    Set.finite_iUnion fun _ => by simp
  exact (Set.finite_range (I.targetInnerDisk k).vertex).union hcuts

namespace LocalizedCutFreeCellData

variable {I : J.InitialAngularArcs} {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

/-- Away from the finite vertex set, the standard inner polygon and one
target cell lie on opposite sides of their common locally straight arc. -/
theorem targetShared_mem_interior_localizedTargetFilledDisk
    (hk : 1 ≤ k) {p : Plane}
    (hpShared : p ∈ range C.targetAttachmentPresentation.shared)
    (hpExceptional : p ∉ I.localizedTargetCellExceptionalSet k)
    (hcanonical : C = I.localizedCutFreeCellData k a) :
    p ∈ interior (I.localizedTargetFilledDisk k) := by
  subst C
  let C : I.LocalizedCutFreeCellData k a :=
    I.localizedCutFreeCellData k a
  have hpNotVertex : p ∉ range (I.targetInnerDisk k).vertex := by
    intro hp
    exact hpExceptional (Or.inl hp)
  obtain ⟨i, hpOpen⟩ :=
    PolygonalCircle.exists_openEdge_of_mem_carrier_not_vertex
      (I.targetInnerDisk k)
      (by
        rw [C.range_targetAttachmentPresentation_shared] at hpShared
        exact C.targetSeparator.innerFirst_range_subset hpShared)
      hpNotVertex
  obtain ⟨rBase, hrBase, hlocalBase⟩ :=
    polygonalCircle_exists_local_determinantLine
      (I.targetInnerDisk k) hpOpen
  let d : Plane :=
    (I.targetInnerDisk k).vertex (i + 1) -
      (I.targetInnerDisk k).vertex i
  let B : Set Plane := range C.targetAttachmentPresentation.shared
  let R : Set Plane := range (C.targetBoundarySplit (k + 1)).second
  have hbaseCarrier : (I.targetInnerDisk k).carrier = B ∪ R := by
    dsimp only [B, R]
    rw [C.range_targetAttachmentPresentation_shared,
      ← (I.targetInnerDisk k).carrier_toJordanCircle]
    exact (C.targetBoundarySplit (k + 1)).cover.symm
  have hpNotR : p ∉ R := by
    intro hpR
    have hpEndsRaw : p ∈
        ({StandardPolygonalCollars.homothetyPoint
            (StandardPolygonalCollars.radius (k + 1))
            (I.levelTargetBoundaryPoint a),
          StandardPolygonalCollars.homothetyPoint
            (StandardPolygonalCollars.radius (k + 1))
            (I.levelTargetBoundaryPoint C.next)} : Set Plane) := by
      rw [← (C.targetBoundarySplit (k + 1)).overlap]
      exact ⟨by
        rw [← C.range_targetAttachmentPresentation_shared]
        exact hpShared, hpR⟩
    have hpEnds : p ∈
        ({(I.levelTargetAnnularCrosscut k a).innerPoint,
          (I.levelTargetAnnularCrosscut k C.next).innerPoint} :
            Set Plane) := by
      simpa only [JordanCircle.InitialAngularArcs.levelTargetAnnularCrosscut,
        JordanCircle.InitialAngularArcs.levelTargetInnerMark] using hpEndsRaw
    rcases hpEnds with hpFirst | hpSecond
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr ⟨a, Or.inl hpFirst⟩
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr
        ⟨C.next, Or.inl (Set.mem_singleton_iff.mp hpSecond)⟩
  have hlocalB : ∃ r : ℝ, 0 < r ∧
      ball p r ∩ B = ball p r ∩ determinantLine p d := by
    apply exists_local_determinantLine_of_union_compact_avoid
      (C := R)
    · rw [← hbaseCarrier]
      exact ⟨rBase, hrBase, hlocalBase⟩
    · exact isCompact_range
        (C.targetBoundarySplit (k + 1)).second.continuous
    · exact hpNotR
  let E : Set Plane := range C.targetAttachmentPresentation.exposed
  have hpNotE : p ∉ E := by
    intro hpE
    have hpEnds : p ∈
        ({C.targetAttachmentPresentation.startPoint,
          C.targetAttachmentPresentation.endPoint} : Set Plane) := by
      rw [← C.targetAttachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpE⟩
    have hstart : C.targetAttachmentPresentation.startPoint =
        C.targetDecomposition.first.innerPoint := by
      classical
      by_cases h : C.targetFirstAlternative
      · rw [LocalizedCutFreeCellData.targetAttachmentPresentation, dif_pos h]
        rfl
      · rw [LocalizedCutFreeCellData.targetAttachmentPresentation, dif_neg h]
        rfl
    have hend : C.targetAttachmentPresentation.endPoint =
        C.targetDecomposition.second.innerPoint := by
      classical
      by_cases h : C.targetFirstAlternative
      · rw [LocalizedCutFreeCellData.targetAttachmentPresentation, dif_pos h]
        rfl
      · rw [LocalizedCutFreeCellData.targetAttachmentPresentation, dif_neg h]
        rfl
    rw [hstart, hend] at hpEnds
    change p ∈
      ({(I.levelTargetAnnularCrosscut k a).innerPoint,
        (I.levelTargetAnnularCrosscut k C.next).innerPoint} :
          Set Plane) at hpEnds
    rcases hpEnds with hpFirst | hpSecond
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr ⟨a, Or.inl hpFirst⟩
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr
        ⟨C.next, Or.inl (Set.mem_singleton_iff.mp hpSecond)⟩
  obtain ⟨rCell, hrCell, hlocalCell⟩ :=
    exists_local_determinantLine_union_of_compact_avoid hlocalB
      (isCompact_range C.targetAttachmentPresentation.exposed.continuous)
      hpNotE
  have hlocalCell' :
      ball p rCell ∩ C.targetAttachmentPresentation.disk.carrier =
        ball p rCell ∩ determinantLine p d := by
    rw [C.targetAttachmentPresentation.carrier_eq]
    exact hlocalCell
  have hdisjoint : Disjoint
      (I.targetInnerDisk k).toJordanCircle.inside
      C.targetAttachmentPresentation.disk.toJordanCircle.inside := by
    simpa only [(I.targetInnerDisk k).inside_toJordanCircle,
      C.targetAttachmentPresentation.disk.inside_toJordanCircle] using
        (C.targetInnerDisk_disjoint_targetDiskInterior hk).mono_left
          (by
            rw [(I.targetInnerDisk k).closedRegion_eq_union]
            exact Set.subset_union_left)
  let r := min rBase rCell
  have hr : 0 < r := lt_min hrBase hrCell
  have hlocalBase' :
      ball p r ∩ (I.targetInnerDisk k).toJordanCircle.carrier =
        ball p r ∩ determinantLine p d := by
    rw [(I.targetInnerDisk k).carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_left _ _) hlocalBase
  have hlocalCell'' :
      ball p r ∩ C.targetAttachmentPresentation.disk.toJordanCircle.carrier =
        ball p r ∩ determinantLine p d := by
    rw [C.targetAttachmentPresentation.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_right _ _) hlocalCell'
  have hpUnion :=
    JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
      hdisjoint hr
      (by
        rw [(I.targetInnerDisk k).carrier_toJordanCircle]
        rw [C.range_targetAttachmentPresentation_shared] at hpShared
        exact C.targetSeparator.innerFirst_range_subset hpShared)
      hlocalBase' hlocalCell''
  apply interior_mono _ hpUnion
  rw [(I.targetInnerDisk k).inside_toJordanCircle,
    C.targetAttachmentPresentation.disk.inside_toJordanCircle]
  change (I.targetInnerDisk k).closedRegion ∪
      C.targetAttachmentPresentation.disk.closedRegion ⊆
    I.localizedTargetFilledDisk k
  apply Set.union_subset Set.subset_union_left
  intro x hx
  right
  exact Set.mem_iUnion.mpr ⟨a, hx⟩

/-- Away from its endpoints, a standard radial cut is swallowed by its two
cyclically adjacent target cells. -/
theorem targetSuccessorCut_mem_interior_localizedTargetFilledDisk
    (k : ℕ) (hk : 1 ≤ k) (a : LevelAddress k) {p : Plane}
    (hpCut : p ∈ range
      (I.levelTargetAnnularCrosscut k
        (I.levelLocalizedSuccessor k a)).path)
    (hpExceptional : p ∉ I.localizedTargetCellExceptionalSet k) :
    p ∈ interior (I.localizedTargetFilledDisk k) := by
  let b : LevelAddress k := I.levelLocalizedSuccessor k a
  let C : I.LocalizedCutFreeCellData k a :=
    I.localizedCutFreeCellData k a
  let D : I.LocalizedCutFreeCellData k b :=
    I.localizedCutFreeCellData k b
  have hab : a ≠ b := (I.levelLocalizedSuccessor_ne k a).symm
  have hCnext : C.next = b := C.next_eq
  have hCSecond : range C.targetDecomposition.second.path =
      range (I.levelTargetAnnularCrosscut k b).path := by
    change range (I.levelTargetAnnularCrosscut k C.next).path = _
    rw [hCnext]
  have hDFirst : range D.targetDecomposition.first.path =
      range (I.levelTargetAnnularCrosscut k b).path := by
    rfl
  have hpNotInnerPoint (c : LevelAddress k) :
      p ≠ (I.levelTargetAnnularCrosscut k c).innerPoint := by
    intro hp
    apply hpExceptional
    exact Or.inr <| Set.mem_iUnion.mpr ⟨c, Or.inl hp⟩
  have hpNotOuterPoint (c : LevelAddress k) :
      p ≠ (I.levelTargetAnnularCrosscut k c).outerPoint := by
    intro hp
    apply hpExceptional
    exact Or.inr <| Set.mem_iUnion.mpr ⟨c, Or.inr hp⟩
  have houterInner :
      (I.levelTargetAnnularCrosscut k b).outerPoint ≠
        (I.levelTargetAnnularCrosscut k b).innerPoint := by
    exact I.levelTargetOuterMark_ne_innerMark k b
  have hcutRange :
      range (I.levelTargetAnnularCrosscut k b).path =
        segment ℝ (I.levelTargetAnnularCrosscut k b).outerPoint
          (I.levelTargetAnnularCrosscut k b).innerPoint := by
    exact Path.range_segment _ _
  have hpSegment : p ∈ segment ℝ
      (I.levelTargetAnnularCrosscut k b).outerPoint
      (I.levelTargetAnnularCrosscut k b).innerPoint := by
    rw [← hcutRange]
    exact hpCut
  have hpOpen : p ∈ openSegment ℝ
      (I.levelTargetAnnularCrosscut k b).outerPoint
      (I.levelTargetAnnularCrosscut k b).innerPoint :=
    mem_openSegment_of_ne_left_right
      (hpNotOuterPoint b).symm (hpNotInnerPoint b).symm hpSegment
  let direction : Plane :=
    (I.levelTargetAnnularCrosscut k b).innerPoint -
      (I.levelTargetAnnularCrosscut k b).outerPoint
  have hlocalCut : ∃ r : ℝ, 0 < r ∧
      ball p r ∩ range (I.levelTargetAnnularCrosscut k b).path =
        ball p r ∩ determinantLine p direction := by
    rw [hcutRange]
    exact exists_local_determinantLine_segment houterInner hpOpen
  have hpCExposed :
      p ∈ range C.targetAttachmentPresentation.exposed := by
    rw [C.range_targetAttachmentPresentation_exposed hk]
    left
    change p ∈ range (I.levelTargetAnnularCrosscut k C.next).path
    rwa [hCnext]
  have hpNotCShared :
      p ∉ range C.targetAttachmentPresentation.shared := by
    intro hpShared
    have hpEnds : p ∈
        ({C.targetAttachmentPresentation.startPoint,
          C.targetAttachmentPresentation.endPoint} : Set Plane) := by
      rw [← C.targetAttachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpCExposed⟩
    have hstart : C.targetAttachmentPresentation.startPoint =
        C.targetDecomposition.first.innerPoint := by
      classical
      rw [LocalizedCutFreeCellData.targetAttachmentPresentation,
        dif_pos (C.targetFirstAlternative_of_one_le hk)]
      rfl
    have hend : C.targetAttachmentPresentation.endPoint =
        C.targetDecomposition.second.innerPoint := by
      classical
      rw [LocalizedCutFreeCellData.targetAttachmentPresentation,
        dif_pos (C.targetFirstAlternative_of_one_le hk)]
      rfl
    rw [hstart, hend] at hpEnds
    change p ∈
      ({(I.levelTargetAnnularCrosscut k a).innerPoint,
        (I.levelTargetAnnularCrosscut k C.next).innerPoint} :
          Set Plane) at hpEnds
    rcases hpEnds with hpFirst | hpSecond
    · exact hpNotInnerPoint a hpFirst
    · exact hpNotInnerPoint C.next
        (Set.mem_singleton_iff.mp hpSecond)
  have hpNotCOuter :
      p ∉ range (C.targetBoundarySplit (k + 2)).first := by
    intro hpOuter
    have hpMeet : p ∈
        range (I.levelTargetAnnularCrosscut k b).path ∩
          (I.targetOuterDisk k).carrier := by
      refine ⟨hpCut, ?_⟩
      rw [← (I.targetOuterDisk k).carrier_toJordanCircle,
        ← (C.targetBoundarySplit (k + 2)).cover]
      exact Or.inl hpOuter
    rw [(I.levelTargetAnnularCrosscut k b).range_inter_outer] at hpMeet
    exact hpNotOuterPoint b (Set.mem_singleton_iff.mp hpMeet)
  have hpNotCFirst :
      p ∉ range C.targetDecomposition.first.path := by
    intro hpFirst
    exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelTargetAnnularCrosscut k
        (I.levelLocalizedSuccessor_ne k a)) hpCut hpFirst
  have hcompactCShared :
      IsCompact (range C.targetAttachmentPresentation.shared) :=
    isCompact_range C.targetAttachmentPresentation.shared.continuous
  have hcompactCOuter :
      IsCompact (range (C.targetBoundarySplit (k + 2)).first) :=
    isCompact_range (C.targetBoundarySplit (k + 2)).first.continuous
  have hcompactCFirst :
      IsCompact (range C.targetDecomposition.first.path) :=
    isCompact_range C.targetDecomposition.first.path.continuous
  obtain ⟨rC, hrC, hlocalCraw⟩ :=
    exists_local_determinantLine_union_of_compact_avoid
      (exists_local_determinantLine_union_of_compact_avoid
        (exists_local_determinantLine_union_of_compact_avoid hlocalCut
          hcompactCShared hpNotCShared)
        hcompactCOuter hpNotCOuter)
      hcompactCFirst hpNotCFirst
  have hcarrierC : C.targetAttachmentPresentation.disk.carrier =
      (((range (I.levelTargetAnnularCrosscut k b).path ∪
          range C.targetAttachmentPresentation.shared) ∪
        range (C.targetBoundarySplit (k + 2)).first) ∪
          range C.targetDecomposition.first.path) := by
    rw [C.targetAttachmentPresentation.carrier_eq,
      C.range_targetAttachmentPresentation_exposed hk, hCSecond]
    ext x
    constructor
    · rintro (hxShared | hxCut | hxOuter | hxFirst)
      · exact Or.inl (Or.inl (Or.inr hxShared))
      · exact Or.inl (Or.inl (Or.inl hxCut))
      · exact Or.inl (Or.inr hxOuter)
      · exact Or.inr hxFirst
    · rintro (((hxCut | hxShared) | hxOuter) | hxFirst)
      · exact Or.inr (Or.inl hxCut)
      · exact Or.inl hxShared
      · exact Or.inr (Or.inr (Or.inl hxOuter))
      · exact Or.inr (Or.inr (Or.inr hxFirst))
  have hlocalC :
      ball p rC ∩ C.targetAttachmentPresentation.disk.carrier =
        ball p rC ∩ determinantLine p direction := by
    rw [hcarrierC]
    exact hlocalCraw
  have hpDExposed :
      p ∈ range D.targetAttachmentPresentation.exposed := by
    rw [D.range_targetAttachmentPresentation_exposed hk]
    exact Or.inr (Or.inr hpCut)
  have hpNotDShared :
      p ∉ range D.targetAttachmentPresentation.shared := by
    intro hpShared
    have hpEnds : p ∈
        ({D.targetAttachmentPresentation.startPoint,
          D.targetAttachmentPresentation.endPoint} : Set Plane) := by
      rw [← D.targetAttachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpDExposed⟩
    have hstart : D.targetAttachmentPresentation.startPoint =
        D.targetDecomposition.first.innerPoint := by
      classical
      rw [LocalizedCutFreeCellData.targetAttachmentPresentation,
        dif_pos (D.targetFirstAlternative_of_one_le hk)]
      rfl
    have hend : D.targetAttachmentPresentation.endPoint =
        D.targetDecomposition.second.innerPoint := by
      classical
      rw [LocalizedCutFreeCellData.targetAttachmentPresentation,
        dif_pos (D.targetFirstAlternative_of_one_le hk)]
      rfl
    rw [hstart, hend] at hpEnds
    change p ∈
      ({(I.levelTargetAnnularCrosscut k b).innerPoint,
        (I.levelTargetAnnularCrosscut k D.next).innerPoint} :
          Set Plane) at hpEnds
    rcases hpEnds with hpFirst | hpSecond
    · exact hpNotInnerPoint b hpFirst
    · exact hpNotInnerPoint D.next
        (Set.mem_singleton_iff.mp hpSecond)
  have hpNotDSecond :
      p ∉ range D.targetDecomposition.second.path := by
    intro hpSecond
    exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelTargetAnnularCrosscut k D.next_ne)
      hpCut hpSecond
  have hpNotDOuter :
      p ∉ range (D.targetBoundarySplit (k + 2)).first := by
    intro hpOuter
    have hpMeet : p ∈
        range (I.levelTargetAnnularCrosscut k b).path ∩
          (I.targetOuterDisk k).carrier := by
      refine ⟨hpCut, ?_⟩
      rw [← (I.targetOuterDisk k).carrier_toJordanCircle,
        ← (D.targetBoundarySplit (k + 2)).cover]
      exact Or.inl hpOuter
    rw [(I.levelTargetAnnularCrosscut k b).range_inter_outer] at hpMeet
    exact hpNotOuterPoint b (Set.mem_singleton_iff.mp hpMeet)
  have hcompactDShared :
      IsCompact (range D.targetAttachmentPresentation.shared) :=
    isCompact_range D.targetAttachmentPresentation.shared.continuous
  have hcompactDSecond :
      IsCompact (range D.targetDecomposition.second.path) :=
    isCompact_range D.targetDecomposition.second.path.continuous
  have hcompactDOuter :
      IsCompact (range (D.targetBoundarySplit (k + 2)).first) :=
    isCompact_range (D.targetBoundarySplit (k + 2)).first.continuous
  obtain ⟨rD, hrD, hlocalDraw⟩ :=
    exists_local_determinantLine_union_of_compact_avoid
      (exists_local_determinantLine_union_of_compact_avoid
        (exists_local_determinantLine_union_of_compact_avoid hlocalCut
          hcompactDShared hpNotDShared)
        hcompactDSecond hpNotDSecond)
      hcompactDOuter hpNotDOuter
  have hcarrierD : D.targetAttachmentPresentation.disk.carrier =
      (((range (I.levelTargetAnnularCrosscut k b).path ∪
          range D.targetAttachmentPresentation.shared) ∪
        range D.targetDecomposition.second.path) ∪
          range (D.targetBoundarySplit (k + 2)).first) := by
    rw [D.targetAttachmentPresentation.carrier_eq,
      D.range_targetAttachmentPresentation_exposed hk, hDFirst]
    ext x
    constructor
    · rintro (hxShared | hxSecond | hxOuter | hxCut)
      · exact Or.inl (Or.inl (Or.inr hxShared))
      · exact Or.inl (Or.inr hxSecond)
      · exact Or.inr hxOuter
      · exact Or.inl (Or.inl (Or.inl hxCut))
    · rintro (((hxCut | hxShared) | hxSecond) | hxOuter)
      · exact Or.inr (Or.inr (Or.inr hxCut))
      · exact Or.inl hxShared
      · exact Or.inr (Or.inl hxSecond)
      · exact Or.inr (Or.inr (Or.inl hxOuter))
  have hlocalD :
      ball p rD ∩ D.targetAttachmentPresentation.disk.carrier =
        ball p rD ∩ determinantLine p direction := by
    rw [hcarrierD]
    exact hlocalDraw
  let r : ℝ := min rC rD
  have hr : 0 < r := lt_min hrC hrD
  have hlocalC' :
      ball p r ∩ C.targetAttachmentPresentation.disk.toJordanCircle.carrier =
        ball p r ∩ determinantLine p direction := by
    rw [C.targetAttachmentPresentation.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_left _ _) hlocalC
  have hlocalD' :
      ball p r ∩ D.targetAttachmentPresentation.disk.toJordanCircle.carrier =
        ball p r ∩ determinantLine p direction := by
    rw [D.targetAttachmentPresentation.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_right _ _) hlocalD
  have hdisjoint :
      Disjoint C.targetAttachmentPresentation.disk.toJordanCircle.inside
        D.targetAttachmentPresentation.disk.toJordanCircle.inside := by
    simpa only [C.targetAttachmentPresentation.disk.inside_toJordanCircle,
      D.targetAttachmentPresentation.disk.inside_toJordanCircle] using
        C.disjoint_targetDiskInterior hk D hab
  have hpUnion :=
    JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
      hdisjoint hr
      (by
        rw [C.targetAttachmentPresentation.disk.carrier_toJordanCircle]
        exact C.targetSecondCrosscut_range_subset_targetDiskCarrier hk <| by
          change p ∈ range
            (I.levelTargetAnnularCrosscut k C.next).path
          rwa [hCnext])
      hlocalC' hlocalD'
  apply interior_mono _ hpUnion
  rw [C.targetAttachmentPresentation.disk.inside_toJordanCircle,
    D.targetAttachmentPresentation.disk.inside_toJordanCircle]
  change C.targetAttachmentPresentation.disk.closedRegion ∪
      D.targetAttachmentPresentation.disk.closedRegion ⊆
    I.localizedTargetFilledDisk k
  intro x hx
  right
  rcases hx with hxC | hxD
  · exact Set.mem_iUnion.mpr ⟨a, hxC⟩
  · exact Set.mem_iUnion.mpr ⟨b, hxD⟩

end LocalizedCutFreeCellData

/-- After deleting the finite seam exceptions, every frontier point of the
filled target union lies on the outer standard polygon. -/
theorem frontier_sdiff_localizedTargetCellExceptionalSet_subset_outerCarrier
    (k : ℕ) (hk : 1 ≤ k) :
    frontier (I.localizedTargetFilledDisk k) \
        I.localizedTargetCellExceptionalSet k ⊆
      (I.targetOuterDisk k).carrier := by
  have hclosed : IsClosed (I.localizedTargetFilledDisk k) :=
    (I.isCompact_localizedTargetFilledDisk k).isClosed
  have hinnerInterior : (I.targetInnerDisk k).interiorRegion ⊆
      interior (I.localizedTargetFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      left
      rw [(I.targetInnerDisk k).closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.targetInnerDisk k).isOpen_interiorRegion
  have hcellInterior (a : LevelAddress k) :
      (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.interiorRegion ⊆
        interior (I.localizedTargetFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      right
      apply Set.mem_iUnion.mpr
      refine ⟨a, ?_⟩
      change x ∈
        (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion
      rw [(I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.isOpen_interiorRegion
  rintro x ⟨hxFrontier, hxNotExceptional⟩
  have hxFilled : x ∈ I.localizedTargetFilledDisk k :=
    hclosed.frontier_subset hxFrontier
  rcases hxFilled with hxInner | hxCells
  · rw [(I.targetInnerDisk k).closedRegion_eq_union] at hxInner
    rcases hxInner with hxInnerInterior | hxInnerCarrier
    · exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier
        (hinnerInterior hxInnerInterior) hxFrontier
    · obtain ⟨a, hxShared⟩ := Set.mem_iUnion.mp <|
        I.targetInnerCarrier_subset_iUnion_targetCellShared k hk hxInnerCarrier
      have hxInterior :=
        (I.localizedCutFreeCellData k a).targetShared_mem_interior_localizedTargetFilledDisk
          hk hxShared hxNotExceptional rfl
      exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier hxInterior hxFrontier
  · obtain ⟨a, hxCell⟩ := Set.mem_iUnion.mp hxCells
    let C : I.LocalizedCutFreeCellData k a :=
      I.localizedCutFreeCellData k a
    change x ∈ C.targetAttachmentPresentation.disk.closedRegion at hxCell
    rw [C.targetAttachmentPresentation.disk.closedRegion_eq_union] at hxCell
    rcases hxCell with hxCellInterior | hxCellCarrier
    · exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier
        (hcellInterior a hxCellInterior) hxFrontier
    · rw [C.targetAttachmentPresentation.carrier_eq,
        C.range_targetAttachmentPresentation_exposed hk] at hxCellCarrier
      rcases hxCellCarrier with
        hxShared | hxSuccessorCut | hxOuter | hxInitialCut
      · have hxInterior :=
          C.targetShared_mem_interior_localizedTargetFilledDisk
            hk hxShared hxNotExceptional rfl
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier
      · have hxInterior :=
          LocalizedCutFreeCellData.targetSuccessorCut_mem_interior_localizedTargetFilledDisk
            (I := I) k hk a (by
              change x ∈ range
                (I.levelTargetAnnularCrosscut k C.next).path at hxSuccessorCut
              rw [C.next_eq] at hxSuccessorCut
              exact hxSuccessorCut)
            hxNotExceptional
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier
      · rw [← (I.targetOuterDisk k).carrier_toJordanCircle,
          ← (C.targetBoundarySplit (k + 2)).cover]
        exact Or.inl hxOuter
      · let previous : LevelAddress k :=
          I.levelLocalizedPredecessor k a
        have hxPreviousSuccessor : x ∈ range
            (I.levelTargetAnnularCrosscut k
              (I.levelLocalizedSuccessor k previous)).path := by
          change x ∈ range
            (I.levelTargetAnnularCrosscut k a).path at hxInitialCut
          dsimp only [previous]
          rw [I.levelLocalizedSuccessor_predecessor]
          exact hxInitialCut
        have hxInterior :=
          LocalizedCutFreeCellData.targetSuccessorCut_mem_interior_localizedTargetFilledDisk
            (I := I) k hk previous hxPreviousSuccessor hxNotExceptional
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier

/-- The finite exceptional set cannot contribute isolated frontier points,
so the whole frontier lies on the outer standard polygon. -/
theorem frontier_localizedTargetFilledDisk_subset_outerCarrier
    (k : ℕ) (hk : 1 ≤ k) :
    frontier (I.localizedTargetFilledDisk k) ⊆
      (I.targetOuterDisk k).carrier := by
  have hclosed : IsClosed (I.localizedTargetFilledDisk k) :=
    (I.isCompact_localizedTargetFilledDisk k).isClosed
  have hdense : frontier (I.localizedTargetFilledDisk k) ⊆
      closure (frontier (I.localizedTargetFilledDisk k) \
        I.localizedTargetCellExceptionalSet k) :=
    frontier_subset_closure_sdiff_finite_of_regularClosed
      hclosed (I.closure_interior_localizedTargetFilledDisk k)
      (I.localizedTargetCellExceptionalSet_finite k)
  have houterClosed : IsClosed (I.targetOuterDisk k).carrier :=
    (I.targetOuterDisk k).isCompact_carrier.isClosed
  exact hdense.trans <| by
    have hclosure := closure_mono
      (I.frontier_sdiff_localizedTargetCellExceptionalSet_subset_outerCarrier
        k hk)
    rwa [houterClosed.closure_eq] at hclosure

/-- The inner standard disk and all standard target cells fill the outer
standard disk. -/
theorem localizedTargetFilledDisk_eq_outerClosedRegion
    (k : ℕ) (hk : 1 ≤ k) :
    I.localizedTargetFilledDisk k =
      (I.targetOuterDisk k).closedRegion := by
  have hinnerInterior : (I.targetInnerDisk k).interiorRegion ⊆
      interior (I.localizedTargetFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      left
      rw [(I.targetInnerDisk k).closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.targetInnerDisk k).isOpen_interiorRegion
  let p : Plane := (I.targetInnerDisk k).toJordanCircle.insidePoint
  have hpInner : p ∈ (I.targetInnerDisk k).interiorRegion := by
    rw [← (I.targetInnerDisk k).inside_toJordanCircle]
    exact (I.targetInnerDisk k).toJordanCircle.insidePoint_mem_inside
  have hpOuter : p ∈ (I.targetOuterDisk k).toJordanCircle.inside := by
    rw [(I.targetOuterDisk k).inside_toJordanCircle]
    apply StandardPolygonalCollars.disk_strictlyNested (k + 1)
    rw [(I.targetInnerDisk k).closedRegion_eq_union]
    exact Or.inl hpInner
  have hintersection :
      (interior (I.localizedTargetFilledDisk k) ∩
        (I.targetOuterDisk k).toJordanCircle.inside).Nonempty :=
    ⟨p, hinnerInterior hpInner, hpOuter⟩
  have hrecognition :=
    (I.targetOuterDisk k).toJordanCircle.eq_closure_inside_of_isCompact_frontier_subset
      (I.isCompact_localizedTargetFilledDisk k)
      (by
        rw [(I.targetOuterDisk k).inside_toJordanCircle]
        exact I.localizedTargetFilledDisk_subset_outerClosedRegion k hk)
      (by
        rw [(I.targetOuterDisk k).carrier_toJordanCircle]
        exact I.frontier_localizedTargetFilledDisk_subset_outerCarrier k hk)
      hintersection
  rw [(I.targetOuterDisk k).inside_toJordanCircle] at hrecognition
  exact hrecognition

/-- The finite union of standard target cells is exactly the standard closed
shell between radii `k + 1` and `k + 2`. -/
theorem iUnion_targetCell_eq_standardClosedShell
    (k : ℕ) (hk : 1 ≤ k) :
    (⋃ a : LevelAddress k,
        (I.localizedCutFreeCellData k a).targetAttachmentPresentation.disk.closedRegion) =
      PolygonalCircle.closedShell
        (I.targetInnerDisk k) (I.targetOuterDisk k) := by
  apply Set.Subset.antisymm
  · exact I.iUnion_targetCell_subset_standardClosedShell k hk
  · intro x hxShell
    have hxFilled : x ∈ I.localizedTargetFilledDisk k := by
      rw [I.localizedTargetFilledDisk_eq_outerClosedRegion k hk]
      exact hxShell.1
    rcases hxFilled with hxInner | hxCells
    · rw [(I.targetInnerDisk k).closedRegion_eq_union] at hxInner
      have hxInnerCarrier : x ∈ (I.targetInnerDisk k).carrier :=
        hxInner.resolve_left hxShell.2
      obtain ⟨a, hxShared⟩ := Set.mem_iUnion.mp <|
        I.targetInnerCarrier_subset_iUnion_targetCellShared
          k hk hxInnerCarrier
      obtain ⟨t, rfl⟩ := hxShared
      apply Set.mem_iUnion.mpr
      exact ⟨a,
        (I.localizedCutFreeCellData k a).targetAttachmentPresentation.shared_mem_closedRegion t⟩
    · exact hxCells

/-- The glued finite-stage map as a homeomorphism between the actual
localized polygonal shell and the full standard polygonal shell. -/
noncomputable def localizedShellHomeomorph
    (k : ℕ) (hk : 1 ≤ k) :
    PolygonalCircle.closedShell
        (I.localizedMarkedPolygonalDisk (k + 1))
        (I.localizedMarkedPolygonalDisk (k + 2)) ≃ₜ
      PolygonalCircle.closedShell
        (I.targetInnerDisk k) (I.targetOuterDisk k) :=
  (I.localizedShellToTargetCellUnionHomeomorph k hk).trans <|
    Homeomorph.setCongr (I.iUnion_targetCell_eq_standardClosedShell k hk)

theorem localizedShellHomeomorph_apply
    (k : ℕ) (hk : 1 ≤ k) (a : LevelAddress k) {x : Plane}
    (hxShell : x ∈ PolygonalCircle.closedShell
      (I.localizedMarkedPolygonalDisk (k + 1))
      (I.localizedMarkedPolygonalDisk (k + 2)))
    (hxCell : x ∈
      (I.localizedCutFreeCellData k a).disk.closedRegion) :
    (I.localizedShellHomeomorph k hk ⟨x, hxShell⟩ : Plane) =
      ((I.localizedCutFreeCellData k a).cellHomeomorph
        ⟨x, hxCell⟩ : Plane) := by
  exact I.localizedShellToTargetCellUnionHomeomorph_apply
    k hk a hxShell hxCell

end JordanCircle.InitialAngularArcs

end

end Schoenflies
