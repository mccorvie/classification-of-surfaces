import Schoenflies.LocalizedAdjacentCellCompatibility
import Schoenflies.JordanThetaRegions
import Schoenflies.JordanRegionRecognition
import Schoenflies.LocallyStraightSets

/-!
# Coverage by the localized collar cells

The independently constructed cyclic cells do not merely have compatible
overlaps: together with the old polygonal disk they exhaust the next
polygonal disk.  The proof recognizes the finite union from its frontier.
Every seam is locally swallowed by the two disks on its sides, so the only
possible frontier is the new outer polygon.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev outerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

/-- The old disk together with all canonical source cells at one level. -/
def localizedFilledDisk (k : ℕ) : Set Plane :=
  (I.innerDisk k).closedRegion ∪
    ⋃ a : LevelAddress k,
      (I.localizedCutFreeCellData k a).disk.closedRegion

theorem isCompact_localizedFilledDisk (k : ℕ) :
    IsCompact (I.localizedFilledDisk k) := by
  exact (I.innerDisk k).isCompact_closedRegion.union <|
    isCompact_iUnion fun a =>
      (I.localizedCutFreeCellData k a).disk.isCompact_closedRegion

theorem localizedFilledDisk_subset_outerClosedRegion (k : ℕ) :
    I.localizedFilledDisk k ⊆ (I.outerDisk k).closedRegion := by
  apply Set.union_subset
  · exact PolygonalCircle.closedRegion_subset_closedRegion_of_strictlyNested
      (I.innerDisk k) (I.outerDisk k)
      (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
  · exact Set.iUnion_subset fun a =>
      (I.localizedCutFreeCellData k a).disk_closedRegion_subset_outerDisk

theorem closure_interior_localizedFilledDisk (k : ℕ) :
    closure (interior (I.localizedFilledDisk k)) =
      I.localizedFilledDisk k := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset
      (I.isCompact_localizedFilledDisk k).isClosed
  · intro x hx
    rcases hx with hxInner | hxCells
    · change x ∈ closure (I.innerDisk k).interiorRegion at hxInner
      apply closure_mono _ hxInner
      apply interior_maximal
      · intro y hy
        left
        rw [(I.innerDisk k).closedRegion_eq_union]
        exact Or.inl hy
      · exact (I.innerDisk k).isOpen_interiorRegion
    · obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxCells
      change x ∈ closure
        (I.localizedCutFreeCellData k a).disk.interiorRegion at hxa
      apply closure_mono _ hxa
      apply interior_maximal
      · intro y hy
        right
        apply Set.mem_iUnion.mpr
        refine ⟨a, ?_⟩
        rw [(I.localizedCutFreeCellData k a).disk.closedRegion_eq_union]
        exact Or.inl hy
      · exact (I.localizedCutFreeCellData k a).disk.isOpen_interiorRegion

theorem innerCarrier_subset_iUnion_localizedCellShared
    (k : ℕ) (hk : 1 ≤ k) :
    (I.innerDisk k).carrier ⊆
      ⋃ a : LevelAddress k,
        range (I.localizedCutFreeCellData k a).attachmentPresentation.shared := by
  intro x hx
  have hcover :=
    JordanCircle.FiniteMarking.carrier_subset_iUnion_successorBoundarySplit_first
      (I.levelLocalizedInnerMarking k)
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp <|
    hcover (by
      simpa only [(I.innerDisk k).carrier_toJordanCircle] using hx)
  apply Set.mem_iUnion.mpr
  refine ⟨a, ?_⟩
  rw [LocalizedCutFreeCellData.range_attachmentPresentation_shared_eq_successorBoundarySplit
    (I.localizedCutFreeCellData k a) hk]
  exact hxa

/-- The finite set at which a seam may meet a polygon vertex or a radial-cut
endpoint.  All other seam points have a common straight-line neighborhood. -/
def localizedCellExceptionalSet (k : ℕ) : Set Plane :=
  range (I.innerDisk k).vertex ∪
    ⋃ a : LevelAddress k,
      ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
        (I.levelLocalizedAnnularCrosscut k a).outerPoint} : Set Plane)

theorem localizedCellExceptionalSet_finite (k : ℕ) :
    (I.localizedCellExceptionalSet k).Finite := by
  have hcuts : (⋃ a : LevelAddress k,
      ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
        (I.levelLocalizedAnnularCrosscut k a).outerPoint} : Set Plane)).Finite :=
    Set.finite_iUnion fun _ => by simp
  exact (Set.finite_range (I.innerDisk k).vertex).union hcuts

namespace LocalizedCutFreeCellData

variable {I : J.InitialAngularArcs} {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

/-- Away from the finite vertex set, the inner polygon and its attached cell
have the same locally straight boundary and lie on opposite sides of it. -/
theorem shared_mem_interior_localizedFilledDisk
    {p : Plane} (hpShared : p ∈ range C.attachmentPresentation.shared)
    (hpExceptional : p ∉ I.localizedCellExceptionalSet k)
    (hcanonical : C = I.localizedCutFreeCellData k a) :
    p ∈ interior (I.localizedFilledDisk k) := by
  subst C
  let C : I.LocalizedCutFreeCellData k a :=
    I.localizedCutFreeCellData k a
  have hpNotVertex : p ∉ range (I.innerDisk k).vertex := by
    intro hp
    exact hpExceptional (Or.inl hp)
  obtain ⟨i, hpOpen⟩ :=
    PolygonalCircle.exists_openEdge_of_mem_carrier_not_vertex
      (I.innerDisk k)
      (by
        rw [C.range_attachmentPresentation_shared] at hpShared
        exact C.separator.innerFirst_range_subset hpShared)
      hpNotVertex
  obtain ⟨rBase, hrBase, hlocalBase⟩ :=
    polygonalCircle_exists_local_determinantLine (I.innerDisk k) hpOpen
  let d : Plane :=
    (I.innerDisk k).vertex (i + 1) - (I.innerDisk k).vertex i
  let B : Set Plane := range C.attachmentPresentation.shared
  let R : Set Plane := range C.separator.innerSplit.second
  have hbaseCarrier : (I.innerDisk k).carrier = B ∪ R := by
    dsimp only [B, R]
    rw [C.range_attachmentPresentation_shared,
      ← (I.innerDisk k).carrier_toJordanCircle]
    exact C.separator.innerSplit.cover.symm
  have hpNotR : p ∉ R := by
    intro hpR
    have hpEnds : p ∈
        ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
          (I.levelLocalizedAnnularCrosscut k C.next).innerPoint} :
            Set Plane) := by
      rw [← C.separator.innerSplit.overlap]
      exact ⟨by
        rw [← C.range_attachmentPresentation_shared]
        exact hpShared, hpR⟩
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
    · exact isCompact_range C.separator.innerSplit.second.continuous
    · exact hpNotR
  let E : Set Plane := range C.attachmentPresentation.exposed
  have hpNotE : p ∉ E := by
    intro hpE
    have hpEnds : p ∈
        ({C.attachmentPresentation.startPoint,
          C.attachmentPresentation.endPoint} : Set Plane) := by
      rw [← C.attachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpE⟩
    have hpCutEnds : p ∈
        ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
          (I.levelLocalizedAnnularCrosscut k C.next).innerPoint} :
            Set Plane) := by
      rw [C.attachmentPresentation_startPoint,
        C.attachmentPresentation_endPoint] at hpEnds
      change p ∈
        ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
          (I.levelLocalizedAnnularCrosscut k C.next).innerPoint} :
            Set Plane) at hpEnds
      exact hpEnds
    rcases hpCutEnds with hpFirst | hpSecond
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr ⟨a, Or.inl hpFirst⟩
    · apply hpExceptional
      exact Or.inr <| Set.mem_iUnion.mpr
        ⟨C.next, Or.inl (Set.mem_singleton_iff.mp hpSecond)⟩
  obtain ⟨rCell, hrCell, hlocalCell⟩ :=
    exists_local_determinantLine_union_of_compact_avoid hlocalB
      (isCompact_range C.attachmentPresentation.exposed.continuous) hpNotE
  have hlocalCell' : ball p rCell ∩ C.disk.carrier =
      ball p rCell ∩ determinantLine p d := by
    change ball p rCell ∩ C.attachmentPresentation.disk.carrier = _
    rw [C.attachmentPresentation.carrier_eq]
    exact hlocalCell
  have hdisjoint : Disjoint
      (I.innerDisk k).toJordanCircle.inside C.disk.toJordanCircle.inside := by
    simpa only [(I.innerDisk k).inside_toJordanCircle,
      C.disk.inside_toJordanCircle] using
        C.innerDisk_disjoint_diskInterior.mono_left
          (by rw [(I.innerDisk k).closedRegion_eq_union]; exact Set.subset_union_left)
  let r := min rBase rCell
  have hr : 0 < r := lt_min hrBase hrCell
  have hlocalBase' : ball p r ∩ (I.innerDisk k).toJordanCircle.carrier =
      ball p r ∩ determinantLine p d := by
    rw [(I.innerDisk k).carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_left _ _) hlocalBase
  have hlocalCell'' : ball p r ∩ C.disk.toJordanCircle.carrier =
      ball p r ∩ determinantLine p d := by
    rw [C.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_right _ _) hlocalCell'
  have hpUnion :=
    JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
        hdisjoint hr
        (by
          rw [(I.innerDisk k).carrier_toJordanCircle]
          rw [C.range_attachmentPresentation_shared] at hpShared
          exact C.separator.innerFirst_range_subset hpShared)
        hlocalBase' hlocalCell''
  apply interior_mono _ hpUnion
  rw [(I.innerDisk k).inside_toJordanCircle,
    C.disk.inside_toJordanCircle]
  change (I.innerDisk k).closedRegion ∪ C.disk.closedRegion ⊆
    I.localizedFilledDisk k
  apply Set.union_subset Set.subset_union_left
  intro x hx
  right
  exact Set.mem_iUnion.mpr ⟨a, hx⟩

/-- Away from its two endpoints, the radial cut shared by two cyclically
successive canonical cells is swallowed by the union of those cells. -/
theorem successorCut_mem_interior_localizedFilledDisk
    (k : ℕ) (hk : 1 ≤ k) (a : LevelAddress k) {p : Plane}
    (hpCut : p ∈ range
      (I.levelLocalizedAnnularCrosscut k
        (I.levelLocalizedSuccessor k a)).path)
    (hpExceptional : p ∉ I.localizedCellExceptionalSet k) :
    p ∈ interior (I.localizedFilledDisk k) := by
  let b : LevelAddress k := I.levelLocalizedSuccessor k a
  let C : I.LocalizedCutFreeCellData k a :=
    I.localizedCutFreeCellData k a
  let D : I.LocalizedCutFreeCellData k b :=
    I.localizedCutFreeCellData k b
  have hab : a ≠ b := by
    exact (I.levelLocalizedSuccessor_ne k a).symm
  have hCnext : C.next = b := C.next_eq
  have hCSecond : range C.decomposition.second.path =
      range (I.levelLocalizedAnnularCrosscut k b).path := by
    change range (I.levelLocalizedAnnularCrosscut k C.next).path = _
    rw [hCnext]
  have hDFirst : range D.decomposition.first.path =
      range (I.levelLocalizedAnnularCrosscut k b).path := by
    rfl
  have hpNotInnerPoint (c : LevelAddress k) :
      p ≠ (I.levelLocalizedAnnularCrosscut k c).innerPoint := by
    intro hp
    apply hpExceptional
    exact Or.inr <| Set.mem_iUnion.mpr ⟨c, Or.inl hp⟩
  have hpNotOuterPoint (c : LevelAddress k) :
      p ≠ (I.levelLocalizedAnnularCrosscut k c).outerPoint := by
    intro hp
    apply hpExceptional
    exact Or.inr <| Set.mem_iUnion.mpr ⟨c, Or.inr hp⟩
  have houterInner :
      (I.levelLocalizedAnnularCrosscut k b).outerPoint ≠
        (I.levelLocalizedAnnularCrosscut k b).innerPoint := by
    intro h
    have hdisjoint :=
      PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
        (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    exact Set.disjoint_left.mp hdisjoint
      (I.levelLocalizedAnnularCrosscut k b).innerPoint_mem
      (h ▸ (I.levelLocalizedAnnularCrosscut k b).outerPoint_mem)
  have hpSegment : p ∈ segment ℝ
      (I.levelLocalizedAnnularCrosscut k b).outerPoint
      (I.levelLocalizedAnnularCrosscut k b).innerPoint := by
    rw [← I.range_levelLocalizedAnnularCrosscut_eq_segment k b]
    exact hpCut
  have hpOpen : p ∈ openSegment ℝ
      (I.levelLocalizedAnnularCrosscut k b).outerPoint
      (I.levelLocalizedAnnularCrosscut k b).innerPoint :=
    mem_openSegment_of_ne_left_right
      (hpNotOuterPoint b).symm (hpNotInnerPoint b).symm hpSegment
  let direction : Plane :=
    (I.levelLocalizedAnnularCrosscut k b).innerPoint -
      (I.levelLocalizedAnnularCrosscut k b).outerPoint
  have hlocalCut : ∃ r : ℝ, 0 < r ∧
      ball p r ∩ range (I.levelLocalizedAnnularCrosscut k b).path =
        ball p r ∩ determinantLine p direction := by
    rw [I.range_levelLocalizedAnnularCrosscut_eq_segment k b]
    exact exists_local_determinantLine_segment houterInner hpOpen
  have hpCExposed : p ∈ range C.attachmentPresentation.exposed := by
    rw [C.range_attachmentPresentation_exposed]
    left
    change p ∈ range
      (I.levelLocalizedAnnularCrosscut k C.next).path
    rwa [hCnext]
  have hpNotCShared :
      p ∉ range C.attachmentPresentation.shared := by
    intro hpShared
    have hpEnds : p ∈
        ({C.attachmentPresentation.startPoint,
          C.attachmentPresentation.endPoint} : Set Plane) := by
      rw [← C.attachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpCExposed⟩
    rw [C.attachmentPresentation_startPoint,
      C.attachmentPresentation_endPoint] at hpEnds
    change p ∈
      ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
        (I.levelLocalizedAnnularCrosscut k C.next).innerPoint} :
          Set Plane) at hpEnds
    rcases hpEnds with hpFirst | hpSecond
    · exact hpNotInnerPoint a hpFirst
    · exact hpNotInnerPoint C.next
        (Set.mem_singleton_iff.mp hpSecond)
  have hpNotCOuter : p ∉ C.exposedOuterArc := by
    intro hpOuter
    have hpMeet : p ∈
        range (I.levelLocalizedAnnularCrosscut k b).path ∩
          (I.outerDisk k).carrier :=
      ⟨hpCut, C.exposedOuterArc_subset_outerCarrier hpOuter⟩
    rw [(I.levelLocalizedAnnularCrosscut k b).range_inter_outer] at hpMeet
    exact hpNotOuterPoint b (Set.mem_singleton_iff.mp hpMeet)
  have hpNotCFirst :
      p ∉ range C.decomposition.first.path := by
    intro hpFirst
    exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k
        (I.levelLocalizedSuccessor_ne k a)) hpCut hpFirst
  have hcompactCShared :
      IsCompact (range C.attachmentPresentation.shared) :=
    isCompact_range C.attachmentPresentation.shared.continuous
  have hcompactCOuter : IsCompact C.exposedOuterArc := by
    rw [← C.range_outerCellBoundarySplit_first]
    exact isCompact_range C.outerCellBoundarySplit.first.continuous
  have hcompactCFirst :
      IsCompact (range C.decomposition.first.path) :=
    isCompact_range C.decomposition.first.path.continuous
  obtain ⟨rC, hrC, hlocalCraw⟩ :=
    exists_local_determinantLine_union_of_compact_avoid
      (exists_local_determinantLine_union_of_compact_avoid
        (exists_local_determinantLine_union_of_compact_avoid hlocalCut
          hcompactCShared hpNotCShared)
        hcompactCOuter hpNotCOuter)
      hcompactCFirst hpNotCFirst
  have hcarrierC : C.disk.carrier =
      (((range (I.levelLocalizedAnnularCrosscut k b).path ∪
          range C.attachmentPresentation.shared) ∪
        C.exposedOuterArc) ∪ range C.decomposition.first.path) := by
    change C.attachmentPresentation.disk.carrier = _
    rw [C.attachmentPresentation.carrier_eq,
      C.range_attachmentPresentation_exposed, hCSecond]
    simp only [Set.union_comm, Set.union_left_comm]
  have hlocalC : ball p rC ∩ C.disk.carrier =
      ball p rC ∩ determinantLine p direction := by
    rw [hcarrierC]
    exact hlocalCraw
  have hpDExposed : p ∈ range D.attachmentPresentation.exposed := by
    rw [D.range_attachmentPresentation_exposed]
    exact Or.inr (Or.inr hpCut)
  have hpNotDShared :
      p ∉ range D.attachmentPresentation.shared := by
    intro hpShared
    have hpEnds : p ∈
        ({D.attachmentPresentation.startPoint,
          D.attachmentPresentation.endPoint} : Set Plane) := by
      rw [← D.attachmentPresentation.boundary_overlap]
      exact ⟨hpShared, hpDExposed⟩
    rw [D.attachmentPresentation_startPoint,
      D.attachmentPresentation_endPoint] at hpEnds
    change p ∈
      ({(I.levelLocalizedAnnularCrosscut k b).innerPoint,
        (I.levelLocalizedAnnularCrosscut k D.next).innerPoint} :
          Set Plane) at hpEnds
    rcases hpEnds with hpFirst | hpSecond
    · exact hpNotInnerPoint b hpFirst
    · exact hpNotInnerPoint D.next
        (Set.mem_singleton_iff.mp hpSecond)
  have hpNotDSecond :
      p ∉ range D.decomposition.second.path := by
    intro hpSecond
    exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k D.next_ne)
      hpCut hpSecond
  have hpNotDOuter : p ∉ D.exposedOuterArc := by
    intro hpOuter
    have hpMeet : p ∈
        range (I.levelLocalizedAnnularCrosscut k b).path ∩
          (I.outerDisk k).carrier :=
      ⟨hpCut, D.exposedOuterArc_subset_outerCarrier hpOuter⟩
    rw [(I.levelLocalizedAnnularCrosscut k b).range_inter_outer] at hpMeet
    exact hpNotOuterPoint b (Set.mem_singleton_iff.mp hpMeet)
  have hcompactDShared :
      IsCompact (range D.attachmentPresentation.shared) :=
    isCompact_range D.attachmentPresentation.shared.continuous
  have hcompactDSecond :
      IsCompact (range D.decomposition.second.path) :=
    isCompact_range D.decomposition.second.path.continuous
  have hcompactDOuter : IsCompact D.exposedOuterArc := by
    rw [← D.range_outerCellBoundarySplit_first]
    exact isCompact_range D.outerCellBoundarySplit.first.continuous
  obtain ⟨rD, hrD, hlocalDraw⟩ :=
    exists_local_determinantLine_union_of_compact_avoid
      (exists_local_determinantLine_union_of_compact_avoid
        (exists_local_determinantLine_union_of_compact_avoid hlocalCut
          hcompactDShared hpNotDShared)
        hcompactDSecond hpNotDSecond)
      hcompactDOuter hpNotDOuter
  have hcarrierD : D.disk.carrier =
      (((range (I.levelLocalizedAnnularCrosscut k b).path ∪
          range D.attachmentPresentation.shared) ∪
        range D.decomposition.second.path) ∪ D.exposedOuterArc) := by
    change D.attachmentPresentation.disk.carrier = _
    rw [D.attachmentPresentation.carrier_eq,
      D.range_attachmentPresentation_exposed, hDFirst]
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
  have hlocalD : ball p rD ∩ D.disk.carrier =
      ball p rD ∩ determinantLine p direction := by
    rw [hcarrierD]
    exact hlocalDraw
  let r : ℝ := min rC rD
  have hr : 0 < r := lt_min hrC hrD
  have hlocalC' : ball p r ∩ C.disk.toJordanCircle.carrier =
      ball p r ∩ determinantLine p direction := by
    rw [C.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_left _ _) hlocalC
  have hlocalD' : ball p r ∩ D.disk.toJordanCircle.carrier =
      ball p r ∩ determinantLine p direction := by
    rw [D.disk.carrier_toJordanCircle]
    exact restrict_local_set_equality (min_le_right _ _) hlocalD
  have hdisjoint : Disjoint C.disk.toJordanCircle.inside
      D.disk.toJordanCircle.inside := by
    simpa only [C.disk.inside_toJordanCircle,
      D.disk.inside_toJordanCircle] using
        C.disjoint_diskInterior hk D hab
  have hpUnion :=
    JordanThetaRegions.mem_interior_union_closure_inside_of_common_local_line
      hdisjoint hr
      (by
        rw [C.disk.carrier_toJordanCircle]
        exact C.secondCrosscut_range_subset_diskCarrier <| by
          change p ∈ range
            (I.levelLocalizedAnnularCrosscut k C.next).path
          rwa [hCnext])
      hlocalC' hlocalD'
  apply interior_mono _ hpUnion
  rw [C.disk.inside_toJordanCircle, D.disk.inside_toJordanCircle]
  change C.disk.closedRegion ∪ D.disk.closedRegion ⊆
    I.localizedFilledDisk k
  intro x hx
  right
  rcases hx with hxC | hxD
  · exact Set.mem_iUnion.mpr ⟨a, hxC⟩
  · exact Set.mem_iUnion.mpr ⟨b, hxD⟩

end LocalizedCutFreeCellData

/-- Once the finite seam exceptions are deleted, every frontier point of
the filled cell union lies on the new outer polygon. -/
theorem frontier_sdiff_localizedCellExceptionalSet_subset_outerCarrier
    (k : ℕ) (hk : 1 ≤ k) :
    frontier (I.localizedFilledDisk k) \
        I.localizedCellExceptionalSet k ⊆
      (I.outerDisk k).carrier := by
  have hclosed : IsClosed (I.localizedFilledDisk k) :=
    (I.isCompact_localizedFilledDisk k).isClosed
  have hinnerInterior : (I.innerDisk k).interiorRegion ⊆
      interior (I.localizedFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      left
      rw [(I.innerDisk k).closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.innerDisk k).isOpen_interiorRegion
  have hcellInterior (a : LevelAddress k) :
      (I.localizedCutFreeCellData k a).disk.interiorRegion ⊆
        interior (I.localizedFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      right
      apply Set.mem_iUnion.mpr
      refine ⟨a, ?_⟩
      rw [(I.localizedCutFreeCellData k a).disk.closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.localizedCutFreeCellData k a).disk.isOpen_interiorRegion
  rintro x ⟨hxFrontier, hxNotExceptional⟩
  have hxFilled : x ∈ I.localizedFilledDisk k :=
    hclosed.frontier_subset hxFrontier
  rcases hxFilled with hxInner | hxCells
  · rw [(I.innerDisk k).closedRegion_eq_union] at hxInner
    rcases hxInner with hxInnerInterior | hxInnerCarrier
    · exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier
        (hinnerInterior hxInnerInterior) hxFrontier
    · obtain ⟨a, hxShared⟩ := Set.mem_iUnion.mp <|
        I.innerCarrier_subset_iUnion_localizedCellShared k hk hxInnerCarrier
      have hxInterior :=
        (I.localizedCutFreeCellData k a).shared_mem_interior_localizedFilledDisk
            hxShared hxNotExceptional rfl
      exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier hxInterior hxFrontier
  · obtain ⟨a, hxCell⟩ := Set.mem_iUnion.mp hxCells
    let C : I.LocalizedCutFreeCellData k a :=
      I.localizedCutFreeCellData k a
    rw [C.disk.closedRegion_eq_union] at hxCell
    rcases hxCell with hxCellInterior | hxCellCarrier
    · exact False.elim <| Set.disjoint_left.mp
        disjoint_interior_frontier
        (hcellInterior a hxCellInterior) hxFrontier
    · change x ∈ C.attachmentPresentation.disk.carrier at hxCellCarrier
      rw [C.attachmentPresentation.carrier_eq,
        C.range_attachmentPresentation_exposed] at hxCellCarrier
      rcases hxCellCarrier with
        hxShared | hxSuccessorCut | hxOuter | hxInitialCut
      · have hxInterior :=
          C.shared_mem_interior_localizedFilledDisk
            hxShared hxNotExceptional rfl
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier
      · have hxInterior :=
          LocalizedCutFreeCellData.successorCut_mem_interior_localizedFilledDisk
              (I := I) k hk a (by
                change x ∈ range
                  (I.levelLocalizedAnnularCrosscut k C.next).path at hxSuccessorCut
                rw [C.next_eq] at hxSuccessorCut
                exact hxSuccessorCut)
              hxNotExceptional
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier
      · exact C.exposedOuterArc_subset_outerCarrier hxOuter
      · let previous : LevelAddress k :=
          I.levelLocalizedPredecessor k a
        have hxPreviousSuccessor : x ∈ range
            (I.levelLocalizedAnnularCrosscut k
              (I.levelLocalizedSuccessor k previous)).path := by
          change x ∈ range
            (I.levelLocalizedAnnularCrosscut k a).path at hxInitialCut
          dsimp only [previous]
          rw [I.levelLocalizedSuccessor_predecessor]
          exact hxInitialCut
        have hxInterior :=
          LocalizedCutFreeCellData.successorCut_mem_interior_localizedFilledDisk
              (I := I) k hk previous hxPreviousSuccessor hxNotExceptional
        exact False.elim <| Set.disjoint_left.mp
          disjoint_interior_frontier hxInterior hxFrontier

/-- The finite exceptional set cannot contribute isolated frontier points,
so the entire frontier lies on the outer polygon. -/
theorem frontier_localizedFilledDisk_subset_outerCarrier
    (k : ℕ) (hk : 1 ≤ k) :
    frontier (I.localizedFilledDisk k) ⊆
      (I.outerDisk k).carrier := by
  have hclosed : IsClosed (I.localizedFilledDisk k) :=
    (I.isCompact_localizedFilledDisk k).isClosed
  have hdense : frontier (I.localizedFilledDisk k) ⊆
      closure (frontier (I.localizedFilledDisk k) \
        I.localizedCellExceptionalSet k) :=
    frontier_subset_closure_sdiff_finite_of_regularClosed
      hclosed (I.closure_interior_localizedFilledDisk k)
      (I.localizedCellExceptionalSet_finite k)
  have houterClosed : IsClosed (I.outerDisk k).carrier :=
    (I.outerDisk k).isCompact_carrier.isClosed
  exact hdense.trans <| by
    have hclosure := closure_mono
      (I.frontier_sdiff_localizedCellExceptionalSet_subset_outerCarrier k hk)
    rwa [houterClosed.closure_eq] at hclosure

/-- The old disk and its canonical cyclic cells exhaust the next closed
polygonal disk. -/
theorem localizedFilledDisk_eq_outerClosedRegion
    (k : ℕ) (hk : 1 ≤ k) :
    I.localizedFilledDisk k = (I.outerDisk k).closedRegion := by
  have hinnerInterior : (I.innerDisk k).interiorRegion ⊆
      interior (I.localizedFilledDisk k) := by
    apply interior_maximal
    · intro x hx
      left
      rw [(I.innerDisk k).closedRegion_eq_union]
      exact Or.inl hx
    · exact (I.innerDisk k).isOpen_interiorRegion
  let p : Plane := (I.innerDisk k).toJordanCircle.insidePoint
  have hpInner : p ∈ (I.innerDisk k).interiorRegion := by
    rw [← (I.innerDisk k).inside_toJordanCircle]
    exact (I.innerDisk k).toJordanCircle.insidePoint_mem_inside
  have hpOuter : p ∈ (I.outerDisk k).toJordanCircle.inside := by
    rw [(I.outerDisk k).inside_toJordanCircle]
    apply I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inl hpInner
  have hintersection :
      (interior (I.localizedFilledDisk k) ∩
        (I.outerDisk k).toJordanCircle.inside).Nonempty :=
    ⟨p, hinnerInterior hpInner, hpOuter⟩
  have hrecognition :=
    (I.outerDisk k).toJordanCircle.eq_closure_inside_of_isCompact_frontier_subset
        (I.isCompact_localizedFilledDisk k)
        (by
          rw [(I.outerDisk k).inside_toJordanCircle]
          exact I.localizedFilledDisk_subset_outerClosedRegion k)
        (by
          rw [(I.outerDisk k).carrier_toJordanCircle]
          exact I.frontier_localizedFilledDisk_subset_outerCarrier k hk)
        hintersection
  rw [(I.outerDisk k).inside_toJordanCircle] at hrecognition
  exact hrecognition

/-- The canonical source cells alone are exactly the closed shell between
successive localized polygonal disks. -/
theorem iUnion_localizedCell_closedRegion_eq_closedShell
    (k : ℕ) (hk : 1 ≤ k) :
    (⋃ a : LevelAddress k,
        (I.localizedCutFreeCellData k a).disk.closedRegion) =
      PolygonalCircle.closedShell (I.innerDisk k) (I.outerDisk k) := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro a x hxCell
    let C : I.LocalizedCutFreeCellData k a :=
      I.localizedCutFreeCellData k a
    refine ⟨C.disk_closedRegion_subset_outerDisk hxCell, ?_⟩
    intro hxInnerInterior
    have hxInnerClosed : x ∈ (I.innerDisk k).closedRegion := by
      rw [(I.innerDisk k).closedRegion_eq_union]
      exact Or.inl hxInnerInterior
    have hxShared : x ∈ range C.attachmentPresentation.shared := by
      rw [← C.base_inter_disk]
      exact ⟨hxInnerClosed, hxCell⟩
    have hxInnerCarrier : x ∈ (I.innerDisk k).carrier := by
      rw [C.range_attachmentPresentation_shared] at hxShared
      exact C.separator.innerFirst_range_subset hxShared
    exact Set.disjoint_left.mp
      (PolygonalCircle.carrier_disjoint_interiorRegion (I.innerDisk k))
      hxInnerCarrier hxInnerInterior
  · intro x hxShell
    have hxFilled : x ∈ I.localizedFilledDisk k := by
      rw [I.localizedFilledDisk_eq_outerClosedRegion k hk]
      exact hxShell.1
    rcases hxFilled with hxInner | hxCells
    · rw [(I.innerDisk k).closedRegion_eq_union] at hxInner
      have hxInnerCarrier : x ∈ (I.innerDisk k).carrier :=
        hxInner.resolve_left hxShell.2
      obtain ⟨a, hxShared⟩ := Set.mem_iUnion.mp <|
        I.innerCarrier_subset_iUnion_localizedCellShared k hk hxInnerCarrier
      obtain ⟨t, rfl⟩ := hxShared
      apply Set.mem_iUnion.mpr
      exact ⟨a,
        (I.localizedCutFreeCellData k a).attachmentPresentation.shared_mem_closedRegion t⟩
    · exact hxCells

end JordanCircle.InitialAngularArcs

end

end Schoenflies
