import Schoenflies.LocalizedAnnularOrder
import Schoenflies.AnnularCellAttachments

/-!
# Cut-free cells in a localized polygonal shell

For every retained shell cut, cyclic order supplies its next neighbor on the
inner polygonal boundary.  The corresponding separator on the outer boundary
is cut-free as well.  This file turns that statement into the relative disk
attachment consumed by the finite gluing construction.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev outerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

/-- The cut-free neighbor and separator selected from one prescribed cut. -/
structure LocalizedCutFreeCellData (k : ℕ) (a : LevelAddress k) where
  next : LevelAddress k
  next_ne : a ≠ next
  next_eq : next = I.levelLocalizedSuccessor k a
  separator : PolygonalCircle.AnnularCrosscut.SeparatorPair
    (I.levelLocalizedAnnularCrosscut k a)
    (I.levelLocalizedAnnularCrosscut k next)
  inner_second : ∀ c : LevelAddress k, c ≠ a → c ≠ next →
    (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
      range separator.innerSplit.second
  side :
    ((I.innerDisk k).interiorRegion ⊆
          (separator.circle₀
            (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
            (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k next_ne)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ next →
          (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
            range separator.outerArc₁) ∨
      ((I.innerDisk k).interiorRegion ⊆
          (separator.circle₁
            (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
            (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k next_ne)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ next →
          (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
            range separator.outerArc₀)

theorem nonempty_localizedCutFreeCellData (k : ℕ)
    (a : LevelAddress k) :
    Nonempty (I.LocalizedCutFreeCellData k a) := by
  obtain ⟨S, hinnerSecond, hS⟩ :=
    I.exists_levelLocalized_cutFreeArcToSuccessor k a
  exact ⟨⟨I.levelLocalizedSuccessor k a,
    (I.levelLocalizedSuccessor_ne k a).symm, rfl, S,
    hinnerSecond, hS⟩⟩

/-- A canonical cut-free cell starting at the prescribed retained cut. -/
noncomputable def localizedCutFreeCellData (k : ℕ)
    (a : LevelAddress k) : I.LocalizedCutFreeCellData k a :=
  Classical.choice (I.nonempty_localizedCutFreeCellData k a)

theorem localizedCutFreeCellData_next (k : ℕ)
    (a : LevelAddress k) :
    (I.localizedCutFreeCellData k a).next =
      I.levelLocalizedSuccessor k a :=
  (I.localizedCutFreeCellData k a).next_eq

theorem localizedCutFreeCellData_next_bijective (k : ℕ) :
    Function.Bijective
      (fun a : LevelAddress k => (I.localizedCutFreeCellData k a).next) := by
  simpa only [I.localizedCutFreeCellData_next] using
    I.levelLocalizedSuccessor_bijective k

namespace LocalizedCutFreeCellData

variable {I : J.InitialAngularArcs} {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

/-- The two exact separator disks determined by the chosen cut-free pair. -/
noncomputable def decomposition :
    PolygonalCircle.AnnularCellDecomposition (I.innerDisk k) (I.outerDisk k) where
  first := I.levelLocalizedAnnularCrosscut k a
  second := I.levelLocalizedAnnularCrosscut k C.next
  separator := C.separator
  nested := I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)
  disjoint := I.pairwise_disjoint_levelLocalizedAnnularCrosscut k C.next_ne
  outerPoints_ne := fun h =>
    C.next_ne (I.levelLocalizedOuterBoundaryMark_injective k h)
  innerPoints_ne := fun h =>
    C.next_ne (I.levelLocalizedPolygonalBoundaryMark_injective k h)
  first_segment := by
    change range (Path.segment
        (I.levelLocalizedOuterBoundaryMark k a)
        (I.levelLocalizedPolygonalBoundaryMark k a)) = _
    exact Path.range_segment _ _
  second_segment := by
    change range (Path.segment
        (I.levelLocalizedOuterBoundaryMark k C.next)
        (I.levelLocalizedPolygonalBoundaryMark k C.next)) = _
    exact Path.range_segment _ _

private def firstAlternative : Prop :=
  (I.innerDisk k).interiorRegion ⊆
      (C.separator.circle₀
        (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
        (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k C.next_ne)).inside ∧
    ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
      (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
        range C.separator.outerArc₁

private theorem secondAlternative_of_not_first
    (h : ¬ C.firstAlternative) :
    (I.innerDisk k).interiorRegion ⊆
        (C.separator.circle₁
          (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
          (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k C.next_ne)).inside ∧
      ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
        (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
          range C.separator.outerArc₀ :=
  C.side.resolve_left h

/-- The cut-free separator disk, presented as a disk attached to the inner
polygonal disk along its selected boundary arc. -/
noncomputable def attachmentPresentation :
    PolygonalDiskAttachment.Presentation (I.innerDisk k).closedRegion := by
  classical
  exact if h : C.firstAlternative then
      C.decomposition.attachmentPresentation₁ h.1
    else
      C.decomposition.attachmentPresentation₀
        (C.secondAlternative_of_not_first h).1

/-- The actual polygonal disk cut off from the localized shell. -/
noncomputable def disk : PolygonalCircle :=
  C.attachmentPresentation.disk

@[simp] theorem attachmentPresentation_startPoint :
    C.attachmentPresentation.startPoint = C.decomposition.first.innerPoint := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, dif_pos h]
    rfl
  · rw [attachmentPresentation, dif_neg h]
    rfl

@[simp] theorem attachmentPresentation_endPoint :
    C.attachmentPresentation.endPoint = C.decomposition.second.innerPoint := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, dif_pos h]
    rfl
  · rw [attachmentPresentation, dif_neg h]
    rfl

theorem attachmentPresentation_exposedSecondCoordinate
    (t : unitInterval) :
    C.attachmentPresentation.exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedSecondCoordinate t) =
      C.decomposition.second.path.symm t := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, dif_pos h]
    exact C.decomposition.exposedPath_exposedSecondCoordinate _ t
  · rw [attachmentPresentation, dif_neg h]
    exact C.decomposition.exposedPath_exposedSecondCoordinate _ t

theorem attachmentPresentation_exposedFirstCoordinate
    (t : unitInterval) :
    C.attachmentPresentation.exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedFirstCoordinate t) =
      C.decomposition.first.path t := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, dif_pos h]
    exact C.decomposition.exposedPath_exposedFirstCoordinate _ t
  · rw [attachmentPresentation, dif_neg h]
    exact C.decomposition.exposedPath_exposedFirstCoordinate _ t

theorem decomposition_firstPath_mem_disk_closedRegion (t : unitInterval) :
    C.decomposition.first.path t ∈ C.disk.closedRegion := by
  change C.decomposition.first.path t ∈
    C.attachmentPresentation.disk.closedRegion
  rw [← C.attachmentPresentation_exposedFirstCoordinate t]
  exact C.attachmentPresentation.exposed_mem_closedRegion _

theorem decomposition_secondPath_mem_disk_closedRegion (t : unitInterval) :
    C.decomposition.second.path t ∈ C.disk.closedRegion := by
  change C.decomposition.second.path t ∈
    C.attachmentPresentation.disk.closedRegion
  have h := C.attachmentPresentation.exposed_mem_closedRegion
    (PolygonalCircle.AnnularCellDecomposition.exposedSecondCoordinate
      (unitInterval.symm t))
  rw [C.attachmentPresentation_exposedSecondCoordinate] at h
  simpa only [Path.symm_apply, Function.comp_apply,
    unitInterval.symm_symm] using h

theorem base_inter_disk :
    (I.innerDisk k).closedRegion ∩ C.disk.closedRegion =
      range C.attachmentPresentation.shared :=
  C.attachmentPresentation.base_inter_disk

theorem range_attachmentPresentation_shared :
    range C.attachmentPresentation.shared =
      range C.separator.innerSplit.first := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, dif_pos h]
    rfl
  · rw [attachmentPresentation, dif_neg h]
    rfl

/-- At a genuine refinement level, the shared side of a selected cell is
the canonical positive successor arc on the inner polygonal boundary. -/
theorem range_attachmentPresentation_shared_eq_successorBoundarySplit
    (hk : 1 ≤ k) :
    range C.attachmentPresentation.shared =
      range ((I.levelLocalizedInnerMarking k).successorBoundarySplit a).first := by
  rw [C.range_attachmentPresentation_shared]
  have hnextPoint :=
    congrArg
      (fun c : LevelAddress k =>
        (I.levelLocalizedAnnularCrosscut k c).innerPoint)
      C.next_eq
  let T := C.separator.innerSplit.cast rfl hnextPoint
  have hTfirst : range T.first = range C.separator.innerSplit.first := by
    dsimp only [T]
    exact C.separator.innerSplit.range_cast_first rfl hnextPoint
  have hTsecond : range T.second = range C.separator.innerSplit.second := by
    dsimp only [T]
    exact C.separator.innerSplit.range_cast_second rfl hnextPoint
  have hother : ∀ c : LevelAddress k, c ≠ a →
      c ≠ I.levelLocalizedSuccessor k a →
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈ range T.second := by
    intro c hca hcsuccessor
    have hcnext : c ≠ C.next := by
      intro h
      exact hcsuccessor (h.trans C.next_eq)
    exact hTsecond.symm ▸ C.inner_second c hca hcnext
  have hT := (I.levelLocalizedInnerMarking k).ranges_eq_successorBoundarySplit
    (three_le_card_levelAddress k hk) a T hother
  exact hTfirst.symm.trans hT.1

/-- The outer-boundary portion selected by this cell, independent of which
separator-side alternative realizes it. -/
noncomputable def exposedOuterArc : Set Plane := by
  classical
  exact if C.firstAlternative then
      range C.separator.outerArc₁
    else
      range C.separator.outerArc₀

/-- Reorient the outer complementary split so its first path traverses the
exposed cell arc from the starting cut to the successor cut. -/
noncomputable def outerCellBoundarySplit :
    (I.outerDisk k).toJordanCircle.TwoBoundaryArcPaths
      (I.levelLocalizedAnnularCrosscut k a).outerPoint
      (I.levelLocalizedAnnularCrosscut k C.next).outerPoint := by
  classical
  exact if C.firstAlternative then C.separator.outerSplit
    else C.separator.outerSplit.swap

theorem range_outerCellBoundarySplit_first :
    range C.outerCellBoundarySplit.first = C.exposedOuterArc := by
  classical
  by_cases h : C.firstAlternative
  · rw [outerCellBoundarySplit, if_pos h, exposedOuterArc, if_pos h]
    exact (Path.symm_range C.separator.outerSplit.first).symm
  · rw [outerCellBoundarySplit, if_neg h, exposedOuterArc, if_neg h]
    exact Path.symm_range C.separator.outerSplit.second

/-- The same outer split with its endpoint index rewritten to the canonical
inner-boundary successor label. -/
noncomputable def outerCellBoundarySplitToSuccessor :
    (I.outerDisk k).toJordanCircle.TwoBoundaryArcPaths
      (I.levelLocalizedAnnularCrosscut k a).outerPoint
      (I.levelLocalizedAnnularCrosscut k
        (I.levelLocalizedSuccessor k a)).outerPoint :=
  C.outerCellBoundarySplit.cast rfl <|
    congrArg
      (fun c : LevelAddress k =>
        (I.levelLocalizedAnnularCrosscut k c).outerPoint)
      C.next_eq

theorem range_outerCellBoundarySplitToSuccessor_first :
    range C.outerCellBoundarySplitToSuccessor.first = C.exposedOuterArc := by
  rw [outerCellBoundarySplitToSuccessor,
    JordanCircle.TwoBoundaryArcPaths.range_cast_first,
    C.range_outerCellBoundarySplit_first]

theorem range_attachmentPresentation_exposed :
    range C.attachmentPresentation.exposed =
      range C.decomposition.second.path ∪
        (C.exposedOuterArc ∪ range C.decomposition.first.path) := by
  classical
  by_cases h : C.firstAlternative
  · rw [attachmentPresentation, exposedOuterArc, dif_pos h, if_pos h]
    exact C.decomposition.range_exposedPath _
  · rw [attachmentPresentation, exposedOuterArc, dif_neg h, if_neg h]
    exact C.decomposition.range_exposedPath _

/-- No third retained outer endpoint lies on the exposed outer boundary arc
of the cut-free cell. -/
theorem other_outerPoint_not_mem_exposedOuterArc :
    ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
      (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
        C.exposedOuterArc := by
  intro c hca hcnext
  by_cases h : C.firstAlternative
  · rw [exposedOuterArc, if_pos h]
    exact h.2 c hca hcnext
  · rw [exposedOuterArc, if_neg h]
    exact (C.secondAlternative_of_not_first h).2 c hca hcnext

theorem other_outerPoint_mem_outerCellBoundarySplit_second
    (c : LevelAddress k) (hca : c ≠ a) (hcnext : c ≠ C.next) :
    (I.levelLocalizedAnnularCrosscut k c).outerPoint ∈
      range C.outerCellBoundarySplit.second := by
  have hcarrier :
      (I.levelLocalizedAnnularCrosscut k c).outerPoint ∈
        (I.outerDisk k).toJordanCircle.carrier :=
    by simpa only [(I.outerDisk k).carrier_toJordanCircle] using
      (I.levelLocalizedAnnularCrosscut k c).outerPoint_mem
  rw [← C.outerCellBoundarySplit.cover] at hcarrier
  rcases hcarrier with hfirst | hsecond
  · exact False.elim <|
      C.other_outerPoint_not_mem_exposedOuterArc c hca hcnext <| by
        rw [← C.range_outerCellBoundarySplit_first]
        exact hfirst
  · exact hsecond

theorem other_outerPoint_mem_outerCellBoundarySplitToSuccessor_second
    (c : LevelAddress k) (hca : c ≠ a)
    (hcsuccessor : c ≠ I.levelLocalizedSuccessor k a) :
    (I.levelLocalizedAnnularCrosscut k c).outerPoint ∈
      range C.outerCellBoundarySplitToSuccessor.second := by
  rw [outerCellBoundarySplitToSuccessor,
    JordanCircle.TwoBoundaryArcPaths.range_cast_second]
  apply C.other_outerPoint_mem_outerCellBoundarySplit_second c hca
  intro h
  exact hcsuccessor (h.trans C.next_eq)

theorem exposedOuterArc_subset_outerCarrier :
    C.exposedOuterArc ⊆ (I.outerDisk k).carrier := by
  classical
  by_cases h : C.firstAlternative
  · rw [exposedOuterArc, if_pos h]
    exact C.separator.outerArc₁_range_subset
  · rw [exposedOuterArc, if_neg h]
    exact C.separator.outerArc₀_range_subset

/-- Every third retained crosscut misses the entire boundary of this
cut-free cell. -/
theorem other_crosscut_disjoint_diskCarrier
    (c : LevelAddress k) (hca : c ≠ a) (hcnext : c ≠ C.next) :
    Disjoint (range (I.levelLocalizedAnnularCrosscut k c).path)
      C.disk.carrier := by
  apply Set.disjoint_left.mpr
  intro x hxCut hxCell
  change x ∈ C.attachmentPresentation.disk.carrier at hxCell
  rw [C.attachmentPresentation.carrier_eq,
    C.range_attachmentPresentation_shared,
    C.range_attachmentPresentation_exposed] at hxCell
  rcases hxCell with hxInner | hxSecond | hxOuter | hxFirst
  · have hxMeet : x ∈
        range (I.levelLocalizedAnnularCrosscut k c).path ∩
          (I.innerDisk k).carrier :=
      ⟨hxCut, C.separator.innerFirst_range_subset hxInner⟩
    rw [(I.levelLocalizedAnnularCrosscut k c).range_inter_inner] at hxMeet
    have hxEq := Set.mem_singleton_iff.mp hxMeet
    subst x
    have hEnds :
        (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
          ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
            (I.levelLocalizedAnnularCrosscut k C.next).innerPoint} :
              Set Plane) := by
      rw [← C.separator.innerSplit.overlap]
      exact ⟨hxInner, C.inner_second c hca hcnext⟩
    rcases hEnds with hEq | hEq
    · exact hca (I.levelLocalizedPolygonalBoundaryMark_injective k hEq)
    · exact hcnext (I.levelLocalizedPolygonalBoundaryMark_injective k
        (Set.mem_singleton_iff.mp hEq))
  · exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hcnext)
      hxCut hxSecond
  · have hxMeet : x ∈
        range (I.levelLocalizedAnnularCrosscut k c).path ∩
          (I.outerDisk k).carrier :=
      ⟨hxCut, C.exposedOuterArc_subset_outerCarrier hxOuter⟩
    rw [(I.levelLocalizedAnnularCrosscut k c).range_inter_outer] at hxMeet
    have hxEq := Set.mem_singleton_iff.mp hxMeet
    subst x
    exact C.other_outerPoint_not_mem_exposedOuterArc c hca hcnext hxOuter
  · exact Set.disjoint_left.mp
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hca)
      hxCut hxFirst

theorem firstCrosscut_range_subset_diskCarrier :
    range C.decomposition.first.path ⊆ C.disk.carrier := by
  intro x hx
  change x ∈ C.attachmentPresentation.disk.carrier
  rw [C.attachmentPresentation.carrier_eq,
    C.range_attachmentPresentation_exposed]
  exact Or.inr (Or.inr (Or.inr hx))

theorem secondCrosscut_range_subset_diskCarrier :
    range C.decomposition.second.path ⊆ C.disk.carrier := by
  intro x hx
  change x ∈ C.attachmentPresentation.disk.carrier
  rw [C.attachmentPresentation.carrier_eq,
    C.range_attachmentPresentation_exposed]
  exact Or.inr (Or.inl hx)

/-- Every selected cell lies in the closed outer polygonal disk. -/
theorem disk_closedRegion_subset_outerDisk :
    C.disk.closedRegion ⊆ (I.outerDisk k).closedRegion := by
  classical
  intro x hx
  rw [← C.decomposition.cellClosedRegions_union]
  by_cases h : C.firstAlternative
  · right
    rw [disk, attachmentPresentation, dif_pos h] at hx
    exact hx
  · left
    rw [disk, attachmentPresentation, dif_neg h] at hx
    exact hx

/-- A selected collar-cell interior is disjoint from the old closed disk. -/
theorem innerDisk_disjoint_diskInterior :
    Disjoint (I.innerDisk k).closedRegion C.disk.interiorRegion := by
  rw [Set.disjoint_left]
  intro x hxInner hxCellInterior
  have hxCellClosed : x ∈ C.disk.closedRegion := by
    rw [C.disk.closedRegion_eq_union]
    exact Or.inl hxCellInterior
  have hxShared : x ∈ range C.attachmentPresentation.shared := by
    rw [← C.base_inter_disk]
    exact ⟨hxInner, hxCellClosed⟩
  have hxCarrier : x ∈ C.disk.carrier := by
    change x ∈ C.attachmentPresentation.disk.carrier
    rw [C.attachmentPresentation.carrier_eq]
    exact Or.inl hxShared
  exact Set.disjoint_left.mp (PolygonalCircle.carrier_disjoint_interiorRegion _)
    hxCarrier hxCellInterior

/-- A selected collar-cell interior also misses the outer boundary. -/
theorem outerCarrier_disjoint_diskInterior :
    Disjoint (I.outerDisk k).carrier C.disk.interiorRegion := by
  apply Set.disjoint_left.mpr
  intro x hxOuter hxCell
  have hxSubset : C.disk.interiorRegion ⊆
      (I.outerDisk k).interiorRegion := by
    rw [← C.disk.interior_closedRegion,
      ← (I.outerDisk k).interior_closedRegion]
    exact interior_mono C.disk_closedRegion_subset_outerDisk
  exact Set.disjoint_left.mp
    (PolygonalCircle.carrier_disjoint_interiorRegion (I.outerDisk k))
    hxOuter (hxSubset hxCell)

/-- Every retained crosscut, not only the two bounding this cell, misses the
cell's open interior. -/
theorem crosscut_disjoint_diskInterior (c : LevelAddress k) :
    Disjoint (range (I.levelLocalizedAnnularCrosscut k c).path)
      C.disk.interiorRegion := by
  by_cases hca : c = a
  · subst c
    exact (PolygonalCircle.carrier_disjoint_interiorRegion C.disk).mono_left
      C.firstCrosscut_range_subset_diskCarrier
  by_cases hcnext : c = C.next
  · subst c
    exact (PolygonalCircle.carrier_disjoint_interiorRegion C.disk).mono_left
      C.secondCrosscut_range_subset_diskCarrier
  have hOff := C.other_crosscut_disjoint_diskCarrier c hca hcnext
  have hInnerClosed :
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
        (I.innerDisk k).closedRegion := by
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inr (I.levelLocalizedAnnularCrosscut k c).innerPoint_mem
  have hInnerNotInterior :
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∉
        C.disk.interiorRegion :=
    Set.disjoint_left.mp C.innerDisk_disjoint_diskInterior hInnerClosed
  have hInnerNotCarrier :
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∉
        C.disk.carrier :=
    Set.disjoint_left.mp hOff
      (Path.target_mem_range (I.levelLocalizedAnnularCrosscut k c).path)
  have hInnerExterior :
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
        C.disk.exteriorRegion := by
    have hSplit :
        (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
          C.disk.interiorRegion ∪ C.disk.exteriorRegion := by
      rw [C.disk.interior_union_exterior]
      exact hInnerNotCarrier
    exact hSplit.resolve_left hInnerNotInterior
  have hMaps : Set.MapsTo
      (I.levelLocalizedAnnularCrosscut k c).path Set.univ
        C.disk.exteriorRegion :=
    C.disk.mapsTo_exteriorRegion_of_isPreconnected
      isPreconnected_univ
      (I.levelLocalizedAnnularCrosscut k c).path.continuous.continuousOn
      (by
        intro t _ htCarrier
        exact Set.disjoint_left.mp hOff ⟨t, rfl⟩ htCarrier)
      ⟨1, Set.mem_univ _, by
        simpa only [Path.target] using hInnerExterior⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨t, rfl⟩ hxInterior
  exact Set.disjoint_left.mp C.disk.disjoint_interior_exterior
    hxInterior (hMaps (Set.mem_univ t))

/-- The entire boundary of any selected collar cell misses the open interior
of every other selected collar cell.  Its four boundary pieces respectively
lie on the old polygon, a retained cut, the outer polygon, and another
retained cut. -/
theorem diskCarrier_disjoint_diskInterior {b : LevelAddress k}
    (D : I.LocalizedCutFreeCellData k b) :
    Disjoint D.disk.carrier C.disk.interiorRegion := by
  apply Set.disjoint_left.mpr
  intro x hxD hxC
  change x ∈ D.attachmentPresentation.disk.carrier at hxD
  rw [D.attachmentPresentation.carrier_eq,
    D.range_attachmentPresentation_shared,
    D.range_attachmentPresentation_exposed] at hxD
  rcases hxD with hxInner | hxSecond | hxOuter | hxFirst
  · have hxInnerClosed : x ∈ (I.innerDisk k).closedRegion := by
      rw [(I.innerDisk k).closedRegion_eq_union]
      exact Or.inr (D.separator.innerFirst_range_subset hxInner)
    exact Set.disjoint_left.mp C.innerDisk_disjoint_diskInterior
      hxInnerClosed hxC
  · exact Set.disjoint_left.mp (C.crosscut_disjoint_diskInterior D.next)
      hxSecond hxC
  · exact Set.disjoint_left.mp C.outerCarrier_disjoint_diskInterior
      (D.exposedOuterArc_subset_outerCarrier hxOuter) hxC
  · exact Set.disjoint_left.mp (C.crosscut_disjoint_diskInterior b)
      hxFirst hxC

/-- At a noninitial shell level, distinct selected cells have different
polygonal boundaries.  A retained cut belonging to the second cell but not
to the first supplies a concrete witness. -/
theorem exists_diskCarrier_not_mem_diskCarrier
    (hk : 1 ≤ k) {b : LevelAddress k}
    (D : I.LocalizedCutFreeCellData k b) (hab : a ≠ b) :
    ∃ x, x ∈ D.disk.carrier ∧ x ∉ C.disk.carrier := by
  by_cases hbnext : b = C.next
  · have hb : b = I.levelLocalizedSuccessor k a :=
      hbnext.trans C.next_eq
    have hDnexta : D.next ≠ a := by
      intro hDnext
      apply I.levelLocalizedSuccessor_successor_ne k hk a
      rw [← hb, ← D.next_eq]
      exact hDnext
    have hDnextCnext : D.next ≠ C.next := by
      intro h
      exact D.next_ne (hbnext.trans h.symm)
    refine ⟨(I.levelLocalizedAnnularCrosscut k D.next).innerPoint,
      D.secondCrosscut_range_subset_diskCarrier
        (Path.target_mem_range _), ?_⟩
    exact Set.disjoint_left.mp
      (C.other_crosscut_disjoint_diskCarrier D.next hDnexta hDnextCnext)
      (Path.target_mem_range _)
  · refine ⟨(I.levelLocalizedAnnularCrosscut k b).innerPoint,
      D.firstCrosscut_range_subset_diskCarrier
        (Path.target_mem_range _), ?_⟩
    exact Set.disjoint_left.mp
      (C.other_crosscut_disjoint_diskCarrier b hab.symm hbnext)
      (Path.target_mem_range _)

/-- Distinct cells in every noninitial localized shell have disjoint open
interiors. -/
theorem disjoint_diskInterior {b : LevelAddress k}
    (hk : 1 ≤ k) (D : I.LocalizedCutFreeCellData k b) (hab : a ≠ b) :
    Disjoint C.disk.interiorRegion D.disk.interiorRegion := by
  exact C.disk.disjoint_interiorRegion_of_boundary_avoidance D.disk
    (D.diskCarrier_disjoint_diskInterior C)
    (C.diskCarrier_disjoint_diskInterior D)
    (C.exists_diskCarrier_not_mem_diskCarrier hk D hab)

end LocalizedCutFreeCellData

/-- A retained inner endpoint lies on the shared side of a canonical cell
exactly when its label is one of that cell's two successor endpoints. -/
theorem levelLocalizedInnerPoint_mem_canonicalCellShared_iff
    (k : ℕ) (hk : 1 ≤ k) (a c : LevelAddress k) :
    (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
        range (I.localizedCutFreeCellData k a).attachmentPresentation.shared ↔
      c = a ∨ c = I.levelLocalizedSuccessor k a := by
  rw [LocalizedCutFreeCellData.range_attachmentPresentation_shared_eq_successorBoundarySplit
    (I.localizedCutFreeCellData k a) hk]
  exact JordanCircle.FiniteMarking.point_mem_successorBoundarySplit_first_iff
    (I.levelLocalizedInnerMarking k) a c

/-- A retained outer endpoint lies on the exposed outer side of a canonical
cell exactly when its label is one of that cell's two successor endpoints. -/
theorem levelLocalizedOuterPoint_mem_canonicalCellExposed_iff
    (k : ℕ) (a c : LevelAddress k) :
    (I.levelLocalizedAnnularCrosscut k c).outerPoint ∈
        (I.localizedCutFreeCellData k a).exposedOuterArc ↔
      c = a ∨ c = I.levelLocalizedSuccessor k a := by
  let C := I.localizedCutFreeCellData k a
  constructor
  · intro hc
    by_cases hca : c = a
    · exact Or.inl hca
    by_cases hcsuccessor : c = I.levelLocalizedSuccessor k a
    · exact Or.inr hcsuccessor
    exact False.elim <|
      C.other_outerPoint_not_mem_exposedOuterArc c hca (by
        intro h
        exact hcsuccessor (h.trans C.next_eq)) hc
  · intro hc
    rw [← C.range_outerCellBoundarySplitToSuccessor_first]
    rcases hc with rfl | rfl
    · exact Path.source_mem_range C.outerCellBoundarySplitToSuccessor.first
    · exact Path.target_mem_range C.outerCellBoundarySplitToSuccessor.first

/-- At a genuine refinement level, the inner shared arcs of distinct
canonical cells meet only at the two endpoints of the first arc. -/
theorem localizedCutFreeCell_shared_inter_subset_endpoints
    (k : ℕ) (hk : 1 ≤ k) {a b : LevelAddress k} (hab : a ≠ b) :
    range (I.localizedCutFreeCellData k a).attachmentPresentation.shared ∩
        range (I.localizedCutFreeCellData k b).attachmentPresentation.shared ⊆
      ({(I.levelLocalizedAnnularCrosscut k a).innerPoint,
        (I.levelLocalizedAnnularCrosscut k
          (I.levelLocalizedSuccessor k a)).innerPoint} : Set Plane) := by
  rw [LocalizedCutFreeCellData.range_attachmentPresentation_shared_eq_successorBoundarySplit
        (I.localizedCutFreeCellData k a) hk,
    LocalizedCutFreeCellData.range_attachmentPresentation_shared_eq_successorBoundarySplit
        (I.localizedCutFreeCellData k b) hk]
  exact JordanCircle.FiniteMarking.successorBoundarySplit_first_inter_subset_endpoints
      (I.levelLocalizedInnerMarking k)
      (three_le_card_levelAddress k hk) hab

/-- At a genuine refinement level, the exposed outer arcs of distinct
canonical cells meet only at the two endpoints of the first arc. -/
theorem localizedCutFreeCell_exposedOuterArc_inter_subset_endpoints
    (k : ℕ) (hk : 1 ≤ k) {a b : LevelAddress k} (hab : a ≠ b) :
    (I.localizedCutFreeCellData k a).exposedOuterArc ∩
        (I.localizedCutFreeCellData k b).exposedOuterArc ⊆
      ({(I.levelLocalizedAnnularCrosscut k a).outerPoint,
        (I.levelLocalizedAnnularCrosscut k
          (I.levelLocalizedSuccessor k a)).outerPoint} : Set Plane) := by
  let T := fun c : LevelAddress k =>
    (I.localizedCutFreeCellData k c).outerCellBoundarySplitToSuccessor
  have hinter :=
    JordanCircle.TwoBoundaryArcPaths.successorSplitFamily_first_inter_subset_endpoints
        (J := (I.outerDisk k).toJordanCircle)
        (fun c : LevelAddress k =>
          (I.levelLocalizedAnnularCrosscut k c).outerPoint)
        (I.levelLocalizedOuterBoundaryMark_injective k)
        (I.levelLocalizedSuccessor k)
        (I.levelLocalizedSuccessor_bijective k).injective
        (I.levelLocalizedSuccessor_successor_ne k hk)
        T
        (fun c d hdc hdsuccessor =>
          LocalizedCutFreeCellData.other_outerPoint_mem_outerCellBoundarySplitToSuccessor_second
            (I.localizedCutFreeCellData k c) d hdc hdsuccessor)
        hab
  simpa only [T,
    LocalizedCutFreeCellData.range_outerCellBoundarySplitToSuccessor_first]
    using hinter

end JordanCircle.InitialAngularArcs

end

end Schoenflies
