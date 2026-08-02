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

private noncomputable def exposedOuterArc : Set Plane := by
  classical
  exact if C.firstAlternative then
      range C.separator.outerArc₁
    else
      range C.separator.outerArc₀

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

end LocalizedCutFreeCellData

end JordanCircle.InitialAngularArcs

end

end Schoenflies
