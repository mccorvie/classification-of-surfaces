import Schoenflies.LocalizedTargetCells

/-!
# Homeomorphisms of corresponding localized collar cells

Each source and target cell is a polygonal disk attached along its selected
inner boundary arc.  The general topological disk-attachment filling maps
the two presentations parametrically, in particular agreeing exactly on
the shared arc.  Global finite-stage gluing is kept separate from this
local construction.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

/-- Fill the canonical source cell by its radially transported standard
target cell. -/
noncomputable def cellHomeomorph :
    C.attachmentPresentation.disk.closedRegion ≃ₜ
      C.targetAttachmentPresentation.disk.closedRegion :=
  PolygonalDiskAttachment.newDiskHomeomorph
    C.attachmentPresentation C.targetAttachmentPresentation

/-- The cell filling uses the same unit-interval parameter on the entire
arc shared with the preceding exhaustion disk. -/
theorem cellHomeomorph_apply_shared (t : unitInterval) :
    (C.cellHomeomorph
        ⟨C.attachmentPresentation.shared t,
          C.attachmentPresentation.shared_mem_closedRegion t⟩ : Plane) =
      C.targetAttachmentPresentation.shared t :=
  PolygonalDiskAttachment.newDiskHomeomorph_apply_shared
    C.attachmentPresentation C.targetAttachmentPresentation t

/-- The cell filling also uses the same unit-interval parameter on the
complementary boundary arc.  In particular, once a radial cut is identified
as a subpath of that arc, adjacent cell fillings agree pointwise on it. -/
theorem cellHomeomorph_apply_exposed (t : unitInterval) :
    (C.cellHomeomorph
        ⟨C.attachmentPresentation.exposed t,
          C.attachmentPresentation.exposed_mem_closedRegion t⟩ : Plane) =
      C.targetAttachmentPresentation.exposed t :=
  PolygonalDiskAttachment.newDiskHomeomorph_apply_exposed
    C.attachmentPresentation C.targetAttachmentPresentation t

/-- Pointwise control on the successor radial cut, in its reversed
orientation as the first third of the exposed boundary route. -/
theorem cellHomeomorph_apply_secondPath_symm (t : unitInterval) :
    (C.cellHomeomorph
        ⟨C.decomposition.second.path.symm t, by
          rw [← C.attachmentPresentation_exposedSecondCoordinate t]
          exact C.attachmentPresentation.exposed_mem_closedRegion _⟩ : Plane) =
      C.targetDecomposition.second.path.symm t := by
  let u := PolygonalCircle.AnnularCellDecomposition.exposedSecondCoordinate t
  calc
    (C.cellHomeomorph
        ⟨C.decomposition.second.path.symm t, _⟩ : Plane) =
        (C.cellHomeomorph
          ⟨C.attachmentPresentation.exposed u,
            C.attachmentPresentation.exposed_mem_closedRegion u⟩ : Plane) := by
      exact congrArg
        (fun x : C.attachmentPresentation.disk.closedRegion =>
          (C.cellHomeomorph x : Plane))
        (Subtype.ext
          (C.attachmentPresentation_exposedSecondCoordinate t).symm)
    _ = C.targetAttachmentPresentation.exposed u :=
      C.cellHomeomorph_apply_exposed u
    _ = C.targetDecomposition.second.path.symm t :=
      C.targetAttachmentPresentation_exposedSecondCoordinate t

/-- Pointwise control on the initial radial cut, in its forward orientation
as the last part of the exposed boundary route. -/
theorem cellHomeomorph_apply_firstPath (t : unitInterval) :
    (C.cellHomeomorph
        ⟨C.decomposition.first.path t, by
          rw [← C.attachmentPresentation_exposedFirstCoordinate t]
          exact C.attachmentPresentation.exposed_mem_closedRegion _⟩ : Plane) =
      C.targetDecomposition.first.path t := by
  let u := PolygonalCircle.AnnularCellDecomposition.exposedFirstCoordinate t
  calc
    (C.cellHomeomorph ⟨C.decomposition.first.path t, _⟩ : Plane) =
        (C.cellHomeomorph
          ⟨C.attachmentPresentation.exposed u,
            C.attachmentPresentation.exposed_mem_closedRegion u⟩ : Plane) := by
      exact congrArg
        (fun x : C.attachmentPresentation.disk.closedRegion =>
          (C.cellHomeomorph x : Plane))
        (Subtype.ext
          (C.attachmentPresentation_exposedFirstCoordinate t).symm)
    _ = C.targetAttachmentPresentation.exposed u :=
      C.cellHomeomorph_apply_exposed u
    _ = C.targetDecomposition.first.path t :=
      C.targetAttachmentPresentation_exposedFirstCoordinate t

/-- The second radial cut in its native outer-to-inner orientation. -/
theorem cellHomeomorph_apply_secondPath (t : unitInterval) :
    (C.cellHomeomorph
        ⟨C.decomposition.second.path t,
          C.decomposition_secondPath_mem_disk_closedRegion t⟩ : Plane) =
      C.targetDecomposition.second.path t := by
  simpa only [Path.symm_apply, Function.comp_apply,
    unitInterval.symm_symm] using
      C.cellHomeomorph_apply_secondPath_symm (unitInterval.symm t)

/-- Concrete control on the cut carrying the cell's initial label. -/
theorem cellHomeomorph_apply_initialCut (t : unitInterval) :
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k a).path t,
          C.decomposition_firstPath_mem_disk_closedRegion t⟩ : Plane) =
      (I.levelTargetAnnularCrosscut k a).path t := by
  exact C.cellHomeomorph_apply_firstPath t

/-- Concrete control on the cut carrying the cell's successor label. -/
theorem cellHomeomorph_apply_successorCut (t : unitInterval) :
    (C.cellHomeomorph
        ⟨(I.levelLocalizedAnnularCrosscut k C.next).path t,
          C.decomposition_secondPath_mem_disk_closedRegion t⟩ : Plane) =
      (I.levelTargetAnnularCrosscut k C.next).path t := by
  exact C.cellHomeomorph_apply_secondPath t

/-- On the part of a cell meeting the outer exhaustion polygon, the cell
homeomorphism lands on the outer standard target polygon. -/
theorem cellHomeomorph_mem_targetOuterCarrier_of_mem_outerCarrier
    (hk : 1 ≤ k) {x : Plane} (hxCell : x ∈ C.disk.closedRegion)
    (hxOuter : x ∈
      (I.localizedMarkedPolygonalDisk (k + 2)).carrier) :
    (C.cellHomeomorph ⟨x, hxCell⟩ : Plane) ∈
      (StandardPolygonalCollars.disk (k + 2)).carrier := by
  have hxCarrier : x ∈ C.disk.carrier := by
    rw [C.disk.closedRegion_eq_union] at hxCell
    rcases hxCell with hxInterior | hxCarrier
    · exact False.elim <| Set.disjoint_left.mp
        C.outerCarrier_disjoint_diskInterior hxOuter hxInterior
    · exact hxCarrier
  change x ∈ C.attachmentPresentation.disk.carrier at hxCarrier
  rw [C.attachmentPresentation.carrier_eq,
    C.range_attachmentPresentation_exposed] at hxCarrier
  rcases hxCarrier with hxShared | hxSecond | hxOuterArc | hxFirst
  · have hxInner : x ∈
        (I.localizedMarkedPolygonalDisk (k + 1)).carrier := by
      rw [C.range_attachmentPresentation_shared] at hxShared
      exact C.separator.innerFirst_range_subset hxShared
    exact False.elim <| Set.disjoint_left.mp
      (PolygonalCircle.AnnularCrosscut.disjoint_inner_outer_carriers
        (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)))
      hxInner hxOuter
  · have hxMeet : x ∈
        range C.decomposition.second.path ∩
          (I.localizedMarkedPolygonalDisk (k + 2)).carrier :=
      ⟨hxSecond, hxOuter⟩
    change x ∈ range
      (I.levelLocalizedAnnularCrosscut k C.next).path ∩
        (I.localizedMarkedPolygonalDisk (k + 2)).carrier at hxMeet
    rw [(I.levelLocalizedAnnularCrosscut k C.next).range_inter_outer] at hxMeet
    have hxEq := Set.mem_singleton_iff.mp hxMeet
    subst x
    have hmap :
        (C.cellHomeomorph
          ⟨(I.levelLocalizedAnnularCrosscut k C.next).outerPoint,
            hxCell⟩ : Plane) =
          (I.levelTargetAnnularCrosscut k C.next).outerPoint := by
      calc
        (C.cellHomeomorph
            ⟨(I.levelLocalizedAnnularCrosscut k C.next).outerPoint,
              hxCell⟩ : Plane) =
            (C.cellHomeomorph
              ⟨(I.levelLocalizedAnnularCrosscut k C.next).path 0,
                C.decomposition_secondPath_mem_disk_closedRegion 0⟩ :
                  Plane) := by
            apply congrArg (fun z => (C.cellHomeomorph z : Plane))
            apply Subtype.ext
            exact (I.levelLocalizedAnnularCrosscut k C.next).path.source.symm
        _ = (I.levelTargetAnnularCrosscut k C.next).path 0 :=
          C.cellHomeomorph_apply_successorCut 0
        _ = (I.levelTargetAnnularCrosscut k C.next).outerPoint :=
          (I.levelTargetAnnularCrosscut k C.next).path.source
    rw [hmap]
    exact (I.levelTargetAnnularCrosscut k C.next).outerPoint_mem
  · obtain ⟨t, hsource⟩ :=
      C.exists_attachmentPresentation_exposedOuterCoordinate_of_mem hxOuterArc
    let u :=
      PolygonalCircle.AnnularCellDecomposition.exposedOuterCoordinate t
    have htarget : C.targetAttachmentPresentation.exposed u ∈
        (StandardPolygonalCollars.disk (k + 2)).carrier := by
      have htargetFirst := C.targetFirstAlternative_of_one_le hk
      rw [targetAttachmentPresentation, dif_pos htargetFirst]
      change (C.targetDecomposition.exposedPath
        C.targetSeparator.outerArc₁) u ∈ _
      rw [C.targetDecomposition.exposedPath_exposedOuterCoordinate]
      exact C.targetSeparator.outerArc₁_range_subset ⟨t, rfl⟩
    have hmap := C.cellHomeomorph_apply_exposed u
    have hsame :
        (C.cellHomeomorph ⟨x, hxCell⟩ : Plane) =
          (C.cellHomeomorph
            ⟨C.attachmentPresentation.exposed u,
              C.attachmentPresentation.exposed_mem_closedRegion u⟩ :
                Plane) := by
      apply congrArg (fun z => (C.cellHomeomorph z : Plane))
      exact Subtype.ext hsource.symm
    rw [hsame, hmap]
    exact htarget
  · have hxMeet : x ∈
        range C.decomposition.first.path ∩
          (I.localizedMarkedPolygonalDisk (k + 2)).carrier :=
      ⟨hxFirst, hxOuter⟩
    change x ∈ range
      (I.levelLocalizedAnnularCrosscut k a).path ∩
        (I.localizedMarkedPolygonalDisk (k + 2)).carrier at hxMeet
    rw [(I.levelLocalizedAnnularCrosscut k a).range_inter_outer] at hxMeet
    have hxEq := Set.mem_singleton_iff.mp hxMeet
    subst x
    have hmap :
        (C.cellHomeomorph
          ⟨(I.levelLocalizedAnnularCrosscut k a).outerPoint,
            hxCell⟩ : Plane) =
          (I.levelTargetAnnularCrosscut k a).outerPoint := by
      calc
        (C.cellHomeomorph
            ⟨(I.levelLocalizedAnnularCrosscut k a).outerPoint,
              hxCell⟩ : Plane) =
            (C.cellHomeomorph
              ⟨(I.levelLocalizedAnnularCrosscut k a).path 0,
                C.decomposition_firstPath_mem_disk_closedRegion 0⟩ :
                  Plane) := by
            apply congrArg (fun z => (C.cellHomeomorph z : Plane))
            apply Subtype.ext
            exact (I.levelLocalizedAnnularCrosscut k a).path.source.symm
        _ = (I.levelTargetAnnularCrosscut k a).path 0 :=
          C.cellHomeomorph_apply_initialCut 0
        _ = (I.levelTargetAnnularCrosscut k a).outerPoint :=
          (I.levelTargetAnnularCrosscut k a).path.source
    rw [hmap]
    exact (I.levelTargetAnnularCrosscut k a).outerPoint_mem

end JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

end

end Schoenflies
