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

end JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

end

end Schoenflies
