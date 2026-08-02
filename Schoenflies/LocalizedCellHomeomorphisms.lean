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
        ⟨C.attachmentPresentation.exposed t, by
          rw [C.attachmentPresentation.disk.closedRegion_eq_union]
          right
          rw [C.attachmentPresentation.carrier_eq]
          exact Or.inr ⟨t, rfl⟩⟩ : Plane) =
      C.targetAttachmentPresentation.exposed t :=
  PolygonalDiskAttachment.newDiskHomeomorph_apply_exposed
    C.attachmentPresentation C.targetAttachmentPresentation t

end JordanCircle.InitialAngularArcs.LocalizedCutFreeCellData

end

end Schoenflies
