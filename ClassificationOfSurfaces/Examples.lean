/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.NormalForm

/-!
# Standard examples

This file names the small surfaces we should keep as regression tests while the definitions mature.
For now most examples are stated as theorem boundaries over the placeholder representative spaces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The normal form for the sphere. -/
def sphereNormalForm : NormalForm :=
  NormalForm.sphere

/-- The normal form for the disk: orientable genus zero with one boundary component. -/
def diskNormalForm : NormalForm :=
  NormalForm.orientable 0 1

/-- The normal form for the annulus: orientable genus zero with two boundary components. -/
def annulusNormalForm : NormalForm :=
  NormalForm.orientable 0 2

/-- The normal form for the torus: orientable genus one with no boundary. -/
def torusNormalForm : NormalForm :=
  NormalForm.orientable 1 0

/-- The normal form for the projective plane: one crosscap and no boundary. -/
def projectivePlaneNormalForm : NormalForm :=
  NormalForm.nonOrientable 1 0

/-- The normal form for the Mobius strip: one crosscap and one boundary component. -/
def mobiusStripNormalForm : NormalForm :=
  NormalForm.nonOrientable 1 1

/-- Placeholder cell complex for the disk example. -/
def diskCellComplex : CellComplex :=
  CellComplex.sphere

/-- Placeholder cell complex for the annulus example. -/
def annulusCellComplex : CellComplex :=
  CellComplex.sphere

/-- Placeholder cell complex for the torus example. -/
def torusCellComplex : CellComplex :=
  CellComplex.sphere

/-- Placeholder cell complex for the projective-plane example. -/
def projectivePlaneCellComplex : CellComplex :=
  CellComplex.sphere

/-- Placeholder cell complex for the Mobius-strip example. -/
def mobiusStripCellComplex : CellComplex :=
  CellComplex.sphere

/-- Example target: the disk cell complex realizes the disk normal form. -/
theorem disk_has_normal_form :
    diskCellComplex.HasNormalForm diskNormalForm := by
  trivial

/-- Example target: the annulus cell complex realizes the annulus normal form. -/
theorem annulus_has_normal_form :
    annulusCellComplex.HasNormalForm annulusNormalForm := by
  trivial

/-- Example target: the torus cell complex realizes the torus normal form. -/
theorem torus_has_normal_form :
    torusCellComplex.HasNormalForm torusNormalForm := by
  trivial

/-- Example target: the projective-plane cell complex realizes the projective-plane normal form. -/
theorem projective_plane_has_normal_form :
    projectivePlaneCellComplex.HasNormalForm projectivePlaneNormalForm := by
  trivial

/-- Example target: the Mobius-strip cell complex realizes the Mobius-strip normal form. -/
theorem mobius_strip_has_normal_form :
    mobiusStripCellComplex.HasNormalForm mobiusStripNormalForm := by
  trivial

/-- Future target: the torus example should be homeomorphic to the orientable representative with
one handle and no boundary. -/
theorem torus_example_matches_representative :
    Nonempty (torusCellComplex.Realization ≃ₜ Quot (OrientableRel 1 0)) := by
  sorry

/-- Future target: the projective-plane example should be homeomorphic to the non-orientable
representative with one crosscap and no boundary. -/
theorem projective_plane_example_matches_representative :
    Nonempty (projectivePlaneCellComplex.Realization ≃ₜ Quot (NonOrientableRel 1 0)) := by
  sorry

/-- Future target: the Mobius-strip example should be homeomorphic to the non-orientable
representative with one crosscap and one boundary component. -/
theorem mobius_strip_example_matches_representative :
    Nonempty (mobiusStripCellComplex.Realization ≃ₜ Quot (NonOrientableRel 1 1)) := by
  sorry

end ClassificationOfSurfaces
end Topology
end LeanEval
