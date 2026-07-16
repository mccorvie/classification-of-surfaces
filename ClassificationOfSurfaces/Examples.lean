/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.NormalForm

/-!
# Standard examples

This file names the small surfaces we should keep as regression tests while the definitions mature.
The examples are concrete one-face boundary-word presentations in the shared `SurfaceCellComplex`
API. Their realization theorems remain theorem boundaries until quotient realizations are
implemented.
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

/-- Edge names for the disk example. -/
inductive DiskEdge where
  | h
deriving DecidableEq, Repr, Fintype

/-- Edge names for the annulus example. -/
inductive AnnulusEdge where
  | c₀
  | c₁
deriving DecidableEq, Repr, Fintype

/-- Edge names for the torus example. -/
inductive TorusEdge where
  | a
  | b
deriving DecidableEq, Repr, Fintype

/-- Edge names for the projective-plane example. -/
inductive ProjectivePlaneEdge where
  | a
deriving DecidableEq, Repr, Fintype

/-- Edge names for the Mobius-strip example. -/
inductive MobiusStripEdge where
  | a
  | h
deriving DecidableEq, Repr, Fintype

open SurfaceCellComplex.SignedDart

/-- One-face boundary-word presentation for the disk. -/
def diskCellComplex : CellComplex :=
  SurfaceCellComplex.oneFacePresentation DiskEdge [pos DiskEdge.h]

/-- One-face boundary-word presentation for the annulus, with two boundary contours. -/
def annulusCellComplex : CellComplex :=
  SurfaceCellComplex.oneFacePresentation AnnulusEdge
    [pos AnnulusEdge.c₀, pos AnnulusEdge.c₁]

/-- One-face boundary-word presentation for the torus: `a b a⁻¹ b⁻¹`. -/
def torusCellComplex : CellComplex :=
  SurfaceCellComplex.oneFacePresentation TorusEdge
    [pos TorusEdge.a, pos TorusEdge.b, neg TorusEdge.a, neg TorusEdge.b]

/-- One-face boundary-word presentation for the projective plane: `a a`. -/
def projectivePlaneCellComplex : CellComplex :=
  SurfaceCellComplex.oneFacePresentation ProjectivePlaneEdge
    [pos ProjectivePlaneEdge.a, pos ProjectivePlaneEdge.a]

/-- One-face boundary-word presentation for the Mobius strip: `a a h`. -/
def mobiusStripCellComplex : CellComplex :=
  SurfaceCellComplex.oneFacePresentation MobiusStripEdge
    [pos MobiusStripEdge.a, pos MobiusStripEdge.a, pos MobiusStripEdge.h]

/-- Regression check: the torus example has the expected four-letter boundary word. -/
example : torusCellComplex.faceBoundaryLength PUnit.unit = 4 := by
  rfl

/-- Regression check: the projective-plane example has the expected two-letter boundary word. -/
example : projectivePlaneCellComplex.faceBoundaryLength PUnit.unit = 2 := by
  rfl

/-- Regression check: edge-orbit multiplicity accepts the non-orientable word `a a`. -/
theorem projectivePlaneCellComplex_isSurfaceValid :
    projectivePlaneCellComplex.IsSurfaceValid := by
  refine ⟨⟨PUnit.unit⟩, ?_, ?_, ?_⟩
  · intro f g _h
    cases f
    cases g
    rfl
  · intro d
    cases d with
    | pos e =>
        change neg e ≠ pos e
        intro h
        cases h
    | neg e =>
        change pos e ≠ neg e
        intro h
        cases h
  · intro d
    right
    let o₀ : projectivePlaneCellComplex.BoundaryOccurrence :=
        ⟨PUnit.unit, ⟨0, by simp [projectivePlaneCellComplex,
          SurfaceCellComplex.oneFacePresentation]⟩⟩
    let o₁ : projectivePlaneCellComplex.BoundaryOccurrence :=
        ⟨PUnit.unit, ⟨1, by simp [projectivePlaneCellComplex,
          SurfaceCellComplex.oneFacePresentation]⟩⟩
    refine ⟨o₀, o₁, ?_, ?_, ?_, ?_⟩
    · intro h
      have hval := congrArg (fun o => o.2.val) h
      simp [o₀, o₁] at hval
    · cases d with
      | pos e =>
          cases e
          change pos ProjectivePlaneEdge.a = pos ProjectivePlaneEdge.a ∨ _
          exact Or.inl rfl
      | neg e =>
          cases e
          change _ ∨ pos ProjectivePlaneEdge.a = pos ProjectivePlaneEdge.a
          exact Or.inr rfl
    · cases d with
      | pos e =>
          cases e
          change pos ProjectivePlaneEdge.a = pos ProjectivePlaneEdge.a ∨ _
          exact Or.inl rfl
      | neg e =>
          cases e
          change _ ∨ pos ProjectivePlaneEdge.a = pos ProjectivePlaneEdge.a
          exact Or.inr rfl
    · rintro ⟨f, i⟩ _hi
      cases f
      change Fin 2 at i
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- Regression check: the Mobius-strip example has the expected three-letter boundary word. -/
example : mobiusStripCellComplex.faceBoundaryLength PUnit.unit = 3 := by
  rfl

/-- A minimal one-triangle triangulation of `PUnit`, used only to test the data conversion API. -/
def oneTriangleTriangulation : FiniteSurfaceTriangulation PUnit where
  Vertex := Fin 3
  Edge := Fin 3
  Triangle := PUnit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := PUnit
  realizationTop := inferInstance
  edgeVertices := fun
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {2, 0}
  triangleVertices := fun _ => Finset.univ
  edgeSource := fun e => e
  edgeTarget := fun e => ⟨(e.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  triangleBoundary := fun _ =>
    [OrientedEdge.pos 0, OrientedEdge.pos 1, OrientedEdge.pos 2]
  edgeIsBoundary := fun _ => True
  isSurfaceTriangulation :=
    { edge_card := by
        intro e
        fin_cases e <;>
        decide
      triangle_card := by
        intro t
        cases t
        decide
      edgeSource_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeTarget_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeSource_ne_edgeTarget := by
        intro e
        fin_cases e <;>
        decide
      boundary_edge_vertices_subset := by
        intro t oe hoe
        exact Finset.subset_univ _ }
  homeomorphSurface := ⟨Homeomorph.refl PUnit⟩

/-- Regression check: triangulation-to-cell-complex keeps triangles as faces. -/
example : oneTriangleTriangulation.toCellComplex.numFaces = 1 := by
  rfl

/-- Regression check: triangulation-to-cell-complex keeps each geometric edge as two darts. -/
example : oneTriangleTriangulation.toCellComplex.numDarts = 6 := by
  rfl

/-- Regression check: the triangle boundary word has length three. -/
example :
    oneTriangleTriangulation.toCellComplex.faceBoundaryLength PUnit.unit = 3 := by
  rfl

/-- A one-triangle fixture with one reversed side, used to test oriented conversion. -/
def reversedSideTriangulation : FiniteSurfaceTriangulation PUnit where
  Vertex := Fin 3
  Edge := Fin 3
  Triangle := PUnit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := PUnit
  realizationTop := inferInstance
  edgeVertices := fun
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {2, 0}
  triangleVertices := fun _ => Finset.univ
  edgeSource := fun e => e
  edgeTarget := fun e => ⟨(e.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  triangleBoundary := fun _ =>
    [OrientedEdge.pos 0, OrientedEdge.pos 1, OrientedEdge.neg 2]
  edgeIsBoundary := fun _ => True
  isSurfaceTriangulation :=
    { edge_card := by
        intro e
        fin_cases e <;>
        decide
      triangle_card := by
        intro t
        cases t
        decide
      edgeSource_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeTarget_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeSource_ne_edgeTarget := by
        intro e
        fin_cases e <;>
        decide
      boundary_edge_vertices_subset := by
        intro t oe hoe
        exact Finset.subset_univ _ }
  homeomorphSurface := ⟨Homeomorph.refl PUnit⟩

/-- Regression check: triangulation-to-cell-complex preserves reversed triangle sides. -/
example :
    reversedSideTriangulation.toCellComplex.boundary PUnit.unit =
      [pos (0 : Fin 3), pos (1 : Fin 3), neg (2 : Fin 3)] := by
  rfl

/-- Example target: the disk cell complex realizes the disk normal form. -/
theorem disk_has_normal_form :
    diskCellComplex.HasNormalForm diskNormalForm := by
  exact SurfaceCellComplex.hasNormalFormOfRealizes diskCellComplex diskNormalForm
    ⟨orientableRelPUnitHomeomorph 0 1⟩

/-- Example target: the annulus cell complex realizes the annulus normal form. -/
theorem annulus_has_normal_form :
    annulusCellComplex.HasNormalForm annulusNormalForm := by
  exact SurfaceCellComplex.hasNormalFormOfRealizes annulusCellComplex annulusNormalForm
    ⟨orientableRelPUnitHomeomorph 0 2⟩

/-- Example target: the torus cell complex realizes the torus normal form. -/
theorem torus_has_normal_form :
    torusCellComplex.HasNormalForm torusNormalForm := by
  exact SurfaceCellComplex.hasNormalFormOfRealizes torusCellComplex torusNormalForm
    ⟨orientableRelPUnitHomeomorph 1 0⟩

/-- Example target: the projective-plane cell complex realizes the projective-plane normal form. -/
theorem projective_plane_has_normal_form :
    projectivePlaneCellComplex.HasNormalForm projectivePlaneNormalForm := by
  exact SurfaceCellComplex.hasNormalFormOfRealizes projectivePlaneCellComplex
    projectivePlaneNormalForm
    ⟨nonOrientableRelPUnitHomeomorph 1 0⟩

/-- Example target: the Mobius-strip cell complex realizes the Mobius-strip normal form. -/
theorem mobius_strip_has_normal_form :
    mobiusStripCellComplex.HasNormalForm mobiusStripNormalForm := by
  exact SurfaceCellComplex.hasNormalFormOfRealizes mobiusStripCellComplex mobiusStripNormalForm
    ⟨nonOrientableRelPUnitHomeomorph 1 1⟩

/-- Future target: the torus example should be homeomorphic to the orientable representative with
one handle and no boundary. -/
theorem torus_example_matches_representative :
    Nonempty (torusCellComplex.Realization ≃ₜ Quot (OrientableRel 1 0)) := by
  exact ⟨orientableRelPUnitHomeomorph 1 0⟩

/-- Future target: the projective-plane example should be homeomorphic to the non-orientable
representative with one crosscap and no boundary. -/
theorem projective_plane_example_matches_representative :
    Nonempty (projectivePlaneCellComplex.Realization ≃ₜ Quot (NonOrientableRel 1 0)) := by
  exact ⟨nonOrientableRelPUnitHomeomorph 1 0⟩

/-- Future target: the Mobius-strip example should be homeomorphic to the non-orientable
representative with one crosscap and one boundary component. -/
theorem mobius_strip_example_matches_representative :
    Nonempty (mobiusStripCellComplex.Realization ≃ₜ Quot (NonOrientableRel 1 1)) := by
  exact ⟨nonOrientableRelPUnitHomeomorph 1 1⟩

end ClassificationOfSurfaces
end Topology
end LeanEval
