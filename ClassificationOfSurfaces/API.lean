/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.EvalStatement
import ClassificationOfSurfaces.Examples
import ClassificationOfSurfaces.Moise.IntrinsicGraphApproximation
import ClassificationOfSurfaces.Moise.IntrinsicGraphPL
import ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary
import ClassificationOfSurfaces.Moise.IntrinsicFaceExtension
import ClassificationOfSurfaces.Moise.IntrinsicFaceFilling
import ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision
import ClassificationOfSurfaces.Moise.FrontierGlue
import ClassificationOfSurfaces.Moise.PlaneCycle

/-!
# Public API map

This file is the preferred first Lean file for collaborators to read. It re-exports the current
project skeleton and documents the intended handoff points between teams.

## Eval input

* `EvalSurface`
* `ChartBoundaryInvariant`
* `evalSurface`
* `eval_surface_hypotheses`
* the typeclass hypothesis block used by `classification_of_surfaces`

## Moise route (current; see `docs/MOISE_ROUTE.md` for status and handoff map)

* `GeometricTriangulation` and `GeometricRealization` (`Moise/GeometricTriangulation.lean`)
* `PlaneComplex`, `IsPLOn`, `IsPLOnSet` (`Moise/PlaneComplex.lean`)
* `IntrinsicTwoComplex`, its faithful `Subdivision`, `IsPLMap`, and `PLHomeomorph`
  (`Moise/IntrinsicComplex.lean`)
* intrinsic one-skeleton polygonal replacement, exact finite edge complexes, and embedding
  (`Moise/IntrinsicGraphApproximation.lean`, `Moise/IntrinsicGraphPL.lean`)
* standard plane models, exact polygonal face-boundary cycles, certified relative PL fillings,
  and faithful arbitrarily fine midpoint subdivisions (`Moise/IntrinsicFaceModel.lean`,
  `Moise/IntrinsicFaceBoundary.lean`, `Moise/IntrinsicFaceExtension.lean`,
  `Moise/IntrinsicFaceFilling.lean`, `Moise/IntrinsicCellwiseExtension.lean`,
  `Moise/IntrinsicFineSubdivision.lean`)
* strongly positive frontier controls and continuous vanishing-error gluing
  (`Moise/FrontierGlue.lean`)
* `PolygonalCircle`, `polygonal_jordan`, the crossing `index` (`Moise/PolygonalJordan.lean`)
* `closedRegion_is_polyhedron`, `polygonal_schoenflies_rel` (`Moise/PolygonalSchoenflies.lean`)
* `pl_approximation_two_manifold` (`Moise/PLApproximation.lean`)
* `JoinedByBrokenLine` (`Moise/BrokenLine.lean`)
* `MoiseChart`, `MoiseChart.BoundaryFaithful`, `exists_moiseChart_core_mem_nhds`
  (`Moise/ChartExtraction.lean`)
* `PartialTriangulation`, `RadoInvariant`, `moise_finite_chart_cover`, `moise_induction_step`,
  `moise_triangulation_of_boundaries` (`Moise/ChartInduction.lean`)
* `moise_triangulation` (`Triangulation.lean`)
* anchors and countermodels: `Moise/Anchors.lean`, `Moise/Countermodels.lean`

The legacy `PL.lean` layer (`EuclideanComplex`, `PLMap`, `PLComplexInSpace`, `MoiseTwoManifold`,
the `mathlib_bordered_surface_*` chain) was deleted after the definition-faithfulness audit — see
`docs/KNOWN_WEAK.md` for the record and git history (`git log -- ClassificationOfSurfaces/PL.lean`)
for the quarry, in particular the concrete closed-triangle geometry.

## Shared triangulation and cell-complex boundary

* `OrientedEdge`
* `FiniteSurfaceTriangulation` (ledgered; fed by the `GeometricTriangulation` bridge)
* `compact_eval_surface_finitely_triangulable`
* `FiniteSurfaceTriangulation.toCellComplex`
* `FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic`
* `finite_triangulation_to_cell_complex`
* `compact_surface_homeomorphic_to_cell_complex`

## Shared finite surface cell complexes

* `SurfaceCellComplex`
* `SurfaceCellComplex.BoundaryOccurrence`
* `SurfaceCellComplex.IsBoundaryDart`
* `SurfaceCellComplex.IsSurfaceValid`
* `SurfaceCellComplex.FaceAdjacent`
* `SurfaceCellComplex.IsConnected`
* `SurfaceCellComplex.SignedDart`
* `SurfaceCellComplex.oneFacePresentation`
* `SurfaceCellComplex.PreRealization`
* `SurfaceCellComplex.gluingRel`
* `SurfaceCellComplex.Realization`
* `SurfaceCellComplex.realizationCongr`
* `SurfaceCellComplex.realizationCongrRight`

The legacy names `CellComplex` and `FiniteTriangulation` remain as compatibility aliases.  New
code should prefer `SurfaceCellComplex` and, for triangulations, `GeometricTriangulation`.

## Gallier-Xu tail

* `NormalForm.IsEvalAdmissible`
* `SurfaceCellComplex.RealizesNormalForm`
* `SurfaceCellComplex.HasNormalForm`
* `surface_cell_complex_reduces_to_normal_form`
* `SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm`
* `SurfaceCellComplex.hasEvalRepresentative`

The Gallier-Xu tail should consume only `SurfaceCellComplex` and quotient-realization APIs. It
should not mention PL maps, Moise triangulation, or manifold chart machinery.

## Eval representatives and final theorem

* `SphereRepresentative`
* `OrientableRel`
* `NonOrientableRel`
* `classification_of_surfaces`
* `topological_classification_of_surfaces`

The final theorem should remain a short assembly proof using
`compact_surface_homeomorphic_to_cell_complex` and `SurfaceCellComplex.hasEvalRepresentative`.
The C0 Eval route is relative to `ChartBoundaryInvariant`; positive-regularity surfaces obtain this
class from mathlib's boundary-point theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

end ClassificationOfSurfaces
end Topology
end LeanEval
