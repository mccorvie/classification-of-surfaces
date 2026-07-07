/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.EvalStatement
import ClassificationOfSurfaces.Examples

/-!
# Public API map

This file is the preferred first Lean file for collaborators to read. It re-exports the current
project skeleton and documents the intended handoff points between teams.

## Eval input

* `EvalSurface`
* `evalSurface`
* the typeclass hypothesis block used by `classification_of_surfaces`

## Moise / PL route

* `EuclideanComplex`
* `EuclideanComplex.Subdivision`
* `PLMap`
* `PLHomeomorph`
* `CombinatorialTwoManifoldWithBoundary`
* `CombinatorialTwoCell`
* `PLComplexInSpace`
* `FinitePLTriangulationData`
* `MoiseTwoManifold`
* `MoiseTwoManifold.finitePLTriangulationData`
* `mathlib_bordered_surface_finitely_triangulable`
* `compact_eval_surface_finitely_triangulable`

The Moise route should produce `FiniteSurfaceTriangulation`; it should not import or depend on the
Gallier-Xu normal-form proof.

## Shared triangulation and cell-complex boundary

* `OrientedEdge`
* `FiniteSurfaceTriangulation`
* `PLComplexInSpace.FiniteSupportData.OneSimplex`
* `PLComplexInSpace.FiniteSupportData.TwoSimplex`
* `PLComplexInSpace.FiniteSupportData.triangleBoundaryWord`
* `PLComplexInSpace.toFiniteSurfaceTriangulation`
* `FinitePLTriangulationData.toFiniteSurfaceTriangulation`
* `FiniteSurfaceTriangulation.toCellComplex`
* `FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic`
* `finite_triangulation_to_cell_complex`
* `compact_surface_homeomorphic_to_cell_complex`

## Shared finite surface cell complexes

* `SurfaceCellComplex`
* `SurfaceCellComplex.SignedDart`
* `SurfaceCellComplex.oneFacePresentation`
* `SurfaceCellComplex.PreRealization`
* `SurfaceCellComplex.gluingRel`
* `SurfaceCellComplex.Realization`
* `SurfaceCellComplex.realizationCongr`
* `SurfaceCellComplex.realizationCongrRight`

The legacy names `CellComplex`, `FiniteTriangulation`, and `Triangulable` remain as compatibility
aliases. New code should prefer the `SurfaceCellComplex` and `FiniteSurfaceTriangulation` names.

## Gallier-Xu tail

* `SurfaceCellComplex.HasNormalForm`
* `surface_cell_complex_reduces_to_normal_form`
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
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

end ClassificationOfSurfaces
end Topology
end LeanEval
