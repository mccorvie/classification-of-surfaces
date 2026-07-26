/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplexQuotient
import ClassificationOfSurfaces.CanonicalCoordinates
import ClassificationOfSurfaces.CanonicalGeneratorMaps
import ClassificationOfSurfaces.CanonicalPairings
import ClassificationOfSurfaces.CanonicalWords
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
import ClassificationOfSurfaces.PolygonalQuotient
import ClassificationOfSurfaces.RepresentativeCarrier
import ClassificationOfSurfaces.SphereCarrierGeometry
import ClassificationOfSurfaces.SphereHemisphere

/-!
# Public API map

This file is the preferred first Lean file for collaborators to read. It re-exports the current
project skeleton and documents the intended handoff points between teams.

## Eval input

* `EvalSurface`
* `ChartBoundaryInvariant`
* `chartBoundaryInvariant_of_invarianceOfDomain`
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
* `PartialTriangulation`, `RadoInvariant`, `moise_finite_chart_cover`,
  `moise_induction_step`, `moise_triangulation_of_boundaries`
  (`Moise/ChartInduction.lean`)
* `nonempty_geometricTriangulation_iff_explicit`, `moise_triangulation`, and
  `moise_triangulation_explicit` (`Moise/GeometricTriangulation.lean`, `Triangulation.lean`)
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

The last two declarations assert only a homeomorphism to the raw presentation's stored
realization.  They do not yet produce `SurfaceCellComplex.IsSurfaceValid` or `.IsConnected`;
`Moise/Countermodels.lean` contains an executable legacy witness showing the gap.

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

## Polygonal quotient foundation

* `PolygonCell`
* `PolygonCell.side`
* `PolygonCell.iUnion_range_side`
* `PolygonGluing.PreRealization`
* `PolygonGluing.Side`
* `PolygonGluing.Identification`
* `PolygonGluing.setoid`
* `PolygonGluing.Realization`
* `PolygonGluing.realizationCongr`
* `SurfaceCellComplex.BoundaryOccurrence`
* `SurfaceCellComplex.BoundaryPairing`
* `SurfaceCellComplex.OccurrencePairingValid`
* `SurfaceCellComplex.wordEdgeOccurrences`
* `SurfaceCellComplex.oneFacePresentation_isSurfaceValid`
* `SurfaceCellComplex.oneFacePresentation_occurrencePairingValid`
* `SurfaceCellComplex.PolygonalRealization`
* `SurfaceCellComplex.mem_polygonalIdentifications_iff_exists_occurrences`
* `SurfaceCellComplex.oneFaceOccurrence`
* `SurfaceCellComplex.oneFace_mem_polygonalIdentifications_iff`
* `SurfaceCellComplex.not_isBoundaryDart_of_occurs_at_ne`
* `SurfaceCellComplex.swapIdentification`
* `SurfaceCellComplex.swapIdentification_mem_polygonalIdentifications`
* `SurfaceCellComplex.oppositeDirectionIdentification_mem_of_get_pos_neg`
* `quotEqvGenHomeomorph`
* `eqvGenQuotientCongrRaw`
* `eqvGenQuotientCongrRawOfGeneratorMaps`
* `Complex.ClosedUnitDisc.bdyPtOfReal_add_int`
* `PolygonCell.closedUnitDiscHomeomorph`
* `PolygonCell.conjHomeomorph`
* `PolygonCell.conj_side_symm_monogon`
* `PolygonCell.hemisphereHeight`
* `PolygonCell.upperHemisphere`
* `PolygonCell.lowerHemisphere`
* `PolygonCell.upperHemisphere_side_eq_lowerHemisphere_side_symm`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph_sidePoint`
* `SurfaceCellComplex.sphereBoundaryOccurrence_eq`
* `SurfaceCellComplex.mem_sphere_polygonalIdentifications_iff`
* `SurfaceCellComplex.spherePreMap`
* `SurfaceCellComplex.spherePreMap_eq_of_generator`

This generic layer supports disk cells with any number of marked sides and generated side
identifications. The additive cell-complex adapter now maps boundary occurrences to polygon sides
and, given incidence validity plus nonempty face boundaries, generates all compatible internal
pairings. Edge-orbit counts and inverse-invariance of boundary status are derived from
`IsSurfaceValid`, not repeated as adapter assumptions. `SurfaceCellComplex.Realization` does not
use the quotient yet; the atomic cutover still depends on a certified
triangulation-to-quotient bridge. The standard one-face examples now have incidence- and
occurrence-validity witnesses, including the corrected length-six annulus word. The carrier bridge
identifies each indexed disk, and hence every one-face pre-realization, with the exact closed unit
disk used by the Eval representatives. It records the side-coordinate formula and reconciles the
raw `Quot` presentation with the equivalence-closure `Quotient` used by polygonal gluings. The
one-face membership theorem further reduces the polygonal generators to compatible pairs of
positions in the boundary word. Exact canonical-word indexing and exhaustive pairing
classifications for both canonical families are complete. Exact carrier coordinates, including
the reversed boundary index, send all five canonical pairing families into the corresponding
trusted equivalence closures. Exhaustive forward maps and constructor-by-constructor reverse maps
therefore identify both generated relations, and the carrier descends to homeomorphisms from the
canonical polygonal realizations to the exact trusted Eval quotients.

## Gallier-Xu tail

* `NormalForm.OrientableEdge`
* `NormalForm.NonOrientableEdge`
* `NormalForm.orientableBoundaryWord`
* `NormalForm.nonOrientableBoundaryWord`
* `NormalForm.orientableHandlePosition`
* `NormalForm.orientableBoundaryPosition`
* `NormalForm.nonOrientableCrosscapPosition`
* `NormalForm.nonOrientableBoundaryPosition`
* `NormalForm.nonOrientableCrosscapIdentification`
* `NormalForm.nonOrientableCrosscapIdentificationReverse`
* `NormalForm.nonOrientableBoundaryIdentification`
* `NormalForm.nonOrientableBoundaryIdentificationReverse`
* `NormalForm.mem_nonOrientable_polygonalIdentifications_iff`
* `NormalForm.orientableHandleAIdentification`
* `NormalForm.orientableHandleAIdentificationReverse`
* `NormalForm.orientableHandleBIdentification`
* `NormalForm.orientableHandleBIdentificationReverse`
* `NormalForm.orientableBoundaryIdentification`
* `NormalForm.orientableBoundaryIdentificationReverse`
* `NormalForm.mem_orientable_polygonalIdentifications_iff`
* `NormalForm.orientableOccurrencePoint`
* `NormalForm.nonOrientableOccurrencePoint`
* `NormalForm.orientableCarrier_occurrencePoint`
* `NormalForm.nonOrientableCarrier_occurrencePoint`
* `NormalForm.orientableBoundary_trustedSource_eq_carrier_c_neg`
* `NormalForm.orientableBoundary_trustedTarget_eq_carrier_c_pos`
* `NormalForm.nonOrientableBoundary_trustedSource_eq_carrier_c_neg`
* `NormalForm.nonOrientableBoundary_trustedTarget_eq_carrier_c_pos`
* `NormalForm.orientableCarrier_handle_a_eqvGen`
* `NormalForm.orientableCarrier_handle_b_eqvGen`
* `NormalForm.orientableCarrier_boundary_c_eqvGen`
* `NormalForm.nonOrientableCarrier_crosscap_a_eqvGen`
* `NormalForm.nonOrientableCarrier_boundary_c_eqvGen`
* `NormalForm.orientableGenerator_to_eqvGen`
* `NormalForm.nonOrientableGenerator_to_eqvGen`
* `NormalForm.orientableRel_to_polygonEqvGen`
* `NormalForm.nonOrientableRel_to_polygonEqvGen`
* `NormalForm.orientablePolygonalRealizationHomeomorph`
* `NormalForm.nonOrientablePolygonalRealizationHomeomorph`
* `NormalForm.orientableCellComplex`
* `NormalForm.nonOrientableCellComplex`
* `NormalForm.canonicalCellComplex`
* `NormalForm.canonicalCellComplex_isSurfaceValid`
* `NormalForm.canonicalCellComplex_isConnected`
* `NormalForm.IsEvalAdmissible`
* `SurfaceCellComplex.RealizesNormalForm`
* `SurfaceCellComplex.HasNormalForm`
* `surface_cell_complex_reduces_to_normal_form`
* `SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm`
* `SurfaceCellComplex.hasEvalRepresentative`

The canonical orientable and nonorientable words have lengths `4 * p + 3 * n` and
`2 * p + 3 * n`. Their edge-occurrence counts give incidence-valid, connected one-face complexes;
under the Eval admissibility bounds they also have occurrence-pairing witnesses for polygonal
realization. Certified block-position and `List.get` theorems expose every handle, crosscap,
seam, and free boundary dart at its exact index. The polygonal identifications in both families
are classified exhaustively as the two directed forms of the expected handle, crosscap, or
boundary-seam pairings, with the singleton free boundary darts excluded. This classifies the raw
generator sets. Exact coordinate theorems transport every explicit pairing family into the
trusted closures; boundary blocks use `Fin.rev` and integral periodicity to reconcile the
benchmark's negative angles. The exhaustive classifications package those facts for arbitrary
polygon generators, while the trusted relation constructors map back to named polygon pairings.
The resulting bidirectional closure comparisons descend to homeomorphisms with `Quot
(OrientableRel p n)` and `Quot (NonOrientableRel p n)`.

The Gallier-Xu tail should otherwise consume only `SurfaceCellComplex` and quotient-realization
APIs. It should not mention PL maps, Moise triangulation, or manifold chart machinery.

## Eval representatives and final theorem

* `SphereRepresentative`
* `OrientableRel`
* `NonOrientableRel`
* `classification_of_surfaces`
* `topological_classification_of_surfaces`

The final theorem should remain a short assembly proof using
`compact_surface_homeomorphic_to_cell_complex` and `SurfaceCellComplex.hasEvalRepresentative`.
The C0 `ChartBoundaryInvariant` interface is discharged unconditionally by planar no-retraction,
Brouwer's fixed-point theorem, and invariance of domain.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

end ClassificationOfSurfaces
end Topology
end LeanEval
