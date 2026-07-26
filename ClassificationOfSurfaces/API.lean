/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplexQuotient
import ClassificationOfSurfaces.CanonicalWords
import ClassificationOfSurfaces.EvalStatement
import ClassificationOfSurfaces.Examples
import ClassificationOfSurfaces.FiniteCyclicPresentation
import ClassificationOfSurfaces.LeanEval.RepresentativeSanity
import ClassificationOfSurfaces.LeanEval.SpecAudit
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
import ClassificationOfSurfaces.SignedPresentation

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
* `SurfaceCellComplex.EdgeOrbit`
* `SurfaceCellComplex.edgeOrbit`
* `SurfaceCellComplex.signedDartEquiv`
* `SurfaceCellComplex.finSignedDartEquiv`
* `SurfaceCellComplex.normalizedBoundary`

The legacy names `CellComplex` and `FiniteTriangulation` remain as compatibility aliases.  New
code should prefer `SurfaceCellComplex` and, for triangulations, `GeometricTriangulation`.

## Finite cyclic presentation layer

* `FiniteCyclicPresentation`
* `FiniteCyclicPresentation.edgeMultiplicity`
* `FiniteCyclicPresentation.IsSurfaceValid`
* `FiniteCyclicPresentation.FaceAdjacent`
* `FiniteCyclicPresentation.IsConnected`
* `FiniteCyclicPresentation.PresentationIso`
* `FiniteCyclicPresentation.PresentationIso.isSurfaceValid_iff`
* `FiniteCyclicPresentation.PresentationIso.isConnected_iff`

This packed layer retains only finite signed face words. Its current presentation isomorphisms
relabel edges without changing their chosen signs, relabel faces, and rotate individual face
boundaries; validity, edge multiplicities, and connectivity are invariant under those operations.
An independent orientation reversal for each edge is the next extension required before the
general Gallier--Xu word moves.

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
* `Complex.ClosedUnitDisc.bdyPtOfReal_add_int`
* `quotEqvGenHomeomorph`
* `eqvGenQuotientCongrRaw`
* `eqvGen_map_of_generator_to_eqvGen`
* `eqvGen_iff_of_generator_maps`
* `eqvGenQuotientCongrRawOfGeneratorMaps`
* `PolygonCell.closedUnitDiscHomeomorph`
* `PolygonCell.closedUnitDiscHomeomorph_side`
* `PolygonGluing.oneFacePreRealizationHomeomorph`
* `PolygonGluing.oneFacePreRealizationHomeomorph_sidePoint`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph_sidePoint`

This generic layer supports disk cells with any number of marked sides and generated side
identifications. The additive cell-complex adapter now maps boundary occurrences to polygon sides
and, given incidence validity plus nonempty face boundaries, generates all compatible internal
pairings. Edge-orbit counts and inverse-invariance of boundary status are derived from
`IsSurfaceValid`, not repeated as adapter assumptions. `SurfaceCellComplex.Realization` does not
use the quotient yet; the atomic cutover still depends on a certified
triangulation-to-quotient bridge. The standard one-face examples now have incidence- and
occurrence-validity witnesses, including the corrected length-six annulus word. The marked sides
are circular arcs; issue #6's straight-edged convex representatives still require a separate PL
bridge or a different concrete carrier. The representative-carrier bridge identifies each
indexed disk, and hence every one-face pre-realization, with the exact vendored closed unit disk.
It records the side-coordinate formula, integral-period boundary invariance, and closure-aware
quotient congruence from the polygonal generated setoid to a raw relation quotient. This completes
the common carrier and quotient-construction subproblem only: the canonical polygon generators
still have to be compared with the vendored relations, and the legacy stored realization is still
unrelated to the polygonal quotient. The one-face membership theorem characterizes every
compatible ordered pairing by two distinct boundary-word positions, their non-boundary
conditions, and the required equality or inverse-dart equality. It does not choose a unique
partner or perform the remaining canonical-word index arithmetic.

## Gallier-Xu tail

* `NormalForm.OrientableEdge`
* `NormalForm.NonOrientableEdge`
* `NormalForm.orientableBoundaryWord`
* `NormalForm.nonOrientableBoundaryWord`
* `NormalForm.orientableBoundaryWord_length`
* `NormalForm.nonOrientableBoundaryWord_length`
* `NormalForm.orientableBoundaryWord_edge_occurrences`
* `NormalForm.nonOrientableBoundaryWord_edge_occurrences`
* `NormalForm.orientableCellComplex_isSurfaceValid`
* `NormalForm.nonOrientableCellComplex_isSurfaceValid`
* `NormalForm.orientableCellComplex_isConnected`
* `NormalForm.nonOrientableCellComplex_isConnected`
* `NormalForm.orientableCellComplex_occurrencePairingValid`
* `NormalForm.nonOrientableCellComplex_occurrencePairingValid`
* `NormalForm.canonicalCellComplex`
* `NormalForm.IsEvalAdmissible`
* `SurfaceCellComplex.RealizesNormalForm`
* `SurfaceCellComplex.HasNormalForm`
* `surface_cell_complex_reduces_to_normal_form`
* `SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm`
* `SurfaceCellComplex.hasEvalRepresentative`

The canonical word families match the exact commutator, crosscap, and boundary-block patterns in
the vendored relations. Their lengths, edge multiplicities, incidence validity, connectivity, and
Eval-admissible occurrence pairings are certified without using the stored realization.

The legacy reduction theorem cannot be the final proof route while
`SurfaceCellComplex.Realization` is an arbitrary stored type. The faithful replacement route
normalizes finite cyclic presentations, proves their polygonal realizations match the vendored
quotient relations, and transports that result across the geometric-triangulation realization
bridge. The combinatorial normalization layer should not mention manifold chart machinery.

## Eval representatives and final theorem

* `Complex.ClosedUnitDisc`, `OrientableRel`, and `NonOrientableRel`
  (`LeanEval/ChallengeDeps.lean`, vendored verbatim from Lean-Eval)
* `Complex.ClosedUnitDisc.norm_bdyPtOfReal`
* `orientableQuotRadius` and `nonOrientableQuotRadius`
* `not_subsingleton_orientableQuot` and `not_subsingleton_nonOrientableQuot`
  (`LeanEval/RepresentativeSanity.lean`, project-owned consequences)
* `SphereRepresentative` and `NormalForm` (project-owned abbreviations and indices)
* `classification_of_surfaces`
* `topological_classification_of_surfaces`

The final theorem should become a short assembly proof from a geometric triangulation, through a
finite cyclic presentation and Gallier-Xu normalization, to separately certified polygonal
realization homeomorphisms for the vendored quotients. The C0 `ChartBoundaryInvariant` interface
is discharged unconditionally by planar no-retraction, Brouwer's fixed-point theorem, and
invariance of domain. `LeanEval/SpecAudit.lean` checks that the current public theorem's conclusion
is the exact published Lean-Eval type over the vendored disc relations.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

end ClassificationOfSurfaces
end Topology
end LeanEval
