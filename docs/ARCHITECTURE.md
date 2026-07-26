# Architecture

This is the short human summary of the project. For the authoritative Lean declarations, read
`ClassificationOfSurfaces/API.lean`. **For the triangulation route (the `Moise/` directory),
read `docs/MOISE_ROUTE.md` — it supersedes the deleted `codex_strategy_moise_pl.md` and any PL-route
description below, which refer to the retired `PL.lean` layer (see `docs/KNOWN_WEAK.md`).**
For the proof dependency graph, read `blueprint/src/content.tex`.

## Target

The Lean Eval theorem says that every compact connected Hausdorff topological 2-manifold with
boundary is homeomorphic to the sphere, an orientable normal-form quotient, or a non-orientable
normal-form quotient.

## Main Split

The completed topological route produces a faithful geometric triangulation. The classification
tail should pass through exact finite cyclic boundary words, not through the arbitrary stored
realization of the legacy cell-complex scaffold:

```text
GeometricTriangulation
  → finite cyclic presentation
  → Gallier-Xu word normalization
  → polygonal realization
  → vendored Lean-Eval quotient
```

The combinatorial normalization and polygonal realization are separate proof layers. The final
theorem should only assemble their homeomorphisms with the geometric-triangulation realization
bridge.

## Current Baseline

The repository builds. On the triangulation side, the Moise/Radó chain is complete end-to-end for
compact connected Eval surfaces, including manifolds with boundary:

```lean
moise_triangulation :
  Nonempty (GeometricTriangulation S)
```

The relative polygonal replacement preserves the ambient boundary stratum exactly, and the
exposed-boundary-face invariant is carried through affine subdivision, common relabeling, and
gluing.  The former C0 chart-boundary hypothesis itself is discharged by planar no-retraction,
Brouwer's fixed-point theorem, and invariance of domain.  See `docs/MOISE_ROUTE.md` for the live
status and `docs/RADO_AUDIT.md` for the definition-faithfulness audit.

The quotient realization and Gallier-Xu normal-form layers are still placeholder scaffolding
(see `docs/KNOWN_WEAK.md`). The bottom API is in place:

- `EvalSurface` packages the Lean Eval hypotheses.
- `ChartBoundaryInvariant` is the low-level chart-extraction interface; its unconditional C0
  instance is proved in `Moise/BoundaryInvariant.lean`.
- `OrientedEdge` records oriented triangle sides.
- `FiniteSurfaceTriangulation` stores finite vertices, edges, triangles, oriented triangle boundary
  words, boundary-edge flags, and a homeomorphism from its realization to the target surface.
- `SurfaceCellComplex` stores finite faces, darts, vertices, source/target maps, inverse darts, and
  face boundary words.
- `SurfaceCellComplex.SignedDart` and `SurfaceCellComplex.oneFacePresentation` support concrete
  polygonal examples.
- `PolygonCell` and `PolygonGluing` provide all-arity disk cells with circular indexed boundary
  arcs, generated side identifications, quotient topology, and quotient-congruence lemmas
  independently of the still-placeholder `SurfaceCellComplex.Realization`.
- `SurfaceCellComplex.BoundaryOccurrence`, `BoundaryPairing`, and `PolygonalRealization` provide
  an additive occurrence-indexed adapter to that quotient. Its pairing facts are derived from
  `IsSurfaceValid`, with nonempty face boundaries as the only polygon-specific extra condition.
  `mem_polygonalIdentifications_iff_exists_occurrences` exposes every compatible ordered pairing,
  and `oneFace_mem_polygonalIdentifications_iff` specializes it to two distinct finite positions
  in a one-face boundary word. Neither theorem chooses a unique matching.
  The atomic realization cutover remains blocked on the certified triangulation-to-quotient
  bridge. Straight-edged convex models remain separate work.
- `FiniteSurfaceTriangulation.toCellComplex` preserves triangle faces, vertices, oriented edge
  darts, and oriented triangle boundary words; boundary status is then derived from occurrence
  multiplicity rather than copied from the triangulation's boundary flags.
- Boundary-word examples for the disk, annulus, torus, projective plane, and Mobius strip have
  incidence- and occurrence-validity witnesses. The annulus now uses the length-six, two-contour
  word.
  Homeomorphisms identifying these polygonal quotients with the named surfaces remain future work.
- `NormalForm.orientableBoundaryWord` and `.nonOrientableBoundaryWord` give the canonical
  parametric families matching the vendored Eval relations. Their lengths, edge multiplicities,
  incidence validity, connectivity, and admissible occurrence pairings are certified without
  consuming the arbitrary stored realization.
- `RepresentativeCarrier.lean` identifies every one-face polygonal pre-realization with the exact
  vendored closed unit disk, computes its side coordinates, proves integral-period boundary
  invariance, and supplies closure-aware quotient congruence. The canonical generator comparison
  and the legacy realization cutover remain separate obligations.

Legacy aliases `CellComplex` and `FiniteTriangulation` remain for early scaffold
compatibility. New code should use the preferred names above.

## File Map

- `ClassificationOfSurfaces/API.lean`: public API map and collaborator entry point.
- `ClassificationOfSurfaces/Surface.lean`: Eval hypothesis wrapper.
- `ClassificationOfSurfaces/Moise/`: the triangulation route (see `docs/MOISE_ROUTE.md`).
- `ClassificationOfSurfaces/Triangulation.lean`: legacy triangulation interface, fed by the
  `GeometricTriangulation` bridge.
- `ClassificationOfSurfaces/CellComplex.lean`: shared finite surface cell-complex API.
- `ClassificationOfSurfaces/CanonicalWords.lean`: certified canonical normal-form words and
  one-face incidence presentations.
- `ClassificationOfSurfaces/RepresentativeCarrier.lean`: the exact one-face disk carrier,
  side-coordinate formulas, and raw/generated quotient bridges.
- `ClassificationOfSurfaces/SignedPresentation.lean`: inverse-dart orbits and lossless
  `Fin`-labelled signed boundary words.
- `ClassificationOfSurfaces/LeanEval/ChallengeDeps.lean`: the verbatim Lean-Eval disc carrier and
  quotient relations.
- `ClassificationOfSurfaces/Representatives.lean`: project-owned sphere abbreviation and
  normal-form indices; it does not redeclare the challenge relations.
- `ClassificationOfSurfaces/NormalForm.lean`: Gallier-Xu normal-form theorem boundaries.
- `ClassificationOfSurfaces/EvalStatement.lean`: final Lean Eval theorem.
- `ClassificationOfSurfaces/LeanEval/SpecAudit.lean`: compile-time check that the public theorem
  has the exact Lean-Eval conclusion over the vendored constants.
- `ClassificationOfSurfaces/Examples.lean`: small regression examples.

## Next Tasks

1. Pack geometric triangulations as valid connected finite cyclic presentations, preserving the
   exact cyclic boundary words.
2. Prove Gallier-Xu rewrites and normalization on those finite cyclic presentations.
3. Give each finite cyclic presentation its faithful polygonal realization and prove the
   elementary rewrites preserve that realization.
4. Identify the normalized polygon generators with the vendored `OrientableRel` and
   `NonOrientableRel` generators up to equivalence closure. The generic one-face pairing-position,
   common-carrier, and quotient-type bridges are complete; the canonical position formulas remain.
5. Compose the geometric and polygonal realization homeomorphisms in the final theorem, retiring
   the false legacy `surface_cell_complex_reduces_to_normal_form` abstraction.
