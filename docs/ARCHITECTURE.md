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

The proof is organized around one shared handoff object:

```lean
SurfaceCellComplex
SurfaceCellComplex.Realization
```

The topological route proves that an Eval surface has a finite triangulation, then shared
infrastructure converts that triangulation to a `SurfaceCellComplex`:

```lean
compact_eval_surface_finitely_triangulable
FiniteSurfaceTriangulation.toCellComplex
compact_surface_homeomorphic_to_cell_complex
```

The Gallier-Xu route consumes only `SurfaceCellComplex` and proves:

```lean
SurfaceCellComplex.hasEvalRepresentative
```

The final theorem should be a short assembly proof using those two bridge theorems.

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

The `SurfaceCellComplex` quotient realization and Gallier-Xu normal-form layers are still
scaffolding (see `docs/KNOWN_WEAK.md`). The public orientable and non-orientable representatives,
however, now use the exact closed-unit-disk relations from the trusted Lean-Eval statement. The
bottom API is in place:

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
  The atomic realization cutover remains blocked on the certified triangulation-to-quotient
  bridge. Straight-edged convex models remain separate work.
- `FiniteSurfaceTriangulation.toCellComplex` preserves triangle faces, vertices, oriented edge
  darts, and oriented triangle boundary words; boundary status is then derived from occurrence
  multiplicity rather than copied from the triangulation's boundary flags.
- Boundary-word examples for the disk, annulus, torus, projective plane, and Mobius strip have
  incidence- and occurrence-validity witnesses. The annulus now uses the length-six, two-contour
  word.
  Homeomorphisms identifying these polygonal quotients with the named surfaces remain future work.
- `NormalForm.orientableBoundaryWord` and `.nonOrientableBoundaryWord` give the two canonical
  parametric families matching the exact Eval relations. Their lengths, edge multiplicities,
  incidence validity, connectivity, and admissible occurrence pairings are certified;
  `NormalForm.canonicalCellComplex` also includes the separate two-face sphere presentation.

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
  one-face presentations.
- `ClassificationOfSurfaces/RepresentativeCarrier.lean`: carrier and quotient bridges between
  one-face polygonal presentations and the exact Eval closed-disk quotients.
- `ClassificationOfSurfaces/Representatives.lean`: exact Eval closed-disk quotient relations and
  definition-faithfulness anchors.
- `ClassificationOfSurfaces/NormalForm.lean`: Gallier-Xu normal-form theorem boundaries.
- `ClassificationOfSurfaces/EvalStatement.lean`: final Lean Eval theorem.
- `ClassificationOfSurfaces/Examples.lean`: small regression examples.

## Next Tasks

1. Certify the finite-triangulation incidence and connectivity hypotheses, prove the polygonal
   realization homeomorphism, then replace the placeholder realization atomically.
2. Prove the canonical word-position formulas and identify the resulting generator closures with
   `OrientableRel` and `NonOrientableRel`; the carrier, quotient-type, and generic one-face pairing
   bridges are complete.
3. Extend the canonical boundary words with cyclic-word infrastructure for Gallier-Xu rewrites.
4. Define elementary Gallier-Xu moves on `SurfaceCellComplex`.
5. Prove elementary moves preserve realization using `SurfaceCellComplex.realizationCongr`.
