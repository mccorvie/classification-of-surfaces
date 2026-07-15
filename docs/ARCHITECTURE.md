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

The repository builds. On the triangulation side, Moise Chapters 1--6, the Radó assembly, finite
chart cover, and chart extraction are proved sorry-free relative to the explicit C0
`ChartBoundaryInvariant` hypothesis.  The single open triangulation leaf is the Chapter 8 Radó
induction step; its intrinsic-complex source API is now in place.  See `docs/MOISE_ROUTE.md` for
the live status.  The intrinsic one-skeleton approximation is an actual embedded polygonal
graph, every face has an exact polygonal boundary cycle, and faithful fine subdivision plus
finite compact-collar extraction are proved.  Cellwise polygonal filling and the locally finite
frontier-compatible chart-overlap glue remain. The quotient realization and
Gallier-Xu normal-form layers are still placeholder scaffolding (see `docs/KNOWN_WEAK.md`). The
bottom API is in place:

- `EvalSurface` packages the Lean Eval hypotheses.
- `ChartBoundaryInvariant` isolates the deferred pure topological boundary-invariance theorem for
  C0 half-space charts.
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

Legacy aliases `CellComplex` and `FiniteTriangulation` remain for early scaffold
compatibility. New code should use the preferred names above.

## File Map

- `ClassificationOfSurfaces/API.lean`: public API map and collaborator entry point.
- `ClassificationOfSurfaces/Surface.lean`: Eval hypothesis wrapper.
- `ClassificationOfSurfaces/Moise/`: the triangulation route (see `docs/MOISE_ROUTE.md`).
- `ClassificationOfSurfaces/Triangulation.lean`: legacy triangulation interface, fed by the
  `GeometricTriangulation` bridge.
- `ClassificationOfSurfaces/CellComplex.lean`: shared finite surface cell-complex API.
- `ClassificationOfSurfaces/Representatives.lean`: Eval quotient representative names.
- `ClassificationOfSurfaces/NormalForm.lean`: Gallier-Xu normal-form theorem boundaries.
- `ClassificationOfSurfaces/EvalStatement.lean`: final Lean Eval theorem.
- `ClassificationOfSurfaces/Examples.lean`: small regression examples.

## Next Tasks

1. Certify the finite-triangulation incidence and connectivity hypotheses, prove the polygonal
   realization homeomorphism, then replace the placeholder realization atomically.
2. Define cyclic-word infrastructure for face boundary words and Gallier-Xu rewrites.
3. Define elementary Gallier-Xu moves on `SurfaceCellComplex`.
4. Prove elementary moves preserve realization using `SurfaceCellComplex.realizationCongr`.
5. Make `OrientableRel` and `NonOrientableRel` genuine quotient relations over polygon models.
6. Decide whether to prove `ChartBoundaryInvariant` for C0 half-space manifolds directly or keep
   the main theorem relative to it while developing the Gallier-Xu tail.
