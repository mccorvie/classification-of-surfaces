# Architecture

This is the short human summary of the project. For the authoritative Lean declarations, read
`ClassificationOfSurfaces/API.lean`. For the detailed Moise/PL route, read
`codex_strategy_moise_pl.md`. For the proof dependency graph, read `blueprint/src/content.tex`.

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

The repository currently builds with named theorem-boundary `sorry`s. The bottom API is in place:

- `EvalSurface` packages the Lean Eval hypotheses.
- `OrientedEdge` records oriented triangle sides.
- `FiniteSurfaceTriangulation` stores finite vertices, edges, triangles, oriented triangle boundary
  words, boundary-edge flags, and a homeomorphism from its realization to the target surface.
- `SurfaceCellComplex` stores finite faces, darts, vertices, source/target maps, inverse darts, and
  face boundary words.
- `SurfaceCellComplex.SignedDart` and `SurfaceCellComplex.oneFacePresentation` support concrete
  polygonal examples.
- `FiniteSurfaceTriangulation.toCellComplex` preserves triangle faces, vertices, oriented edge
  darts, boundary flags, and oriented triangle boundary words.
- Examples for the disk, annulus, torus, projective plane, and Mobius strip compile as concrete
  boundary-word presentations.

Legacy aliases `CellComplex`, `FiniteTriangulation`, and `Triangulable` remain for early scaffold
compatibility. New code should use the preferred names above.

## File Map

- `ClassificationOfSurfaces/API.lean`: public API map and collaborator entry point.
- `ClassificationOfSurfaces/Surface.lean`: Eval hypothesis wrapper.
- `ClassificationOfSurfaces/PL.lean`: Moise/PL definitions and theorem boundaries.
- `ClassificationOfSurfaces/Triangulation.lean`: finite triangulation API.
- `ClassificationOfSurfaces/CellComplex.lean`: shared finite surface cell-complex API.
- `ClassificationOfSurfaces/Representatives.lean`: Eval quotient representative names.
- `ClassificationOfSurfaces/NormalForm.lean`: Gallier-Xu normal-form theorem boundaries.
- `ClassificationOfSurfaces/EvalStatement.lean`: final Lean Eval theorem.
- `ClassificationOfSurfaces/Examples.lean`: small regression examples.

## Next Tasks

1. Replace placeholder `SurfaceCellComplex.Realization` with a quotient of polygonal
   pre-realizations.
2. Define cyclic-word infrastructure for face boundary words and Gallier-Xu rewrites.
3. Define elementary Gallier-Xu moves on `SurfaceCellComplex`.
4. Prove elementary moves preserve realization using `SurfaceCellComplex.realizationCongr`.
5. Make `OrientableRel` and `NonOrientableRel` genuine quotient relations over polygon models.
6. Continue the Moise/PL triangulation route behind `compact_eval_surface_finitely_triangulable`.
