# Contributing

This is a collaborative Lean formalization project for the classification of compact surfaces.

## Workflow

- Keep PRs small and centered on one mathematical interface or one file.
- Run `lake build` before handing work to someone else.
- It is acceptable to introduce `sorry` for a named theorem boundary, but avoid anonymous local
  `sorry`s inside definitions or routine lemmas.
- State theorem boundaries at the level where another contributor could plausibly work on them.
- Prefer definitions that support computation and examples before proving large theorems over them.

## Coordination

Start with `ClassificationOfSurfaces/API.lean` for the current Lean API map. The short architecture
summary is in `docs/ARCHITECTURE.md`; the detailed Moise/PL route is in
`codex_strategy_moise_pl.md`. Agent-assisted work should follow
`docs/AUTOFORMALIZATION_GUIDE.md`.

When starting a task, record which file and theorem boundary you are working on. If a definition
choice affects both the topology and combinatorics tracks, document the decision before building on
it heavily.

## API Boundaries

- New code should prefer `SurfaceCellComplex`, `FiniteSurfaceTriangulation`, and
  `SurfaceTriangulable`. The old names `CellComplex`, `FiniteTriangulation`, and `Triangulable`
  are compatibility aliases only.
- The Moise/PL route should produce `FiniteSurfaceTriangulation`; it should not depend on
  Gallier-Xu normal-form definitions.
- Shared infrastructure should convert finite triangulations to `SurfaceCellComplex`.
- The Gallier-Xu route should consume only `SurfaceCellComplex` and quotient-realization APIs. It
  should not mention PL maps, Moise manifolds, or manifold chart machinery.
- Public theorem names listed in `ClassificationOfSurfaces/API.lean` should not be renamed casually
  once another file or collaborator depends on them.

## Useful Commands

```bash
lake build
lake env lean ClassificationOfSurfaces/API.lean
lake env lean ClassificationOfSurfaces/NormalForm.lean
```
