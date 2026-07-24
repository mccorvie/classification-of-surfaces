# Classification of Compact Surfaces

This repository is a collaborative Lean formalization project for the Lean Eval challenge
`topological_classification_of_surfaces`.  [Link](https://lean-lang.org/eval/problems/topological_classification_of_surfaces/)

Goal: prove that every compact connected Hausdorff topological 2-manifold with boundary is
homeomorphic to the sphere, an orientable normal-form quotient, or a non-orientable normal-form
quotient.

## Documents

- `ClassificationOfSurfaces/API.lean`: public Lean API map and preferred collaborator entry point.
- `docs/ARCHITECTURE.md`: concise architecture overview and current next tasks.
- `docs/AUTOFORMALIZATION_GUIDE.md`: operating rules for human-plus-agent formalization work.
- `docs/MOISE_ROUTE.md`: the completed triangulation route and handoff map.
- `docs/RADO_AUDIT.md`: primary-source and executable definition-faithfulness audit.
- `docs/KNOWN_WEAK.md`: weakness ledger (placeholder definitions; do not extend).
- `blueprint/src/content.tex`: Lean blueprint, kept in sync with the repository state.
- `docs/MATHLIB_SURVEY.md`: current mathlib starting points and gaps.
- `docs/DESIGN_DECISIONS.md`: accepted decisions and still-open design questions.
- `CONTRIBUTING.md`: collaboration workflow.

## Build

```bash
lake build
```

The current repository intentionally contains theorem-boundary `sorry`s while the project skeleton
is being refined.

## Architecture

The project is organized around one shared handoff object:

```lean
SurfaceCellComplex
SurfaceCellComplex.Realization
```

The completed Moise–Radó topological route produces a faithful `GeometricTriangulation`, then
passes through the ledgered compatibility records:

```lean
GeometricTriangulation S
FiniteSurfaceTriangulation S
FiniteSurfaceTriangulation.toCellComplex
compact_surface_homeomorphic_to_cell_complex
```

The last handoff currently preserves raw data and a stored realization but does not yet certify
`SurfaceCellComplex.IsSurfaceValid`, `.IsConnected`, or the polygonal quotient realization.

The Gallier-Xu normal-form route should consume only `SurfaceCellComplex` and prove:

```lean
SurfaceCellComplex.hasEvalRepresentative
```

The final theorem `classification_of_surfaces`, with blueprint-facing wrapper
`topological_classification_of_surfaces`, should then be a short composition of these two bridges.
Legacy aliases `CellComplex` and `FiniteTriangulation` still compile for
compatibility, but new code should use the preferred names above.

## Current Status

- The repository builds with `lake build`.
- The bottom API has concrete finite combinatorial data:
  `SurfaceCellComplex`, signed darts, oriented triangulation edges, one-face presentations, and a
  data-preserving triangulation-to-cell-complex conversion.
- Standard example boundary words for the disk, annulus, torus, projective plane, and Mobius strip
  compile as `SurfaceCellComplex` values.
- The C0 chart-boundary seam is discharged: planar no-retraction gives Brouwer's fixed-point
  theorem, hence invariance of domain and an unconditional `ChartBoundaryInvariant` instance.
- The Moise/PL triangulation route is complete for compact connected Eval surfaces, including
  surfaces with manifold boundary, and uses only the hypotheses in the Lean Eval statement.
- The triangulation-to-cell-presentation compatibility bridge remains deliberately weak as
  recorded in `docs/KNOWN_WEAK.md`.
- Quotient realizations and Gallier-Xu normal-form reductions are still theorem boundaries marked
  by named `sorry`s.
