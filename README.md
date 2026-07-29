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

The public classification proof is complete and contains no `sorry`.

## Architecture

The proof is organized around the faithful finite-cyclic polygonal-realization handoff:

```lean
GeometricTriangulation.toFiniteCyclicPresentation
FiniteCyclicPresentation.PolygonalRealization
```

The completed Moise–Radó route produces a faithful `GeometricTriangulation`. Its cyclic face
presentation is homeomorphic to the geometric realization, Gallier–Xu normalization preserves the
polygonal realization, and the three canonical endpoints realize the exact Lean-Eval
representatives:

```text
GeometricTriangulation
  → FiniteCyclicPresentation
  → NormalForm.canonicalPresentation
  → vendored Lean-Eval quotient
```

The final theorem `classification_of_surfaces`, with blueprint-facing wrapper
`topological_classification_of_surfaces`, is the composition of these faithful homeomorphisms.
The legacy `SurfaceCellComplex.Realization`, `CellComplex`, and `FiniteTriangulation` scaffolding
still compiles for compatibility but is not used by the public proof.

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
- The geometric triangulation is faithfully identified with its finite-cyclic polygonal quotient.
- Gallier–Xu normalization reaches an admissible canonical presentation while preserving that
  quotient.
- The sphere, orientable, and nonorientable canonical presentations realize the exact vendored
  Lean-Eval representatives.
- `classification_of_surfaces` composes this chain without using the legacy arbitrary stored
  realization.
