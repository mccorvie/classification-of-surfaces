# Classification of Compact Surfaces

This repository is a collaborative Lean formalization project for the Lean Eval challenge
`topological_classification_of_surfaces`.  [Link](https://lean-lang.org/eval/problems/topological_classification_of_surfaces/)

Goal: prove that every compact connected Hausdorff topological 2-manifold with boundary is
homeomorphic to the sphere, an orientable normal-form quotient, or a non-orientable normal-form
quotient.

## Documents

- `docs/PROOF_STRATEGY.md`: proof split, theorem interface, and work packages.
- `docs/MATHLIB_SURVEY.md`: current mathlib starting points and gaps.
- `docs/DESIGN_DECISIONS.md`: accepted and open design decisions.
- `ROADMAP.md`: concise project roadmap and first contributor tasks.
- `CONTRIBUTING.md`: collaboration workflow.

## Build

```bash
lake build
```

The current repository intentionally contains theorem-boundary `sorry`s while the project skeleton
is being refined.
