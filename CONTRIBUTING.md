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

The main proof plan is in `docs/PROOF_STRATEGY.md`.

When starting a task, record which file and theorem boundary you are working on. If a definition
choice affects both the topology and combinatorics tracks, document the decision before building on
it heavily.

## Useful Commands

```bash
lake build
lake env lean ClassificationOfSurfaces/NormalForm.lean
```
