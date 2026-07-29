# Contributing

The classification theorem is complete. Contributions should preserve the faithful statement and
proof chain while improving maintainability, exposition, or reusable supporting mathematics.

## Branches and PRs

- Keep each branch and pull request focused on one coherent change.
- Reference the relevant issue in the pull request when one exists.
- `lake build` must be green before you open the PR, and `Moise/Countermodels.lean` must stay green.
- Explain public API changes and update the blueprint when theorem names or dependencies change.

## Touching shared definitions

`API.lean`, `Surface.lean`, `CellComplex.lean`, `Representatives.lean`, and
`Triangulation.lean` contain the seams between the Moise route, finite-cyclic normalization, and
the exact Lean-Eval representatives. Changes to these files should:

- preserve the direct faithful polygonal-realization handoff;
- avoid adding independent realization fields to combinatorial structures;
- include matching updates to `ClassificationOfSurfaces/API.lean`,
  `docs/ARCHITECTURE.md`, and `blueprint/src/content.tex`;
- record lasting architectural choices in `docs/DESIGN_DECISIONS.md`.

## Definition faithfulness

Read `docs/AUTOFORMALIZATION_GUIDE.md`, especially its definition-faithfulness section. New
load-bearing definitions need a vacuity probe and, where feasible, an executable anchor in
`Moise/Countermodels.lean` or `Moise/Anchors.lean`.

Do not weaken statements to make proofs close, add junk fields that store the desired conclusion,
or introduce `sorry`, project axioms, `native_decide`, or `implemented_by` into the completed proof
chain.

## Verification

Run:

```bash
lake build
leanblueprint checkdecls
git diff --check
rg -n '\bsorry\b|\baxiom\b|native_decide|implemented_by|\badmit\b' ClassificationOfSurfaces
```

For substantial theorem changes, also inspect `#print axioms` for the affected public
declarations. The expected logical dependencies are `propext`, `Classical.choice`, and
`Quot.sound`.
