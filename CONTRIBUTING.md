## Claiming work

**Work is claimed on the issue tracker** 

- Every open task is a GitHub issue. Start at
  [open issues](https://github.com/mccorvie/classification-of-surfaces/issues);
  `good first issue` is the shallow end, `blocking` is where the leverage is.
- **To claim:** self-assign the issue. If you cannot assign yourself, comment "taking this" and a
  maintainer will assign you. One issue at a time.
- **To release:** unassign yourself, or say so in a comment. No explanation is owed and no apology
  is wanted. Dropping a claim is a normal event, don't stress about it.
- A claim with no visible activity for two weeks and no comment may be unassigned by the organizer for bookkeeping.  You are welcome to re-claim it.

A claim is on an **issue**, not on a file and not on the repository. Several people can and should hold live claims in the same directory. Nothing is locked.

## Branches and PRs

- Branch off `master`: `git checkout -b NN-short-name` where `NN` is the issue number.
- One issue per branch, one branch per PR. Put `Closes #NN` in the PR body.
- `lake build` must be green before you open the PR, and `Moise/Countermodels.lean` must stay green.
- Draft PRs are welcome and encouraged early. A draft PR with `sorry`d theorem boundaries is a useful artifact: it lets someone else see the shape of your interface before you have finished the proofs, and it lets the sub-lemmas be split off and claimed by other people.

## Touching shared definitions

If your work needs to change anything in `API.lean`, `Surface.lean`, `CellComplex.lean`,
`Representatives.lean`, or `Triangulation.lean`, **say so in the issue before you write the code.**
These are the seams between the Moise route and the Gallier-Xu route, and a silent change to one
will break the other. Record the outcome in `docs/DESIGN_DECISIONS.md`.

If two open issues genuinely collide on a definition, that is a design decision to be settled in a
comment on both issues, not a race to push first.

## Sorry discipline

- A named theorem boundary may carry a `sorry` with a citation in its docstring. That is how work
  gets handed off, and it is encouraged.
- Anonymous `sorry`s inside definitions or routine lemmas are not acceptable.
- **Never weaken a statement to close a goal.** Leave the honest statement with a named `sorry`.
- A hard-named theorem that closes without new mathematics is a statement bug, not progress.
- Verify each closure: `lake build`, then `#print axioms <name>`. The target is
  `[propext, Classical.choice, Quot.sound]`; `sorryAx` should disappear leaf-by-leaf.
- `native_decide` is banned in committed proofs. Scratchpad only.

## Definition faithfulness

Read `docs/AUTOFORMALIZATION_GUIDE.md` before your first PR, in particular the Definition
Faithfulness section. New definitions need a vacuity probe and, where feasible, an anchor in
`Moise/Countermodels.lean` or `Moise/Anchors.lean`.

**Do not extend anything listed in `docs/KNOWN_WEAK.md`.** Strengthen it first. If you must consume
a ledgered entry, add yourself to its dependents list.
