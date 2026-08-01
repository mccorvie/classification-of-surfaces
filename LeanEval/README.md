# Lean Eval submission workspaces

This directory makes the repository URL directly consumable by the
[Lean Eval submission service](https://lean-lang.org/eval/submit/).  The service
recursively finds every directory containing both:

- a `lakefile.toml` whose `name` is a Lean Eval problem id; and
- an adjacent `Submission.lean`.

For each match it overlays only `Submission.lean` and `.lean` files below
`Submission/` onto a pristine copy of that benchmark workspace.  Files such as
`Challenge.lean`, `Solution.lean`, `config.json`, and the local `lakefile.toml`
are present here for local verification; the submission service ignores the
repository's copies of those trusted files.

The trusted files in all three directories were byte-for-byte checked against
`leanprover/lean-eval` commit `3f3786f3b4d9a4b64a5859b3036aca190cd25613`.

## Status

| Problem | Source root | Status |
| --- | --- | --- |
| `jordan_curve` | `JordanCurve.lean` | ready; generated payload builds through `Solution.lean` |
| `schoenflies` | not yet present | workspace scaffold only; its shim still contains `sorry` |
| `topological_classification_of_surfaces` | `ClassificationOfSurfaces.EvalStatement` | ready; generated payload builds through `Solution.lean` |

The Jordan proof and its three dependency modules were ported from the
Apache-2.0 [`rkirov/jordan_pick`](https://github.com/rkirov/jordan_pick)
development.  The previously copied dependency files were byte-identical to
that repository at commit `ad2aa1f637609c212210888b4ad9e926c30debb4`; this
repository also carries the formerly missing root theorem module, with two
small compatibility changes for the current Lean Eval Mathlib pin.

## Generated versus maintained files

Maintain these by hand:

- the ordinary source modules at the repository root;
- each workspace's thin `Submission.lean` theorem shim; and
- `PROBLEMS` in `port_submission.py`, which declares source roots, local module
  prefixes, and imports supplied by a trusted problem workspace.

Do not edit files below a ready workspace's `Submission/` directory.  They are
generated transitive import closures with local imports re-rooted below the
mandatory `Submission` module:

```bash
python3 port_submission.py
python3 port_submission.py --check
python3 port_submission.py --problem jordan_curve --list-closure
```

The generator owns only `Submission/`.  It never changes the trusted benchmark
files or the hand-written `Submission.lean` shims.  Submission CI runs `--check`
when a maintainer marks a PR as submission-ready, so it rejects a stale
checked-in payload before that revision is submitted.

### The classification problem's trusted definitions

The main project currently imports a vendored
`ClassificationOfSurfaces.LeanEval.ChallengeDeps` so it can build independently.
The generated classification payload deliberately does not copy that module.
Instead, the generator rewrites that import to the pristine workspace's
`ChallengeDeps`.  This is essential: copying the inductive relations would
create different Lean constants and comparator would reject the theorem even if
the definitions had identical text.

This temporary source-level duplication can be addressed during the later
common-module reorganization without changing the submission layout.

## Local checks

Fast structural and elaboration checks are:

```bash
python3 port_submission.py --check
(cd LeanEval/jordan_curve && lake build Submission Solution)
(cd LeanEval/topological_classification_of_surfaces && lake build Submission Solution)
```

The authoritative check is `lake test`, which runs
[`leanprover/comparator`](https://github.com/leanprover/comparator), checks the
exact statement and permitted axiom closure, and replays the result through the
external kernel required by the workspace.  Install the pinned tools into a
disposable or cached directory, add the printed directories to `PATH`, then run
the test from a workspace:

```bash
bash scripts/setup_lean_eval_tools.sh /tmp/lean-eval-tools \
  LeanEval/jordan_curve/lean-toolchain

export PATH="/tmp/lean-eval-tools/bin:/tmp/lean-eval-tools/lean4export/.lake/build/bin:/tmp/lean-eval-tools/comparator/.lake/build/bin:/tmp/lean-eval-tools/nanoda/target/release:$PATH"
(cd LeanEval/jordan_curve && lake test)
```

### Submission-ready CI

Ordinary pull requests run the repository's normal `Lean Action CI` build but
do not build the standalone submission workspaces.  To prepare a particular PR
for submission:

1. Run `python3 port_submission.py` and commit the refreshed `Submission/`
   payloads.
2. Apply the `lean-eval-submission` label to the PR.
3. Require the `Lean Eval Submissions` checks to pass before submitting that
   revision.

The label runs the freshness check and full comparator pipeline for every ready
problem.  New commits to a labeled PR rerun the checks automatically.  Removing
the label opts the PR out again.  A maintainer can also run the workflow against
any branch or commit using **Actions → Lean Eval Submissions → Run
workflow**; manual runs do not require a label.

Schoenflies is excluded from the comparator matrix until it has a complete
proof.

## Adding the Schoenflies solution or another problem

1. Put the maintained proof in normal source modules.  Shared modules can live
   at a future higher-level prefix; they do not need to be duplicated by hand.
2. Add the source root and every reachable local top-level prefix to the problem
   entry in `PROBLEMS` in `port_submission.py`.
3. Replace the workspace's `Submission.lean` body with a thin delegation to the
   source theorem, matching the trusted statement exactly.
4. Run `python3 port_submission.py`, build `Submission Solution` in that
   workspace, and run comparator.
5. Add the problem id to the CI matrix in `.github/workflows/lean_eval.yml`.

Because the generator computes a transitive closure per problem, common modules
will automatically be included in every payload that imports them.  This keeps
the future module-tree cleanup independent from the evaluator-facing layout.
