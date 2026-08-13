# Lean Pool cleanup handoff

This document records the state of the `lean-pool-submission` branch after the broad cleanup
checkpoint. It is intentionally a focused engineering handoff, not a project overview.

## Verified baseline

At this checkpoint, the ordinary project is healthy:

- `lake build ClassificationOfSurfaces` passes.
- `lake exe runLinter ClassificationOfSurfaces` passes.
- `lake exe lint-style ClassificationOfSurfaces` passes.
- `python3 port_submission.py --check` reports all three Lean Eval payloads current.
- `git diff --check` passes.
- The two headline classification theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- No main-library file exceeds Lean Pool's 10,000 non-comment-code-line limit.

The former oversized modules were split without changing their public import paths:

- `FiniteCyclicWordReduction.lean` imports `FiniteCyclicWordReductionCore.lean`.
- `Moise/ChartInduction.lean` imports `Moise/ChartInductionCore.lean`.

The generated Lean Eval payloads include those new modules. After any source edit, run
`python3 port_submission.py` and then `python3 port_submission.py --check`.

## Outstanding blocker 1: forbidden heartbeat overrides

Lean Pool forbids `set_option`, and also forbids moving heartbeat overrides into the Lake
configuration. One source override remains:

1. `ClassificationOfSurfaces/Moise/ChartInduction.lean`, around line 255:
   `MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening` needs
   `maxHeartbeats 900000`.

Treat this as a proof-design task, not a formatting task. The proof deterministically times out at
Lean's default 200,000-heartbeat budget when the override is simply removed.

The first chart-weld refactor reduced the verified ceiling from 2,500,000 to 900,000 heartbeats.
Reusable declarations now handle simplex-vertex evaluation, repeated mapped-finset membership,
the fan coordinate relabeling chain, and the injective amalgamation of old and local target
vertices. The full file passes with `-DmaxHeartbeats=900000` and fails with
`-DmaxHeartbeats=800000`. With the source override removed, the first default-budget failure is in
`localFanMixedFaceMap_eq_iff`, while constructing the positive-base-weight case.

### Resolved: `FiniteCyclicDerivedRewrites`

`HandleToCrosscaps.normalizationEquivalent` now composes a private `RewriteCertificate` interface
whose validity transport is hidden from the final dependent chain. Generic positive and negative
cross-cap certificates avoid specializing the largest presentation expressions in theorem
headers; the three rotations have separate compact certificates. The public theorem statement is
unchanged, the `maxHeartbeats 1600000` override is gone, and the complete file compiles with a
40,000-heartbeat command-line cap.

### Suggested approach for the chart weld

The crossing-weld proof is also the largest proof-size violation below. Extract mathematical phases
into named theorem/lemma declarations with compact interfaces: chart replacement, common
subdivision, old/new embedding construction, boundary regularity, and final coverage. Avoid merely
moving tactic blocks into definitions: Lean Pool's proof-size checker ends a proof block only at the
next `theorem` or `lemma`, and the heartbeat problem requires reducing elaboration work as well.

The next useful boundary is `localFanMixedFaceMap_eq_iff`: package the local face, marked fan face,
and their shared edge data into a compact compatibility certificate, then prove its positive-weight
and endpoint cases as separate top-level lemmas. After that, split the final common-coordinate
agreement phase beginning with `fanFace_oldPoint_mem_selected_of_common`.

## Outstanding blocker 2: proofs over 200 code lines

Lean Pool's current quality checker uses a textual heuristic: for each `theorem` or `lemma`, it
counts non-comment code from the declaration's `:=` through the next theorem/lemma. Private helpers
count too. At this checkpoint it reports 28 oversized blocks:

| File | Approximate line | Code lines |
| --- | ---: | ---: |
| `FiniteCyclicReduction.lean` | 938 | 237 |
| `FiniteCyclicTerminalNormalization.lean` | 928 | 288 |
| `FiniteCyclicTerminalNormalization.lean` | 1796 | 277 |
| `FiniteCyclicWordReduction.lean` | 139 | 234 |
| `FiniteCyclicWordReduction.lean` | 674 | 234 |
| `FiniteCyclicWordReduction.lean` | 2801 | 228 |
| `FiniteCyclicWordReduction.lean` | 3046 | 708 |
| `FiniteCyclicWordReduction.lean` | 3959 | 240 |
| `FiniteCyclicWordReduction.lean` | 5628 | 209 |
| `FiniteCyclicWordReduction.lean` | 5867 | 874 |
| `FiniteCyclicWordReduction.lean` | 6978 | 202 |
| `FiniteCyclicWordReductionCore.lean` | 248 | 394 |
| `FiniteCyclicWordReductionCore.lean` | 3636 | 213 |
| `FiniteCyclicWordReductionCore.lean` | 3902 | 250 |
| `FiniteCyclicWordReductionCore.lean` | 4459 | 254 |
| `Moise/AdaptiveFanComplex.lean` | 2071 | 274 |
| `Moise/ChartInduction.lean` | 257 | about 4500 |
| `Moise/ChartInductionCore.lean` | 1685 | 219 |
| `Moise/ChartInductionCore.lean` | 5306 | 387 |
| `Moise/ChartInductionCore.lean` | 6391 | 287 |
| `Moise/EmbeddedComplexValence.lean` | 53 | 315 |
| `Moise/FacewiseComparison.lean` | 948 | 239 |
| `Moise/IntrinsicFaceExtension.lean` | 780 | 212 |
| `Moise/IntrinsicMarkedFan.lean` | 3059 | 223 |
| `Moise/LineSubdivision.lean` | 3164 | 243 |
| `Moise/PLApproximation.lean` | 1235 | 275 |
| `Moise/PolygonalCrosscut.lean` | 413 | 211 |
| `Moise/PolygonalSchoenflies.lean` | 503 | 207 |
| `Topology/InvarianceOfDomain.lean` | 193 | 218 |

Line numbers will drift as helpers are extracted. Re-run Lean Pool's actual quality checker after
each batch instead of treating this table as permanent.

Recommended sequencing:

1. Handle one file or one proof family per session.
2. Start with the near-limit proofs (202--250 lines) to establish good extraction patterns.
3. Address the remaining chart-weld heartbeat proof as a dedicated session.
4. Leave the 708-, 874-, and 4709-line proofs until their surrounding APIs suggest natural helper
   certificates.
5. After every edit, compile the affected module first; run the full build only at a checkpoint.

Do not change theorem statements or add waivers merely to satisfy the textual check.

## Outstanding blocker 3: actual Lean Pool port

This repository has been prepared for a future Lean Pool content PR, but it has not yet been copied
into a Lean Pool checkout or registered there. Once the source blockers are resolved:

1. Re-read Lean Pool's current `CONTRIBUTING.md`, `.github/CODE_QUALITY.md`, and review rules; the
   rules and pinned Lean/Mathlib versions may have changed.
2. Port the project under `LeanPool/<ProjectName>/` with narrow imports and the exact required
   four-line headers.
3. Add the `LeanPool/projects.yml` entry, including source, license, provenance, tags, MSC, authors,
   and summary fields required at that time.
4. Run `lake exe mk_all`, the project build, `runLinter`, `lint-style`, and the Python quality
   checker in the Lean Pool checkout.
5. Re-run the headline axiom audit in the target toolchain.

The local project uses Lean `v4.32.2` and a pinned Mathlib commit. Expect a real compatibility pass
if Lean Pool has moved to another toolchain before submission.

## Scope notes

- The `sorry` declarations under Lean Eval challenge templates are intentional benchmark inputs;
  they are not main-library proof holes and must not be copied into the pooled project.
- `ClassificationOfSurfaces/LeanEval/SpecAudit.lean` was removed from the library during cleanup.
- `DIGESTION.md` was deliberately removed by the maintainer; do not recreate it.
- The current pull request is based on `master`, not the old `Schoenflies` base.
