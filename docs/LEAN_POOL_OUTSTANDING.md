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

## Resolved: forbidden heartbeat override in `ChartInduction`

Lean Pool forbids `set_option`, and also forbids moving heartbeat overrides into the Lake
configuration. The override on
`MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening` has now been removed.

The chart-weld proof now uses opaque `ChartInductionGeometry` components and small phase
certificates for the old and target embeddings, boundary regularity, selected-fan lifting,
old/target agreement, relabeled agreement and separation, and final coverage. In particular,
`finish_crossing_weld` is a short certificate assembly instead of a second elaboration of the
synchronized mesh construction.

The full file passes with `-DmaxHeartbeats=101500` and fails with
`-DmaxHeartbeats=101400`. This reduces the verified ceiling from 790,000 by about 87%, and leaves
substantial headroom below Lean's default 200,000-heartbeat budget. The hottest remaining
declaration is the public construction theorem, not the final weld assembly.

### Resolved: `FiniteCyclicDerivedRewrites`

`HandleToCrosscaps.normalizationEquivalent` now composes a private `RewriteCertificate` interface
whose validity transport is hidden from the final dependent chain. Generic positive and negative
cross-cap certificates avoid specializing the largest presentation expressions in theorem
headers; the three rotations have separate compact certificates. The public theorem statement is
unchanged, the `maxHeartbeats 1600000` override is gone, and the complete file compiles with a
40,000-heartbeat command-line cap.

The crossing-weld public construction remains a proof-size cleanup target, but it is no longer a
heartbeat blocker. Continue extracting its construction phases only where the resulting interfaces
also improve readability and satisfy Lean Pool's textual proof-size check.

## Outstanding blocker 2: proofs over 200 code lines

Lean Pool's current quality checker uses a textual heuristic: for each `theorem` or `lemma`, it
counts non-comment code from the declaration's `:=` through the next theorem/lemma. Private helpers
count too. At this checkpoint it reports 7 oversized blocks:

The latest near-limit pass removed five blocks from the exact checker output:
`MarkedBoundaryPairContraction.contract`, `pairReducedNormalForm_isEvalAdmissible`,
`CrosscapBlockCommute.exists_normalizationEquivalent`,
`faceBoundarySubdivision_middleSource`, `insertZero_nonadjacent_disjoint`, and
`PolygonalCircle.edgeSegment_subset_normalized_baseHalf_or_disjoint`. The first two shared one
counted span in `FiniteCyclicWordReduction.lean`, so six named declarations account for five
reported blocks.

The follow-up finite-cyclic pass removed six more blocks:
`ActionablePairReductionFeature.extractedEdges_subset_source`,
`MarkedActionablePairReductionFeature.targetTokens_isSeparated`,
`MarkedResidualCancellablePair.exists_betweenAtoms`,
`OppositeArcForm.exists_step_of_usedMultiplicities`, `mergeSource_isSurfaceValid`, and
`dist_completePath_comparison_lt`.

The final word-reduction pass removed the deliberately deferred 708- and 874-line blocks. The
boundary-commute span now factors surface multiplicity through private boundary, crosscap, and
handle freshness certificates plus a shared count-exhaustion lemma. The resolver span now uses
exact primitive target-interval lemmas, a uniform completed-block shortening, a certified
one-step disposition, and a single recursive shortening branch. The two public theorems that
headed the charged spans retain their original statements and proofs.

The subsequent extraction pass removed thirteen further blocks. Reusable helpers now isolate the
radial-projection separator argument, chart-frontier matching, marked-fan edge uniqueness,
three-point convex-hull separation, positive normalization, interval endpoint order, repositioning
support behavior, triangular graph purity, two-page edge neighborhoods, and the two outcomes of
inverse-pair cancellation. Natural accessor lemmas also split checker-charged runs of definitions
in the boundary-envelope, terminal-normalization, and chart-geometry APIs. The public theorem
statements are unchanged.

| File | Approximate line | Code lines |
| --- | ---: | ---: |
| `Moise/ChartInduction.lean` | 1034 | 409 |
| `Moise/ChartInduction.lean` | 2570 | 523 |
| `Moise/ChartInduction.lean` | 4323 | 1388 |
| `Moise/ChartInductionCore.lean` | 5303 | 387 |
| `Moise/ChartInductionCore.lean` | 6388 | 287 |

Line numbers will drift as helpers are extracted. Re-run Lean Pool's actual quality checker after
each batch instead of treating this table as permanent.

Recommended sequencing:

1. Handle one file or one proof family per session.
2. Start with the near-limit proofs (202--250 lines) to establish good extraction patterns.
3. Split the remaining chart-weld public construction for the proof-size check.
4. Use certificate and step abstractions for the remaining large construction proofs when their
   surrounding APIs expose natural phase boundaries.
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
