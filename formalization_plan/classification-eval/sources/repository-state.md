# Repository and benchmark sources

This dependency graph was built against upstream `mccorvie/classification-of-surfaces` at
`8e726bc`, plus the open pull-request tips listed below, on 2026-07-16.

- Trusted Lean Eval statement:
  <https://github.com/leanprover/lean-eval/blob/main/LeanEval/Topology/ClassificationOfSurfaces.lean>
- Project repository: <https://github.com/mccorvie/classification-of-surfaces>
- PR #11, C0 chart-boundary invariance:
  <https://github.com/mccorvie/classification-of-surfaces/pull/11>
- PR #13, incidence-derived validity:
  <https://github.com/mccorvie/classification-of-surfaces/pull/13>
- PR #14, polygonal quotient foundation:
  <https://github.com/mccorvie/classification-of-surfaces/pull/14>
- PR #15, incidence certificates:
  <https://github.com/mccorvie/classification-of-surfaces/pull/15>
- PR #16, Radó dual-connectivity base cases:
  <https://github.com/mccorvie/classification-of-surfaces/pull/16>
- Issue #4, the generic Radó induction branch:
  <https://github.com/mccorvie/classification-of-surfaces/issues/4>
- Issues #6-#8, representatives, realization, and elementary moves:
  <https://github.com/mccorvie/classification-of-surfaces/issues/6>,
  <https://github.com/mccorvie/classification-of-surfaces/issues/7>, and
  <https://github.com/mccorvie/classification-of-surfaces/issues/8>
- Issue #12, certified Radó-to-cell-complex bridge:
  <https://github.com/mccorvie/classification-of-surfaces/issues/12>
- Gallier and Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Chapter 6:
  <https://www.cis.upenn.edu/~jean/surfclassif-root.pdf>
- Benedetti, *Discrete Morse Theory for Manifolds with Boundary*, Section 2.2:
  <https://arxiv.org/abs/1007.3175>

The synthetic integration audit merged PR #14 and PR #11 into the PR #16 stack. The Lean sources
merged without conflict; the sole conflict was duplicate numbering in `docs/DESIGN_DECISIONS.md`.
After renumbering the two independent decisions, `lake build` succeeded for all 2,992 jobs.
