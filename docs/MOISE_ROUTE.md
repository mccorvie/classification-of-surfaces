# The Moise triangulation route: status and handoff map

The authoritative onboarding doc for the triangulation half of the project (the
`ClassificationOfSurfaces/Moise/` directory). Updated 2026-07-10. Supersedes
`codex_strategy_moise_pl.md` and the "Moise / PL route" section of `API.lean`, which describe
the retired `PL.lean` layer (see `docs/KNOWN_WEAK.md` for why it was retired).

## Goal and shape

Prove `moise_triangulation` (in `Triangulation.lean`): every compact Eval surface admits a
`GeometricTriangulation` — a homeomorphism onto the realization of a finite two-dimensional
simplicial complex, computed from the combinatorial data in barycentric coordinates
(`Moise/GeometricTriangulation.lean`). The proof follows Moise, *Geometric Topology in
Dimensions 2 and 3* (PDF in the repo root), Ch. 8 (Radó's theorem), whose honest dependency
tree is:

```
Thm 8.3 (Radó)  ←  8.1 chart cover  +  8.2 polyhedral neighborhoods  +  6.3 PL approximation  +  7.6 gluing
Thm 6.3         ←  6.2 (← 6.1 broken lines, Ch. 1)  +  5.3/5.4 combinatorial Schoenflies
Thm 5.3         ←  Ch. 2 polygonal Jordan  +  Ch. 3 polygonal Schoenflies
```

Full JCT (Ch. 4) and full Schoenflies (Ch. 9) are **not** on this route. The one deliberate
assumption is `ChartBoundaryInvariant` (`Surface.lean`): C0 invariance of the boundary. Its
consequences are isolated in `MoiseChart.BoundaryFaithful` (`Moise/ChartExtraction.lean`),
deliberately stated as the two provable clauses only — do not strengthen it to an iff.

## What is already proved (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`)

- The Radó induction assembly: `moise_triangulation_of_boundaries` (`Moise/ChartInduction.lean`)
  — reduces `moise_triangulation` to the leaves below.
- The finite chart cover `moise_finite_chart_cover` and the local chart extraction
  `exists_moiseChart_core_mem_nhds` (`Moise/ChartExtraction.lean`) — Moise Thm 8.1.
- Broken-line connectivity of open connected plane sets (`Moise/BrokenLine.lean`) — Moise Ch. 1.
- Ch. 2, Lemma 2 assembly: `compl_carrier_not_isPreconnected` (`Moise/PolygonalJordan.lean`),
  from the crossing-index machinery (half-open edge convention — no general-position choices).
- Ch. 2, Lemma 2 details: `index_locallyConstant` and `exists_index_eq_one`, including the
  finite crossing-set parity argument and Moise's generic-height/leftmost-crossing construction.
- Ch. 2 strip infrastructure: a uniform feature radius, exact two-sector vertex-ball model,
  isolated two-scale edge tubes, an open strip covering the carrier, and a finite decomposition
  of its complement into local vertex sectors and edge half-rectangles.
- Ch. 2 polygonal Jordan theorem: explicit endpoint overlaps assemble the local strip pieces into
  two path-connected bands, both bands accumulate on the full carrier, and `toTwoGateStrip`
  supplies the geometric input to `polygonal_jordan_of_twoGateStrip`.  Thus `polygonal_jordan`
  proves both complementary regions connected, their bounded/unbounded distinction, and both
  frontier equalities.
- The realization bridge `PlaneComplex.toGeometricTriangulation`.
- Concrete anchors (`Moise/Anchors.lean`) and countermodels (`Moise/Countermodels.lean`), which
  are the executable definition-faithfulness checks (see `docs/AUTOFORMALIZATION_GUIDE.md`).

## The open leaves (each is a named `sorry` with a Moise citation in its docstring)

| Leaf | File | Moise | Difficulty |
|---|---|---|---|
| `polygonal_schoenflies_rel` | PolygonalSchoenflies.lean | Ch. 3 Thms 4/7 | hard |
| `pl_extension_of_triangle_boundary` | PLApproximation.lean | Ch. 5 Thms 3–6 | medium |
| `pl_approximation_one_skeleton` | PLApproximation.lean | Ch. 6 Thm 2 | hard |
| `pl_approximation_two_manifold` | PLApproximation.lean | Ch. 6 Thm 3 | **the crux** |
| `moise_induction_step` | ChartInduction.lean | Ch. 8 Thm 3 step | hard; design interface with the proof |

Also needed (no sorry yet, but the chapter proofs will want it): a `PlaneComplex` API layer —
subdivisions, barycentric subdivision, stars, gluing along a subcomplex (Moise Thm 7.6).
Elementary but voluminous; good parallel work. `AffineIndependent.convexHull_inter` (mathlib)
is the key lemma — see `Moise/Anchors.lean` for the pattern.

## Working rules (short version; full rules in `docs/AUTOFORMALIZATION_GUIDE.md`)

1. Never weaken a statement to close a goal — leave the honest statement with a named `sorry`.
2. New definitions need a vacuity probe and, where feasible, an anchor in
   `Moise/Countermodels.lean` or `Moise/Anchors.lean`.
3. Verify each closure: `lake build` (Countermodels must stay green), then
   `#print axioms <name>` — the target is `[propext, Classical.choice, Quot.sound]`, and
   `sorryAx` should disappear one leaf at a time.
4. A hard-named theorem that closes without new mathematics is a statement bug, not progress.
5. Do not extend anything listed in `docs/KNOWN_WEAK.md`.  The legacy `PL.lean` layer has been
   deleted; its one quarry — the concrete closed-triangle geometry with explicit estimates — is
   recoverable via `git show 868b8d9:ClassificationOfSurfaces/PL.lean` (lines 4685–5320 and the
   `EuclideanComplex.Examples` section).

## Suggested next targets, in order

1. Prove `polygonal_schoenflies_rel` by Moise's supported free-triangle-removal induction.  Chapter
   2 is complete, and ordinary `polygonal_schoenflies` now follows formally from the relative
   theorem and affine equivalence of triangles.
2. Continue with Ch. 5–6, then the Ch. 8 induction step.
