# The Moise triangulation route: status and handoff map

The authoritative onboarding doc for the triangulation half of the project (the
`ClassificationOfSurfaces/Moise/` directory). Updated 2026-07-19. Supersedes
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

Full JCT (Ch. 4) and full Schoenflies (Ch. 9) are **not** on this route. C0 invariance of the
boundary is now proved: `Moise/Brouwer.lean` derives planar Brouwer from the existing
no-retraction theorem, `Topology/InvarianceOfDomain.lean` derives invariance of domain, and
`Moise/BoundaryInvariant.lean` supplies `ChartBoundaryInvariant` unconditionally. Its consequences
remain isolated in `MoiseChart.BoundaryFaithful` (`Moise/ChartExtraction.lean`) and deliberately
use only the two clauses needed by the Radó route.

## What is already proved (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`)

- The Radó induction assembly: `moise_triangulation_of_boundaries` (`Moise/ChartInduction.lean`)
  — reduces `moise_triangulation` to the leaves below.
- The finite chart cover `moise_finite_chart_cover` and the local chart extraction
  `exists_moiseChart_core_mem_nhds` (`Moise/ChartExtraction.lean`) — Moise Thm 8.1.
- Broken-line connectivity of open connected plane sets and the broken-line-in-thickening form
  used by PL approximation (`Moise/BrokenLine.lean`) — Moise Ch. 1 and Thm 6.1.
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
- Ch. 3 relative polygonal Schoenflies: supported one-edge and two-edge free-triangle moves,
  finite boundary avoidance for thin-kite moves, and strong induction on the finite triangle mesh
  prove `polygonal_schoenflies_rel`; ordinary `polygonal_schoenflies` follows by straightening
  both polygons and using an affine equivalence of triangles.
- Ch. 5 cone extension: `pl_extension_of_triangle_boundary` now constructs compatible source and
  target cone complexes and the barycentric PL homeomorphism between them.  The supporting API
  in `Moise/ConeExtension.lean` includes active-vertex reduction, graph images, convex radial
  decomposition, all-face realizations, and PL barycentric repositioning.
- Ch. 6.2 finite graph approximation: `pl_approximation_one_skeleton` is proved.  The proof in
  `GraphPolygonalization.lean` samples the source graph, constructs disjoint vertex disks and
  central tubes, replaces all edges simultaneously by simple polygonal arcs, builds one common
  breakpoint subdivision, proves the resulting map PL and globally injective, preserves original
  vertices, and establishes the uniform approximation estimate.
- Ch. 6.3 finite two-manifold approximation: `pl_approximation_two_manifold` is proved.  The
  one-skeleton approximation is chosen below a finite vertex-to-cell separation scale; each
  polygonal boundary is filled by the certified Schoenflies extension; a bounded
  finite-dimensional Tietze extension and the no-retraction theorem determine the correct side;
  finite graph-side propagation and cellwise gluing give global injectivity and the uniform
  estimate.
- The no-retraction and side-control layer (`Moise/NoRetraction.lean` and
  `Moise/PLApproximation.lean`): no retraction of a closed triangle to its frontier, bounded
  vector-valued Tietze extension, and stability of the inside/outside certificate under a small
  boundary perturbation.
- The C0 boundary-invariance layer (`Moise/Brouwer.lean`,
  `Topology/InvarianceOfDomain.lean`, and `Moise/BoundaryInvariant.lean`): planar Brouwer from
  no-retraction, invariance of domain, chart-independence of the boundary stratum, and the
  unconditional `ChartBoundaryInvariant` instance.
- Common graph-refinement support: `GraphSubdivision.lean` and `GraphRefinement.lean` provide
  fine sampled subdivisions, marked refinements, exact support/subdivision theorems, and the
  interval-face lemma used by the PL proof.  `PlaneComplex.used` removes genuinely unused
  ambient arrangement vertices without changing support.
- `PolygonalCircle.mapEmbedding` transports a polygon through a carrier-injective edgewise
  straight map.  This is the first bridge needed to recognize the image of a PL triangle
  boundary as a polygon in Ch. 6.3.
- The realization bridge `PlaneComplex.toGeometricTriangulation`.
- The intrinsic source layer (`Moise/IntrinsicComplex.lean`): canonical barycentric face
  carriers, faithful subdivision data, intrinsic PL maps and PL homeomorphisms.  A
  `PartialTriangulation` exposes this complex via `toIntrinsic`, and `MoiseChart.partialChartMap`
  is the honest chart-coordinate embedding of a patch lying in one chart.
- The intrinsic graph approximation (`Moise/IntrinsicGraphApproximation.lean` and
  `Moise/IntrinsicGraphPL.lean`): simultaneous polygonal replacement is a continuous embedding
  of the intrinsic one-skeleton; every replacement edge is the exact support of a finite plane
  complex with a simple endpoint-to-endpoint vertex path; and distinct replacement edges meet
  only at images of shared abstract vertices.  Maximal faces now have a canonical cyclic
  vertex/edge API.  `IntrinsicFaceBoundary.lean` places each face's three finite paths in one
  arrangement complex, concatenates them into a simple cycle, and produces the exact
  `PolygonalCircle` needed by cellwise Schoenflies.
- Faithful intrinsic midpoint subdivision (`Moise/IntrinsicMidpointSubdivision.lean` and
  `Moise/IntrinsicFineSubdivision.lean`): the full 1-to-4 complex, its explicit barycentric
  homeomorphism, iterated half-mesh estimate, open-cover subordination, and finite
  compact-in-open subcomplex extraction are proved.  `PartialTriangulation` lifts the latter to
  ambient compact/open collars through `exists_refinedSubcomplex_between`.
- Concrete disk and half-disk chart patches (`Moise/ChartPatch.lean`): finite pure diamond
  meshes lying inside the model region, with the radius-`1/2` core in relative interior.  Their
  transport through a `MoiseChart` gives `patchPartialTriangulation`, and
  `radoInvariant_chartPatch` proves the full corrected Rado invariant for one chart, including
  genuine boundary-line points.
- The facewise comparison layer (`Moise/FacewiseComparison.lean`): the per-face comparison
  map for the locally finite side-preservation interface, its two-sided uniform-continuity
  comparison scale, the shrunken-control choice, and the adaptive corollary
  `exists_polygonalReplacement_of_comparison` — the locally finite Chapter 6 cellwise
  replacement with no residual separation hypothesis (crossing-weld plan, item 3,
  side-preservation half).
- Concrete anchors (`Moise/Anchors.lean`) and countermodels (`Moise/Countermodels.lean`), which
  are the executable definition-faithfulness checks (see `docs/AUTOFORMALIZATION_GUIDE.md`).

## The open leaf

| Leaf | File | Moise | Difficulty |
|---|---|---|---|
| `MoiseChart.exists_crossing_weld` | ChartInduction.lean | Ch. 8 Thm 3 step, crossing case | hard |

`moise_induction_step` itself is now proved: its two absorption branches were already closed, and
the crossing branch is derived from `PartialTriangulation.exists_glued` (Moise Thm. 7.6 on a
common vertex type — **proved**: the union family's realization is the set-union of the two
realizations, so the glued embedding is a two-sided paste, an embedding by compactness) together
with the single remaining leaf `exists_crossing_weld`: in the genuine crossing case, the
straightened old complex and the chart patch admit a common welded presentation (common vertex
type, exact agreement on the shared realization, joint edge-face bound, `A ∪ core` interior to
the united image).  Its intended proof is the adaptive overlap machinery already in this
repository (`adaptiveOverlapGraphRealization`, the locally finite controlled polygonal
replacement, `replaceOnOpen`/`frontierGlue`, `CommonSubdivision`), respecting the
vanishing-tolerance warning below.

The precise remaining work inside this leaf, in dependency order:

1. **Instantiation lemmas at the adaptive overlap** — **DONE** (2026-07-13, clean axioms; the
   layer's stray `native_decide` in `midpointCentralFace_card` was also replaced by kernel
   `decide`).  `AdaptiveOpenCover.faceVertices_injective` and
   `RegionControlledAdaptiveComplex.faceVertices_injective` discharge the `hfaces` entry of
   `exists_polygonalReplacement` unconditionally;
   `PartialTriangulation.injective_faceVertices_adaptiveOverlapComplex` is the overlap
   instance.  The separation entry is
   `PartialTriangulation.exists_separating_control_adaptiveOverlap`, built on the new generic
   `LocallyFiniteTriangleComplex.vertexSeparationControl` (`LocallyFinitePLApproximation.lean`):
   the locally finite analogue of the finite `exists_uniform_vertex_face_separation`, with
   positivity, strong positivity on compacts, `SeparatesVerticesFromFaces`, and a `mono` lemma.
   **Statement caveat, discovered while proving it**: separation had to be stated
   existentially (`∃ phi` strongly positive) for a *fixed* complex.  It is *not* provable with
   the same `phi` that builds `regionControlledAdaptiveComplex`, because the control bounds the
   local image mesh only from above while nonincident vertex gaps in the chart image can be
   smaller than the cover scale wherever the chart map contracts.  Consumers must therefore
   either fix the complex first and shrink only the arc approximation controls
   (`withApproximationControls`), entering through
   `exists_controlled_polygonalReplacement_of_facewise_close` /
   `faceVertexSeparationRadius` (whose separation half is already proved), or generalize
   `exists_polygonalReplacement` to decouple the separation control from the mesh control.
   This mirrors the proved finite sequencing in `exists_intrinsic_pl_approximation`
   (complex fixed, then `ρ = min r η` chosen for the arcs only).
2. **Frontier-glue application** — analytic halves **DONE** (2026-07-14, clean axioms); only
   the assembly with the part-3 replacement remains.
   `PartialTriangulation.exists_chartMatchingControl` (with its metric-target core
   `exists_chartMatchingControl_of_metricSpace`) produces one strongly positive control on the
   chart overlap such that EVERY chart-coordinate replacement within it satisfies
   `MatchesAtFrontier` against `T.embed`; `disjoint_image_chartOverlap_embed_compl` is the
   crossing disjointness (free once the replacement stays in the chart domain).
   **Statement caveat, discovered while proving it**: the original plan item — derive
   `MatchesAtFrontier` from the `≤ regionSafeControl` bound alone — is FALSE for a C0 chart:
   compose a chart with the disk twist `(r, θ) ↦ (r, θ + 1/(1-r))` and a radial displacement of
   `frontierDistance/4` is sheared to unbounded angular displacement, so `chart.symm` of the
   replacement need not converge at the frontier.  The matching control must be extracted from
   the chart homeomorphism itself (sSup of admissible moduli against a surface scale vanishing
   at the frontier trace; strong positivity by Heine–Cantor on compact products).  Consumers
   must intersect the part-1 separation control, this matching control, and the
   `regionSafeControl` reduction; each is strongly positive and each condition is monotone
   downward, so the minimum serves all three.  The final assembly is
   `T.replaceOnOpen`/`isEmbedding_frontierGlue_of_matches` on the part-3 replacement (which
   supplies `ContinuousOn`/`InjOn` on the overlap and containment in the model region — the
   half-plane preservation results already exist).
3. **Conforming layer** (Moise's conditions (a)–(h)): common subdivision of the straightened
   trace with the fixed patch complex, and selection of the patch sub-mesh keeping the cores
   interior (Moise's L, conditions (b) and (d)).

   **Side-preservation half — DONE (2026-07-19, clean axioms;
   `Moise/FacewiseComparison.lean`).**  The per-face comparison map planned on 2026-07-15 was
   built, and it came out *simpler* than the plan: the entire map factors through the original
   face chart.  `facewiseComparison G f` is `faceOriginalMap G f` composed with a clamped
   radial reparametrization of the standard triangle (`sidePiece`, glued over three closed
   sectors by opposite-coordinate minimality; interfaces agree by the corner-evaluation
   lemmas, no minimality needed).  On each side the boundary parameter is redistributed so
   the replacement's middle range covers exactly the matched trim window
   (`sideParamProfile`), and the spoke ranges cover the trimmed-off end pieces.  All values
   lie in the face image, so cthickening membership is automatic — no plane-level spoke
   segments or corner interpolation zones were needed.  The 2026-07-15 worry that the
   last-exit trim lets the trimmed-off original piece wander is neutralized by the TWO-SIDED
   uniform-continuity modulus (`exists_comparisonScale`): the face chart and its inverse are
   both uniformly continuous on the compact standard triangle, so once
   `vertexIsolationRadius + centralTubeRadius` is below the per-face `comparisonScale`
   (per-vertex/per-edge finite minima: `comparisonVertexControl`/`comparisonEdgeControl`),
   the trimmed-off pieces' *endpoints* have close images, hence close standard parameters
   (inverse modulus), hence the whole reparametrized piece is image-small (forward modulus).
   Entry points: `cellwiseCompatibility_of_comparisonScale` (compatibility from
   scale-small isolation/tube radii), `exists_controls_cellwiseCompatibility` (chooses the
   shrunken controls; `faceVertexSeparationRadius`/`comparisonScale` are invariant under
   `withApproximationControls` by `rfl`), and the adaptive-complex corollary
   `RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison`
   (`AdaptiveControlledApproximation.lean`): the full cellwise replacement with `dist ≤ phi`
   and NO residual separation hypothesis — the `hsep` entry of
   `exists_polygonalReplacement` is discharged for good.

   **Still open in item 3**: the genuine conforming layer — apply the item-2 analytic halves
   (`exists_chartMatchingControl`, `disjoint_image_chartOverlap_embed_compl`) to the
   replacement produced above (`replaceOnOpen`/`isEmbedding_frontierGlue_of_matches`; the
   replacement's chart-coordinate closeness `≤ phi ≤ mu` feeds `MatchesAtFrontier`), then
   the common subdivision of the straightened trace with the fixed patch complex
   (`CommonSubdivision`, Moise's conditions (a)–(h)) and the selection of the patch sub-mesh
   keeping the cores interior.  The straightening tolerance is
   `min (regionSafeControl …) (matching control)` — both strongly positive, both conditions
   downward monotone; the arc controls are now chosen separately and do not interact.
4. **Assembly**: read off the common-vertex welded presentation and the interior coverage of
   `A ∪ core`; `PartialTriangulation.exists_glued` (proved) consumes it.

The remaining mismatch is now precise.  Chapter 6.3 is proved for a finite source
`PlaneComplex`, while the old complex near the next Rado chart is intrinsically PL and need not
be straight in one global plane.  The intrinsic one-skeleton replacement, exact face cycles,
faithful fine subdivisions, and finite compact collars are proved.  Chapter 8 still needs
cellwise polygonal filling and gluing along a common intrinsic subcomplex (Moise Thm. 7.6).

There is an important finiteness issue in that last sentence.  Moise applies Chapter 6.3 on the
open complex `K_U` supplied by Thm. 8.2, with a strongly positive tolerance tending to zero at
the frontier of `U`.  `K_U` is generally locally finite and infinite even when the old complex
is finite.  That vanishing-mesh construction is what makes the modified transition map agree
continuously with the unchanged map outside `U`.  The proved finite compact-collar theorem does
not replace it: doing so would require a new relative annulus/Schoenflies extension theorem.
The implementation must therefore either formalize the locally finite open-complex step used by
Moise or deliberately prove that additional relative theorem; it must not silently identify the
two.  Do not solve this by restoring the
deleted `PL.lean` chart-union witness: its carrier and simplex data were unrelated.

Chart initialization is no longer part of the open leaf: the fixed chart patch gives an explicit
finite base.  What remains is extending an already nonempty intrinsic partial triangulation
across the overlap with the next chart.

The bordered invariant now correctly requires absorbed cores to lie in the *topological interior
in the ambient surface* of the partial support.  Requiring combinatorial interior would exclude
the boundary-line points of every half-disk core and make the bordered induction false.

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

1. Generalize the proved graph/cell approximation argument to an intrinsic source mapped into
   the plane; reuse the exact face cycles and all target-plane polygonal Jordan, Schoenflies,
   Tietze, and side-control results unchanged.
2. Add the locally finite open-complex/strongly-positive layer used in Moise Ch. 8, Thm. 2 and
   Ch. 6, Thm. 3, including the frontier convergence glue.  A finite replacement is acceptable
   only if it proves an explicit relative annulus extension theorem.
3. Prove faithful gluing along the resulting common intrinsic subcomplex (Moise Thm. 7.6), then
   close the genuine crossing branch of `moise_induction_step`.  The already-covered and
   chart-patch-contained branches are proved.
