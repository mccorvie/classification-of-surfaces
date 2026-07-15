# The Moise triangulation route: status and handoff map

The authoritative onboarding doc for the triangulation half of the project (the
`ClassificationOfSurfaces/Moise/` directory). Updated 2026-07-12. Supersedes
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

   **Refined map (2026-07-14, sharpened 2026-07-15), after verifying every entry of the
   replacement pipeline.**  The apparent crux was that the canonical `graphReplacementMap`
   arcs only satisfy the mesh-scale pointwise bound `< 2 * diam (edgeImage e)`, while the
   side-preservation entries compare against the complex's own Classical.choose-selected
   separation radii — a race no mesh control `phi` can win (in the adaptive fan complex,
   consecutive interval vertices on one tile edge can have image gaps arbitrarily small
   relative to the tile's cover scale).  **The resolution does NOT require new arcs.**  The
   `CentralPolygonalArc` structure already carries `curve_close`: the arc's parametrized curve
   tracks the trimmed original edge curve pointwise within `centralTubeRadius e ≤
   edgeApproximationControl e` — an approximation control we may shrink freely
   (`withApproximationControls`).  The mesh-scale weakness is purely a PARAMETRIZATION
   artifact: `completePath` splits its parameter by `Path.trans` at 1/2, 3/4, misaligned with
   the edge trim, so the same-parameter comparison against `faceOriginalMap` picks up the edge
   diameter.  Accordingly the consumer was generalized (2026-07-15, proved clean):
   `faceFillingsVerticesAvoidClosedRegions_of_comparison` and
   `cellwiseCompatibility_of_comparison` (`LocallyFiniteSidePreservation.lean`) accept ANY
   continuous comparison map `comp f` on the standard region with values in the
   `r f / 2`-cthickening of the original face image and within `r f / 2` of the replacement
   boundary on the frontier — the Tietze/no-retraction argument never needed the original
   parametrization, only continuity, frontier closeness, and set-proximity to the face image.
   The remaining work for the straightened complex is the per-face comparison map: on each
   side of the standard triangle, (i) on the arc's middle range, `chartEdgeCurve` composed
   with the trim-affine reparametrization matched to `middlePath`'s parameter — pointwise
   `< centralTubeRadius` by `curve_close`; (ii) on the spoke ranges, the straight segment from
   the shared vertex image to the matched trimmed curve point, pointwise `< tube` against the
   spoke (two segments from a common start differ by at most the distance of their far
   endpoints) and within `vertexIsolationRadius + tube` of the face image (the far endpoints
   lie in the vertex disk); junction values agree by construction, and corners carry the
   shared vertex images.  Note the trim is a LAST-exit trim (`EdgeTrimData.after_left`), so
   the trimmed-off original curve may wander outside the vertex disk — the comparison must be
   the disk segment, not a reparametrized original; that is exactly why the `of_comparison`
   generalization measures `comp` against the face image by cthickening membership rather
   than requiring frontier values.  Discharging the `r f / 2` bounds needs the controls shrunk
   below the finitely many incident faces' radii (per-vertex and per-edge minima; the
   `edgeFaceSeparationRadius` machinery and part-1 `vertexSeparationControl` supply them).
   `exists_controlled_polygonalReplacement_of_facewise_close` (proved) then assembles the
   replacement with the adaptive `FaceBoundariesControlled`/`UniformFrontierControl` (proved);
   containment/local-finiteness and side-preservation take different controls there, so no
   single-control coupling remains.  The straightening tolerance is
   `min (regionSafeControl …) (matching control) (control-shrunk radii)` — all strongly
   positive, every condition downward monotone.
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
