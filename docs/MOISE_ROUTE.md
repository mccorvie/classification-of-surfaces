# The Moise triangulation route: status and handoff map

The authoritative onboarding doc for the triangulation half of the project (the
`ClassificationOfSurfaces/Moise/` directory). Updated 2026-07-23. Supersedes
`codex_strategy_moise_pl.md` and the "Moise / PL route" section of `API.lean`, which describe
the retired `PL.lean` layer (see `docs/KNOWN_WEAK.md` for why it was retired).

## Goal and shape

The boundaryless checkpoint is now proved:
`moise_triangulation_boundaryless` (in both `Moise/ChartInduction.lean` and the public
`Triangulation.lean` wrapper) shows that every compact boundaryless Eval surface admits a
`GeometricTriangulation` — a homeomorphism onto the realization of a finite two-dimensional
simplicial complex, computed from the combinatorial data in barycentric coordinates
(`Moise/GeometricTriangulation.lean`).  The remaining goal is to remove the single relative
boundary-preservation dependency from the generic bordered `moise_triangulation`.
The proof follows Moise, *Geometric Topology in
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
record exactly the clauses needed by the Radó route: disk domains avoid the manifold boundary,
while in a half-disk domain the manifold boundary is equivalent to the zero normal coordinate.
`BoundaryInvariant.lean` also proves relative invariance of domain for a boundary-line-preserving
half-plane embedding by doubling it across the boundary.

## What is already proved (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`)

- The complete bordered Radó chain:
  `PartialTriangulation.exists_boundaryPreservingStraightening`,
  `MoiseChart.exists_crossing_weld`, `moise_induction_step`, and
  `moise_triangulation_of_boundaries` (`Moise/ChartInduction.lean`), plus the public
  `moise_triangulation` wrapper (`Triangulation.lean`).
- The boundaryless specialization:
  `PartialTriangulation.exists_boundaryPreservingStraightening_boundaryless`,
  `MoiseChart.exists_crossing_weld_boundaryless`, `moise_induction_step_boundaryless`, and
  `moise_triangulation_boundaryless` (`Moise/ChartInduction.lean`), plus the public
  `moise_triangulation_boundaryless` wrapper (`Triangulation.lean`).  The final theorem has the
  faithful conclusion `Nonempty (GeometricTriangulation S)` and no `sorryAx`.
- The shared crossing and induction implementations:
  `MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening` and
  `moise_triangulation_of_induction`.  The boundaryless and bordered routes do not duplicate the
  long crossing construction.
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
| `PartialTriangulation.exists_boundaryPreservingStraightening` | ChartInduction.lean | Ch. 8 Thm 3, relative boundary seam | hard |

The long crossing weld, `PartialTriangulation.exists_glued`, both easy absorption branches, and
the finite Radó assembly are proved.  The shared declaration
`MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening` consumes the single
certificate above.  The generic `exists_crossing_weld` obtains it from the open bordered
provider; `exists_crossing_weld_boundaryless` obtains it cleanly from emptiness of the manifold
boundary.  Thus the genuine crossing presentation (common vertex type, exact agreement and
separation, joint surface incidence, and `A ∪ core` interior coverage) is already checked.

The completion history leading to this single remaining certificate is:

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
2. **Frontier-glue application on the full chart overlap** — **DONE** (2026-07-22, clean
   axioms).
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
   half-plane preservation results already exist).  This assembly is now the theorem
   `PartialTriangulation.exists_straightenedChartOverlap`: it constructs the locally finite
   replacement, proves disk/half-disk model containment, establishes frontier matching and
   crossing disjointness, and returns the global pasted embedding.  The compact Eval hypotheses
   also now have the explicit finite-chart consequence `moise_secondCountableTopology`.

   **Relative protected-set version — DONE (2026-07-22, clean axioms).**
   `PartialTriangulation.exists_chartMatchingControlOn_of_metricSpace` works on an arbitrary
   open `U ⊆ chartOverlap`; one surface-distance control simultaneously proves frontier
   matching and separation from the entire unchanged complement.  The graph approximation
   requires its coordinate trace to be closed relative to its perturbation region, so
   `exists_straightenedChartOpen` records precisely that hypothesis.
   `exists_straightenedChartAway` supplies the Moise specialization: delete the closed chart
   trace of the protected set from the perturbation region, restrict the overlap to its open
   complement, and apply the relative construction.  The resulting global embedding fixes every
   old source point whose image lies in `A` exactly.  Thus preservation of the already absorbed
   physical set is no longer part of the crossing-weld gap.
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

   **Finite synchronized patch weld — DONE (2026-07-22, clean axioms).**
   `PolygonalFamily.selectedClosedRegionMesh` restricts the one common supporting-line
   arrangement by an arbitrary predicate on the polygon family, and
   `selectedClosedRegionMesh_support` proves that its support is exactly the selected union.
   `TriangleMesh.refineToSupport` now handles unequal supports: it cuts the ambient mesh by the
   target coordinate lines, retains exactly the chambers meeting the target, proves exact target
   support, and proves subdivision of both sides.  On top of it,
   `PolygonalFamily.synchronizedArrangement`, `selectedSynchronizedMesh`, and
   `targetSynchronizedMesh` give the old and patch sides literally the same ambient vertices;
   their exact supports and joint edge-valence bound are proved.

   `ChartKind.patchInPerturbation` is compact.  For a full-overlap polygonal presentation `Q`,
   `Q.PatchFaces` is therefore the finite family of replacement faces meeting the patch, and
   `support_inter_patch_subset_closedRegion` is the compact-to-finite carrier cut.  The patch is
   proved to lie in this family's enclosing arrangement.  `Q.patchOldMesh` and `Q.patchNewMesh`
   have respectively the selected polygonal support and the exact fixed-patch support.
   Their barycentric coordinate embeddings are embeddings and agree iff their common coordinate
   functions agree.  After transport by the disk/half-disk chart, the same is true in the
   surface (`patchOldSurfaceEmbed`, `patchNewSurfaceEmbed`, `patchSurfaceEmbed_eq_iff`).
   `exists_patch_local_weld` packages face cardinality, both embeddings, exact agreement,
   exact separation, and the joint edge-valence condition in precisely the interface consumed
   by `PartialTriangulation.exists_glued`.  The full-overlap straightening theorem now exposes
   the `PolygonalReplacementPresentation` and its coordinate equality, rather than discarding
   that certificate.

   The finite selection is now closed under whole adaptive tiles.  For the common midpoint
   level supplied by `adaptiveFaceCommonLevel`, `Q.patchTiles` is finite and
   `Q.PatchTileFaces` is exactly the finite source subcomplex made from all common-level faces
   in those tiles (`sourcePatchTiles_eq_faces`, `sourcePatchTileFaces_eq_levelFaces`).  The
   generic `SynchronizedPatch` construction gives synchronized old/new meshes for any such
   finite polygon family, and `exists_patchTile_local_weld` specializes it to this tile-closed
   source family.  Its coordinate preimage is exactly the selected adaptive source carriers
   (`sourcePatchTileFaces_eq_coordinatePreimage`).

   The presentation now retains the actual finite PL certificate for every polygonal face
   (`faceFillingMap`, `faceMap_eq`, `faceCertificate`), rather than only its carrier.  The
   tile-closed source union is proved compact, contained in the replacement open set, and to
   carry the whole old trace over the fixed patch
   (`isCompact_sourcePatchTileFaces`, `sourcePatchTileFaces_subset_open`,
   `coordinatePreimage_patch_subset_sourcePatchTileFaces`).  The general relative theorem
   `exists_straightenedChartOpen`, and hence `exists_straightenedChartAway`, now returns its
   `PolygonalReplacementSourceAtlas`; the relative crossing proof no longer loses this data
   when it chooses the open set disjoint from the protected old buffer.

   `FinitePLHomeomorphBetween.pullbackSubdivision` now performs the next facewise operation:
   for any prescribed pure target mesh with the polygonal closed region as support, it takes a
   common target refinement with the retained certificate and maps that refinement back through
   the certified inverse.  `PullbackSubdivision.source_support`, `source_pure`, and
   `image_source_cellCarrier` prove exact source support, purity, and face-by-face transport.
   `SynchronizedPatch.singlePolygonMesh` and
   `PolygonalReplacementSourceAtlas.patchTileFacePullback` specialize this construction to
   every face in the tile-closed synchronized family.  Thus pulling synchronized arrangement
   boundary marks back to each selected standard source triangle is no longer an open leaf.
   The new pullback and coverage declarations have the clean axiom set
   `[propext, Classical.choice, Quot.sound]`.

   **Protected-trace-relative target selection — DONE (2026-07-22).**
   The fixed-full-patch specialization is no longer used as a substitute for the relative
   crossing construction.  `PolygonalReplacementSourceAtlas.tilesMeeting`,
   `TileFacesMeeting`, and `sourceTileFacesMeeting_eq_levelFaces` close the replacement faces
   meeting an arbitrary compact subset of the actual coordinate region `V` under whole adaptive
   tiles, retaining exact common-level source support, compactness, open-set containment, and
   coordinate-preimage coverage.  `tileFacePolygonMeeting` packages the corresponding finite
   polygon family.

   `FineSubdivision.lean` now proves
   `PlaneComplex.exists_subdivision_subordinate_openCover` and
   `PlaneComplex.exists_openSubmesh`: a compact subset of an open part of a pure finite plane
   complex is covered by a finite triangle submesh contained in that open set and subordinate
   facewise to the original complex.  `SynchronizedTarget.exists_local_weld` synchronizes an
   arbitrary such finite target mesh with an arbitrary finite polygon family; it is not tied to
   the full chart patch.

   `exists_straightenedChartAway` additionally exposes the exact complement fact for its
   coordinate region: a model point outside `V` maps back into the protected closed trace.
   In `exists_crossing_weld`, the genuinely uncovered compact set
   `c.core \ interior T.support` is transported to plane coordinates, proved disjoint from that
   protected trace, and covered by an `OpenSubmesh` `N ⊆ V` of the fixed patch.  The whole support
   of `N`, regarded as a compact subset of `V`, now selects the tile-closed old family, and
   `exists_tileFacesMeeting_local_weld` produces the finite synchronized old/new local weld.
   Thus the relative construction now has the correct compact target and no longer assumes that
   the deleted protected trace is disjoint from the entire fixed patch.

   **Relative boundary-subdivision extension — DONE (2026-07-22).**  The selected
   common-level faces are retained with their synchronized source triangulation.  Every refined
   old edge receives a midpoint mark in addition to all synchronized source vertices; globally
   ordered consecutive marks are coned to the centers of precisely the unselected faces.
   Selected edge midpoints are synchronized anchors, while an unselected edge whose endpoints
   happen to be local has a nonlocal midpoint.  This supplies the full-subcomplex attaching
   condition and makes the independently pulled-back copies agree on every shared intrinsic
   edge.  Source factorization, whole-tile closure, finite face extraction, outside-chamber
   selection, coordinate support, both surface embeddings, and exact interface agreement and
   separation are now closed.  The joint-valence bookkeeping is closed below.

   **Global marked-edge fan — DONE (2026-07-22,
   `Moise/IntrinsicMarkedFan.lean`).**  A finite intrinsic `EdgeMarking` now enlarges arbitrary
   prescribed source points by every old edge endpoint, filters and orders the marks once on
   each global abstract edge, and constructs its consecutive intervals.  The ordering is
   independent of incident face charts; it proves strict endpoint order, coverage of every old
   edge, and exclusion of further marks from interval interiors.  Coning those intervals to the
   barycentric center of each incident old face now gives genuine three-point fan faces with
   continuous injective affine parametrizations.  Every marked edge is exactly covered by their
   bases, every old closed face is covered by its fan triangles, and the local geometric points
   have been relabeled into one finite global used-vertex type.  Equality of global barycentric
   coordinates is already proved sufficient for equality of fan images.

   The converse face-to-face statement is now proved
   (`globalFanExtendedCoordinates_eq_of_faceMap_eq` /
   `globalFanFaceMap_eq_iff`), as are the full finite intrinsic subdivision,
   its support, and its evaluation homeomorphism (`markedFanSubdivision`,
   `markedFanHomeomorph`).  The crossing proof instantiates the marking from every synchronized
   source vertex and the midpoint of every refined intrinsic edge, retains synchronized faces
   over the selected common-level subcomplex, and uses the fan on exactly the unselected faces.

   **Relative attaching interface — DONE (2026-07-22, clean Lean check).**
   `exists_crossing_weld` now includes the complete mixed old complex and common-vertex
   relabeling.  The additional midpoint marks enforce the full-subcomplex condition: if both
   ends of a consecutive outside fan interval are synchronized local vertices, its old edge is
   contained in a selected common-level face
   (`selectedFace_of_fanInterval_endpoints_local`).  Positive common-coordinate weights force
   the corresponding fan vertices to be local, so every common-coordinate fan point lies in
   the selected source subcomplex (`fanFace_oldPoint_mem_selected_of_common`).  Consequently
   both exact weld-interface directions are proved: `hagree` by the retained-face/fan-face
   split, and `hsep` by the protected chart-overlap argument.

   **Embedded-complex edge valence — DONE (2026-07-22, clean Lean check).**
   `Moise/EmbeddedComplexValence.lean` proves that any finite family of abstract triangles
   embedded in a surface has edge valence at most two.  The proof builds an explicit open
   two-page fan around the midpoint of a putative edge, applies invariance of domain, and rules
   out a third page.  `PartialTriangulation.exists_glued` now derives its output valence bound
   from the pasted embedding, so the former selected/fan incidence obligation and the explicit
   crossing-weld valence output have both disappeared.

   **Still open in the final crossing assembly: the bordered seam in Moise conditions
   (a)--(c).**  The checked `hagree`/`hsep` construction does *not* imply
   ```
   c.core ∩ interior T.support ⊆ interior T₀.support.
   ```
   That proposed last step is false: a small re-embedding of a disk can move its boundary
   inward and lose old physical interior points, and on a bordered surface an embedding of a
   half-plane can additionally push its boundary stratum into the ambient interior.  Pointwise
   fixation of a closed buffer only preserves the interior of that buffer, not its frontier.

   That false shortcut has now been removed from the Lean proof.  The target mesh is selected
   from the actual compact loss
   ```
   D = c.core \ interior T₀.support,
   ```
   so the final old/target union coverage follows directly once `D` lies in the permitted
   perturbation region.  Fixed protected points in the ambient interior are proved to remain
   interior by ordinary invariance of domain.

   The long crossing proof now consumes the named proposition
   `PartialTriangulation.BoundaryPreservingStraightening`.  The one remaining bordered leaf is
   exactly its provider
   `PartialTriangulation.exists_boundaryPreservingStraightening`, under the existing
   `MoiseChart.BoundaryFaithful` hypothesis, whose final conjunct says
   ```lean
   PreservesManifoldBoundary
     (frontierGlue U g T.embed) T.embed
   ```
   or, unfolded,
   ```
   ∀ y,
     frontierGlue U g T.embed y ∈
         (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
       T.embed y ∈
         (modelWithCornersEuclideanHalfSpace 2).boundary S.
   ```
   `BoundaryInvariant.lean` now proves the relative half-plane invariance-of-domain theorem
   that turns this certificate into preservation of protected boundary points.  What remains is
   to extract exact zero-coordinate preservation
   for the relative polygonal replacement from the synchronized arrangement (equivalently,
   construct the replacement relative to its boundary-line subcomplex).  Once this is supplied,
   the actual loss avoids the deleted protected trace and the existing finite target construction
   covers it.

   This is the bordered counterpart of Moise's choice of the finite new complex `L` so that
   (a) both `|L|` and `W = |L| ∪ f'_n(|K_n|)` are 2-manifolds with boundary,
   (b) all old cores and the new core lie in `Int W`, and
   (c) the old and new pieces meet along their boundaries.  The bordered provider still has one
   named `sorry` at this exact boundary-stratum leaf; no weaker conclusion has been introduced.
   Under `BoundarylessManifold`, `ModelWithCorners.Boundaryless.boundary_eq_empty` proves the
   certificate immediately.  The clean provider then runs through the same weld and finite
   induction to `moise_triangulation_boundaryless`.
4. **Assembly**: read off the common-vertex welded presentation and the interior coverage of
   `A ∪ core`; `PartialTriangulation.exists_glued` (proved) consumes it.

The former finite-versus-locally-finite mismatch is resolved in the checked crossing
implementation: the old complex is replaced on the locally finite open complex with a strongly
positive tolerance tending to zero at the frontier, and `frontierGlue` assembles it continuously
with the unchanged embedding.  Cellwise filling, synchronized common subdivision, intrinsic
fan completion, the exact attaching interface, finite target extraction, and Thm. 7.6 gluing are
all present.  The bordered endpoint verifies that these pieces compose end-to-end while retaining
the boundary-line subcomplex; it does not substitute a finite compact-collar shortcut or restore
the deleted `PL.lean` witness.

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

## Suggested next targets

The Moise triangulation route itself is complete.  The remaining project-level targets are the
quotient-realization and normal-form layers listed in `docs/KNOWN_WEAK.md`.
