# Known-Weak Ledger

Deliberately-weak, placeholder, or vacuous definitions. Rule (see AUTOFORMALIZATION_GUIDE.md,
Definition Faithfulness): **strengthen before extending** — do not build new layers on an entry
here. If you must consume one, add yourself to its dependents list.

Entries found by the 2026-07-08 audit. Status values: `placeholder` (intentional scaffold),
`vacuous` (satisfiable by junk witnesses), `retiring` (superseded by the Moise route rebuild).

## Triangulation route — DELETED

**`PL.lean` and the vacuous predicates below were deleted** (last present at commit `868b8d9`;
recover with `git show 868b8d9:ClassificationOfSurfaces/PL.lean`).  The entries are kept as the
record of the failure mode.  The quarry worth mining from git history: the concrete
closed-triangle geometry with explicit estimates (PL.lean:4685–5320 and the
`EuclideanComplex.Examples` section), useful for the Ch. 2–3 proofs.  `SurfaceTriangulable`,
`Triangulable`, and the machine-checked vacuity proof in `Countermodels.lean` were deleted
together with the layer.

| Declaration | File | Status | Problem | Intended meaning |
|---|---|---|---|---|
| `FiniteSurfaceTriangulation` | Triangulation.lean | vacuous, retiring | `realization : Type` is arbitrary and the combinatorial data are unlinked to it; `Countermodels.arbitrarySpaceLegacyTriangulation` inhabits the record for every universe-0 space and converts to data that are neither `IsSurfaceValid` nor `IsConnected` | superseded by `GeometricTriangulation`, whose concrete barycentric faces intersect in common faces |
| `EuclideanComplex` | PL.lean | vacuous, retiring | `support` has no linkage to simplicial data; `realizesSimplexes` duplicates `simplex_nonempty` | geometric simplicial complex with real carriers |
| `PLMap` / `PLSubdivisionSupportWitness` | PL.lean | vacuous, retiring | any continuous map qualifies (`onIdentitySubdivisions`) | map affine on each simplex of some subdivision |
| `IsPLOnSimplexes` / `IsPLOnSkeleton` | PL.lean | vacuous, retiring | true for every function (`isPLOnSimplexes_identity`); witness never mentions the function | PL condition on the restriction to those simplexes |
| `SeparatedOnEdges` | PL.lean | vacuous, retiring | true for every map; no metric content | disjoint edges have disjoint images |
| `EmbeddingLikeApproximation` | PL.lean | vacuous, retiring | `f = h ∨ Injective f` | the approximation is a (PL) embedding |
| `PLComplexInSpace.simplexSupport` | PL.lean | vacuous, retiring | arbitrary set-valued assignment; no face-intersection condition; chart-union takes disjoint sums without overlap reconciliation | carriers are simplex images meeting in common faces |
| Schoenflies/approximation "theorem boundaries" (PL.lean:2825–3060) | PL.lean | vacuous, retiring | trivially satisfiable because the predicates above are vacuous; names promise Moise Ch. 2–6 content that is absent | re-stated honestly in `Moise/PolygonalJordan.lean` (Ch. 2), `Moise/PolygonalSchoenflies.lean` (Ch. 2–3), `Moise/PLApproximation.lean` (Ch. 5–6), `Moise/ChartInduction.lean` (Ch. 8) |

**Salvageable from PL.lean** (real content, to be ported, not weak): `RadoChartPair` +
`fromChartAt` (3749–4060), `FiniteChartPairCover.exists_of_compact_local` (4248),
triangle/homothety fitting lemmas (4685–5320), `euclideanHalfSpace` polygonal-neighborhood
theorems (8077–8460), and the historical `ChartBoundaryInvariant` isolation (now discharged in
`Moise/BoundaryInvariant.lean`).

## Cell-complex / normal-form side (owned separately; listed so nobody extends them)

The former `SurfaceCellComplex.surfaceValid` and `.connected` entries were removed: they are now
incidence-derived predicates `SurfaceCellComplex.IsSurfaceValid` and `.IsConnected`, with positive
anchors and countermodels. The legacy triangulation bridge does not yet prove these predicates; its
missing multiplicity/connectivity assumptions remain part of the `FiniteSurfaceTriangulation` entry
above. `finite_triangulation_to_cell_complex` and
`compact_surface_homeomorphic_to_cell_complex` therefore assert only a homeomorphism to the raw
presentation's stored realization. Consequently the normal-form and Eval call chain cannot yet
take the explicit validity and connectedness hypotheses that issue #9 ultimately requires.

| Declaration | File | Status | Problem | Intended meaning |
|---|---|---|---|---|
| `SurfaceCellComplex.realization` / `gluingRel` | CellComplex.lean | placeholder | arbitrary stored type; `gluingRel = ⊥`; `Equivalent` = homeomorphic stored types, not Gallier–Xu moves | generic disks and quotients live in `PolygonalQuotient.lean`; the occurrence adapter lives in `CellComplexQuotient.lean`; remaining work is the atomic realization cutover and its triangulation bridge |
| `SurfaceCellModel`, `OrientableRel`, `NonOrientableRel` | Representatives.lean | placeholder | `PUnit` with `⊥` relations: `Quot (OrientableRel p n)` is a point, so the eval conclusion's non-sphere branches assert `S ≃ₜ point` | actual polygon quotient representatives |
| `surface_cell_complex_reduces_to_normal_form` | NormalForm.lean | **false as stated** | besides the placeholder-representative counterexample (`realization := Bool`), the signature still lacks explicit `IsSurfaceValid` and `IsConnected` hypotheses because the triangulation bridge cannot yet supply them | implement representatives, certify triangulation incidence, then re-state with both hypotheses |

Dependents of the cell-complex entries: `NormalForm.lean`, `EvalStatement.lean`,
`Examples.lean` (all pre-existing; no new dependents allowed).
