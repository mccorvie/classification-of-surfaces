# Radó triangulation faithfulness audit

Audit date: 2026-07-23.  Baseline: commit `b193c89`.

## Verdict

**The Radó conclusion passes the definition-faithfulness audit.**

`moise_triangulation` concludes `Nonempty (GeometricTriangulation S)`.
`nonempty_geometricTriangulation_iff_explicit` proves that this means exactly:

```lean
∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (F : Finset (Finset V)),
  (∀ t ∈ F, t.card = 3) ∧
    Nonempty (GeometricRealization V F ≃ₜ S)
```

The realization is computed from `V` and `F`; there is no arbitrary carrier field.  It is the
finite union of the barycentric faces inside `stdSimplex ℝ V`.
`GeometricFace.inter` proves that two such faces meet exactly in the face on their common
vertices.  Thus the conclusion is Moise's first interpretation of “triangulable”: the surface is
homeomorphic to the realization of a Euclidean complex.

**The immediate legacy cell-presentation handoff does not pass the stronger interpretation
“certified valid connected surface cellulation.”**  This limitation was already in
`KNOWN_WEAK.md` and is now executable in `Countermodels.lean`.  It does not weaken the Radó
theorem, whose conclusion is the faithful geometric object.

## Primary-source comparison

The primary source is the repository copy of Edwin E. Moise, *Geometric Topology in Dimensions
2 and 3*, Chapter 8, especially pp. 58–62.

Moise defines an `n`-manifold to be locally Euclidean, and separately defines a manifold with
boundary.  His Theorem 8.3 states that every 2-manifold is triangulable.  The proof gives two
equivalent meanings:

1. a Euclidean complex `K` with `M ≅ |K|`;
2. a PL complex in `M` whose support is all of `M`.

The Lean conclusion implements (1).  Its hypotheses are `T2Space`, `ConnectedSpace`,
`CompactSpace`, a charted space modeled on the Euclidean half-space, and the corresponding
two-manifold instance.  Thus it proves the compact connected case, not Moise's full
possibly-noncompact generality.  Because the input surface is compact, the resulting complex is
finite.  In the boundary direction it extends the induction to half-space charts.  Documentation
therefore calls it the **compact bordered extension after Moise 8.3**, rather than attributing
the bordered statement verbatim to Moise.

### Proof crosswalk

| Moise Chapter 8 component | Lean implementation |
|---|---|
| Thm. 8.1: countable chart pairs with smaller cores | `exists_moiseChart_core_mem_nhds`, followed by compact finite subcover `moise_finite_chart_cover` |
| Initial finite PL patch covering one core | disk/half-disk `patchPartialTriangulation` and `radoInvariant_chartPatch` |
| Inductive embedded PL complexes and protected interiors | `PartialTriangulation` plus the valence, `BoundaryFacewiseRegular`, and `coresInside` fields of `RadoInvariant` |
| Earlier chart cores remain in the interior | `RadoInvariant.coresInside`, using ambient topological interior |
| Open subcomplex near the new chart boundary | adaptive locally finite overlap complex and intrinsic fine-subdivision/collar machinery |
| Strongly positive approximation control tending to zero at the frontier | locally finite controlled approximation and `MatchesAtFrontier` |
| Replacement map glues to the unchanged old embedding | `frontierGlue` and `exists_boundaryPreservingStraightening` |
| Conditions (a)–(c): both pieces and their union are surface neighborhoods with protected cores inside | boundary-stratum preservation, compact-loss selection, embedded-complex valence, and final interior-coverage proof |
| Conditions (d)–(h): sufficiently fine compatible subdivisions and retention of old interior faces | synchronized arrangements, marked intrinsic fans, common relabeling, and exact agreement/separation |
| Thm. 7.6 union of compatible PL complexes | `PartialTriangulation.exists_glued` |
| Countable induction and union | finite induction over the compact chart cover in `moise_triangulation_of_induction` |
| Convert the covering PL complex to a Euclidean realization | `PartialTriangulation.toGeometricTriangulation` |

The half-space extension adds the obligation that the replacement preserves manifold-boundary
membership pointwise.  `MoiseChart.BoundaryFaithful` identifies that stratum with zero normal
coordinate, and the synchronized arrangement proves the coordinate is zero before and after
replacement.

## Definition audit

### `GeometricRealization` and `GeometricTriangulation`

- `GeometricRealization V F` is a set derived from `V` and `F`, not stored data.
- `faces_card` constrains the actual face family and forces every maximal listed face to have
  three vertices.
- `homeo` targets that computed realization.
- `GeometricRealization.eq_biUnion_geometricFace` and `GeometricFace.inter` make the union and
  common-face semantics executable.
- `compactSpace` and `t2Space` are must-imply anchors.
- `faces_nonempty` and `three_le_card_vertex` rule out empty-face and one-vertex witnesses for
  nonempty targets.

The face family lists only maximal two-faces, not every lower-dimensional face as a separate
element.  This is harmless for the theorem statement: the lower faces are already present as
subsets of the geometric faces, and their intersections are computed barycentrically.

### `PartialTriangulation`

The realization is again computed from the finite face family.  The ambient map is required to be
a topological embedding, so its support cannot be assigned independently.  The empty instance is
legitimate only for the empty absorbed set and has empty support.

### `RadoInvariant`

This is a proposition about a particular partial triangulation and absorbed set.  Every field
mentions and constrains that data:

- `coresCompact` supplies the compact set used for protected collars;
- `combSurface` bounds the actual face incidence along every edge;
- `boundaryFacewiseRegular` exposes the actual intersection with the manifold boundary;
- `coresInside` places the absorbed set in the actual support interior.

No field stores the induction conclusion or an unrelated proposition.

The invariant does **not** prove that every intermediate support is a combinatorial manifold:
edge valence at most two does not imply connected vertex links.  The Lean construction instead
uses exact embedded gluing and the stated boundary regularity.  At the end, support equality and
the realization homeomorphism identify the finite complex with the given topological surface.
This is a difference from Moise's presentation of the intermediate invariant, not a weakening of
the final triangulation statement.

### `BoundaryPreservingStraightening`

Every quantified certificate constrains the constructed replacement, its chart coordinates,
frontier behavior, protected-set fixation, injectivity, separation, global embedding, or
manifold-boundary membership.  The final provider derives the boundary certificate from the
synchronized zero-coordinate theorem; it is not assumed as a typeclass or structure field.

## Executable vacuity probes

| Probe | Result |
|---|---|
| Standard 2-simplex, one three-vertex face | accepted (`stdSimplexTriangulation`) |
| Empty face family for a nonempty target | rejected by `faces_nonempty` |
| `PUnit`/one-vertex face data for a nonempty target | rejected by the three-vertex cardinality probe |
| Arbitrary realization field | unavailable: `GeometricTriangulation` has no such field |
| `Homeomorph.refl` | works only when the target really is the computed geometric realization |
| `ℝ` or `ℚ` | rejected because a finite geometric realization is compact |
| `Set.univ` as the single face on `Fin 3` | accepted, correctly giving the standard 2-simplex |
| Identity subdivision | does not construct a target homeomorphism and cannot inhabit the theorem conclusion |
| Reference map as its own approximation | useful only inside genuine approximation data; it does not bypass PL, embedding, boundary, or weld obligations |

## Legacy bridge finding

`Countermodels.arbitrarySpaceLegacyTriangulation S` uses:

- `realization := S`;
- `homeomorphSurface := Homeomorph.refl S`;
- two triangle labels with empty boundary words.

It inhabits `FiniteSurfaceTriangulation S` for every universe-0 topological space, but
`toCellComplex` is provably neither `IsSurfaceValid` nor `IsConnected`.  Therefore:

- `GeometricTriangulation.toFiniteSurfaceTriangulation` is acceptable only as a compatibility
  projection from the faithful object;
- the standalone legacy type must not be used as the meaning of triangulability;
- `finite_triangulation_to_cell_complex` and
  `compact_surface_homeomorphic_to_cell_complex` currently assert only a homeomorphism to a
  stored realization;
- a future certified handoff must prove incidence multiplicity, face-edge connectivity, and
  agreement with the polygonal quotient realization.

## Proof-layer verification

Final verification passed:

- `lake build`: success, 2,998 jobs;
- `leanblueprint all`: success, including the PDF, web output, declaration check, and full Lean
  replay;
- `git diff --check`: clean;
- the deleted boundaryless declaration names are absent from Lean, the public API, and the
  blueprint (they remain only in the removal ledger below).

`#print axioms` was run on the face-intersection and explicit-statement anchors, compactness and
Hausdorff anchors, boundary-preserving straightening, crossing weld, induction step, final
assembly, both public Radó statements, and both legacy countermodel conclusions.  Every one
reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The forbidden-token sweep finds one actual `sorry`, the pre-existing
`ClassificationOfSurfaces/NormalForm.lean:70`; it is outside the Radó import dependency of the
audited declarations.  No `axiom`, `admit`, `native_decide`, or `implemented_by` occurs in the
proof chain.

## Simplification report

| Measurement | Before | After | Change |
|---|---:|---:|---:|
| Audited Lean set | 86,766 | 86,717 | -49 |
| `ChartInduction.lean` | 11,736 | 11,497 | -239 |
| Markdown docs plus blueprint content | 2,188 | 1,773 | -415 |
| `MOISE_ROUTE.md` | 460 | 126 | -334 |
| `BOUNDARYLESS_CHECKPOINT.md` | 314 | 0 | -314 |

Removed as obsolete intermediate shadow declarations:

- `PartialTriangulation.boundaryEdges`;
- `manifoldBoundaryEdges` and `manifoldBoundaryCarrier`;
- the superseded `BoundaryCompatible` predicate and its three helper/fixture theorems;
- `boundarySupport`, `combInterior`, and `combInterior_subset_support`, which were abandoned when
  the correct bordered invariant switched to ambient topological interior;
- `boundaryFacewiseRegularEmbedding_of_boundaryless`;
- `boundaryFacewiseRegular_of_boundaryless`;
- `boundaryCompatible_of_boundaryless`;
- `exists_boundaryPreservingStraightening_boundaryless`;
- `exists_crossing_weld_boundaryless`;
- `moise_induction_step_boundaryless`;
- the internal and public `moise_triangulation_boundaryless`.

The shared crossing-weld theorem also dropped the unused `hcore` and `hA` arguments.  The relative
straightening theorem no longer carries unused connectedness/manifold parameters, and the generic
finite-induction assembler no longer carries unused Hausdorff/connectedness/manifold parameters.

The historical checkpoint document was deleted, and the route document was replaced by the
current dependency map; git history remains the record of the intermediate strategy.  Across all
14 changed paths, the final working diff is 649 additions and 1,101 deletions
(-452 net lines), including this new audit report.
