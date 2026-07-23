# Boundaryless triangulation checkpoint

Status: completed and Lean-verified, 2026-07-23.

This document describes a temporary but mathematically meaningful checkpoint for the Moise
triangulation route.  It does not replace `docs/MOISE_ROUTE.md`, which remains the authoritative
status map for the full theorem with boundary.

## Decision

Before completing the relative boundary-preservation argument, prove a sorry-free end-to-end
triangulation theorem under the standard mathlib hypothesis

```lean
[BoundarylessManifold (modelWithCornersEuclideanHalfSpace 2) S]
```

The intended public checkpoint is:

```lean
theorem moise_triangulation_boundaryless :
    Nonempty (GeometricTriangulation S)
```

with the usual compact Eval-surface hypotheses and the additional
`BoundarylessManifold` instance.

This should be a specialization of the existing Radó development.  It must not become a second
triangulation proof.

## Why this checkpoint is useful

The current crossing-weld proof has one remaining `sorry`.  At the 2026-07-23 snapshot it is the
claim that the straightened embedding preserves membership in the ambient manifold boundary:

```lean
∀ y : T.toIntrinsic.realization,
  frontierGlue U g T.embed y ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
    T.embed y ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S
```

The downstream protected-boundary argument is now written and uses the relative half-plane
invariance-of-domain theorem in `Moise/BoundaryInvariant.lean`.  The compact-loss construction,
target selection, synchronized weld, Radó induction, and final conversion are also already
written.

On a boundaryless manifold the displayed equivalence is immediate because the ambient boundary
is empty.  Mathlib supplies:

- `BoundarylessManifold.isInteriorPoint`;
- `ModelWithCorners.Boundaryless.boundary_eq_empty`;
- an `IsEmpty` instance for the manifold boundary.

A clean boundaryless endpoint will therefore check, without assuming the bordered seam, that all
other pieces of the current triangulation route compose correctly.  It will also formalize the
ambient-boundary-free theorem proved in Moise Chapter 8 before completing this project's genuine
extension to bordered surfaces.

The checkpoint does **not** establish that the bordered extension is routine.  It establishes
the more precise claim that the only unresolved dependency in the current triangulation chain is
the relative boundary-preservation capability.

## Non-goals

The checkpoint must not:

1. remove the existing disk/half-disk chart encoding;
2. construct a new disk-only chart cover;
3. duplicate the body of `MoiseChart.exists_crossing_weld`;
4. weaken `RadoInvariant`, `GeometricTriangulation`, or any existing coverage statement;
5. replace topological interior by combinatorial interior;
6. use the generic bordered theorem, directly or indirectly, if that theorem still depends on
   `sorryAx`;
7. hide the bordered obligation in a new typeclass instance or an unproved structure field;
8. claim completion of the later cell-complex or Gallier--Xu normal-form routes.

The boundary machinery should remain compiled.  Boundarylessness is used only to discharge the
single ambient-boundary seam.

## Architecture

### One shared crossing implementation

Factor the crossing proof at the narrowest useful seam: availability of a straightening together
with a proof that it preserves the ambient boundary stratum.  The large construction after that
certificate must be shared by both variants.

The preferred shape is:

1. retain the existing raw straightening construction;
2. name the predicate saying that two embeddings of the same intrinsic source preserve boundary
   membership pointwise;
3. package, or otherwise name, the capability to obtain the existing straightening data together
   with that predicate;
4. make the large crossing-weld implementation consume this capability;
5. provide a sorry-free boundaryless capability using emptiness of the ambient boundary;
6. leave exactly one honest bordered capability theorem as the open leaf;
7. derive the boundaryless and bordered crossing-weld declarations from the same implementation.

The exact names may follow the surrounding namespace conventions.  Suggested descriptive names
are:

```lean
PreservesManifoldBoundary
BoundaryPreservingStraightening
exists_boundaryPreservingStraightening_boundaryless
exists_boundaryPreservingStraightening
exists_crossing_weld_boundaryless
```

Do not introduce a large structure merely for aesthetic packaging.  A named proposition or
private helper theorem is sufficient if it keeps the dependency visible and avoids repeating the
crossing proof.

### Boundaryless theorem chain

Add boundaryless variants only where the call graph actually branches:

```text
boundaryless straightening certificate
  → boundaryless crossing weld
  → boundaryless Radó induction step
  → boundaryless finite chart induction
  → moise_triangulation_boundaryless
```

The induction step and finite induction are short enough that small wrapper declarations are
acceptable.  The long crossing construction is not.

The existing generic declarations should retain their intended bordered statements.  During the
checkpoint they may continue to depend on the single named bordered boundary-preservation leaf.
Their documentation and axiom status must say so explicitly.

### Public location

The main theorem should live beside the existing assembly theorem in
`Moise/ChartInduction.lean`.  If the public compatibility layer needs the result, add a
corresponding boundaryless wrapper in `Triangulation.lean`; do not change the meaning of the
existing generic `moise_triangulation`.

## Execution plan

### Phase 0: stabilize the current development

Before refactoring:

1. preserve all current source work and inspect the complete diff;
2. remove or explain accidental filesystem artifacts;
3. run the targeted `ChartInduction.lean` check;
4. run `lake build`;
5. record the sorry sweep and axiom output of the current generic triangulation theorem;
6. update `docs/MOISE_ROUTE.md` so it identifies the actual remaining local statement,
   `hBoundaryPreservation`, rather than the earlier protected-point formulation.

This phase is a prerequisite for attributing any later failure to the checkpoint refactor.

### Phase 1: expose the boundary-preservation seam

Introduce the smallest reusable predicate/capability described above.  Move no geometric or
combinatorial content across module boundaries unless required by Lean dependencies.

Acceptance criteria:

- the generic crossing proof still elaborates with its one named bordered leaf;
- no long proof body is copied;
- no new `sorry` appears in a helper lemma;
- the statement of the bordered obligation explicitly relates the raw straightening data to
  ambient boundary membership.

### Phase 2: discharge the seam under boundarylessness

Prove the boundaryless provider from
`BoundarylessManifold (modelWithCornersEuclideanHalfSpace 2) S`.

The proof should use emptiness of
`(modelWithCornersEuclideanHalfSpace 2).boundary S`; it should not analyze chart kinds or alter
the polygonal replacement.  Both directions of the boundary-membership equivalence are false by
the same empty-boundary argument.

### Phase 3: assemble the boundaryless endpoint

Thread the boundaryless crossing theorem through the existing two easy branches of the Radó
induction step and through the finite chart induction.  Export
`moise_triangulation_boundaryless`.

Do not derive it from the generic theorem while the generic theorem has `sorryAx`: the checkpoint
must have an independent clean proof term even though both variants share implementation.

### Phase 4: verify the checkpoint

Run:

```bash
lake build
git status --short
rg -n '\bsorry\b|axiom |native_decide|implemented_by' ClassificationOfSurfaces
```

Inspect:

```lean
#print axioms Moise.moise_triangulation_boundaryless
```

and any public wrapper added in `Triangulation.lean`.

Success requires:

- the full build, including countermodels, passes;
- the boundaryless triangulation theorem contains no `sorryAx`;
- its expected axioms are only
  `[propext, Classical.choice, Quot.sound]`;
- the generic bordered route has exactly one named triangulation dependency on the relative
  boundary-preservation leaf;
- no new definition weakens the faithful `GeometricTriangulation` endpoint;
- `docs/MOISE_ROUTE.md`, `docs/ARCHITECTURE.md`, and this document agree about what is and is not
  proved.

The unrelated normal-form `sorry` is outside this checkpoint and should be reported separately,
not confused with the Moise-route audit.

### Phase 5: return to the bordered theorem

After recording the checkpoint:

1. construct the polygonal replacement relative to the boundary-line subcomplex, or extract the
   required exact zero-coordinate preservation from the synchronized arrangement;
2. use that result to prove the generic boundary-preserving straightening capability;
3. let the already shared crossing implementation close the bordered crossing weld;
4. rebuild and inspect axioms for `moise_triangulation_of_boundaries` and
   `moise_triangulation`;
5. retain `moise_triangulation_boundaryless` as a regression theorem, or make it a short
   corollary of the now-clean generic theorem once doing so no longer hides an axiom.

## Effort and stop conditions

Expected checkpoint cost: roughly 2--6 focused hours and 50--250 lines of Lean, excluding
documentation and pre-existing work.

Stop and reassess if:

- more than about 500 lines are needed;
- the crossing-weld body must be copied;
- chart extraction must be redesigned;
- the proposal starts removing boundary-aware types from shared infrastructure;
- a new assumption is needed beyond the standard `BoundarylessManifold` class;
- the boundaryless theorem still reports `sorryAx`.

Crossing one of these thresholds means the checkpoint is becoming a parallel formalization rather
than a thin audit of the existing one.

## Completion report

The checkpoint was completed on 2026-07-23.

The exact clean chain is:

```lean
PartialTriangulation.exists_boundaryPreservingStraightening_boundaryless
MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening
MoiseChart.exists_crossing_weld_boundaryless
moise_induction_step_boundaryless
moise_triangulation_of_induction
Moise.moise_triangulation_boundaryless
ClassificationOfSurfaces.moise_triangulation_boundaryless
```

`lake build` succeeds for all 2998 jobs, including
`ClassificationOfSurfaces.Moise.Countermodels`.  `#print axioms` reports

```text
[propext, Classical.choice, Quot.sound]
```

for every declaration in the displayed clean chain.  The generic bordered
`Moise.moise_triangulation_of_boundaries` and public `moise_triangulation` still additionally
report `sorryAx`, as intended.

The remaining bordered declaration is
`PartialTriangulation.exists_boundaryPreservingStraightening`.  For a
`MoiseChart.BoundaryFaithful` chart it constructs the same raw straightening data and leaves only
the certificate

```lean
PreservesManifoldBoundary (frontierGlue U g T.embed) T.embed
```

whose unfolded statement is

```lean
∀ y,
  frontierGlue U g T.embed y ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
    T.embed y ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S
```

The implementation changed about 189 added and 31 removed Lean source lines across
`Moise/ChartInduction.lean`, `Triangulation.lean`, and `API.lean`, excluding documentation.
No stop condition was approached: the crossing body was not copied, chart extraction and
boundary-aware types were untouched, no assumption beyond `BoundarylessManifold` was added, and
the faithful `GeometricTriangulation` conclusion was retained.  Both routes invoke
`MoiseChart.exists_crossing_weld_of_boundaryPreservingStraightening`, so the long crossing proof
is shared.

Conclusion:

> The Moise/Radó triangulation chain is complete for compact boundaryless Eval surfaces.  In the
> bordered extension, the remaining open dependency is exact preservation of the ambient
> boundary stratum by the relative polygonal straightening.

Do not strengthen that conclusion until the generic bordered endpoint also has clean axioms.
