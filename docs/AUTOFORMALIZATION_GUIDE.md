# Autoformalization Guide

This file records project-specific operating rules for human-plus-agent work. The goal is to make
autonomous sessions useful without confusing scaffold movement for mathematical progress.

## Core Rules

- Prefer one reasoned recommendation over a menu of options.
- Keep theorem boundaries honest. Never replace hard mathematics with junk fields, hidden
  typeclass assumptions, circular structures, or weakened statements.
- Every work session should leave the repo compiling with `lake build`, **including
  `Countermodels.lean`** (see Definition Faithfulness below).
- Public API names listed in `ClassificationOfSurfaces/API.lean` are coordination points. Do not
  rename them casually once other work depends on them.
- Build bottom-up usable definitions before trying to close major theorems.
- Aim at risky interfaces early. If a definition will fail downstream, it is better to learn that
  before proving many small lemmas around it.
- Connect upstream to downstream. Avoid isolated kernels that do not feed
  `compact_eval_surface_polygonalRealization_homeomorphic_surface` or
  `FiniteCyclicPresentation.hasEvalRepresentative`.

## Definition Faithfulness

An early discarded triangulation predicate passed proof-layer checks while remaining provable for
*every* topological space. The lesson is that proof-layer checks alone do not establish that a
definition says what its name promises. The proof layer is checked by `lake build` and
`#print axioms`; the definition layer is guarded by the mechanisms below.

**Countermodels.** Every load-bearing definition ships with, in `Countermodels.lean` (part of the
default build target):

- a *positive example*: a genuine instance (e.g., the standard 2-simplex triangulates itself);
- a *must-imply anchor*: a consequence any faithful version must have (e.g., a finitely
  triangulable space is compact);
- where cheap, a *proved non-example*: a junk object shown NOT to satisfy the definition.

If you cannot produce a must-imply anchor for a definition, you do not yet know what it means;
stop and work that out before building on it.

**Vacuity probe.** Before building on a predicate or structure `P`, spend ten minutes trying to
prove `∀ x, P x` (or inhabit the structure) using the junk checklist: `PUnit`, `Empty`, `id`,
`Set.univ`, the `⊥` relation/setoid, the identity subdivision, `Homeomorph.refl`, and taking the
approximating map to be the reference map itself (`F := h`). If any of these succeeds, the
definition is not ready. Record the probe result in the session notes.

**Field rules for structures.**

- No `Prop`-typed *data* fields (`foo : Prop`). State a proposition *about* the other fields
  instead. A stored proposition that is never required to hold asserts nothing.
- A hypothesis field must mention the data it constrains. An anonymized binder (`_f`) in a field
  that is supposed to constrain `f` is the tell that it constrains nothing.
- A field added to "strengthen" a structure must come with an object that *fails* it. If every
  candidate object satisfies the new field, it is bookkeeping, not strengthening.

**Trivial-closure alarm.** If a theorem named after hard mathematics closes without new
mathematics being formalized, treat that as a defect in the *statement*, not as progress. The
session notes must answer: "where did the hard content go?" A known-hard theorem that stops
needing its `sorry` is a red flag first and a win only after that question has a good answer.

**Semantic anchors.** Each named theorem boundary gets, in the blueprint or its docstring: the
textbook statement it corresponds to (with a citation, e.g. "Moise, Ch. 3"), one consequence it
must imply, and one junk instance it must rule out.

**Naming honesty.** Names and docstrings describe what is proved *now*, not what is aspired to.
A trivially-satisfiable statement named `..._by_pl_schoenflies` is a false coordination point —
the same failure as stale documentation, applied to declarations.

## Project Boundaries

- The Moise route produces `GeometricTriangulation`; an internal bridge feeds the finite
  `FiniteSurfaceTriangulation` interface consumed by the cell-complex conversion.
- Shared infrastructure converts finite triangulations to `SurfaceCellComplex`.
- The Gallier-Xu route consumes only `SurfaceCellComplex` and quotient-realization APIs.
- PL maps, Moise charts, and manifold machinery should not appear in Gallier-Xu normal-form
  declarations.

## Good Agent Tasks

Good prompts have a bounded subsystem, a concrete deliverable, and a verification command:

```text
Prove index_locallyConstant in ClassificationOfSurfaces/Moise/PolygonalJordan.lean (Moise Ch. 2,
Thm. 1, Lemma 2 casework; the proof sketch is in the docstring). Do not weaken any statement to
close a goal — if the honest statement is stuck, leave a named sorry and report where. Run the
vacuity probe on every definition you touch and keep Countermodels.lean compiling. Verify with
lake build and #print axioms before reporting.
```

Prefer tasks like:

- make a structure usable by examples;
- prove identity/composition/symmetry lemmas for an existing API;
- replace a placeholder with real finite data;
- wire an upstream object into a downstream theorem boundary;
- add regression examples that make future breakage obvious.

Avoid tasks like:

- "prove the classification theorem";
- "finish Moise triangulation";
- "clean up everything";
- "make progress on normal forms".

Those are too broad to audit and too easy to satisfy with scaffolding theater.

## Proof Completeness

The completed project contains no `sorry`. Maintenance changes must preserve that property.
Project axioms, `native_decide`, and `implemented_by` are likewise not accepted as substitutes for
proofs. Temporary experiments containing these constructs must not be committed.

## Verification

Before handing work to another person:

```bash
lake build   # must include Countermodels.lean
git status --short
rg -n '\bsorry\b|\baxiom\b|native_decide|implemented_by|\badmit\b' ClassificationOfSurfaces
```

The search must find no proof escape hatches.

For larger proof closures, also inspect axioms for the declarations you claim are complete:

```lean
#print axioms declaration_name
```

Do not trust labels like "PROVEN" or "done" unless the build and relevant axiom checks support
them. Remember that `lake build` and `#print axioms` only audit the proof layer: a vacuous
definition passes both. Definition-layer claims are audited by the countermodels and vacuity
probes in the Definition Faithfulness section.

## Documentation Discipline

- `ClassificationOfSurfaces/API.lean` is the Lean API map.
- `docs/ARCHITECTURE.md` is the short human architecture summary.
- `docs/DESIGN_DECISIONS.md` records stable architectural decisions.
- `blueprint/src/content.tex` is the proof dependency blueprint.

If a document becomes stale, update it immediately or delete/merge it. Git history records
superseded strategies.
