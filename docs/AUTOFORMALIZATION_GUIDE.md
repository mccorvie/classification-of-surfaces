# Autoformalization Guide

This file records project-specific operating rules for human-plus-agent work. The goal is to make
autonomous sessions useful without confusing scaffold movement for mathematical progress.

## Core Rules

- Prefer one reasoned recommendation over a menu of options.
- Keep theorem boundaries honest. A named `sorry` on a real theorem is acceptable; fake progress
  through junk fields, hidden typeclass assumptions, or circular structures is not.
- **Never weaken a statement to close a goal.** If the honest statement is stuck, leave a named
  `sorry`. A visible sorry is recoverable debt; a weakened definition is hidden debt that
  propagates into everything built on top of it.
- Every work session should leave the repo compiling with `lake build`, **including
  `Countermodels.lean`** (see Definition Faithfulness below).
- Public API names listed in `ClassificationOfSurfaces/API.lean` are coordination points. Do not
  rename them casually once other work depends on them.
- Build bottom-up usable definitions before trying to close major theorems.
- Aim at risky interfaces early. If a definition will fail downstream, it is better to learn that
  before proving many small lemmas around it.
- Connect upstream to downstream. Avoid isolated kernels that do not feed
  `compact_surface_homeomorphic_to_cell_complex` or `SurfaceCellComplex.hasEvalRepresentative`.

## Definition Faithfulness

The 2026-07 audit found a repo that satisfied every proof-layer check in this guide (no bad
sorries, clean axioms, green builds) while the top-level triangulation predicate was provable for
*every* topological space. The lesson: rules about honesty do not bind autonomous sessions unless
each rule has an executable test. The proof layer is checked by `lake build` and `#print axioms`;
the definition layer is checked by the mechanisms below.  `docs/RADO_AUDIT.md` applies this
checklist to the completed Radó theorem and records the remaining weak compatibility bridge.

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

**Weakness ledger.** Deliberately-weak or placeholder definitions are listed in
`docs/KNOWN_WEAK.md` with their intended final meaning and their current dependents. Rule:
*strengthen before extending* — do not stack new layers on a ledger entry. If you must consume
one, add your code to its dependents list so the rework cost stays visible.

**Naming honesty.** Names and docstrings describe what is proved *now*, not what is aspired to.
A trivially-satisfiable statement named `..._by_pl_schoenflies` is a false coordination point —
the same failure as a stale plan document, applied to declarations. Reserve aspirational names via
the weakness ledger instead.

## Project Boundaries

- The Moise route produces `GeometricTriangulation`; the compatibility bridge feeds the legacy
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

## Sorries

Allowed:

- hard named theorem boundaries, especially topology, quotient realization, and Gallier-Xu
  normal-form theorems;
- wrappers whose proof is blocked by a named upstream theorem boundary.

Not allowed:

- anonymous `sorry`s in routine helper lemmas;
- `sorry`s hiding a false or under-specified statement;
- typeclass assumptions added only to make a theorem trivially true;
- structure fields whose only purpose is to smuggle in the desired conclusion.

When adding a `sorry`, make the theorem name and statement precise enough that another contributor
can reasonably take ownership of it.

## Verification

Before handing work to another person:

```bash
lake build   # must include Countermodels.lean
git status --short
grep -rn --include='*.lean' -E 'sorry|axiom |native_decide|implemented_by' ClassificationOfSurfaces
```

The grep sweep must show sorries only on named theorem boundaries, and nothing else.

For larger proof closures, also inspect axioms for the declarations you claim are complete:

```lean
#print axioms declaration_name
```

Do not trust labels like "PROVEN" or "done" unless the build and relevant axiom checks support
them. Remember that `lake build` and `#print axioms` only audit the proof layer: a vacuous
definition passes both. Definition-layer claims are audited by the countermodels and vacuity
probes in the Definition Faithfulness section.

## Documentation Discipline

- `ClassificationOfSurfaces/API.lean` is the current Lean API map.
- `docs/ARCHITECTURE.md` is the short human architecture summary.
- `docs/DESIGN_DECISIONS.md` records accepted decisions and open design questions.
- `docs/KNOWN_WEAK.md` is the weakness ledger: placeholder definitions, their intended final
  meaning, and their dependents.
- `docs/MOISE_ROUTE.md` is the triangulation route status and handoff map.
- `docs/RADO_AUDIT.md` is the triangulation theorem's primary-source and faithfulness audit.
- `blueprint/src/content.tex` is the proof dependency blueprint.

If a doc becomes stale, either update it immediately or delete/merge it. Stale plans are worse than
missing plans because they create false coordination points.
