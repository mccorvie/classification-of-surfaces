# Autoformalization Guide

This file records project-specific operating rules for human-plus-agent work. The goal is to make
autonomous sessions useful without confusing scaffold movement for mathematical progress.

## Core Rules

- Prefer one reasoned recommendation over a menu of options.
- Keep theorem boundaries honest. A named `sorry` on a real theorem is acceptable; fake progress
  through junk fields, hidden typeclass assumptions, or circular structures is not.
- Every work session should leave the repo compiling with `lake build`.
- Public API names listed in `ClassificationOfSurfaces/API.lean` are coordination points. Do not
  rename them casually once other work depends on them.
- Build bottom-up usable definitions before trying to close major theorems.
- Aim at risky interfaces early. If a definition will fail downstream, it is better to learn that
  before proving many small lemmas around it.
- Connect upstream to downstream. Avoid isolated kernels that do not feed
  `compact_surface_homeomorphic_to_cell_complex` or `SurfaceCellComplex.hasEvalRepresentative`.

## Project Boundaries

- The Moise/PL route should produce `FiniteSurfaceTriangulation`.
- Shared infrastructure converts finite triangulations to `SurfaceCellComplex`.
- The Gallier-Xu route consumes only `SurfaceCellComplex` and quotient-realization APIs.
- PL maps, Moise manifolds, and chart machinery should not appear in Gallier-Xu normal-form
  declarations.
- Do not create a second realization theory inside the Moise route. Use
  `SurfaceCellComplex.Realization`.

## Good Agent Tasks

Good prompts have a bounded subsystem, a concrete deliverable, and a verification command:

```text
Work on the PL bottom layer. Replace placeholder definitions in PL.lean with a usable finite
complex API sufficient for later combinatorial surfaces. Keep existing public theorem names
compiling. Add small examples/tests. Use sorry only for genuinely hard topology theorem
boundaries. Run lake build.
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
lake build
git status --short
```

For larger proof closures, also inspect axioms for the declarations you claim are complete:

```lean
#print axioms declaration_name
```

Do not trust labels like "PROVEN" or "done" unless the build and relevant axiom checks support
them.

## Documentation Discipline

- `ClassificationOfSurfaces/API.lean` is the current Lean API map.
- `docs/ARCHITECTURE.md` is the short human architecture summary.
- `docs/DESIGN_DECISIONS.md` records accepted decisions and open design questions.
- `codex_strategy_moise_pl.md` is the detailed Moise/PL handoff plan.
- `blueprint/src/content.tex` is the proof dependency blueprint.

If a doc becomes stale, either update it immediately or delete/merge it. Stale plans are worse than
missing plans because they create false coordination points.
