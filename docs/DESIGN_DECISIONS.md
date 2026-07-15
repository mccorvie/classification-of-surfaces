# Design Decisions

This file records project-level design decisions and open design questions. It is intentionally
shorter and more stable than `docs/MOISE_ROUTE.md`: use this file to see what choices are
accepted, provisional, or still open before building new code on top of them.

Not every item in this file is decided. The `Active Decisions` section records choices the current
code and docs assume; the `Open Decisions` section records questions that still need resolution.

## Active Decisions

### D1. Main Interface Between Topology and Combinatorics

Decision: the intended meeting point is a theorem producing a `SurfaceCellComplex` whose realization is
homeomorphic to the input surface.

```lean
∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization)
```

Reason: Gallier-Xu's normal-form proof works on cell complexes, not directly on arbitrary
triangulations. Triangulations should be internal to the topology bridge.

Status: accepted.

Preferred Lean name: `SurfaceCellComplex`. The older `CellComplex` name remains as a compatibility
alias for early scaffold code and should not be used in new declarations.

### D2. Direction of Development

Decision: develop the combinatorial objects from the bottom first, while keeping the topology bridge
as a named theorem boundary.

Reason: top-down decomposition often fails when the bottom definitions do not match the high-level
interfaces. Here the clean split is useful only if `SurfaceCellComplex` is the right concrete object.

Status: accepted.

### D3. Non-Homeomorphism of Normal Forms

Decision: non-homeomorphism/uniqueness of normal forms is out of the critical path for the Lean Eval
statement.

Reason: the eval theorem asks for existence of a normal-form representative, not uniqueness.
Homology, Euler characteristic, and orientability invariants should be introduced only if needed for
existence-side arguments.

Status: accepted.

## Open Decisions

### O1. Cyclic Words

Options:

- represent cyclic words as quotient types of lists under rotation;
- represent them as lists plus a relation `CyclicPerm` used in theorem statements;
- use a canonical rotation when labels have decidable order.

Current leaning: start with lists plus an explicit relation. Quotients may make rewriting painful too
early.

Status: open.

### O2. Boundary Components

Options:

- store boundary components explicitly in `SurfaceCellComplex`;
- derive them from unmatched boundary cycles;
- avoid boundary-component data until normal forms.

Current leaning: derive when possible, but keep normal-form parameters explicit because the eval
statement uses `p n`.

Status: open.

### O3. Realization of `SurfaceCellComplex`

Options:

- quotient of a disjoint union of polygonal disks;
- quotient of abstract faces/edges/vertices with topology induced later;
- bridge through finite CW complexes.

Current leaning: use the generic quotient foundation in `PolygonalQuotient.lean`. It models an
`n`-sided cell as a closed disk with `n` marked circular boundary arcs, so monogons and digons do
not degenerate. Side identifications use either the identity parameter or the affine reversal
`t ↦ 1 - t`, and their equivalence closure has the quotient topology. The remaining adapter must
pair boundary *occurrences* rather than dart values and must explicitly handle an empty boundary
word: a disk with no marked sides is not a sphere. This topological carrier does not by itself
supply the straight-edged convex polygons requested for the explicit normal-form representatives.

Status: open.

### O4. Topological Bridge Target

Options:

- project-specific finite triangulations;
- mathlib classical CW complexes;
- theorem-boundary triangulation directly to `SurfaceCellComplex`.

Current leaning: keep the public bridge as `SurfaceCellComplex`; investigate CW and finite triangulations
behind that boundary.

Status: open.
