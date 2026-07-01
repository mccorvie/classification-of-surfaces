# Design Decisions

This file records project-level design decisions. Proposed changes should be discussed before large
amounts of code depend on them.

## Active Decisions

### D1. Main Interface Between Topology and Combinatorics

Decision: the intended meeting point is a theorem producing a `CellComplex` whose realization is
homeomorphic to the input surface.

```lean
∃ K : CellComplex, Nonempty (S ≃ₜ K.Realization)
```

Reason: Gallier-Xu's normal-form proof works on cell complexes, not directly on arbitrary
triangulations. Triangulations should be internal to the topology bridge.

Status: accepted provisionally.

### D2. Direction of Development

Decision: develop the combinatorial objects from the bottom first, while keeping the topology bridge
as a named theorem boundary.

Reason: top-down decomposition often fails when the bottom definitions do not match the high-level
interfaces. Here the clean split is useful only if `CellComplex` is the right concrete object.

Status: accepted provisionally.

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

### O2. Boundary Components

Options:

- store boundary components explicitly in `CellComplex`;
- derive them from unmatched boundary cycles;
- avoid boundary-component data until normal forms.

Current leaning: derive when possible, but keep normal-form parameters explicit because the eval
statement uses `p n`.

### O3. Realization of `CellComplex`

Options:

- quotient of a disjoint union of polygonal disks;
- quotient of abstract faces/edges/vertices with topology induced later;
- bridge through finite CW complexes.

Current leaning: polygon quotient is closest to the eval representatives, but requires quotient-map
work. Keep placeholder until the combinatorial structure is clearer.

### O4. Topological Bridge Target

Options:

- project-specific finite triangulations;
- mathlib classical CW complexes;
- theorem-boundary triangulation directly to `CellComplex`.

Current leaning: keep the public bridge as `CellComplex`; investigate CW and finite triangulations
behind that boundary.
