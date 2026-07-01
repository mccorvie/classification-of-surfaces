# Proof Strategy

This document describes the intended formalization strategy for the Lean Eval challenge
`topological_classification_of_surfaces`.

The target theorem says that every compact connected Hausdorff topological 2-manifold with boundary
is homeomorphic to either the sphere, an orientable normal-form quotient, or a non-orientable
normal-form quotient.

## Main Claim About the Split

There appears to be a clean separation between two parts of the proof:

1. **Topological bridge:** show that every space satisfying the eval surface hypotheses can be
   represented by finite combinatorial data.
2. **Combinatorial classification:** show that the finite combinatorial data can be transformed into
   one of the normal forms named in the eval statement.

This split is supported directly by Gallier-Xu, Section 1.1: the proof is described as a
triangulation step followed by a finite combinatorial normal-form step. Gallier-Xu Chapter 6 then
runs the combinatorial part using cell complexes, and Appendix E gives a compact-surface
triangulation route. Moise gives a broader PL/topological triangulation framework for 2-manifolds.

The split is not automatic in Lean. It becomes clean only if we choose the interface object well.
The interface should be concrete enough for combinatorial rewriting, but topological enough that the
triangulation theorem can actually produce it.

## Proposed Interface

The interface should eventually be a theorem of the following form:

```lean
theorem compact_surface_homeomorphic_to_cell_complex
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ K : CellComplex, Nonempty (S ≃ₜ K.Realization)
```

This is better than exposing triangulations directly to the final theorem, because Gallier-Xu's
normal-form proof works with cell complexes. A triangulation is then an internal tool used to build
`K`.

The combinatorial side should prove:

```lean
theorem cell_complex_has_eval_representative (K : CellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n)))
```

The final assembly is then mostly homeomorphism composition.

## Why Not Pure Top-Down?

A purely top-down split risks introducing theorem statements that are too abstract or not aligned
with the combinatorial objects people can actually manipulate. The safer approach is:

1. Build the combinatorial `CellComplex` and normal-form quotient representatives from the bottom.
2. In parallel, investigate which topological realization theorem can produce that exact structure.
3. Treat `compact_surface_homeomorphic_to_cell_complex` as the meeting point, but let the concrete
   definition of `CellComplex` be driven by the combinatorial proof.

This is a controlled meet-in-the-middle approach: the meeting point is a single explicit type and a
single explicit homeomorphism theorem, not a loose family of informal assumptions.

## Work Packages

### A. Combinatorial Core

Files:

- `ClassificationOfSurfaces/CellComplex.lean`
- `ClassificationOfSurfaces/NormalForm.lean`
- `ClassificationOfSurfaces/Representatives.lean`

Tasks:

- Define oriented edge labels and inverse orientation.
- Define words and cyclic words over oriented edges.
- Define Gallier-Xu-style finite cell complexes `(F, E, B)`.
- Define elementary subdivision/equivalence moves from Gallier-Xu Definition 6.3.
- Define canonical/normal forms from Gallier-Xu Definition 6.5.
- Prove every finite connected surface cell complex reduces to normal form.
- Define the polygon quotient relations `OrientableRel p n` and `NonOrientableRel p n`.
- Prove normal-form cell complexes realize those quotient spaces.

This track can be worked mostly independently of manifold topology once `CellComplex.Realization`
is fixed.

### B. Topological Bridge

Files:

- `ClassificationOfSurfaces/Surface.lean`
- `ClassificationOfSurfaces/Triangulation.lean`

Tasks:

- Decide whether to build on mathlib CW-complexes, define a project-specific finite simplicial
  complex, or use a theorem boundary while formalizing prerequisites.
- Prove compact eval-surfaces are triangulable.
- Convert a finite triangulation to a `CellComplex`.
- Prove the resulting realization is homeomorphic to the original surface.

This track should not depend on the details of the normal-form reduction, only on the final
`CellComplex` data structure and its realization.

### C. Final Assembly

File:

- `ClassificationOfSurfaces/EvalStatement.lean`

Tasks:

- Use the topological bridge to obtain `K : CellComplex` and `S ≃ₜ K.Realization`.
- Use the combinatorial theorem on `K`.
- Compose homeomorphisms to match the exact Lean Eval theorem statement.

## Current Lean Skeleton

The current files are intentionally skeletal. The existing `sorry`s mark major theorem boundaries,
not missing one-line proofs.

- `Surface.lean`: eval hypothesis interface.
- `Representatives.lean`: names for sphere and quotient representative families.
- `Triangulation.lean`: triangulation theorem boundary.
- `CellComplex.lean`: placeholder finite cell complex type.
- `NormalForm.lean`: normal-form theorem boundary.
- `EvalStatement.lean`: final theorem statement.
- `Examples.lean`: standard example surfaces used as regression targets.

## Open Design Decisions

1. What should `CellComplex.Realization` be? A quotient of polygonal disks is closest to the eval
   representatives, but may require more topology upfront.
2. Should cyclic words be represented as quotients of lists under rotation, or as lists with lemmas
   modulo cyclic permutation?
3. Should boundary components be part of the cell complex structure, or derived from unmatched
   boundary cycles?
4. Should the topological bridge target project-specific finite complexes or mathlib's CW-complex
   API?
5. How much PL topology should be formalized before we state triangulation as a theorem boundary?

## Recommended Near-Term Plan

1. Make the combinatorial objects precise first: oriented edges, cyclic words, cell complexes.
2. Define normal-form words and quotient representatives in terms of those objects.
3. Add small examples: sphere, disk, torus, projective plane, annulus, Mobius strip.
4. In parallel, survey mathlib's CW-complex and quotient-topology APIs and write a short design note
   recommending the triangulation target.
5. Only then harden the topological bridge theorem statement.
