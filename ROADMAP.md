# Classification of Compact Surfaces: Project Roadmap

Goal: formalize the Lean Eval challenge `topological_classification_of_surfaces`:
every compact connected Hausdorff topological 2-manifold with boundary is homeomorphic to the
sphere, an orientable polygon quotient, or a non-orientable polygon quotient.

Primary references:

- Gallier-Xu, *A Guide to the Classification Theorem for Compact Surfaces*.
  - Chapter 3: simplices, complexes, triangulations.
  - Chapter 6: cell complexes, normal form, proof of classification.
  - Appendix E: every compact surface can be triangulated.
- Moise, *Geometric Topology in Dimensions 2 and 3*.
  - Early chapters: PL complexes and triangulated 2-manifolds.
  - Chapter 8: triangulation theorem for 2-manifolds.

## Proof Architecture

### 1. Eval Surface Interface

Define and consistently use the exact Lean Eval hypothesis block:

```lean
(S : Type*) [TopologicalSpace S]
[T2Space S] [ConnectedSpace S] [CompactSpace S]
[ChartedSpace (EuclideanHalfSpace 2) S]
[IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
```

This lives in `ClassificationOfSurfaces/Surface.lean`.

### 2. Representative Spaces

Define the two quotient families in the eval statement:

- `OrientableRel p n`
- `NonOrientableRel p n`

The eventual carrier should be a polygonal disk/cell model with boundary-edge identifications. This
lives in `ClassificationOfSurfaces/Representatives.lean`.

### 3. Triangulation Bridge

Formal target:

```lean
theorem compact_surface_triangulable : Triangulable S
```

This is likely the hardest topological bridge. We should decide whether to:

- develop a finite simplicial complex realization directly,
- bridge to mathlib CW-complex infrastructure,
- formalize a compact version of Gallier-Xu Appendix E/Thomassen,
- or use Moise/Rado triangulation as a theorem boundary and progressively fill prerequisites.

This lives in `ClassificationOfSurfaces/Triangulation.lean`.

### 4. Cell Complexes

Implement Gallier-Xu Definition 6.1 style finite cell complexes:

- finite faces, edges, vertices,
- oriented edges and inverse edge operation,
- face boundary words up to cyclic permutation,
- incidence/source/target data,
- connectedness,
- geometric realization as a quotient space.

This lives in `ClassificationOfSurfaces/CellComplex.lean`.

### 5. Normal-Form Reduction

Formal target:

```lean
theorem cell_complex_reduces_to_normal_form :
  ∀ K : CellComplex, ∃ N : NormalForm, K.HasNormalForm N
```

This is the combinatorial core from Gallier-Xu Chapter 6. We do not need to prove distinct normal
forms are non-homeomorphic for the eval statement, so homology and Euler characteristic should be
kept out of the critical path unless needed for some local argument.

This lives in `ClassificationOfSurfaces/NormalForm.lean`.

### 6. Final Assembly

Combine:

1. triangulate `S`,
2. convert the triangulation to a finite cell complex,
3. reduce the cell complex to normal form,
4. identify that normal form with the eval quotient representative.

This lives in `ClassificationOfSurfaces/EvalStatement.lean`.

## Suggested First Contributor Tasks

- Replace the placeholder `CellComplex` with a finite combinatorial structure close to Gallier-Xu
  Definition 6.1.
- Define cyclic words over oriented edge labels and prove basic operations on cyclic permutation.
- Define the normal-form words for orientable and non-orientable surfaces with boundary.
- Investigate mathlib topology/CW-complex files and decide whether the triangulation bridge should
  target CW complexes, simplicial complexes, or a project-specific finite complex.
- Make `OrientableRel` and `NonOrientableRel` genuine quotient relations over polygon models.

## Current Policy

It is acceptable for the repo to contain named theorem boundaries with `sorry` while the project is
being decomposed. Each `sorry` should represent a mathematically meaningful milestone and should be
local enough that a contributor can work on it independently.
