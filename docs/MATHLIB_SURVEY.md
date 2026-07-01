# Mathlib Survey

This is a first-pass survey against the pinned dependency in `lakefile.toml` (`mathlib` v4.31.0).
It is not exhaustive; it records likely starting points and gaps for this project.

## Manifolds

Relevant files:

- `Mathlib.Geometry.Manifold.Instances.Real`
- `Mathlib.Geometry.Manifold.Instances.Sphere`
- `Mathlib.Geometry.Manifold.IsManifold.Basic`

Useful names:

- `EuclideanHalfSpace n`
- `modelWithCornersEuclideanHalfSpace n`
- `ChartedSpace`
- `IsManifold`
- `Metric.sphere`
- sphere manifold instances via stereographic charts

The Lean Eval statement uses the standard mathlib manifold stack directly:

```lean
[ChartedSpace (EuclideanHalfSpace 2) S]
[IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
```

## Quotient Topology

Relevant files:

- `Mathlib.Topology.Constructions`
- `Mathlib.Topology.Maps.Basic`
- `Mathlib.Topology.ContinuousMap.Basic`

Useful names:

- topological space instances on `Quot` and `Quotient`
- `continuous_quot_mk`
- `continuous_quotient_mk'`
- `isQuotientMap_quot_mk`
- `isQuotientMap_quotient_mk'`
- `Topology.IsQuotientMap.continuous_iff`
- `Topology.IsQuotientMap.homeomorph`
- `Topology.IsQuotientMap.lift`

This is likely strong enough for polygon quotients and for proving maps out of quotient
representatives.

## CW Complexes

Relevant files:

- `Mathlib.Topology.CWComplex.Classical.Basic`
- `Mathlib.Topology.CWComplex.Classical.Finite`
- `Mathlib.Topology.CWComplex.Classical.Graph`
- `Mathlib.Topology.CWComplex.Abstract.Basic`

Useful names:

- `CWComplex`
- `RelCWComplex`
- `CWComplex.Finite`
- `CWComplex.FiniteType`
- `CWComplex.FiniteDimensional`
- `CWComplex.OneSkeletonGraph`
- `RelCWComplex.openCell`, `closedCell`, `cellFrontier`

Potential use:

- The topology track could target finite CW complexes and then extract a finite 2-dimensional cell
  complex.

Concern:

- Gallier-Xu cell complexes are combinatorial edge-word objects. mathlib CW complexes are
  topological cell-attachment structures. Bridging from CW cells to cyclic boundary words may be a
  substantial project by itself.

## Simplices and Triangulations

Relevant files:

- `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic`
- Euclidean simplex files under `Mathlib.Geometry.Euclidean.*`

Useful names:

- `Affine.Simplex`
- simplex faces, interiors, closed interiors, affine combinations

Observed gap:

- I did not find an obvious mature API for finite abstract simplicial complexes with geometric
  realization and triangulated manifolds matching Moise/Gallier-Xu directly.

Potential response:

- Define a project-specific finite triangulation structure if the topological bridge needs it.
- Keep the final interface at `CellComplex`, so this choice remains internal to
  `Triangulation.lean`.

## Graphs and Combinatorics

Mathlib has graph theory APIs, but Gallier-Xu's cell-complex normal-form proof is closer to cyclic
word rewriting with incidence constraints than to ordinary graph algorithms. We should expect to
build project-specific combinatorial infrastructure for:

- oriented edge labels,
- inverse labels,
- words and cyclic words,
- face boundary functions,
- elementary cut/glue transformations.

## Recommendation

For the near term:

1. Use mathlib quotient topology for representative spaces.
2. Build project-specific combinatorial cell complexes and cyclic words.
3. Do not commit yet to CW complexes as the topological bridge target.
4. Keep a theorem boundary from compact eval-surfaces to `CellComplex.Realization` while the
   combinatorial representation stabilizes.

The main risk is picking a topological interface too early. The combinatorial side should determine
what data `CellComplex` must contain.
