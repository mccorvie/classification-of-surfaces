# The Moise–Radó triangulation route

This is the onboarding and handoff map for `ClassificationOfSurfaces/Moise/`.  For the executable
faithfulness review, read `RADO_AUDIT.md`; for deliberately weak downstream interfaces, read
`KNOWN_WEAK.md`.

## Result

The route is complete for compact connected Eval surfaces, including surfaces with manifold
boundary:

```lean
moise_triangulation :
  Nonempty (GeometricTriangulation S)
```

`GeometricTriangulation S` consists of a finite vertex type, a finite family of three-vertex
faces, and a homeomorphism from their concrete barycentric realization to `S`.  Its meaning is
pinned independently by `nonempty_geometricTriangulation_iff_explicit`, and the public theorem
`moise_triangulation_explicit` exposes the flattened conclusion.

Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 8, Thm. 3 proves the result for
2-manifolds in his boundary-free sense.  This repository extends the induction to half-disk
charts.  The extra content is exact preservation of the mathlib manifold-boundary stratum during
relative polygonal straightening and through the synchronized weld.  It should therefore be
described as a bordered extension of Moise's proof, not as Moise's theorem quoted verbatim.

## Dependency map

```text
moise_triangulation
  ← moise_triangulation_of_boundaries
  ← moise_triangulation_of_induction
  ← moise_finite_chart_cover + moise_induction_step
  ← radoInvariant_chartPatch + MoiseChart.exists_crossing_weld
  ← exists_boundaryPreservingStraightening
     + exists_crossing_weld_of_boundaryPreservingStraightening
     + PartialTriangulation.exists_glued
  ← chart extraction + locally finite PL approximation
     + synchronized arrangements + boundary-face preservation
```

The classical source dependencies are:

```text
Moise 8.3  ←  8.1 chart cover + 8.2 open polyhedra + 6.3 PL approximation + 7.6 gluing
Moise 6.3  ←  6.2 graph approximation + 5.3/5.4 combinatorial Schoenflies
Moise 5.3  ←  Ch. 2 polygonal Jordan + Ch. 3 polygonal Schoenflies
```

The full Jordan curve theorem from Ch. 4 and the full Schoenflies theorem from Ch. 9 are not
used.

## Load-bearing interfaces

- `GeometricRealization` is the finite union of `GeometricFace`s in a standard simplex.
  `GeometricFace.inter` proves that two faces meet exactly in their common barycentric face.
- `GeometricTriangulation` has no arbitrary realization field.  Its homeomorphism targets the
  realization computed from its vertices and faces.
- `PartialTriangulation` is the corresponding finite realization embedded into the surface.
- `RadoInvariant` records compact absorbed cores, edge valence at most two, exposed
  boundary-face regularity, and containment of the cores in the ambient topological interior of
  the support.
- `MoiseChart.BoundaryFaithful` distinguishes disk charts from half-disk charts and identifies
  manifold-boundary membership with zero normal coordinate in the latter.
- `BoundaryPreservingStraightening` records exact preservation of that boundary stratum by the
  frontier-glued replacement.

The bordered invariant deliberately uses topological interior relative to the ambient surface.
A point of the manifold boundary can be interior to a half-disk neighborhood in the surface
while lying on its combinatorial boundary.

## Where the hard content lives

- Polygonal Jordan and relative polygonal Schoenflies:
  `PolygonalJordan.lean`, `PolygonalSchoenflies.lean`.
- Finite and locally finite PL approximation:
  `GraphPolygonalization.lean`, `PLApproximation.lean`,
  `LocallyFiniteControlledApproximation.lean`.
- Faithful intrinsic refinement and cellwise filling:
  `IntrinsicMidpointSubdivision.lean`, `IntrinsicFineSubdivision.lean`,
  `IntrinsicFaceFilling.lean`, `IntrinsicCellwiseExtension.lean`.
- Chart extraction, fixed disk/half-disk patches, and boundary invariance:
  `ChartExtraction.lean`, `ChartPatch.lean`, `BoundaryInvariant.lean`.
- Frontier matching, synchronized finite welding, gluing, and finite induction:
  `FrontierGlue.lean`, `RelativeSynchronizedArrangement.lean`, `ChartInduction.lean`.

`ChartInduction.lean` is large because it contains the complete synchronized crossing
construction.  It should be split only along a genuine reusable interface, not merely to move
line counts between files.

## Definition-faithfulness checks

`Countermodels.lean`, which is part of the default build, checks:

- the standard 2-simplex has a one-face geometric triangulation;
- `ℝ` and `ℚ` have no finite geometric triangulation;
- a nonempty triangulated space has a nonempty face family and at least three vertices;
- the empty-face and one-vertex junk strategies fail;
- the legacy `FiniteSurfaceTriangulation` record can still be inhabited for arbitrary
  universe-0 spaces and need not convert to valid or connected incidence data.

The last item is a boundary between projects, not a defect in Radó's conclusion.  The compatibility
bridge preserves raw finite data and a stored realization, but it does not yet certify
`SurfaceCellComplex.IsSurfaceValid`, `SurfaceCellComplex.IsConnected`, or the polygonal quotient
realization.  Do not describe that bridge as a certified surface cellulation.

## Verification

For changes to this route:

```bash
lake build
rg -n '\bsorry\b|\baxiom\b|native_decide|implemented_by|admit' ClassificationOfSurfaces
```

Then inspect axioms for the declarations touched.  The completed Radó chain is expected to use
only `[propext, Classical.choice, Quot.sound]`.  Compilation and axiom checks audit the proof
layer; `Countermodels.lean` and `RADO_AUDIT.md` audit the meanings of the definitions.

## Downstream handoff

New triangulation work should consume `GeometricTriangulation`.  The legacy
`FiniteSurfaceTriangulation` and `SurfaceCellComplex.realization` remain in `KNOWN_WEAK.md`.
The next project-level task is to certify incidence and connectivity and replace the stored
realization with the polygonal quotient before the Gallier–Xu normal-form chain relies on it.
