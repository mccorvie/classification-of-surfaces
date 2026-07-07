# Codex strategy: Moise / PL-complex route to surface classification

This document is a handoff guide for Codex and human contributors working from the Lean blueprint file `blueprint_moise_pl_route.tex`. Its purpose is not to ask Codex to prove the full classification theorem in one pass. The goal is to keep the proof modular, so several people or autoformalizers can work independently on topology, PL infrastructure, quotient spaces, and Gallier--Xu normal-form reductions.

The Moise route should prove the topological bridge by building a finite triangulation of a compact bordered surface, then converting that triangulation to the shared finite surface cell-complex API used by the combinatorial classification.

The central design principle is:

```text
Do not let the Moise / PL code leak into the Gallier--Xu normal-form code.
Moise produces finite triangulations.
The shared infrastructure converts finite triangulations to finite cell complexes.
Gallier--Xu only consumes finite cell complexes.
```

The intended proof path is:

```text
Lean Eval compact surface with boundary
  -> Moise-compatible bordered surface interface
  -> PL-complex / PL-approximation machinery
  -> finite triangulation of compact bordered surfaces
  -> finite surface cell complex
  -> quotient realization
  -> Gallier--Xu elementary moves
  -> canonical quotient representatives
  -> Lean Eval classification theorem
```

## Compilation policy

The first milestone is a compiling project with stable theorem statements. Heavy topology theorems may initially be proved by `by sorry`, but their declarations should have the right shape and should not be changed casually once downstream work depends on them.

Prefer small definitions and explicit theorem boundaries over ambitious monolithic statements. If Codex is asked to work on a hard theorem, it should usually be asked to create the declaration, prove easy wrappers, and leave the source theorem as a named `sorry` rather than inventing a fragile proof.

Use a single project namespace. The blueprint currently proposes names under:

```lean
namespace LeanEval.Topology.ClassificationOfSurfaces
```

or an equivalent project namespace. Do not create parallel duplicate notions in different namespaces unless they are explicitly route-specific wrappers.

Use `noncomputable section` and `open Classical` freely where this simplifies finite choices. This project is not aiming for computable extraction.

## Common proof API

These are the hinge points that both the Moise route and the Mohar--Thomassen route should share. They are the most important interfaces to stabilize early.

Current Lean status: the project now has a compiling bottom-layer scaffold for these names. The
preferred public names are `SurfaceCellComplex`, `FiniteSurfaceTriangulation`, and
`SurfaceTriangulable`; legacy aliases `CellComplex`, `FiniteTriangulation`, and `Triangulable`
remain only for compatibility with early scaffold code. See `ClassificationOfSurfaces/API.lean`
for the current declaration map.

### API 0: Eval surface wrapper

Blueprint label:

```text
moise:def:eval_surface
```

Proposed Lean name:

```lean
LeanEval.Topology.ClassificationOfSurfaces.EvalSurface
```

Purpose: package the hypotheses of the Lean Eval problem.

The Eval input is a compact connected Hausdorff topological 2-manifold with boundary, expressed using mathlib's charted-space manifold stack:

```lean
[TopologicalSpace S]
[T2Space S]
[ConnectedSpace S]
[CompactSpace S]
[ChartedSpace (EuclideanHalfSpace 2) S]
[IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
```

Do not replace this with a closed-surface definition. Boundary is part of the final theorem.

A wrapper structure is optional, but useful for blueprint and Codex work:

```lean
structure EvalSurface (S : Type*) [TopologicalSpace S] : Prop where
  t2 : T2Space S
  connected : ConnectedSpace S
  compact : CompactSpace S
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  manifold : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S
```

This exact code may need adjustment because some of these are typeclasses rather than fields. The important point is that downstream bridge theorems should use the Eval hypotheses verbatim or through a transparent wrapper.

### API 1: finite surface cell complex

Blueprint labels:

```text
moise:def:surface_cell_complex
moise:def:cell_realization
```

Proposed Lean names:

```lean
SurfaceCellComplex
SurfaceCellComplex.Realization
```

This is the common combinatorial target. It should be independent of the chosen topological route.

A good first implementation is a finite polygon-gluing object with oriented darts:

```lean
structure SurfaceCellComplex where
  Face : Type u
  Dart : Type v
  Vertex : Type w
  [faceFinite : Fintype Face]
  [dartFinite : Fintype Dart]
  [vertexFinite : Fintype Vertex]

  inv : Dart ≃ Dart
  source : Dart → Vertex
  target : Dart → Vertex
  boundary : Face → List Dart

  inv_source : ∀ d, source (inv d) = target d
  inv_target : ∀ d, target (inv d) = source d

  -- Surface-validity conditions may begin as fields or separate predicates.
  -- For example: every non-boundary dart is paired, each vertex link is a
  -- circle or interval, each face boundary is cyclically composable, etc.
```

Do not over-optimize the first version. It is acceptable to store vertices explicitly even if Gallier--Xu derives vertices from successor relations. Explicit vertices usually make Lean proofs easier.

The realization should be a quotient of a disjoint union of standard polygons:

```lean
def SurfaceCellComplex.PreRealization (K : SurfaceCellComplex) : Type :=
  Σ f : K.Face, StandardPolygon (K.boundary f).length

def SurfaceCellComplex.Realization (K : SurfaceCellComplex) : Type :=
  Quotient K.gluingSetoid
```

The exact `StandardPolygon` representation is a separate design choice. It may be a closed disk with marked boundary arcs, a convex polygon in `ℝ²`, or a combinatorial topological polygon already known homeomorphic to a disk. The quotient API should hide this choice.

The key downstream fact is not that `K.Realization` is a manifold. The key fact is that it is a topological space and that quotient presentations can be compared by induced homeomorphisms.

### API 2: quotient realization congruence

Blueprint labels:

```text
moise:def:polygonal_prerealization
moise:def:gluing_relation
moise:thm:mathlib_quotient_congr
moise:lem:cell_realization_quotient_congr
```

Proposed Lean names:

```lean
SurfaceCellComplex.PreRealization
SurfaceCellComplex.gluingRel
SurfaceCellComplex.realizationCongr
```

Purpose: turn “these two quotient presentations describe the same glued space” into an actual homeomorphism.

The common theorem shape should be:

```lean
theorem SurfaceCellComplex.realizationCongr
    {K L : SurfaceCellComplex}
    (e : K.PreRealization ≃ₜ L.PreRealization)
    (hrel : ∀ x y, K.gluingRel x y ↔ L.gluingRel (e x) (e y)) :
    K.Realization ≃ₜ L.Realization := by
  -- use mathlib quotient-homeomorphism API
  sorry
```

This theorem is the engine behind all elementary cut/glue moves. The quotient team should own it. The Gallier--Xu team should not reprove quotient topology facts for every move.

A second useful form is relation-only congruence on the same pre-space:

```lean
theorem SurfaceCellComplex.realizationCongrRight
    {X : Type*} [TopologicalSpace X]
    {r s : Setoid X}
    (h : ∀ x y, r x y ↔ s x y) :
    Quotient r ≃ₜ Quotient s := by
  sorry
```

Use mathlib's quotient homeomorphism lemmas where possible. Do not build a custom quotient topology theory unless mathlib lacks a needed API.

### API 3: finite triangulation to cell complex

Blueprint labels:

```text
moise:def:finite_surface_triangulation
moise:def:triangulation_cell_complex
moise:lem:triangulation_to_cell_complex_realization
moise:thm:finite_triangulation_to_cell_complex
```

Proposed Lean names:

```lean
FiniteSurfaceTriangulation
FiniteSurfaceTriangulation.toCellComplex
FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic
finite_triangulation_to_cell_complex
```

The Moise topology route should output finite triangulations. The common infrastructure should convert them to `SurfaceCellComplex`.

Suggested interface:

```lean
structure FiniteSurfaceTriangulation (S : Type*) [TopologicalSpace S] where
  Complex : Type u
  realization : Type v
  [realizationTop : TopologicalSpace realization]
  finiteVertices : Prop
  finiteEdges : Prop
  finiteFaces : Prop
  isSurfaceTriangulation : Prop
  homeomorphSurface : Nonempty (realization ≃ₜ S)
```

This is only schematic. A stronger implementation should explicitly store finite vertices, edges, triangles, incidence maps, and realization. The main point is that the triangulation object should be finite and should include or produce a homeomorphism to the original surface.

The conversion theorem should be the only bridge from triangulations to Gallier--Xu cell complexes:

```lean
def FiniteSurfaceTriangulation.toCellComplex
    (T : FiniteSurfaceTriangulation S) : SurfaceCellComplex :=
  sorry

theorem FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic
    (T : FiniteSurfaceTriangulation S) :
    Nonempty (T.realization ≃ₜ T.toCellComplex.Realization) := by
  sorry
```

For a triangular complex, each triangle becomes a face whose boundary word has length three. Each geometric edge gives a dart-pair. Vertices are inherited from the triangulation.

This conversion is conceptually routine but Lean-heavy. It should be developed by the common infrastructure team, not by the Moise topology team.

### API 4: Gallier--Xu normal-form theorem

Blueprint labels:

```text
moise:def:gx_elementary_moves
moise:lem:elementary_moves_preserve_realization
moise:thm:equivalent_cell_complexes_homeomorphic
moise:def:gx_invariants
moise:def:canonical_cell_complex
moise:thm:gx_normal_form
moise:def:eval_quotient_representatives
moise:lem:canonical_realization_eval_quotient
moise:thm:cell_complex_has_eval_representative
```

Proposed Lean names:

```lean
SurfaceCellComplex.ElementaryMove
SurfaceCellComplex.Equivalent
SurfaceCellComplex.elementaryMove_homeomorph
SurfaceCellComplex.equivalent_homeomorph
SurfaceCellComplex.normalForm
SurfaceCellComplex.hasEvalRepresentative
```

The Gallier--Xu theorem should consume only `SurfaceCellComplex`:

```lean
theorem SurfaceCellComplex.hasEvalRepresentative
    (K : SurfaceCellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
    (∃ p n, (1 ≤ p ∨ 1 ≤ n) ∧
      Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
    (∃ p n, 1 ≤ p ∧
      Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) := by
  sorry
```

This theorem should not mention PL maps, charts, Moise, Jordan curves, or embedded plane graphs.

### API 5: topological bridge for Moise

Blueprint labels:

```text
moise:thm:compact_eval_surface_finitely_triangulable
moise:thm:compact_surface_cellulable
```

The Moise route should prove:

```lean
theorem compact_eval_surface_finitely_triangulable
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ T : FiniteSurfaceTriangulation S, True := by
  sorry
```

A better final form is:

```lean
theorem compact_eval_surface_finitely_triangulable
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ T : FiniteSurfaceTriangulation S,
      Nonempty (T.realization ≃ₜ S) := by
  sorry
```

Then assemble:

```lean
theorem compact_surface_homeomorphic_to_cell_complex
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization) := by
  obtain ⟨T, hT⟩ := compact_eval_surface_finitely_triangulable S
  let K := T.toCellComplex
  -- compose hT with T.toCellComplex_realization_homeomorphic
  sorry
```

This is the main hinge between topology and combinatorics.

## Moise-specific route

The Moise route should be developed as a PL-topology library culminating in a finite triangulation theorem for compact bordered surfaces.

The blueprint labels to follow are:

```text
moise:def:euclidean_complex
moise:def:subdivision
moise:def:pl_map_homeomorphism
moise:lem:pl_invariant_under_subdivision
moise:def:combinatorial_surface
moise:def:combinatorial_two_cell
moise:lem:polygonal_disk_combinatorial_cell
moise:thm:pl_schoenflies_combinatorial_cell
moise:def:strongly_positive
moise:def:phi_approximation
moise:lem:pl_approximation_one_skeleton
moise:thm:pl_approximation_plane
moise:thm:pl_approximation_between_surfaces
moise:def:pl_complex_in_space
moise:def:pl_complex_interior_subcomplex
moise:thm:open_subset_complex
moise:lem:compact_locally_finite_complex_finite
moise:def:moise_two_manifold
moise:lem:chart_pair_exhaustion
moise:lem:initial_pl_neighborhood
moise:lem:extend_pl_complex_across_chart
moise:thm:rado_triangulation_moise_manifold
moise:thm:compact_moise_surface_finitely_triangulable
moise:thm:bordered_pl_approximation
moise:thm:rado_bordered_surface_triangulation
moise:lem:eval_to_moise_bordered_surface
moise:thm:compact_eval_surface_finitely_triangulable
```

### Moise work package M1: Euclidean complexes and subdivisions

Implement the basic PL objects before attempting triangulation.

Minimum declarations:

```lean
structure EuclideanComplex where
  Point : Type u
  -- or: ambient : Type; [NormedAddCommGroup ambient]; [NormedSpace ℝ ambient]
  Simplex : Type v
  finiteSimplex : Fintype Simplex
  support : Set Point
  -- incidence / face data

structure EuclideanComplex.Subdivision (K : EuclideanComplex) where
  K' : EuclideanComplex
  same_support : K'.support = K.support
  simplex_refines : Prop
```

If mathlib's abstract or geometric simplicial complexes can be used cleanly, wrap them. If not, define a project-specific `EuclideanComplex` with the fields needed for Moise. Avoid getting blocked by the perfect general abstraction.

Current scaffold note: the standard combinatorial triangle keeps finite vertex/simplex data, but
its support is now the geometric closed triangle in `EuclideanSpace ℝ (Fin 2)`. This avoids the
old one-point triangle carrier, which made genuine embedded chart disks impossible.
`RadoChartPair.standardTrianglePlaneCore` and
`ChartPolygonalDisk.standardTriangleInPlane` provide the concrete model chart disk in the
coordinate plane.

Required theorem boundary:

```lean
theorem common_subdivision
    (K₁ K₂ : EuclideanComplex) :
    -- appropriate common-refinement statement
    sorry
```

Use this to make PL maps stable under subdivision.

### Moise work package M2: PL maps and PL homeomorphisms

Implement:

```lean
structure PLMap (K L : EuclideanComplex) where
  toFun : K.support → L.support
  continuous_toFun : Continuous toFun
  exists_subdivision_linear : Prop

structure PLHomeomorph (K L : EuclideanComplex) where
  toHomeomorph : K.support ≃ₜ L.support
  pl_toFun : PLMap K L
  pl_invFun : PLMap L K
```

Prove basic closure properties:

```lean
theorem PLHomeomorph.refl : PLHomeomorph K K := by sorry

theorem PLHomeomorph.symm (e : PLHomeomorph K L) : PLHomeomorph L K := by sorry

theorem PLHomeomorph.trans (e₁ : PLHomeomorph K L) (e₂ : PLHomeomorph L M) :
    PLHomeomorph K M := by sorry

theorem pl_iff_pl_after_subdivision : ... := by sorry
```

This is reusable infrastructure. It should not depend on surfaces.

### Moise work package M3: combinatorial surfaces and cells

Implement combinatorial local conditions:

```lean
structure CombinatorialTwoManifoldWithBoundary where
  K : EuclideanComplex
  isTwoDimensional : Prop
  vertex_link_circle_or_interval : Prop

structure CombinatorialTwoCell where
  K : EuclideanComplex
  boundary : EuclideanComplex
  pl_homeomorphic_to_closed_triangle : Prop
```

Useful theorem boundaries:

```lean
theorem support_of_combinatorial_surface_is_manifold_with_boundary
    (K : CombinatorialTwoManifoldWithBoundary) :
    IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 K.K.support := by
  sorry

theorem pl_schoenflies_combinatorial_two_cell
    {C D : CombinatorialTwoCell}
    (e : PLHomeomorph C.boundary D.boundary) :
    ∃ E : PLHomeomorph C.K D.K, E.restrict_boundary = e := by
  sorry
```

`pl_schoenflies_combinatorial_two_cell` is a major but controlled theorem. It is far more manageable than general Jordan--Schoenflies and should be a named milestone.

### Moise work package M4: strongly positive functions and approximation

Define the approximation language before proving approximation theorems:

```lean
structure StronglyPositive {X : Type*} [TopologicalSpace X] (φ : X → ℝ) : Prop where
  positive : ∀ x, 0 < φ x
  -- choose either Moise's exact notion or a continuous-positive surrogate

structure PhiApproximation
    {X Y : Type*} [PseudoMetricSpace Y]
    (φ : X → ℝ) (f g : X → Y) : Prop where
  close : ∀ x, dist (f x) (g x) < φ x
```

The first serious theorem boundary is one-skeleton approximation:

```lean
theorem pl_approximation_one_skeleton
    (K : CombinatorialTwoManifoldWithBoundary)
    (h : K.K.support ≃ₜ SetLikePlaneRegion)
    (φ : K.K.support → ℝ)
    (hφ : StronglyPositive φ) :
    ∃ f₁, IsPLApproximationOnOneSkeleton K h φ f₁ := by
  sorry
```

This theorem requires polygonal approximation of finitely many edge images with separation control. It may be split further into finite families of arcs, edge separation, and vertex preservation.

### Moise work package M5: PL approximation theorem

Main theorem boundary:

```lean
theorem pl_approximation_plane_combinatorial_surface
    (K : CombinatorialTwoManifoldWithBoundary)
    (h : K.K.support ≃ₜ PlaneRegion)
    (φ : K.K.support → ℝ)
    (hφ : StronglyPositive φ) :
    ∃ f : PLHomeomorph K.K PlaneComplex,
      PhiApproximation φ f.toHomeomorph h := by
  sorry
```

Expected proof structure:

1. Subdivide `K` finely enough that each simplex is small relative to the local tolerance.
2. Approximate the one-skeleton by a PL embedding.
3. Use PL Schoenflies to extend over each 2-cell.
4. Prove the extensions agree on shared edges.
5. Prove global injectivity and surjectivity using the separation estimates.

Do not ask Codex to invent this proof at once. Ask it to formalize the statement, create auxiliary predicates, and prove small composition/monotonicity lemmas for approximation.

### Moise work package M6: PL complexes inside arbitrary spaces

Moise builds PL complexes inside the surface. Define:

```lean
structure PLComplexIn (X : Type*) [TopologicalSpace X] where
  Complex : EuclideanComplex
  embed : Complex.support ↪ X
  embedding : Embedding embed
  locallyFinite : Prop
```

Needed operations:

```lean
def PLComplexIn.support (K : PLComplexIn X) : Set X := Set.range K.embed

def PLComplexIn.interiorSubcomplex ... := sorry

theorem open_subset_complex
    (K : EuclideanComplex) (U : Set K.support) (hU : IsOpen U) :
    ∃ KU : EuclideanComplex, KU.support ≃ₜ U := by
  sorry

theorem compact_locally_finite_complex_finite
    (K : PLComplexIn X) [CompactSpace X]
    (hSupport : K.support = Set.univ)
    (hLoc : K.locallyFinite) :
    K.Complex.IsFinite := by
  sorry
```

`open_subset_complex` is one of the Moise Chapter 8 support theorems. It may be left as a theorem boundary at first.

### Moise work package M7: Rado induction for closed surfaces

Define a Moise-style 2-manifold interface if needed:

```lean
structure MoiseTwoManifold (M : Type*) [TopologicalSpace M] where
  t2 : T2Space M
  local_disk_or_half_disk : Prop
  secondCountable_or_separable_metric : Prop
  chartPairExhaustion : ChartPairExhaustion M
  radoInductionData : RadoInductionData chartPairExhaustion
```

For the Eval problem, this is not the final interface. It is an intermediate bridge from
mathlib's charted-space manifold to Moise's hypotheses. The hard extraction from mathlib's
`ChartedSpace` atlas to a countable chart-pair exhaustion and the associated local Rado
induction data is isolated in `mathlib_bordered_surface_moise_extraction_data`.

Current extraction layer:

```lean
structure FiniteChartPairCover (M : Type*) [TopologicalSpace M] where
  Index : Type*
  indexFintype : Fintype Index
  pair : Index → RadoChartPair M
  covers : ∀ x : M, ∃ i : Index, x ∈ (pair i).core

structure MoiseExtractionData (M : Type*) [TopologicalSpace M] where
  finiteCover : FiniteChartPairCover M
  local_disk_or_half_disk : Prop
  secondCountable_or_separable_metric : Prop
  radoInductionData : RadoInductionData finiteCover.toChartPairExhaustion

structure FiniteChartPolygonalDiskData
    {M : Type*} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  disk : C.Index → ChartPolygonalDisk M
  chart_eq : ∀ i : C.Index, (disk i).chart = C.pair i
  compatibleChartShrinks : Prop
  boundaryCompatibleChartShrinks : Prop

structure LocalChartPolygonalDiskData (M : Type*) [TopologicalSpace M] where
  pairAt : M → RadoChartPair M
  diskAt : M → ChartPolygonalDisk M
  chart_eq : ∀ x : M, (diskAt x).chart = pairAt x
  core_mem_nhds : ∀ x : M, (pairAt x).core ∈ 𝓝 x
  compatibleChartShrinks : Prop
  boundaryCompatibleChartShrinks : Prop

structure PointChartPolygonalDiskData (M : Type*) [TopologicalSpace M] (x : M) where
  disk : ChartPolygonalDisk M
  core_mem_nhds : disk.chart.core ∈ 𝓝 x

structure FiniteRadoInductionGeometry
    {M : Type*} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  initial : InitialPLNeighborhoodData C.toChartPairExhaustion
  step :
    ∀ (_n : ℕ) (S : RadoInductionState M),
      RadoStepExtensionData C.toChartPairExhaustion S
  compatibleStages : Prop
  locallyFiniteUnion : Prop
  boundaryCompatibleUnion : Prop
```

Proved finite/combinatorial bridge:

1. `FiniteChartPairCover.exists_of_compact_local`:
   local chart-pair cores that are neighborhoods of their points admit a finite subcover by
   compactness.
2. `FiniteChartPairCover.toChartPairExhaustion`:
   a finite chart-pair cover can be enumerated by `ℕ` and used as the Rado chart-pair exhaustion.
3. `RadoChartPair.fromChartAt` and `mathlib_bordered_surface_finite_chart_pair_cover`:
   the preferred mathlib chart at each point gives a chart pair whose core is a neighborhood, so a
   compact bordered surface has a finite chart-pair cover.
4. `InitialPLNeighborhoodData.ofChartPolygonalDisk`:
   a polygonal disk covering the first chart core gives the stage-zero initialization data.
5. `rado_step_extension_from_chart_polygonal_disk`:
   the current scaffold can extend a Rado stage by taking the union of the old support and the
   next chart-disk support.
6. `finite_chart_polygonal_disk_data_of_local`:
   compactness extracts a finite chart-pair cover while carrying pointwise polygonal disk data
   along the selected finite indices.
7. `local_chart_polygonal_disk_data_of_pointwise`:
   pointwise chart-disk data packages into the local function-valued data used for compactness.
8. `mathlib_bordered_surface_point_chart_polygonal_disk_data`:
   a polygonal disk core inside the preferred mathlib chart packages as pointwise chart-disk data.
9. `finite_rado_geometry_of_chart_polygonal_disk_data` and
   `mathlib_bordered_surface_finite_rado_geometry`:
   finite chart polygonal disk data plus the one-step extension theorem packages as
   `FiniteRadoInductionGeometry`; the mathlib wrapper first extracts the finite cover with this
   disk data.
10. `FiniteRadoInductionGeometry.toRadoInductionData` and
   `rado_induction_data_of_finite_geometry`:
   once the local polygonal chart geometry is supplied over a finite cover, the recursive
   `RadoInductionData` is pure packaging.
11. `mathlib_bordered_surface_rado_induction_data`:
   finite Rado geometry packages as Rado induction data.
12. `mathlib_bordered_surface_moise_extraction_data`:
   finite cover extraction plus local Rado induction data packages as `MoiseExtractionData`.
13. `moise_two_manifold_of_extraction_data`:
   extracted finite cover plus local Rado data packages as `MoiseTwoManifold`.

Closed coordinate-local bridge:

```lean
theorem euclideanHalfSpace_boundary_polygonal_neighborhood_at
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) (hyU : y.1 ∈ (Subtype.val '' U)) :
    ∃ _N : PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩, True
```

The coordinate-local boundary half-disk case is now proved.  The interior case shrinks an arbitrary
interior half-plane neighborhood to a sufficiently small centered copy of the standard triangle.
The boundary case shrinks a relative neighborhood in the closed coordinate half-plane to a small
positive homothetic copy of the standard triangle anchored at
`EuclideanComplex.Examples.closedTriangleBoundaryAnchor`.  The combined
`euclideanHalfSpace_open_neighborhood_contains_polygonal_neighborhood` theorem is a proved case
split on whether `y.1 0 = 0`; the public interior/boundary wrappers also prove the point-membership
bookkeeping via `euclideanHalfSpace_point_mem_image_of_mem_nhds`.

The subtype-neighborhood bookkeeping below those constructors is now proved:

1. `euclideanHalfSpace_interior_halfspace_mem_nhds`:
   at a strict interior point, the ambient closed half-space is a neighborhood.
2. `euclideanHalfSpace_interior_map_nhds_eq`:
   at such a point, the half-space subtype neighborhood filter maps to the ordinary ambient
   Euclidean neighborhood filter.
3. `euclideanHalfSpace_image_mem_nhdsWithin_halfspace`:
   the image of any half-space neighborhood is a relative ambient neighborhood in the closed
   half-space.
4. `euclideanHalfSpace_interior_image_mem_nhds`:
   in the interior case, the image of a half-space neighborhood is an ordinary ambient
   neighborhood.

Consequently, `euclideanHalfSpace_interior_polygonal_neighborhood_at` now begins from an ambient
plane-neighborhood hypothesis, while
`euclideanHalfSpace_boundary_polygonal_neighborhood_at` begins from a relative-neighborhood
hypothesis in the closed half-plane.  Both constructors now build the required triangulated
`PlaneRegionPolygonalNeighborhood` package.

The standard-triangle part of the interior construction is also factored:

1. `EuclideanComplex.Examples.closedTriangleCentroid` is the point `(1 / 3, 1 / 3)`.
2. `EuclideanComplex.Examples.closedTriangleSupport_mem_nhds_centroid` proves that the closed
   standard triangle is a neighborhood of that centroid, using the strict inequalities
   `0 < p 0`, `0 < p 1`, and `p 0 + p 1 < 1`.
3. `EuclideanComplex.Examples.dist_centroid_le_three_of_mem_closedTriangleSupport` gives a coarse
   uniform distance bound for all points of the standard triangle.
4. `PlaneRegionTriangleCopy` records a plane homeomorphism taking that centroid to the target
   region point and sending the standard closed triangle into the region.
5. `PlaneRegionTriangleCopy.centeredHomothety` is the explicit translation and nonzero scaling
   about the centroid; `PlaneRegionTriangleCopy.ofCenteredHomothety` packages it as a
   `PlaneRegionTriangleCopy` once the scaled triangle is known to lie in the region.
6. `PlaneRegionTriangleCopy.dist_center_centeredHomothety` records the metric scaling formula.
7. `PlaneRegionTriangleCopy.exists_centeredHomothety_image_subset_of_mem_nhds` proves that every
   ambient plane neighborhood contains a sufficiently small centered triangle.
8. `PlaneRegionPolygonalNeighborhood.ofTriangleCopy` converts such a copy into the
   `PlaneRegionPolygonalNeighborhood` object, proving the embedding and neighborhood fields.

Thus `euclideanHalfSpace_interior_polygonal_neighborhood_at` is proved.  The boundary case should
is factored through the analogous anchored triangle API:

1. `EuclideanComplex.Examples.closedTriangleBoundaryAnchor` is the point `(0, 1 / 3)`.
2. `EuclideanComplex.Examples.closedTriangleSupport_mem_nhdsWithin_halfspace_boundaryAnchor`
   proves that the closed standard triangle is a relative neighborhood of that anchor in the
   closed coordinate-0 half-plane.
3. `EuclideanComplex.Examples.dist_boundaryAnchor_le_three_of_mem_closedTriangleSupport` gives
   the coarse metric bound needed for shrinking.
4. `PlaneRegionBoundaryTriangleCopy` records a plane homeomorphism taking the boundary anchor to
   the target point, sending the triangle into the region, and making the image a relative
   neighborhood there.
5. `PlaneRegionBoundaryTriangleCopy.boundaryAnchoredHomothety` is the explicit positive scaling
   about the boundary anchor followed by translation to the target boundary point.
6. `PlaneRegionBoundaryTriangleCopy.exists_boundaryAnchoredHomothety_image_subset_of_mem_nhdsWithin`
   proves that every relative half-plane neighborhood of a boundary-line point contains such a
   small anchored triangle.
7. `PlaneRegionPolygonalNeighborhood.ofBoundaryTriangleCopy` converts the anchored copy into the
   `PlaneRegionPolygonalNeighborhood` object.

`PlaneRegionPolygonalNeighborhood` packages this chart-free coordinate object, and
`PlaneRegionPolygonalNeighborhood.toModelChartPolygonalDisk` converts it to the chart-pair API.
The topological pullback from a model-neighborhood statement to a
manifold-neighborhood statement is proved by
`ModelChartPolygonalDisk.pulledCore_mem_nhds_of_range_mem_nhds`.  The transport of disk data
through the mathlib chart atlas is formalized by `ModelChartPolygonalDisk.toChartPolygonalDisk`,
and core refinement is formalized by `RadoChartPair.withCore_refines`.  The helper
`ModelChartPolygonalDisk.standardTriangleInModel` supplies a concrete model disk whenever the chart
model region contains the standard simplex.  The public theorems
`mathlib_chartAt_model_region_contains_polygonal_neighborhood`,
`mathlib_chartAt_contains_model_polygonal_disk_core` and
`mathlib_chartAt_contains_polygonal_disk_core` are proved wrappers around the coordinate-local
boundary.

Compact finite-subcover extraction is proved separately by `finite_chart_polygonal_disk_data_of_local`,
and pointwise data is packaged into local function-valued data by
`local_chart_polygonal_disk_data_of_pointwise`.
The formerly broad `mathlib_bordered_surface_rado_induction_data`,
`mathlib_bordered_surface_finite_rado_geometry`, finite chart-disk extraction, local chart-disk
data, point chart-disk data, and one-step extension theorems are proved wrappers around this
sharper coordinate-local polygonal-core boundary.

The Rado theorem boundary:

```lean
theorem rado_triangulation_moise_manifold
    (M : Type*) [TopologicalSpace M]
    (hM : MoiseTwoManifold M) :
    ∃ K : PLComplexIn M, K.support = Set.univ := by
  sorry
```

For compact surfaces:

```lean
theorem compact_moise_surface_finitely_triangulable
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    (hM : MoiseTwoManifold M) :
    ∃ T : FiniteSurfaceTriangulation M,
      Nonempty (T.realization ≃ₜ M) := by
  -- use Rado plus compact/local-finite implies finite
  sorry
```

Expected Rado induction shape:

1. Choose the chart exhaustion stored in `MoiseTwoManifold`.
2. Produce `RadoInductionData` over the exhaustion:
   - stage `0` comes from the initial PL neighborhood;
   - stage `n+1` uses PL approximation in a chart to make the overlap compatible with the
     previous complex;
   - in the current scaffold this local-data package is part of the strengthened
     `MoiseTwoManifold` interface for its stored exhaustion, so the hard proof obligation has
     moved to constructing that interface from the mathlib manifold atlas.
3. Build a `RadoInductiveSequence` by recursion from `RadoInductionData`:
   - the `n`th stage covers the `n`th chart core.
4. Prove the union of stage supports covers `Set.univ`; this is now a Lean proof from the
   exhaustion coverage field.
5. Build the union complex using `Small`/`Shrink`: each stage support is small, so the countable
   stage-support union is small and can be used as the point carrier of the scaffold embedded PL
   complex.
6. For compact `M`, reduce locally finite countable triangulation to finite triangulation.

### Moise work package M8: boundary adaptation

The Eval theorem needs manifolds with boundary.

Do not treat the closed case as sufficient unless a boundary reduction theorem is already in the API.

Preferred theorem boundary:

```lean
theorem rado_bordered_surface_triangulation
    (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M] :
    ∃ T : FiniteSurfaceTriangulation M,
      Nonempty (T.realization ≃ₜ M) := by
  sorry
```

Possible proof strategies:

1. Direct half-plane / half-disk adaptation of Moise's proof.
2. Double the surface along its boundary, triangulate the double, and restrict to one side.
3. Cap boundary components by disks, triangulate the closed surface, then remove the disks.

For Lean, the direct adaptation may be the least global but requires half-disk chart bookkeeping. Doubling or capping requires collars and proofs about boundary components. The blueprint should allow either proof strategy behind the same theorem name.

Also provide:

```lean
theorem eval_to_moise_bordered_surface
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    MoiseBorderedSurface S := by
  sorry
```

This is the bridge from mathlib's manifold language to Moise's surface language.

### Moise work package M9: final Moise bridge

Main route output:

```lean
theorem compact_eval_surface_finitely_triangulable
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ T : FiniteSurfaceTriangulation S,
      Nonempty (T.realization ≃ₜ S) := by
  -- eval_to_moise_bordered_surface
  -- rado_bordered_surface_triangulation
  sorry
```

Then:

```lean
theorem compact_surface_homeomorphic_to_cell_complex
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ K : SurfaceCellComplex, Nonempty (S ≃ₜ K.Realization) := by
  obtain ⟨T, hTS⟩ := compact_eval_surface_finitely_triangulable S
  refine ⟨T.toCellComplex, ?_⟩
  -- compose hTS.symm with T.toCellComplex_realization_homeomorphic
  sorry
```

## Gallier--Xu tail instructions

The Gallier--Xu team should work identically for both topological routes. It should not import Moise-specific files.

### G1: elementary moves

Define moves on `SurfaceCellComplex`:

```lean
inductive SurfaceCellComplex.ElementaryMove : SurfaceCellComplex → SurfaceCellComplex → Prop
| relabel : ...
| rotateFace : ...
| reverseFace : ...
| splitEdge : ...
| splitFace : ...
| mergeFaces : ...
| removeDanglingPair : ...
```

The exact constructors should follow Gallier--Xu's subdivision/equivalence operations and the normal-form proof. Keep the move relation broad enough to express the proof, even if some moves are later derived from primitive subdivisions.

### G2: moves preserve realization

For each move, prove a homeomorphism:

```lean
theorem SurfaceCellComplex.elementaryMove_homeomorph
    {K L : SurfaceCellComplex}
    (h : SurfaceCellComplex.ElementaryMove K L) :
    Nonempty (K.Realization ≃ₜ L.Realization) := by
  cases h
  -- use SurfaceCellComplex.realizationCongr where possible
  sorry
```

This is the main consumer of quotient-homeomorphism infrastructure.

### G3: equivalence preserves realization

Define reflexive-transitive-symmetric closure:

```lean
inductive SurfaceCellComplex.Equivalent : SurfaceCellComplex → SurfaceCellComplex → Prop
```

Then:

```lean
theorem SurfaceCellComplex.equivalent_homeomorph
    {K L : SurfaceCellComplex}
    (h : SurfaceCellComplex.Equivalent K L) :
    Nonempty (K.Realization ≃ₜ L.Realization) := by
  induction h
  -- compose homeomorphisms
  sorry
```

### G4: normal forms

Define canonical complexes:

```lean
def SphereCellComplex : SurfaceCellComplex := sorry

def OrientableCellComplex (p n : Nat) : SurfaceCellComplex := sorry

def NonOrientableCellComplex (p n : Nat) : SurfaceCellComplex := sorry
```

Prove normal-form existence:

```lean
theorem SurfaceCellComplex.gx_normal_form
    (K : SurfaceCellComplex) :
    SurfaceCellComplex.Equivalent K SphereCellComplex ∨
    (∃ p n, (1 ≤ p ∨ 1 ≤ n) ∧
      SurfaceCellComplex.Equivalent K (OrientableCellComplex p n)) ∨
    (∃ p n, 1 ≤ p ∧
      SurfaceCellComplex.Equivalent K (NonOrientableCellComplex p n)) := by
  sorry
```

This is a combinatorial theorem. It should not involve quotient topology except through the later homeomorphism theorem.

### G5: connect canonical complexes to Eval quotient representatives

The Eval problem uses quotient spaces such as `Quot (OrientableRel p n)` and `Quot (NonOrientableRel p n)`. Define the relation representatives once and prove:

```lean
theorem canonical_realization_eval_quotient_orientable
    (p n : Nat) :
    Nonempty ((OrientableCellComplex p n).Realization ≃ₜ Quot (OrientableRel p n)) := by
  sorry

theorem canonical_realization_eval_quotient_nonorientable
    (p n : Nat) :
    Nonempty ((NonOrientableCellComplex p n).Realization ≃ₜ Quot (NonOrientableRel p n)) := by
  sorry
```

This should again use quotient congruence. Do not prove separate ad hoc gluing theorems.

### G6: final cell-complex classification

```lean
theorem SurfaceCellComplex.hasEvalRepresentative
    (K : SurfaceCellComplex) :
    Nonempty (K.Realization ≃ₜ SphereRepresentative) ∨
    (∃ p n, (1 ≤ p ∨ 1 ≤ n) ∧
      Nonempty (K.Realization ≃ₜ Quot (OrientableRel p n))) ∨
    (∃ p n, 1 ≤ p ∧
      Nonempty (K.Realization ≃ₜ Quot (NonOrientableRel p n))) := by
  rcases SurfaceCellComplex.gx_normal_form K with h | h | h
  -- convert equivalence to homeomorphism, then compose with canonical quotient homeomorphism
  sorry
```

## Final assembly

Once the Moise bridge and Gallier--Xu tail exist, the final theorem should be short:

```lean
theorem eval_classification_of_surfaces
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    -- exact Lean Eval conclusion
    := by
  obtain ⟨K, hSK⟩ := compact_surface_homeomorphic_to_cell_complex S
  rcases SurfaceCellComplex.hasEvalRepresentative K with hSphere | hOrient | hNonorient
  -- compose hSK with the chosen representative homeomorphism
  sorry
```

The final theorem should not know whether `K` came from Moise or Mohar--Thomassen. That is the reason the topological bridge outputs `SurfaceCellComplex`.

## Parallelization plan

### Team Common-1: `SurfaceCellComplex`

Owns:

```text
SurfaceCellComplex
SurfaceCellComplex.PreRealization
SurfaceCellComplex.gluingRel
SurfaceCellComplex.Realization
```

Deliverable: definitions compile and can represent a one-triangle disk, a two-triangle sphere, an annulus, and a one-polygon torus presentation.

### Team Common-2: quotient homeomorphisms

Owns:

```text
SurfaceCellComplex.realizationCongr
SurfaceCellComplex.realizationCongrRight
canonical_realization_eval_quotient_* lemmas
```

Deliverable: relabeling, cyclic rotation, and orientation reversal of a polygon boundary produce homeomorphic realizations.

### Team Common-3: finite triangulation conversion

Owns:

```text
FiniteSurfaceTriangulation
toCellComplex
toCellComplex_realization_homeomorphic
```

Deliverable: any finite triangular surface presentation compiles into a `SurfaceCellComplex` with boundary words of length three.

### Team Moise-1: PL foundations

Owns:

```text
EuclideanComplex
Subdivision
PLMap
PLHomeomorph
CombinatorialTwoManifoldWithBoundary
CombinatorialTwoCell
```

Deliverable: basic closure under subdivision and composition.

### Team Moise-2: PL approximation

Owns:

```text
StronglyPositive
PhiApproximation
pl_approximation_one_skeleton
pl_approximation_plane_combinatorial_surface
```

Deliverable: theorem statements and proof boundaries compile; easy monotonicity/composition lemmas for approximations are proved.

### Team Moise-3: Rado triangulation and boundary

Owns:

```text
PLComplexIn
open_subset_complex
rado_triangulation_moise_manifold
rado_bordered_surface_triangulation
compact_eval_surface_finitely_triangulable
```

Deliverable: closed and bordered triangulation theorem boundaries with stable APIs.

### Team GX: normal form

Owns:

```text
ElementaryMove
Equivalent
gx_normal_form
hasEvalRepresentative
```

Deliverable: finite combinatorial normal form theorem independent of topology route.

## What Codex should not do

Do not attempt to prove the full Eval classification theorem directly.

Do not let PL definitions appear in the Gallier--Xu normal-form theorem.

Do not treat closed surfaces as sufficient for the final theorem unless a boundary theorem is already present.

Do not invent a second cell-complex realization inside the Moise route. Use the shared `SurfaceCellComplex.Realization`.

Do not prove each Gallier--Xu move by custom quotient-topology arguments. Use the shared quotient congruence theorem.

Do not make the final classification theorem depend on the details of Moise's PL approximation theorem. The final theorem should depend only on `compact_surface_homeomorphic_to_cell_complex` and `SurfaceCellComplex.hasEvalRepresentative`.

## Suggested first Codex tasks

1. Create compiling declarations for the shared API: `SurfaceCellComplex`, `Realization`, `FiniteSurfaceTriangulation`, `toCellComplex`, and the quotient congruence lemmas.
2. Create theorem stubs matching the Moise blueprint labels.
3. Prove tiny structural lemmas: homeomorphism composition wrappers, `Nonempty` composition helpers, equivalence relation reflexivity/transitivity wrappers.
4. Implement the simplest Gallier--Xu moves: relabeling, cyclic rotation, and face reversal, each using quotient congruence.
5. Only after the common infrastructure compiles, ask Codex to work on PL foundations.

A useful first prompt to Codex is:

```text
Read `codex_strategy_moise_pl.md` and `blueprint_moise_pl_route.tex`.
Create Lean declarations for the common API and Moise theorem boundaries.
Use `by sorry` for hard theorems, but make all definitions and theorem statements elaborate.
Do not change the theorem names in the blueprint unless the code cannot elaborate.
```
