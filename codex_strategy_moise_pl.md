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
structure EvalSurface (S : Type*) [TopologicalSpace S] where
  t2 : T2Space S
  connected : ConnectedSpace S
  compact : CompactSpace S
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  manifold : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S
```

The current Lean file also provides `evalSurface`, which packages active typeclass hypotheses, and
`eval_surface_hypotheses : Nonempty (EvalSurface S)` as a blueprint-facing marker.  Downstream
bridge theorems should use the Eval hypotheses verbatim or through this transparent wrapper.

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

Current Lean status: `SurfaceCellComplex` now carries its own realization type.  For converted
finite triangulations, this is the triangulation realization itself, so
`FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic` is proved by the identity
homeomorphism rather than by pretending every realization is `PUnit`.  `PreRealization` is
currently this same carrier and `gluingRel` is still the bottom relation.  Once `PreRealization`
becomes the disjoint union of polygons and `Realization` becomes the quotient, `realizationCongr`
should switch to mathlib's quotient homeomorphism API.  It remains the intended engine behind all
elementary cut/glue moves. The quotient team should own that final upgrade; the Gallier--Xu team
should not reprove quotient topology facts for every move.

A second useful form is relation-only congruence on the same pre-space:

```lean
theorem SurfaceCellComplex.realizationCongrRight
    {X : Type*} [TopologicalSpace X]
    {r s : Setoid X}
    (h : ∀ x y, r x y ↔ s x y) :
    Quotient r ≃ₜ Quotient s := by
  exact Homeomorph.Quotient.congrRight h
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
  Vertex Edge Triangle : Type u
  realization : Type v
  [realizationTop : TopologicalSpace realization]
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  edgeFintype : Fintype Edge
  triangleFintype : Fintype Triangle
  edgeVertices : Edge → Finset Vertex
  triangleVertices : Triangle → Finset Vertex
  edgeSource edgeTarget : Edge → Vertex
  triangleBoundary : Triangle → List (OrientedEdge Edge)
  edgeIsBoundary : Edge → Prop
  isSurfaceTriangulation :
    FiniteSurfaceTriangulation.Valid Vertex Edge Triangle edgeVertices triangleVertices
      edgeSource edgeTarget triangleBoundary
  homeomorphSurface : Nonempty (realization ≃ₜ S)
```

`FiniteSurfaceTriangulation.Valid` is the current finite combinatorial validity predicate:
edges have two vertices, triangles have three vertices, recorded endpoints lie on their edge,
edge endpoints are distinct, and every edge listed in a triangle boundary has its vertices
contained in the triangle vertex set.
The PL handoff proves this from one-simplex/two-simplex cardinal lemmas and the boundary-simplex
relation, so the triangulation object no longer uses `isSurfaceTriangulation := True`.

The conversion theorem should be the only bridge from triangulations to Gallier--Xu cell complexes:

```lean
def FiniteSurfaceTriangulation.toCellComplex
    (T : FiniteSurfaceTriangulation S) : SurfaceCellComplex :=
  sorry

theorem FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic
    (T : FiniteSurfaceTriangulation S) :
    Nonempty (T.realization ≃ₜ T.toCellComplex.Realization) := by
  exact ⟨Homeomorph.refl T.realization⟩
```

For a triangular complex, each triangle becomes a face whose boundary word has length three. Each
geometric edge gives a dart-pair. Vertices are inherited from the triangulation.  The converted
cell complex carries `T.realization`, so the realization comparison is closed now.  The future
quotient-realization upgrade should replace that identity comparison with the genuine quotient
comparison.

The remaining common-infrastructure work is no longer this handoff theorem; it is the quotient
realization upgrade and the Gallier--Xu move semantics.

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
NormalForm.IsEvalAdmissible
SurfaceCellComplex.RealizesNormalForm
SurfaceCellComplex.HasNormalForm
SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm
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

Current Lean status: `SurfaceCellComplex.HasNormalForm` is no longer a `True` placeholder.  It is
an existential witness carrying a representative cell complex, an equivalence from the input
complex to that representative, and a proof that the representative realizes the named Eval
quotient.  The easy bridge
`SurfaceCellComplex.hasEvalRepresentative_of_hasNormalForm` is proved.  The hard combinatorial
boundary is now `surface_cell_complex_reduces_to_normal_form`, which must produce an admissible
normal-form witness.  `SurfaceCellComplex.hasEvalRepresentative` is now a proved wrapper around
that boundary and the witness-to-Eval bridge.

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
  simplexNonempty : Nonempty Simplex
  support : Set Point
  -- incidence / face data

structure EuclideanComplex.Subdivision (K : EuclideanComplex) where
  K' : EuclideanComplex
  supportHomeomorph : K'.support ≃ₜ K.support
  vertexCarrier : K'.Vertex → K.Vertex
  carrier : K'.Simplex → K.Simplex
  simplex_refines :
    ∀ ⦃σ' : K'.Simplex⦄ ⦃v' : K'.Vertex⦄,
      v' ∈ K'.vertices σ' → vertexCarrier v' ∈ K.vertices (carrier σ')
  dimension_le : ∀ σ' : K'.Simplex, K'.simplexDim σ' ≤ K.simplexDim (carrier σ')
  face_refines : ∀ {τ' σ' : K'.Simplex}, K'.IsFace τ' σ' → K.IsFace (carrier τ') (carrier σ')
  covers_old_simplexes : ∀ σ : K.Simplex, ∃ σ' : K'.Simplex, carrier σ' = σ
```

Current status: `EuclideanComplex` now carries a nonempty simplex type, exposed by
`EuclideanComplex.defaultSimplex`, and `EuclideanComplex.realizesSimplexes` and
`EuclideanComplex.faceClosed` are no longer free propositions.  The realization field records that
every simplex has a nonempty finite vertex set, exposed by
`EuclideanComplex.realizesSimplex_nonempty`.  The face-closure field records a codimension-one face
witness: if a simplex has at least two vertices, then erasing any vertex from that simplex gives
the vertex set of another simplex.  The helper `EuclideanComplex.exists_erase_vertex_face` exposes
this data.
`EuclideanComplex.Subdivision.covers_old_simplexes` is also proof-bearing carrier-surjectivity:
every coarse simplex has a fine simplex carried to it, exposed by
`EuclideanComplex.Subdivision.exists_carrier_eq`.  `EuclideanComplex.Subdivision.simplex_refines`
is no longer a free proposition: the subdivision stores a vertex carrier and proves that every
vertex of a fine simplex maps to a vertex of its carrier coarse simplex, exposed by
`EuclideanComplex.Subdivision.carrierVertex` and
`EuclideanComplex.Subdivision.vertex_mem_carrier`.  `EuclideanComplex.Subdivision.CommonRefinement`
now carries lift maps from a common refinement to both subdivisions with compatible coarse
carriers, and `common_subdivision` constructs this carrier-level common refinement using
carrier-surjectivity.

If mathlib's abstract or geometric simplicial complexes can be used cleanly, wrap them. If not, define a project-specific `EuclideanComplex` with the fields needed for Moise. Avoid getting blocked by the perfect general abstraction.

Current scaffold note: the standard combinatorial triangle keeps finite vertex/simplex data, but
its support is now the geometric closed triangle in `EuclideanSpace ℝ (Fin 2)`. This avoids the
old one-point triangle carrier, which made genuine embedded chart disks impossible.
`RadoChartPair.standardTrianglePlaneCore` and
`ChartPolygonalDisk.standardTriangleInPlane` provide the concrete model chart disk in the
coordinate plane.

Existing theorem interface:

```lean
theorem common_subdivision
    (S T : K.Subdivision) :
    ∃ U : K.Subdivision, EuclideanComplex.Subdivision.CommonRefinement S T U
```

Use this to make PL maps stable under subdivision.

### Moise work package M2: PL maps and PL homeomorphisms

Implement:

```lean
structure PLSubdivisionSupportWitness (K L : EuclideanComplex)
    (toFun : K.support → L.support) where
  domainSubdivision : K.Subdivision
  targetSubdivision : L.Subdivision
  compatibleWithSupports :
    ∀ x : domainSubdivision.K'.support,
      targetSubdivision.supportHomeomorph
          (targetSubdivision.supportHomeomorph.symm
            (toFun (domainSubdivision.supportHomeomorph x))) =
        toFun (domainSubdivision.supportHomeomorph x)

structure PLMap (K L : EuclideanComplex) where
  toFun : K.support → L.support
  continuous_toFun : Continuous toFun
  subdivisionSupportWitness : Nonempty (PLSubdivisionSupportWitness K L toFun)

structure PLHomeomorph (K L : EuclideanComplex) where
  toHomeomorph : K.support ≃ₜ L.support
  pl_toFun : PLMap K L
  pl_invFun : PLMap L K

structure PLMap.SubcomplexMapData
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) where
  simplexMap : K.Simplex → L.Simplex
  simplexMap_mem :
    ∀ {σ : K.Simplex}, σ ∈ A.simplexes → simplexMap σ ∈ B.simplexes
  face_compatible :
    ∀ {τ σ : K.Simplex}, τ ∈ A.simplexes → σ ∈ A.simplexes → K.IsFace τ σ →
      L.IsFace (simplexMap τ) (simplexMap σ)
  linearWitness : f.HasLinearSubdivisionWitness

def PLMap.RespectsSubcomplex
    (f : PLMap K L) (A : K.Subcomplex) (B : L.Subcomplex) : Prop :=
  Nonempty (f.SubcomplexMapData A B)
```

Current status: `PLMap.exists_subdivision_linear` is now a Prop-style API backed by the concrete
`PLMap.subdivisionSupportWitness` field rather than a free `Prop` field.  The stored
`PLSubdivisionSupportWitness` records chosen domain and target subdivisions together with the
support-homeomorphism compatibility equation.  `PLMap.LinearOnSubdivision` now stores
`PLMap.FineSimplexTargetData` and `PLMap.AffineOnFineSimplexData` for each fine domain simplex:
target-simplex assignment data plus domain and target subdivision dimension bounds.  Actual affine
formulas remain the next refinement point once simplex carriers become geometric.  The helper
theorems are `PLMap.LinearOnSubdivision.targetSimplex_dimension_le`,
`PLMap.LinearOnSubdivision.affine_domain_dimension_le`, and
`PLMap.LinearOnSubdivision.support_compatible`.

Prove basic closure properties:

```lean
theorem PLHomeomorph.refl : PLHomeomorph K K := by sorry

theorem PLHomeomorph.symm (e : PLHomeomorph K L) : PLHomeomorph L K := by sorry

theorem PLHomeomorph.trans (e₁ : PLHomeomorph K L) (e₂ : PLHomeomorph L M) :
    PLHomeomorph K M := by sorry

theorem pl_iff_pl_after_subdivision : ... := by sorry
```

This is reusable infrastructure. It should not depend on surfaces.

Restriction status: `PLMap.RespectsSubcomplex` is now proof-bearing at the current
combinatorial level.  It is backed by `PLMap.SubcomplexMapData`, so callers must provide a finite
simplex assignment into the target subcomplex, prove face compatibility, and carry a PL linearity
witness.  `PLHomeomorph.RestrictsTo` requires this condition in both directions and now has identity,
symmetry, and composition APIs.  `pl_schoenflies_combinatorial_two_cell` composes the stored
boundary restrictions through the standard triangle boundary instead of using a nonempty-target
restriction placeholder.

### Moise work package M3: combinatorial surfaces and cells

Implement combinatorial local conditions:

```lean
structure CombinatorialTwoManifoldWithBoundary where
  K : EuclideanComplex
  isTwoDimensional : Prop
  vertex_link_circle_or_interval : Prop
  shared_two_simplex_faces_in_oneSkeleton : Prop

structure CombinatorialTwoCell where
  K : EuclideanComplex
  boundary : EuclideanComplex
  boundarySubcomplex : K.Subcomplex
  boundaryInclusion : PLMap boundary K
  boundary_embeds_in_cell : CellBoundaryEmbeddingData boundarySubcomplex boundaryInclusion
  frontier_covered_by_boundary : FrontierCoveredByBoundary K boundarySubcomplex
  closedTriangleBoundary : EuclideanComplex.Examples.triangle.Subcomplex
  closedTriangleModel_is_triangle : ClosedTriangleBoundaryModel closedTriangleBoundary
  cellHomeomorphToTriangle : PLHomeomorph K EuclideanComplex.Examples.triangle
  cellHomeomorph_respects_boundary :
    cellHomeomorphToTriangle.RestrictsTo boundarySubcomplex closedTriangleBoundary
  pl_homeomorphic_to_closed_triangle :
    Nonempty (PLHomeomorph K EuclideanComplex.Examples.triangle)
```

Current status: vertex-link connectedness is no longer the placeholder `True`.  The complex API
defines `EuclideanComplex.LinkAdjacent`, `LinkWalk`, `LinkReachable`, and `LinkConnected`, with
reachability bounded by the finite vertex count so link-connectedness remains decidable for small
examples.  The surface structure also records the finite intersection axiom
`shared_two_simplex_faces_in_oneSkeleton`: any common face of two distinct two-simplexes lies in
the one-skeleton.  The helper theorem
`CombinatorialTwoManifoldWithBoundary.sharedFace_mem_oneSkeleton` is the intended way for gluing
arguments to use this condition.

Current status: the two-cell and polygonal-disk fields that used to be `True` have been split into
named proof-bearing records:

- `CellBoundaryEmbeddingData` records PL boundary inclusion and subcomplex respect.
- `FrontierCoveredByBoundary` records that codimension-one faces of two-simplexes land in the
  distinguished boundary subcomplex.
- `ClosedTriangleBoundaryModel` records that the standard triangle boundary contains the top
  simplex boundary faces and excludes the interior face.
- `PolygonalBoundaryData` and `ClosedInteriorTriangulationData` package the polygonal-disk
  boundary and closed-interior triangulation obligations.

The standard triangle example now uses `EuclideanComplex.Examples.triangleBoundarySubcomplex`
instead of the full triangle as its boundary subcomplex.

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
    (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ)
    (hφ : StronglyPositive φ) :
    Nonempty (OneSkeletonApproximation K Ω.carrier φ h) := by
  sorry
```

This theorem requires polygonal approximation of finitely many edge images with separation control. It may be split further into finite families of arcs, edge separation, and vertex preservation.

Current one-skeleton predicate status: the local predicates are no longer functions into `True`.
`PreservesVertices` is backed by finite `VertexPreservationData`, recording a finite vertex set
that contains every vertex represented by a zero-simplex.  `IsPLOnSimplexes` is backed by finite
`PLOnSimplexesData`, recording a domain subdivision whose fine simplexes cover the requested
coarse simplexes.  `SeparatedOnEdges` is backed by finite `EdgeSeparationData`, recording all
nonincident edge pairs that require separation.  The half-plane boundary predicates recover
`IsBoundaryVertex`/`IsBoundaryEdge` from membership in the boundary vertex/edge finsets.  These are
still combinatorial stand-ins until vertex and edge realizations are geometric, but they remove the
old excluded-middle and reflexivity witnesses.

### Moise work package M5: PL approximation theorem

Main theorem boundary:

```lean
theorem pl_approximation_plane_combinatorial_surface
    (K : CombinatorialTwoManifoldWithBoundary)
    (Ω : PlaneRegion)
    (h : K.K.support ≃ₜ Ω.carrier)
    (φ : K.K.support → ℝ)
    (hφ : StronglyPositive φ) :
    Nonempty (GlobalPLSurfaceApproximation K Ω.carrier φ h) := by
  sorry
```

Expected proof structure:

1. Subdivide `K` finely enough that each simplex is small relative to the local tolerance.
2. Approximate the one-skeleton by a PL embedding.
3. Use PL Schoenflies to extend over each 2-cell.
4. Prove the extensions agree on shared edges.
5. Prove global injectivity and surjectivity using the separation estimates.

Do not ask Codex to invent this proof at once. Ask it to formalize the statement, create auxiliary predicates, and prove small composition/monotonicity lemmas for approximation.

Current gluing API status: `CellwiseExtension` and `BoundaryCellwiseExtension` carry
proof-bearing output conditions.  `IsPLOnTwoSkeleton` records PL behavior on all two-skeleton
simplexes, `ExtendsOneSkeletonApproximation` records a `PhiApproximation` to the one-skeleton map,
`ExtensionsAgreeOnSharedBoundary` is backed by `SharedBoundaryCompatibilityData`, which records PL
behavior on the one-skeleton and proves that common faces of distinct two-simplexes lie in the
one-skeleton.  `EmbeddingLikeApproximation` records that the output map either agrees with the
reference map or is injective, and `RelativeBoundaryCells` records the boundary-respecting
conditions for the half-plane route.  These replace the old `True` fields on global PL
approximation outputs while leaving the hard planar topology as named theorem boundaries.

### Moise work package M6: PL complexes inside arbitrary spaces

Moise builds PL complexes inside the surface. Define:

```lean
structure PLComplexIn (X : Type*) [TopologicalSpace X] where
  Complex : EuclideanComplex
  embed : Complex.support ↪ X
  embedding : Embedding embed
  locallyFinite : Finite Complex.Simplex
  compatibleCharts : Function.Injective embed ∧ Continuous embed

structure PLComplexIn.BoundarySubcomplexData (K : PLComplexIn X) where
  boundary : K.Complex.Subcomplex
  boundarySupport : Set X
  coversBoundary : boundarySupport ⊆ K.support
  compatibleWithAmbient : ∀ x ∈ boundarySupport, x ∈ K.support
  boundaryCarrier_subset :
    ∀ ⦃σ : K.Complex.Simplex⦄, σ ∈ boundary.simplexes →
      K.simplexCarrier σ ⊆ boundarySupport
  boundarySupport_covered :
    ∀ x ∈ boundarySupport, ∃ σ ∈ boundary.simplexes, x ∈ K.simplexCarrier σ
  locallyFiniteBoundary : Finite {σ : K.Complex.Simplex // σ ∈ boundary.simplexes}
```

The two carrier-direction fields are packaged by
`PLComplexInSpace.BoundarySubcomplexData.mem_boundarySupport_iff` and
`PLComplexInSpace.BoundarySubcomplexData.boundarySupport_eq_iUnion_simplexCarrier`: the stored
boundary support is exactly the union of carriers of the stored boundary simplexes.

Current overlap and Rado-state status: `PLComplexInSpace.CompatibleOnOverlap` is no longer an
arbitrary proposition or a tautological containment witness.  It is `Nonempty
PLComplexInSpace.OverlapCompatibilityData`: a common carrier for the ambient overlap with maps into
both complex supports, equality after embedding in the ambient space, injectivity on both sides,
and coverage of every ambient overlap point.  Rado induction states carry this overlap witness for
the current complex and `BoundarySubcomplexFaceClosed` for the stored boundary subcomplex.
`boundaryCompatibleOnOverlaps` now uses the proof-bearing `BoundaryCompatibleOnOverlap` predicate:
the complex must be compatible with the comparison complex on the ambient overlap, and the stored
boundary subcomplex must be face-closed.
`boundaryRespectsCharts` is now finite `ChartModelCompatibilityData`: a finite family of chart
polygonal disks whose supports lie in the current complex and whose coordinate images respect the
stored model regions.  Initial states use the singleton package, chart-extension steps append the
new disk, and empty-chart steps preserve the previous package.
The old `coversPreviousCores : Prop` and `coversPreviousBoundaryCores : Prop` state fields have
been replaced by finite `RadoStageCoverageData`: numbered ordinary and boundary chart-core sets
with support-containment proofs.  The separate `CoversCoresUpTo` and
`CoversBoundaryCoresUpTo` predicates remain the exhaustion-specific cumulative statements proved
by the induction lemmas.

Needed operations:

```lean
def PLComplexIn.support (K : PLComplexIn X) : Set X := Set.range K.embed

def PLComplexIn.interiorSubcomplex ... := sorry

theorem open_subset_complex
    (K : EuclideanComplex) (U : Set K.support) (hU : IsOpen U) :
    Nonempty (PLComplexInSpace.OpenSubsetComplex K U) := by
  sorry

theorem compact_locally_finite_complex_finite
    (K : PLComplexIn X) [CompactSpace X]
    (hSupport : K.support = Set.univ)
    (hLoc : K.locallyFinite) :
    Nonempty K.FiniteSupportData := by
  sorry
```

`open_subset_complex` is one of the Moise Chapter 8 support theorems. It may be left as a theorem boundary at first.
`PLComplexInSpace.OpenSubsetComplex` now carries proof-bearing ambient compatibility: the
inclusion of the open-subset complex support into the original support is injective and
continuous, derived from the stored embedding.  `PLComplexInSpace` now stores simplex-carrier
data directly: every abstract simplex has an ambient carrier subset of the embedded support, and
the embedded support is covered by these carriers.  `PLComplexInSpace.SimplexRelevant` is no
longer `True` or full finite-set membership; it means the stored ambient carrier is nonempty.
`FiniteSupportData.covers` proves that the selected relevant simplex carriers cover the embedded
support, and `FiniteSupportData.support_eq_iUnion_simplexCarrier` packages this as an exact
support-as-union statement over the selected simplexes.  The ambient PL complex itself also has
`PLComplexInSpace.mem_support_iff` and `PLComplexInSpace.support_eq_iUnion_simplexCarrier`.
`locallyFiniteComplex_finite_of_compact_support` returns `Nonempty K.FiniteSupportData` rather
than data plus a trailing truth witness.

### Moise work package M7: Rado induction for closed surfaces

Define a Moise-style 2-manifold interface if needed:

```lean
structure MoiseTwoManifold (M : Type*) [TopologicalSpace M] where
  t2 : T2Space M
  chartPairExhaustion : ChartPairExhaustion M
  localDiskOrHalfDiskModels : chartPairExhaustion.HasDiskOrHalfDiskModelCover
  chartModelsMatchKind : chartPairExhaustion.ModelsMatchKind
  radoInductionData : RadoInductionData chartPairExhaustion
```

For the Eval problem, this is not the final interface. It is an intermediate bridge from
mathlib's charted-space manifold to Moise's hypotheses. The hard extraction from mathlib's
`ChartedSpace` atlas to a countable chart-pair exhaustion and the associated local Rado
induction data is isolated in `mathlib_bordered_surface_moise_extraction_data`.

Current extraction layer:

```lean
def RadoChartKind.ModelMatchesRegion (kind : RadoChartKind) (Ω : Set Plane) : Prop :=
  match kind with
  | disk => IsOpen Ω
  | halfDisk => ∃ U : Set (EuclideanHalfSpace 2), Ω = Subtype.val '' U

structure RadoChartPair (M : Type*) [TopologicalSpace M] where
  kind : RadoChartKind
  domain core : Set M
  domain_open : IsOpen domain
  core_subset_domain : core ⊆ domain
  modelRegion : Set Plane
  chartHomeomorph : domain ≃ₜ modelRegion
  model_matches_kind : kind.ModelMatchesRegion modelRegion
  chart_to_model : ∀ x : domain, (chartHomeomorph x : Plane) ∈ modelRegion
  boundaryCore : Set M
  boundaryCore_subset_core : boundaryCore ⊆ core
  boundaryCore_empty_of_disk : kind = RadoChartKind.disk → boundaryCore = ∅
  boundaryCore_in_boundary_chart :
    kind = RadoChartKind.halfDisk →
      ∀ x : domain, (x : M) ∈ boundaryCore → ((chartHomeomorph x : Plane) 0 = 0)

structure FiniteChartPairCover (M : Type*) [TopologicalSpace M] where
  Index : Type*
  indexFintype : Fintype Index
  pair : Index → RadoChartPair M
  boundaryCarrier : Set M
  boundarySet : Set M
  boundarySet_subset_boundaryCarrier : boundarySet ⊆ boundaryCarrier
  covers : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCovers :
    ∀ x : M, x ∈ boundaryCarrier → ∃ i : Index, x ∈ (pair i).boundaryCore
  interiorChartsCoverInterior : ∀ x : M, ∃ i : Index, x ∈ (pair i).core
  boundaryCore_subset_boundaryCarrier :
    ∀ i : Index, (pair i).boundaryCore ⊆ boundaryCarrier
  locallyFinite : ∀ x : M, ∃ t : Finset Index, ∀ i, x ∈ (pair i).core → i ∈ t
  nestedControl : ∀ i : Index, (pair i).core ⊆ (pair i).domain
  boundaryLocallyFinite :
    ∀ x : M, ∃ t : Finset Index, ∀ i, x ∈ (pair i).boundaryCore → i ∈ t
  boundaryNestedControl : ∀ i : Index, (pair i).boundaryCore ⊆ (pair i).core

structure MoiseExtractionData (M : Type*) [TopologicalSpace M] where
  finiteCover : FiniteChartPairCover M
  localDiskOrHalfDiskModels : finiteCover.HasDiskOrHalfDiskModelCover
  chartModelsMatchKind : finiteCover.ModelsMatchKind
  radoInductionData : RadoInductionData finiteCover.toChartPairExhaustion

structure FiniteChartPolygonalDiskData
    {M : Type*} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  disk : C.Index → ChartPolygonalDisk M
  chart_eq : ∀ i : C.Index, (disk i).chart = C.pair i
  compatibleChartShrinks : ∀ i : C.Index, (disk i).chart.Refines (C.pair i)
  boundaryCompatibleChartShrinks :
    ∀ i : C.Index, (disk i).chart.boundaryCore ⊆ (C.pair i).boundaryCore
  boundaryFaithful : ∀ i : C.Index, (disk i).BoundaryFaithful

structure LocalChartPolygonalDiskData (M : Type*) [TopologicalSpace M] where
  boundarySet : Set M
  pairAt : M → RadoChartPair M
  diskAt : M → ChartPolygonalDisk M
  chart_eq : ∀ x : M, (diskAt x).chart = pairAt x
  core_mem_nhds : ∀ x : M, (pairAt x).core ∈ 𝓝 x
  compatibleChartShrinks : ∀ x : M, (diskAt x).chart.Refines (pairAt x)
  boundaryCompatibleChartShrinks :
    ∀ x : M, (diskAt x).chart.boundaryCore ⊆ (pairAt x).boundaryCore
  boundaryFaithful : ∀ x : M, (diskAt x).BoundaryFaithful
  boundarySet_subset_boundaryCore :
    ∀ x : M, boundarySet ∩ (pairAt x).core ⊆ (pairAt x).boundaryCore

structure PointChartPolygonalDiskData
    (M : Type*) [TopologicalSpace M] (boundarySet : Set M) (x : M) where
  disk : ChartPolygonalDisk M
  core_mem_nhds : disk.chart.core ∈ 𝓝 x
  boundaryFaithful : disk.BoundaryFaithful
  boundarySet_subset_boundaryCore :
    boundarySet ∩ disk.chart.core ⊆ disk.chart.boundaryCore
  boundaryFaithful : disk.BoundaryFaithful

structure FiniteRadoInductionGeometry
    {M : Type*} [TopologicalSpace M] (C : FiniteChartPairCover M) where
  initial : InitialPLNeighborhoodData C.toChartPairExhaustion
  step :
    ∀ (_n : ℕ) (S : RadoInductionState M),
      RadoStepExtensionData C.toChartPairExhaustion S
  compatibleStages : RadoInductionStepCompatible initial step
  locallyFiniteUnion :
    ∀ n, Finite ((radoInductionStage initial step n).complex.Complex.Simplex)
  boundaryCompatibleUnion : RadoInductionBoundaryStepCompatible initial step
```

The compatibility fields are not free placeholders: `RadoInductionStepCompatible` says each
successor complex is compatible on overlaps with the previous recursive stage, and
`RadoInductionBoundaryStepCompatible` says the same step supplies boundary-overlap compatibility
for its boundary subcomplex.  `FiniteChartPolygonalDiskData.toFiniteRadoInductionGeometry` proves
these aggregate fields from the per-step `RadoStepExtensionData` fields.

Proved finite/combinatorial bridge:

1. `FiniteChartPairCover.exists_of_compact_local`:
   local chart-pair cores that are neighborhoods of their points admit a finite subcover by
   compactness.
2. `FiniteChartPairCover.toChartPairExhaustion`:
   a finite chart-pair cover can be enumerated by `ℕ` and used as the Rado chart-pair exhaustion.
   The helper API `zeroIndex`, `toChartPairExhaustion_pair_of_lt`,
   `toChartPairExhaustion_pair_of_not_lt`, and `toChartPairExhaustion_pair_zero` names the first
   finite chart and the in-range/out-of-range enumeration cases.  The finite-cover and exhaustion
   local-finiteness fields are proof-bearing: finite covers use explicit finite index sets, and
   the countable enumeration uses `Finset.range (Fintype.card C.Index)` because all out-of-range
   chart pairs are empty.  The boundary side now carries a named `boundaryCarrier`; the fields
   `boundaryCovers` and `boundaryCore_subset_boundaryCarrier` prove that this carrier is exactly
   the union of boundary cores.  A separate `boundarySet` records the intended ambient boundary,
   and `boundarySet_subset_boundaryCarrier` proves it lands in the selected carrier.  The named
   APIs are
   `FiniteChartPairCover.boundaryCarrier_eq_iUnion_boundaryCore` and
   `FiniteChartPairCover.boundarySet_subset_iUnion_boundaryCore`, together with
   `ChartPairExhaustion.boundaryCarrier_eq_boundaryCoreUnion` and
   `ChartPairExhaustion.boundarySet_subset_boundaryCoreUnion`.
3. `RadoChartPair.fromChartAt` and `mathlib_bordered_surface_finite_chart_pair_cover`:
   the preferred mathlib chart at each point gives a chart pair whose core is a neighborhood, so a
   compact bordered surface has a finite chart-pair cover.  Its boundary core is now the part of
   the chart source mapped to the coordinate boundary line, exposed by
   `fromChartAt_boundaryCore_in_model_boundary` and
   `fromChartAt_mem_boundaryCore_of_chart_coord_zero`, instead of the old empty-core placeholder.
   `fromChartAt_mem_boundaryCore_of_manifold_boundary` connects mathlib's
   `ModelWithCorners.boundary` to this preferred-chart boundary core using the frontier of
   `EuclideanHalfSpace`.  The finite-cover route needs the corresponding arbitrary-chart C0
   boundary-invariance statement; this is isolated at the frontier-of-target level as the hard
   theorem boundary `chartAt_extend_mem_frontier_target_of_manifold_boundary`.  The coordinate
   consequence `fromChartAt_chart_coord_zero_of_manifold_boundary` is now proved from that
   lower-level boundary.  The positive-regularity companion is now proved in the general
   nonzero-regularity form
   `fromChartAt_chart_coord_zero_of_manifold_boundary_of_isManifold_ne_zero`, with the C1 wrapper
   `fromChartAt_chart_coord_zero_of_manifold_boundary_of_contMDiff`, using mathlib's
   `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`.  The positive-regularity extraction path
   is threaded through
   `mathlib_chartAt_contains_polygonal_disk_core_of_contMDiff`,
   `mathlib_bordered_surface_localChartPolygonalDiskData_of_contMDiff`,
   `mathlib_bordered_surface_finitePLTriangulationData_of_contMDiff`,
   `rado_bordered_surface_triangulation_of_contMDiff`,
   `mathlib_bordered_surface_finitely_triangulable_of_contMDiff`, and
   `compact_eval_surface_finitely_triangulable_of_contMDiff`.  Thus the remaining gap for the
   original Eval theorem is specifically the topological C0 invariance needed for Moise.
4. `InitialPLNeighborhoodData.ofChartPolygonalDisk`:
   a polygonal disk covering the first chart core gives the stage-zero initialization data.
   `ChartPolygonalDisk` now carries explicit simplex-carrier data for its embedded PL complex,
   so `ChartPolygonalDisk.toPLComplexInSpace` no longer hardcodes every simplex carrier as the
   whole disk image.  `PlaneRegionPolygonalNeighborhood` and `ModelChartPolygonalDisk` now carry
   the same explicit carrier data, and the named conversion lemmas
   `toModelChartPolygonalDisk_simplexCarrier` and `toChartPolygonalDisk_simplexCarrier` expose
   that the data is preserved through the coordinate-to-manifold pipeline.  The standard-triangle
   constructors use `EuclideanComplex.Examples.closedTriangleSimplexCarrier`, with singleton
   vertex carriers, line-segment edge carriers, and the closed face carrier.  Generic constructors
   may still use coarse carriers where detailed simplex geometry is not supplied, but the local
   chart pipeline now accepts and transports faithful carrier data.  Plane-region neighborhoods
   also carry a boundary carrier; boundary-anchored triangle copies prove that the standard
   boundary edge maps to the coordinate boundary line and that every support point mapped to the
   coordinate boundary line comes from that edge.  `PlaneRegionPolygonalNeighborhood` now carries
   `boundaryCarrier_contains_coordBoundary`, `ModelChartPolygonalDisk` carries
   `modelBoundaryCore_contains_boundary_chart`, and
   `ModelChartPolygonalDisk.toChartPolygonalDisk_boundaryFaithful` proves the pulled-back
   `ChartPolygonalDisk.BoundaryFaithful` predicate.  Thus `ModelChartPolygonalDisk.toChartPair`
   pulls back a boundary core that is not merely included in the model boundary line but also
   contains the local polygonal support lying on that line.
   `ChartPolygonalDisk.boundaryCore_subset_boundarySupport` now exposes the stronger fact that
   chart boundary cores are covered by the disk boundary subcomplex, and the initial Rado state
   records this with `toState_coversBoundaryCoresInBoundaryUpTo`.
5. `RadoStepExtensionData.chartUnionPLComplexData`,
   `RadoStepExtensionData.fromChartPolygonalDisk`, `RadoStepExtensionData.emptyChart`, and
   `rado_step_extension_from_chart_polygonal_disk`:
   the current carrier-level construction extends a Rado stage by taking the union of the old
   support and the next chart-disk support.  The chart-union complex now keeps simplexes as the
   disjoint sum of old-stage simplexes and chart-disk simplexes, with simplex carriers inherited
   from the corresponding side; `chartUnionOldVertexEmbedding`,
   `chartUnionNewVertexEmbedding`, `chartUnionPLComplex_simplex`,
   `chartUnionPLComplex_old_simplexCarrier`, `chartUnionPLComplex_new_simplexCarrier`,
   `chartUnionPLComplex_old_vertices`, and `chartUnionPLComplex_new_vertices` expose this API.
   The successor boundary subcomplex is now `chartUnionBoundarySubcomplex`, the finite disjoint
   sum of the previous boundary subcomplex and the chart-disk boundary subcomplex; the old/right
   membership lemmas expose the two summands.  `RadoStepExtensionData.preservesOldBoundarySupport`
   and `oldBoundarySupport_subset_toState_boundarySupport` record that a successor step really
   carries the previous boundary support into the next boundary support.
   `boundaryCore_subset_toState_boundarySupport` and
   `toState_coversBoundaryCoresInBoundaryUpTo` record the parallel fact for the next boundary
   chart core itself.  The finite chart step
   selector now calls the named constructors directly rather than choosing witnesses from
   existential theorem wrappers, and
   `RadoStepExtensionData.fromChartPolygonalDisk_nextComplex_support` exposes the support
   computation for later induction proofs.
6. `LocalChartPolygonalDiskData.toFiniteChartPolygonalDiskData`,
   `LocalChartPolygonalDiskData.finiteChartPairCover`,
   `LocalChartPolygonalDiskData.finiteChartPolygonalDiskData`, and
   `finite_chart_polygonal_disk_data_of_local`:
   compactness extracts a finite chart-pair cover while carrying pointwise polygonal disk data
   along the selected finite indices.  The chart-shrink compatibility fields are proof-bearing:
   every chosen disk chart refines the selected chart pair, and boundary cores are compatible by
   inclusion.  The sigma-valued construction is the reusable data extraction; the theorem with
   the original public name now returns a nonempty dependent sigma package.  For compact mathlib
   bordered surfaces, the named
   `mathlib_bordered_surface_finiteChartPairCover` is this stronger polygonal-disk extraction
   cover, not merely the earlier preferred-chart finite subcover: its `boundarySet` is exactly
   `(modelWithCornersEuclideanHalfSpace 2).boundary M`, and
   `mathlib_bordered_surface_boundary_subset_finiteChartPairCover_boundaryCarrier` exposes that
   the actual manifold boundary lies in its selected boundary carrier.
7. `local_chart_polygonal_disk_data_of_pointwise`:
   pointwise chart-disk data packages into the local function-valued data used for compactness.
8. `mathlib_bordered_surface_point_chart_polygonal_disk_data`:
   a polygonal disk core inside the preferred mathlib chart packages as pointwise chart-disk data.
9. `FiniteChartPolygonalDiskData.initialData`, `FiniteChartPolygonalDiskData.stepData`,
   `FiniteChartPolygonalDiskData.toFiniteRadoInductionGeometry`,
   `finite_rado_geometry_of_chart_polygonal_disk_data`, and
   `mathlib_bordered_surface_finite_rado_geometry`:
   finite chart polygonal disk data plus the named one-step constructors packages as
   `FiniteRadoInductionGeometry`; the theorem wrappers expose the named constructor rather than
   rebuilding this package inline.  The selector lemmas
   `FiniteChartPolygonalDiskData.stepData_nextChartDisk_of_lt`,
   `FiniteChartPolygonalDiskData.stepData_nextChartDisk_of_not_lt`,
   `FiniteChartPolygonalDiskData.stepData_nextComplex_support_of_lt`, and
   `FiniteChartPolygonalDiskData.stepData_nextComplex_of_not_lt` make the finite in-range and
   out-of-range branches explicit; the in-range branch uses the disjoint-sum chart-union complex.
10. `FiniteRadoInductionGeometry.toRadoInductionData` and
   `rado_induction_data_of_finite_geometry`:
   once the local polygonal chart geometry is supplied over a finite cover, the recursive
   `RadoInductionData` is pure packaging.  The finite-cover endpoint API
   `RadoInductionData.finiteCover_core_subset_stage_card`,
   `RadoInductionData.finiteCover_boundaryCore_subset_stage_card`, and
   `RadoInductionData.finiteCover_stage_card_support_eq_univ` proves that stage
   `Fintype.card C.Index` already covers the whole space for an exhaustion coming from a finite
   chart-pair cover.  The boundary-support thread is also explicit:
   `boundarySupport_subset_succ`, `covers_boundaryCore_in_boundary_of_le`, and
   `finiteCover_boundaryCore_subset_stage_card_boundarySupport` show that selected boundary
   cores land in the terminal finite stage's boundary support.  The carrier-level lemmas
   `finiteCover_boundaryCarrier_subset_stage_card`,
   `finiteCover_boundaryCarrier_subset_stage_card_boundarySupport`, and
   `finiteStagePLTriangulationData_boundaryCarrier_subset` push the finite cover's named
   `boundaryCarrier` into the terminal stage and its packaged boundary data.  The finite and
   stagewise boundary packages also expose exact support-as-union APIs via
   `PLComplexInSpace.BoundarySubcomplexData.boundarySupport_eq_iUnion_simplexCarrier`,
   `StagewisePLComplexInSpace.support_eq_iUnion_simplexCarrier`, and
   `StagewisePLComplexInSpace.boundarySupport_eq_iUnion_simplexCarrier`.
   `RadoInductionData.finiteStagePLTriangulationData` is now the reusable compact-case exit from
   the Rado layer: it packages that terminal state as finite PL triangulation data, including the
   terminal state's stored boundary subcomplex.
11. `mathlib_bordered_surface_rado_induction_data`:
   finite Rado geometry packages as Rado induction data.
12. `LocalChartPolygonalDiskData.toMoiseExtractionData`,
   `mathlib_bordered_surface_moiseExtractionData`, and
   `mathlib_bordered_surface_moise_extraction_data`:
   finite cover extraction plus local Rado induction data packages as named `MoiseExtractionData`;
   the theorem with the original public name is now the nonempty-data wrapper.  At this level,
   `MoiseExtractionData.finiteStage`, `MoiseExtractionData.finiteStagePLComplex`, and
   `MoiseExtractionData.finiteStagePLTriangulationData` use the finite terminal Rado stage
   directly, avoiding the countable support-union complex after compactness has produced a finite
   cover.  The extraction wrapper delegates to
   `RadoInductionData.finiteStagePLTriangulationData`, so the boundary package comes from the
   terminal Rado state's stored boundary subcomplex rather than `fullBoundarySubcomplexData`.
   `MoiseExtractionData.finiteStagePLTriangulationData_support` records the support equality, and
   `mathlib_bordered_surface_moiseExtractionData_finiteCover` identifies the extraction package's
   finite cover with the named polygonal-disk finite cover.  The boundary-set simp theorem
   `mathlib_bordered_surface_moiseExtractionData_finiteCover_boundarySet` records that this cover
   carries the actual mathlib manifold boundary.
   The public extraction-level wrappers `moise_extraction_finitely_triangulable` and
   `moise_extraction_finite_pl_triangulation_data` expose the finite terminal-stage output without
   passing through `MoiseTwoManifold.supportUnionFinitePLTriangulationData`.
13. `mathlib_bordered_surface_moiseTwoManifold`,
   `mathlib_bordered_surface_to_moise_two_manifold`, and
   `moise_two_manifold_of_extraction_data`:
   extracted finite cover plus local Rado data packages as the named `MoiseTwoManifold` object used
   by the Rado theorem wrappers.

The PL-to-triangulation bridge uses finite support data as the combinatorial handoff:
`PLComplexInSpace.FiniteSupportData.OneSimplex` supplies triangulation edges,
`TwoSimplex` supplies triangles, and `triangleBoundaryWord` records the supported
codimension-one faces of a two-simplex as the current scaffold boundary word.
`EuclideanComplex.vertices_card_eq_two_of_mem_oneSimplexes` and
`EuclideanComplex.vertices_card_eq_three_of_mem_twoSimplexes` prove the edge and triangle vertex
cardinality fields in `FiniteSurfaceTriangulation.Valid`, `edgeTargetVertex_ne_source` proves the
distinct-endpoint field, and `edgeVertices_subset_triangleVertices_of_mem_boundaryWord` proves that
every listed boundary edge is a face of its triangle.
Because the current `EuclideanComplex` API has finite simplex types,
`PLComplexInSpace.fullFiniteSupportData` is the named finite-support package taking all simplexes;
its coverage proof now uses the `PLComplexInSpace.simplexCarrier` cover stored on the embedded
complex, not the tautology `K.support ⊆ K.support`.
`locallyFiniteComplex_finite_of_compact_support` is the Moise-facing wrapper around that package
rather than the source of the finite data.  `PLComplexInSpace.locallyFinite` and
`PLComplexInSpace.compatibleCharts` are no longer free propositions: local finiteness is a finite
simplex-type proof, and compatibility is supplied by injectivity and continuity of the embedding.
`PLComplexInSpace.toFiniteSurfaceTriangulation` is the named construction behind the public
existential theorem.  `FinitePLTriangulationData` is the named Rado-output package for a covering
embedded PL complex, finite support data, and boundary-subcomplex data; the bordered Rado theorem
now wraps `mathlib_bordered_surface_finitePLTriangulationData`, which is built from the finite
terminal Rado stage in `MoiseExtractionData` and carries that stage's boundary subcomplex data.
The theorem `mathlib_bordered_surface_boundaryCarrier_subset_finitePL_boundary` exposes that the
finite cover's selected boundary carrier lies in the packaged finite PL boundary support, and
`mathlib_bordered_surface_manifoldBoundary_subset_finitePL_boundary` specializes this to the
actual mathlib manifold boundary set.
`mathlib_bordered_surface_finiteSurfaceTriangulation` and
`compact_eval_surface_finiteSurfaceTriangulation` are the named finite triangulation objects used
by the public existential wrappers
`mathlib_bordered_surface_finitely_triangulable` and
`compact_eval_surface_finitely_triangulable`.  The positive-regularity route now has parallel
finite-output names ending in `_of_contMDiff`, including
`mathlib_bordered_surface_finiteSurfaceTriangulation_of_contMDiff` and
`compact_eval_surface_finitely_triangulable_of_contMDiff`; these avoid the C0 boundary-invariance
theorem boundary.

Closed coordinate-local bridge:

```lean
theorem euclideanHalfSpace_boundary_polygonal_neighborhood_at
    (U : Set (EuclideanHalfSpace 2)) (y : EuclideanHalfSpace 2) (hU : U ∈ 𝓝 y)
    (hy : y.1 0 = 0) (hyU : y.1 ∈ (Subtype.val '' U)) :
    Nonempty (PlaneRegionPolygonalNeighborhood (Subtype.val '' U) ⟨y.1, hyU⟩)
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
   For the half-plane interior route, the triangle is chosen inside the positive coordinate
   half-plane, so its empty boundary carrier is justified by a genuine no-boundary-line proof.

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
   neighborhood there.  It records both directions of the boundary-line relation: the standard
   boundary edge maps into the coordinate boundary line, and any point of the standard support
   mapped to that line lies on the distinguished edge.
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
boundary.  The last wrapper now returns boundary-core compatibility with the preferred chart as
well as ordinary core refinement, boundary faithfulness, and the statement that manifold-boundary
points in the local core lie in the local boundary core.

Compact finite-subcover extraction is packaged by
`LocalChartPolygonalDiskData.toFiniteChartPolygonalDiskData` and exposed through
`finite_chart_polygonal_disk_data_of_local`, and pointwise data is packaged into local function-valued data by
`localChartPolygonalDiskDataOfPointwise` / `local_chart_polygonal_disk_data_of_pointwise`.
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
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      K.support = Set.univ := by
  -- use Rado plus compact/local-finite finite-support packaging
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
   - the `n`th stage covers the `n`th chart core;
   - `RadoInductionState.CoversCoresUpTo` and
     `RadoInductionState.CoversBoundaryCoresUpTo` are the named state-level predicates for
     cumulative coverage through a finite stage;
   - `InitialPLNeighborhoodData.toState_coversCoresUpTo` and
     `InitialPLNeighborhoodData.toState_coversBoundaryCoresUpTo` prove the base case;
   - `RadoStepExtensionData.toState_coversCoresUpTo` and
     `RadoStepExtensionData.toState_coversBoundaryCoresUpTo` prove the induction step from the
     extension relation;
   - `RadoInductionData.stage_coversCoresUpTo` and
     `RadoInductionData.stage_coversBoundaryCoresUpTo` prove the cumulative invariant for the
     recursively generated stages;
   - `InitialPLNeighborhoodData.toState_coversPreviousCores`,
     `InitialPLNeighborhoodData.toState_coversPreviousBoundaryCores`,
     `RadoStepExtensionData.toState_coversPreviousCores`,
     `RadoStepExtensionData.toState_coversPreviousBoundaryCores`,
     `RadoInductionData.stage_coversPreviousCores`, and
     `RadoInductionData.stage_coversPreviousBoundaryCores` prove the stored finite coverage
     packages cover their recorded ordinary and boundary chart-core sets;
   - `RadoInductionData.covers_core_of_le`,
     `RadoInductionData.covers_boundaryCore_of_le`,
     `RadoInductiveSequence.core_subset_stage_of_le`, and
     `RadoInductiveSequence.boundaryCore_subset_stage_of_le` now prove the cumulative invariant:
     every later stage still covers every earlier chart core and boundary core.
4. Prove the union of stage supports covers `Set.univ`; this is now a Lean proof from the
   exhaustion coverage field.
5. Build the union complex in two layers.  The faithful Rado object is now
   `StagewisePLComplexInSpace`, which records the finite embedded PL complex at each stage,
   monotone extension data, genuine stage-indexed simplex carriers, and boundary simplex carriers.
   The named API is `RadoInductiveSequence.stagewisePLComplex`,
   `RadoInductiveSequence.stagewisePLComplex_support`,
   `RadoInductiveSequence.stagewisePLComplex_boundarySupport`,
   `rado_union_stagewise_complex`, `MoiseTwoManifold.radoStagewisePLComplex`, and
   `rado_triangulation_moise_two_manifold_stagewise`.  Because raw stage-indexed simplexes can
   duplicate persistent simplexes in later stages, this interface records finite data stagewise
   rather than claiming local finiteness of the raw countable simplex type.  Because
   `EuclideanComplex` is still a finite-complex interface, the old support-union embedded complex
   remains a compatibility wrapper built using `Small`/`Shrink`.  The wrapper API is
   `RadoInductiveSequence.unionPLComplexData`, `RadoInductiveSequence.unionPLComplex`,
   `RadoInductiveSequence.unionPLComplex_support`, and
   `RadoInductiveSequence.unionPLComplex_covers_univ`; `rado_union_complex` remains as the public
   existential wrapper for old downstream APIs.  The faithful countable geometry is exposed by
   `RadoInductiveSequence.StageUnionSimplex`,
   `RadoInductiveSequence.stageUnionSimplexCarrier`,
   `RadoInductiveSequence.supportUnion_covered_by_stageUnionSimplexCarrier`,
   `RadoInductiveSequence.StageBoundarySimplex`,
   `RadoInductiveSequence.stageBoundarySimplexCarrier`, and
   `RadoInductiveSequence.boundarySupportUnion_covered_by_stageBoundarySimplexCarrier`.
   The union complex also has a small boundary/interior carrier simplex API:
   `RadoInductiveSequence.boundarySupportUnion`,
   `RadoInductiveSequence.unionBoundarySubcomplex`, and
   `RadoInductiveSequence.unionBoundarySubcomplexData` record the union of stage boundary supports
   as a genuine boundary subcomplex rather than using the whole support as boundary.
   At the Moise interface level, `MoiseTwoManifold.radoSequence`,
   `MoiseTwoManifold.radoStagewisePLComplex`, and
   `MoiseTwoManifold.radoStagewisePLComplex_support` are the preferred API for using the completed
   countable construction.  `MoiseTwoManifold.radoPLComplex` and
   `MoiseTwoManifold.radoPLComplex_support` are compatibility-wrapper names.  For compact Moise surfaces,
   `MoiseTwoManifold.supportUnionFinitePLTriangulationData` is the named finite-support package
   built from the support-union Rado complex and the union boundary-subcomplex data;
   `MoiseTwoManifold.finitePLTriangulationData` is kept as a compatibility wrapper.  Compact
   finite-cover extraction should instead use
   `MoiseExtractionData.finiteStagePLTriangulationData`, which carries the terminal finite Rado
   state's boundary subcomplex data.
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
    ∃ K : PLComplexInSpace M, ∃ _finiteSupport : K.FiniteSupportData,
      ∃ _boundary : K.BoundarySubcomplexData, K.support = Set.univ := by
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
theorem surface_cell_complex_reduces_to_normal_form
    (K : SurfaceCellComplex) :
    ∃ N : NormalForm, N.IsEvalAdmissible ∧ K.HasNormalForm N := by
  sorry
```

This is a combinatorial theorem.  It should construct canonical representatives and equivalences
by the Gallier--Xu moves, then attach the quotient-realization theorem for the chosen canonical
representative.

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
