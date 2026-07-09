/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PLApproximation
import ClassificationOfSurfaces.Surface

/-!
# The Radó chart induction

The skeleton of Moise Ch. 8 (the triangulation theorem for 2-manifolds), extended to bordered
surfaces as required by the Eval statement.

Moise's proof of Thm. 8.3 (Radó): cover the surface by chart pairs (Thm. 8.1; finitely many, by
compactness), and build an increasing sequence of embedded complexes, absorbing one chart core at
each step.  The step adjusts the new chart's polyhedral disk by a PL approximation (Thm. 6.3,
`pl_approximation_two_manifold`) so that it meets the already-built complex simplicially
(conditions (a)-(h) in Moise's proof), and glues (Thm. 7.6).

This file provides the honest objects for that induction:

* `PartialTriangulation S` — an embedded finite complex that need not cover `S`; its realization
  is computed from the combinatorial data exactly as in `GeometricTriangulation`, so junk
  witnesses cannot inhabit it;
* `MoiseChart S` — a disk or half-disk chart with an explicit compact core;
* `moise_finite_chart_cover` — the finite-cover boundary (Moise Thm. 8.1 plus compactness; the
  bordered version).  `PL.lean` already contains a genuine proof of essentially this statement
  (`FiniteChartPairCover.exists_of_compact_local` and the `fromChartAt` constructions); filling
  this boundary is a port, not new mathematics.

**Deliberately not yet stated**: the induction-step boundary.  Its hypothesis package (Moise's
invariants (3)-(5): the built support is a 2-manifold with boundary, previously absorbed cores
lie in its combinatorial interior) is a design decision that should be made together with the
proof attempt, per the Definition Faithfulness rules: refining hypotheses later is expected,
weakening conclusions is not.  Designing that interface is the next task on this route.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A finite two-dimensional complex embedded in `S`, not necessarily covering it.  The
realization is computed from the combinatorial data (as in `GeometricTriangulation`), so the
support of a partial triangulation is a genuine finite polyhedron sitting inside `S`. -/
structure PartialTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: three-element vertex sets. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The embedding of the realization into `S`. -/
  embed : GeometricRealization Vertex faces → S
  /-- `embed` is a topological embedding. -/
  isEmbedding : _root_.Topology.IsEmbedding embed

attribute [instance] PartialTriangulation.vertexFintype
attribute [instance] PartialTriangulation.vertexDecidableEq

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S] (T : PartialTriangulation S)

/-- The part of `S` covered by the partial triangulation. -/
def support : Set S :=
  Set.range T.embed

/-- The support of a partial triangulation is compact. -/
theorem isCompact_support : IsCompact T.support :=
  isCompact_range T.isEmbedding.continuous

/-- A partial triangulation covering all of `S` is a geometric triangulation.  This is the final
conversion at the top of the Radó induction. -/
noncomputable def toGeometricTriangulation (hcovers : T.support = Set.univ) :
    GeometricTriangulation S where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card
  homeo :=
    T.isEmbedding.toHomeomorphOfSurjective (Set.range_eq_univ.mp hcovers)

/-- The edges of a partial triangulation: the two-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

/-- The boundary edges: edges lying in exactly one face. -/
def boundaryEdges : Finset (Finset T.Vertex) :=
  T.edges.filter fun e => (T.faces.filter fun t => e ⊆ t).card = 1

/-- The image in `S` of the combinatorial boundary: points of the realization supported on a
boundary edge. -/
def boundarySupport : Set S :=
  T.embed '' {x | ∃ e ∈ T.boundaryEdges, ∀ v ∉ e, x.1 v = 0}

/-- The combinatorial interior of the covered region: the support minus the image of the
combinatorial boundary.  The Radó induction keeps every absorbed chart core inside this set
(Moise Ch. 8, Thm. 3, invariant (4)). -/
def combInterior : Set S :=
  T.support \ T.boundarySupport

theorem combInterior_subset_support : T.combInterior ⊆ T.support :=
  Set.sdiff_subset

/-- The empty partial triangulation. -/
def empty (S : Type*) [TopologicalSpace S] : PartialTriangulation S where
  Vertex := Empty
  faces := ∅
  faces_card := by simp
  embed := fun x => isEmptyElim x
  isEmbedding := Topology.IsEmbedding.of_subsingleton _

/-- A partial triangulation with no faces covers nothing: its realization is empty. -/
theorem support_eq_empty_of_faces_eq_empty {S : Type*} [TopologicalSpace S]
    (T : PartialTriangulation S) (h : T.faces = ∅) : T.support = ∅ := by
  ext x
  simp only [support, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, rfl⟩
  rcases p.2.2 with ⟨t, ht, -⟩
  rw [h] at ht
  exact absurd ht (Finset.notMem_empty t)

@[simp] theorem empty_support (S : Type*) [TopologicalSpace S] :
    (empty S).support = ∅ :=
  support_eq_empty_of_faces_eq_empty _ rfl

end PartialTriangulation

/-- The invariant carried through the Radó induction (Moise Ch. 8, Thm. 3, invariants (3)-(4)):
the built complex is a combinatorial surface (every edge in at most two faces), and the region
`A` absorbed so far lies in its combinatorial interior.

This invariant is expected to be *strengthened* during the proof of `moise_induction_step`
(candidates: connected vertex links, and the bordered bookkeeping locating `∂S ∩ support` inside
the combinatorial boundary).  Strengthening tightens the step's hypothesis and conclusion
together and keeps the assembly proof below valid; weakening the step's conclusion instead is
the failure mode this rebuild exists to prevent. -/
structure RadoInvariant {S : Type*} [TopologicalSpace S]
    (T : PartialTriangulation S) (A : Set S) : Prop where
  combSurface : ∀ e ∈ T.edges, (T.faces.filter fun t => e ⊆ t).card ≤ 2
  coresInside : A ⊆ T.combInterior

/-- The empty partial triangulation satisfies the invariant for the empty region: the base case
of the Radó induction. -/
theorem radoInvariant_empty (S : Type*) [TopologicalSpace S] :
    RadoInvariant (PartialTriangulation.empty S) ∅ where
  combSurface := by
    intro e he
    simp only [PartialTriangulation.edges, PartialTriangulation.empty,
      Finset.biUnion_empty] at he
    exact absurd he (Finset.notMem_empty e)
  coresInside := Set.empty_subset _

/-- The kind of a Moise chart: interior charts are disks, boundary charts are half-disks. -/
inductive ChartKind where
  | disk
  | halfDisk
deriving DecidableEq, Repr

/-- The model region of a chart kind: the open unit disk, or its closed-right half. -/
def ChartKind.modelRegion : ChartKind → Set Plane
  | .disk => Metric.ball 0 1
  | .halfDisk => {x ∈ Metric.ball 0 1 | 0 ≤ x 0}

/-- The model core of a chart kind: the closed disk of radius one half, or its right half.  Cores
are compact and their union over a chart cover is what the Radó induction absorbs. -/
def ChartKind.modelCore : ChartKind → Set Plane
  | .disk => Metric.closedBall 0 (1 / 2)
  | .halfDisk => {x ∈ Metric.closedBall 0 (1 / 2) | 0 ≤ x 0}

theorem ChartKind.modelCore_subset_modelRegion (k : ChartKind) :
    k.modelCore ⊆ k.modelRegion := by
  cases k with
  | disk =>
      exact (Metric.closedBall_subset_ball (by norm_num))
  | halfDisk =>
      rintro x ⟨hx, hx0⟩
      exact ⟨Metric.closedBall_subset_ball (by norm_num) hx, hx0⟩

/-- A chart of the Moise cover: an open domain homeomorphic to the model disk or half-disk, with
the compact core marked out by the chart. -/
structure MoiseChart (S : Type*) [TopologicalSpace S] where
  /-- Whether this is an interior (disk) or boundary (half-disk) chart. -/
  kind : ChartKind
  /-- The chart domain. -/
  domain : Set S
  /-- Chart domains are open. -/
  isOpen_domain : IsOpen domain
  /-- The chart homeomorphism onto the model region. -/
  chart : domain ≃ₜ kind.modelRegion

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- The core of a chart: the part of the domain corresponding to the model core. -/
def core : Set S :=
  Subtype.val '' (c.chart ⁻¹' {p : c.kind.modelRegion | (p : Plane) ∈ c.kind.modelCore})

theorem core_subset_domain : c.core ⊆ c.domain := by
  rintro x ⟨p, -, rfl⟩
  exact p.2

end MoiseChart

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
variable [ChartBoundaryInvariant S]

/-- **Theorem boundary** (Moise Ch. 8, Thm. 1, plus compactness; bordered version).

A compact Eval surface has a finite cover by Moise chart cores, with half-disk charts placing the
manifold boundary on the model boundary line.  `PL.lean` contains a genuine proof of essentially
this statement (`RadoChartPair.fromChartAt`, `FiniteChartPairCover.exists_of_compact_local`, and
the boundary-faithfulness lemmas using `ChartBoundaryInvariant`); discharging this boundary is a
port of that spine to the fresh objects, not new mathematics. -/
theorem moise_finite_chart_cover :
    ∃ (m : ℕ) (charts : Fin m → MoiseChart S),
      (⋃ i, (charts i).core) = Set.univ ∧
      ∀ i, (charts i).kind = ChartKind.halfDisk →
        ∀ x (hx : x ∈ (charts i).domain),
          x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
            (((charts i).chart ⟨x, hx⟩ : Plane) 0 = 0) := by
  sorry

/-- A chart is boundary-faithful when, in the half-disk case, the chart coordinate detects the
manifold boundary.  This is the property the cover theorem provides and the induction step
consumes. -/
def MoiseChart.BoundaryFaithful (c : MoiseChart S) : Prop :=
  c.kind = ChartKind.halfDisk →
    ∀ x (hx : x ∈ c.domain),
      x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔ ((c.chart ⟨x, hx⟩ : Plane) 0 = 0)

/-- **Theorem boundary** (Moise Ch. 8, Thm. 3, the induction step; bordered version).

Given a partial triangulation satisfying the Radó invariant for the absorbed region `A`, and one
more boundary-faithful chart, the chart's core can be absorbed: there is a partial triangulation
satisfying the invariant for `A ∪ c.core`.

Moise's proof of the step: work in the chart's model coordinates; take a polyhedral neighborhood
of the part of the built complex meeting the chart (Thm. 8.2); adjust it by a PL approximation of
the chart-transition homeomorphism (Thm. 6.3, `pl_approximation_two_manifold`) so that it meets a
fine complex containing the model core simplicially (conditions (a)-(h)); glue (Thm. 7.6).  The
polygonal Jordan and Schoenflies theorems enter through Thm. 6.3.

Hypothesis refinement is expected here (see `RadoInvariant`); conclusion weakening is not. -/
theorem moise_induction_step (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ T' : PartialTriangulation S, RadoInvariant T' (A ∪ c.core) := by
  sorry

/-- The Radó induction assembled: a compact Eval surface admits a geometric triangulation.

This is a genuine proof from the two theorem boundaries above: starting from the empty complex,
absorb the finitely many chart cores one at a time by `moise_induction_step`; when all cores are
absorbed the invariant forces the support to be everything, and a fully covering partial
triangulation is a geometric triangulation. -/
theorem moise_triangulation_of_boundaries :
    Nonempty (GeometricTriangulation S) := by
  classical
  obtain ⟨m, charts, hcover, hbd⟩ := moise_finite_chart_cover S
  -- Absorb the first `k` cores.
  have Hrec : ∀ k : ℕ,
      ∃ T : PartialTriangulation S,
        RadoInvariant T (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
    intro k
    induction k with
    | zero =>
        refine ⟨PartialTriangulation.empty S, ?_⟩
        have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < 0), (charts i).core) = (∅ : Set S) := by
          simp
        rw [hA]
        exact radoInvariant_empty S
    | succ k ih =>
        rcases ih with ⟨T, hT⟩
        by_cases hk : k < m
        · obtain ⟨T', hT'⟩ :=
            moise_induction_step S (charts ⟨k, hk⟩) (hbd ⟨k, hk⟩) hT
          refine ⟨T', ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) ∪
                (charts ⟨k, hk⟩).core := by
            ext x
            simp only [Set.mem_iUnion, Set.mem_union]
            constructor
            · rintro ⟨i, hik, hx⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hik with hik' | hik'
              · exact Or.inl ⟨i, hik', hx⟩
              · refine Or.inr ?_
                have : i = ⟨k, hk⟩ := Fin.ext hik'
                rwa [← this]
            · rintro (⟨i, hik, hx⟩ | hx)
              · exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
              · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
          rw [hA]
          exact hT'
        · refine ⟨T, ?_⟩
          have hA : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k + 1), (charts i).core) =
              (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < k), (charts i).core) := by
            ext x
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨i, hik, hx⟩
              have : (i : ℕ) < k := by
                have := i.isLt
                omega
              exact ⟨i, this, hx⟩
            · rintro ⟨i, hik, hx⟩
              exact ⟨i, Nat.lt_succ_of_lt hik, hx⟩
          rw [hA]
          exact hT
  obtain ⟨T, hT⟩ := Hrec m
  have hall : (⋃ i : Fin m, ⋃ (_ : (i : ℕ) < m), (charts i).core) = Set.univ := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨i, i.isLt, hx⟩
  have hsupport : T.support = Set.univ := by
    have huniv : (Set.univ : Set S) ⊆ T.combInterior := by
      rw [← hall]
      exact hT.coresInside
    exact Set.eq_univ_of_univ_subset
      (huniv.trans T.combInterior_subset_support)
  exact ⟨T.toGeometricTriangulation hsupport⟩

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
