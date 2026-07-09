/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PolygonalSchoenflies

/-!
# PL approximation of homeomorphisms

The crux of the Moise route (Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 5-6):

* Ch. 5, Thms. 3-6 (combinatorial Schoenflies and cone extension): a PL homeomorphism between
  the boundaries of two triangles extends to a PL homeomorphism of the triangles;
* Ch. 6, Thm. 2: an embedding of a finite one-dimensional complex into the plane can be
  approximated, arbitrarily closely and fixing vertex images, by a PL embedding;
* Ch. 6, Thm. 3: an embedding of a finite combinatorial 2-manifold-with-boundary into the plane
  can be approximated, arbitrarily closely, by a PL embedding.

Moise's own remark (end of Ch. 8): the restriction to dimension 2 in the entire triangulation
proof is used *only* through Thm. 6.3.  This file is therefore the mathematical core of the
route.  Moise states Ch. 6 with strongly positive control functions `φ ≫ 0` to handle
non-compact complexes; our complexes are finite, so uniform `ε`-control is equivalent and the
statements below use it.

The full Jordan curve theorem (Ch. 4) is not used by these theorems: Thm. 6.2 needs only
broken-line connectivity (Ch. 1), and Thm. 6.3 needs the polygonal theorems of Ch. 2-3 through
the combinatorial Schoenflies theorem.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- `f` is piecewise linear on the set `A`: `A` carries some finite plane complex on which `f`
is PL.  In particular `A` must itself be a compact polyhedron. -/
def IsPLOnSet (A : Set Plane) (f : Plane → Plane) : Prop :=
  ∃ K : PlaneComplex, K.support = A ∧ IsPLOn K f

namespace PlaneComplex

/-- A finite plane complex is a combinatorial 2-manifold-with-boundary in the weak sense needed
by the approximation theorem: purely two-dimensional, with every edge in at most two cells.
(Moise additionally asks for connected vertex links; embeddability in the plane forces the link
conditions, so they are omitted from the hypothesis here — if the proof turns out to need them,
strengthen this predicate rather than weakening the theorem.) -/
def IsCombinatorial2ManifoldWithBoundary (K : PlaneComplex) : Prop :=
  K.IsPure2 ∧ ∀ e ∈ K.edges, (K.cells.filter fun s => e ⊆ s).card ≤ 2

end PlaneComplex

/-- **Theorem boundary** (Moise Ch. 5, Thms. 3-6: combinatorial Schoenflies / cone extension).

A map that is PL and injective on the frontier of a triangle, carrying it onto the frontier of a
second triangle, extends to a map of the closed triangles with the same properties.  Moise proves
this by coning from an interior point: the extension is linear on each segment from the cone
point to the boundary. -/
theorem pl_extension_of_triangle_boundary {C C' : Set Plane}
    (hC : IsTriangle C) (hC' : IsTriangle C') {f : Plane → Plane}
    (hpl : IsPLOnSet (frontier C) f) (hinj : Set.InjOn f (frontier C))
    (himage : f '' frontier C = frontier C') :
    ∃ F : Plane → Plane,
      Set.EqOn F f (frontier C) ∧ ContinuousOn F C ∧ Set.InjOn F C ∧
      F '' C = C' ∧ IsPLOnSet C F := by
  sorry

/-- **Theorem boundary** (Moise Ch. 6, Thm. 2: PL approximation on one-dimensional complexes).

An embedding of the support of a finite one-dimensional complex into the plane can be
`ε`-approximated by a PL embedding that agrees with it on every vertex.  Moise's proof: choose a
fine subdivision, replace each small arc by a broken line in a small neighborhood (Ch. 6, Thm. 1,
which rests on the broken-line connectivity of open connected sets, Ch. 1), keeping the broken
lines disjoint except at shared endpoints. -/
theorem pl_approximation_one_skeleton (K : PlaneComplex)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      (∀ v : K.Vertex, f (K.position v) = h (K.position v)) ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε := by
  sorry

/-- **Theorem boundary** (Moise Ch. 6, Thm. 3: PL approximation of embedded 2-manifolds — the
mathematical core of the triangulation theorem).

An embedding of the support of a finite combinatorial 2-manifold-with-boundary into the plane can
be `ε`-approximated by a PL embedding.  Moise's proof: approximate on the one-skeleton by
Thm. 6.2, then extend across each 2-cell by the combinatorial Schoenflies theorem
(`pl_extension_of_triangle_boundary`), with the subdivision chosen fine enough that the extended
images of distinct cells have disjoint interiors.

This is the single point where the whole triangulation proof uses dimension 2 (Moise, end of
Ch. 8). -/
theorem pl_approximation_two_manifold (K : PlaneComplex)
    (hsurface : K.IsCombinatorial2ManifoldWithBoundary)
    {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    (hinj : Set.InjOn h K.support)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Plane → Plane,
      IsPLOn K f ∧ Set.InjOn f K.support ∧
      ∀ x ∈ K.support, dist (f x) (h x) < ε := by
  sorry

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
