/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PolygonalJordan

/-!
# The Schoenflies theorem for polygons

Statements following Moise, *Geometric Topology in Dimensions 2 and 3*:

* Ch. 2, Thm. 2: the closed region bounded by a polygon is a finite polyhedron — this is the
  triangulation theorem for polygonal disks, proved by cutting along the lines through the edges;
* Ch. 3, Thm. 5: any two polygons are equivalent under an ambient homeomorphism of the plane;
* Ch. 3, Thm. 7: the ambient homeomorphism can be chosen supported in any open set containing
  the closed region (the relative version used for gluing).

Only the polygonal case is stated.  The full Schoenflies theorem (Moise Ch. 9) comes *after* the
triangulation theorem in Moise and is not on this route's critical path.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A closed triangle in the plane: the convex hull of three affinely independent points. -/
def IsTriangle (C : Set Plane) : Prop :=
  ∃ p : Fin 3 → Plane, AffineIndependent ℝ p ∧ C = convexHull ℝ (Set.range p)

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- **Theorem boundary** (Moise Ch. 2, Thm. 2: polygonal disks are finite polyhedra).

The closed region bounded by a polygon is the support of a finite plane complex, purely
two-dimensional, whose edge skeleton along the polygon refines the polygon's edges.  Moise's
proof cuts the region by the finitely many lines through the polygon's edges and triangulates
each convex piece. -/
theorem closedRegion_is_polyhedron :
    ∃ K : PlaneComplex, K.support = J.closedRegion ∧ K.IsPure2 ∧
      ∃ E ⊆ K.edges, J.carrier = ⋃ e ∈ E, K.cellCarrier e := by
  sorry

/-- The closed region bounded by a polygon admits a geometric triangulation.

This is real glue (not a boundary): it consumes `closedRegion_is_polyhedron` (Moise Ch. 2,
Thm. 2) and the realization bridge `PlaneComplex.toGeometricTriangulation`. -/
theorem closedRegion_triangulable :
    Nonempty (GeometricTriangulation J.closedRegion) := by
  obtain ⟨K, hsupport, hpure, -⟩ := J.closedRegion_is_polyhedron
  obtain ⟨T⟩ := K.toGeometricTriangulation hpure
  exact ⟨{ T with homeo := T.homeo.trans (Homeomorph.setCongr hsupport) }⟩

/-- **Theorem boundary** (Moise Ch. 3, Thm. 5: the Schoenflies theorem for polygons).

Any two polygons in the plane are equivalent under a homeomorphism of the whole plane. -/
theorem polygonal_schoenflies (J' : PolygonalCircle) :
    ∃ h : Plane ≃ₜ Plane, h '' J.carrier = J'.carrier := by
  sorry

/-- **Theorem boundary** (Moise Ch. 3, Thm. 7: the relative Schoenflies theorem for polygons).

The straightening homeomorphism can be chosen to fix everything outside a prescribed open set
containing the closed region: `h` sends the polygon to the frontier of a triangle and is the
identity off `U`.  This is the version used to reconcile chart triangulations without disturbing
the part of the complex already built. -/
theorem polygonal_schoenflies_rel (U : Set Plane) (hU : IsOpen U)
    (hregion : J.closedRegion ⊆ U) :
    ∃ h : Plane ≃ₜ Plane, (∃ C : Set Plane, IsTriangle C ∧ h '' J.carrier = frontier C) ∧
      Set.EqOn h id Uᶜ := by
  sorry

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
