import Schoenflies.ReturnPathCrossings
import ClassificationOfSurfaces.Moise.PolygonalCrosscut

/-!
# Refining a separator frame at all return-path crossings

Moise's cyclic pairing argument is most convenient when every intersection of
the separator polygon with the return path is a polygon vertex.  The Chapter 2
polygon-refinement API supplies exactly this operation without changing the
polygon's carrier or either complementary region.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- Refine a polygonal separator at its finitely many return-path crossings.
The geometric carrier and its inside/outside regions are unchanged, and every
crossing point is a vertex in the refined cyclic presentation. -/
theorem exists_intersectionVertexRefinement
    (A : J.AccessibleAngularArc) (Q : PolygonalCircle)
    (hfinite : (Q.carrier ∩ range A.returnPath).Finite) :
    ∃ K : PolygonalCircle,
      K.carrier = Q.carrier ∧
      K.interiorRegion = Q.interiorRegion ∧
      K.exteriorRegion = Q.exteriorRegion ∧
      ∀ p ∈ Q.carrier ∩ range A.returnPath, K.IsVertexPoint p := by
  classical
  let F : Finset Plane := hfinite.toFinset
  have hF : ∀ p ∈ F, p ∈ Q.carrier := by
    intro p hp
    have hp' : p ∈ Q.carrier ∩ range A.returnPath := by
      simpa only [F, Set.Finite.mem_toFinset] using hp
    exact hp'.1
  obtain ⟨K, hcarrier, hvertices⟩ := Q.exists_refinement_vertices F hF
  have hregions := PolygonalCircle.regions_eq_of_carrier_eq hcarrier
  refine ⟨K, hcarrier, hregions.1, hregions.2, ?_⟩
  intro p hp
  apply hvertices p
  simpa only [F, Set.Finite.mem_toFinset]

end AccessibleAngularArc
end JordanCircle

end Schoenflies
