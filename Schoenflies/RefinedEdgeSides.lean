import Schoenflies.RefinedSeparatorFrame
import Schoenflies.SideConstancy

/-!
# Side labels on refined separator edges

Once every auxiliary-circle intersection is a polygon vertex, each relative
open edge of the refined separator is crossing-free.  Its midpoint therefore
gives a well-defined Boolean side label for the entire open edge.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- The midpoint used to label a refined polygon edge. -/
noncomputable def refinedEdgeMidpoint (K : PolygonalCircle) (i : ZMod K.n) : Plane :=
  midpoint ℝ (K.vertex i) (K.vertex (i + 1))

/-- `true` exactly when the relative interior of edge `i` lies on the inside
of the auxiliary Jordan circle. -/
noncomputable def refinedEdgeInside
    (A : J.AccessibleAngularArc) (K : PolygonalCircle)
    (i : ZMod K.n) : Bool := by
  classical
  exact decide (refinedEdgeMidpoint K i ∈ A.auxiliaryJordanCircle.inside)

/-- Every point in a crossing-free refined open edge is on the same auxiliary
side as the edge midpoint. -/
theorem refined_openEdge_same_auxiliarySide
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range A.returnPath,
      K.IsVertexPoint p)
    (i : ZMod K.n) {p : Plane}
    (hp : p ∈ openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :
    ((p ∈ A.auxiliaryJordanCircle.inside ∧
        refinedEdgeMidpoint K i ∈ A.auxiliaryJordanCircle.inside) ∨
      (p ∈ A.auxiliaryJordanCircle.outside ∧
        refinedEdgeMidpoint K i ∈ A.auxiliaryJordanCircle.outside)) := by
  have hdisjoint := A.refined_openEdge_disjoint_auxiliaryCarrier Q K
    hArcInside hcarrier hvertices i
  have hsubset : openSegment ℝ (K.vertex i) (K.vertex (i + 1)) ⊆
      A.auxiliaryJordanCircle.carrierᶜ := by
    intro x hxOpen hxCarrier
    exact Set.disjoint_left.mp hdisjoint hxOpen hxCarrier
  apply A.auxiliaryJordanCircle.preconnected_subset_same_side
    (convex_openSegment (𝕜 := ℝ) (K.vertex i)
      (K.vertex (i + 1))).isPreconnected
    hsubset hp
  exact midpoint_mem_openSegment _ _

/-- Membership in the auxiliary inside is constant on a refined open edge
and is represented by `refinedEdgeInside`. -/
theorem mem_auxiliaryInside_iff_refinedEdgeInside
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range A.returnPath,
      K.IsVertexPoint p)
    (i : ZMod K.n) {p : Plane}
    (hp : p ∈ openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :
    p ∈ A.auxiliaryJordanCircle.inside ↔
      A.refinedEdgeInside K i = true := by
  classical
  rcases A.refined_openEdge_same_auxiliarySide Q K hArcInside
      hcarrier hvertices i hp with hinside | houtside
  · simp [refinedEdgeInside, hinside.1, hinside.2]
  · have hpNotInside : p ∉ A.auxiliaryJordanCircle.inside := by
      intro hpInside
      exact Set.disjoint_left.mp A.auxiliaryJordanCircle.inside_disjoint_outside
        hpInside houtside.1
    have hmidNotInside : refinedEdgeMidpoint K i ∉
        A.auxiliaryJordanCircle.inside := by
      intro hmidInside
      exact Set.disjoint_left.mp A.auxiliaryJordanCircle.inside_disjoint_outside
        hmidInside houtside.2
    simp [refinedEdgeInside, hpNotInside, hmidNotInside]

end AccessibleAngularArc
end JordanCircle

end Schoenflies
