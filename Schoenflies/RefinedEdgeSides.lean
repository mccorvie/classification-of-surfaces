import Schoenflies.RefinedSeparatorFrame
import Schoenflies.SideConstancy
import Schoenflies.AuxiliaryTransverseIntersections

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

/-- At a transverse auxiliary-circle crossing, the two refined separator
edges incident to the crossing vertex have opposite side labels. -/
theorem refined_crossingVertex_changes_edgeSide
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range A.returnPath,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin A.returnCarrierBrokenLine.data.n),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (A.returnCarrierBrokenLine.data.vertex j.succ -
          A.returnCarrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (A.returnCarrierBrokenLine.data.n + 1)),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (i : ZMod K.n)
    (hiAux : K.vertex i ∈ A.auxiliaryJordanCircle.carrier) :
    A.refinedEdgeInside K (i - 1) ≠ A.refinedEdgeInside K i := by
  classical
  have hiKCarrier : K.vertex i ∈ K.carrier := K.vertex_mem_carrier i
  have hiQCarrier : K.vertex i ∈ Q.carrier := by
    rw [← hcarrier]
    exact hiKCarrier
  have hiReturn : K.vertex i ∈ range A.returnPath := by
    rw [A.carrier_auxiliaryJordanCircle] at hiAux
    rcases hiAux with hiArc | hiReturn
    · have hiComplement : K.vertex i ∈ Q.carrierᶜ := by
        rw [← Q.interior_union_exterior]
        exact Or.inl (hArcInside hiArc)
      exact False.elim (hiComplement hiQCarrier)
    · exact hiReturn
  have hiBroken : K.vertex i ∈
      A.returnCarrierBrokenLine.data.segmentCarrier := by
    rw [A.segmentCarrier_returnCarrierBrokenLine]
    exact hiReturn
  obtain ⟨X⟩ :=
    A.returnCarrierBrokenLine.exists_transverseIntersection_of_generic
      Q hpolygonVertices hbrokenVertices ⟨hiQCarrier, hiBroken⟩
  obtain ⟨eps, heps, hlength, _hedges, hseparation⟩ :=
    K.exists_featureRadius
  have hseparation3 : ∀ a b : ZMod K.n, a ≠ b → a ≠ b + 1 →
      ∀ y ∈ K.edgeSegment b, 3 * eps < dist (K.vertex a) y := by
    intro a b hab habPrev y hy
    have := hseparation a b hab habPrev y hy
    nlinarith
  obtain ⟨delta, hdelta, hplusBall, hminusBall,
      hplusQEdge, hminusQEdge, hsides⟩ :=
    Schoenflies.JordanCircle.AccessibleAngularArc.SimpleBrokenLine.TransverseIntersection.exists_points_opposite_auxiliarySides_in_ball
      A Q hArcInside X (R := 3 * eps) (by positivity)
  let e : Plane :=
    Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge
  let plus : Plane := K.vertex i + delta • e
  let minus : Plane := K.vertex i - delta • e
  change plus ∈ Metric.ball (K.vertex i) (3 * eps) at hplusBall
  change minus ∈ Metric.ball (K.vertex i) (3 * eps) at hminusBall
  change plus ∈ Q.edgeSegment X.polygonEdge at hplusQEdge
  change minus ∈ Q.edgeSegment X.polygonEdge at hminusQEdge
  change
    ((plus ∈ A.auxiliaryJordanCircle.inside ∧
        minus ∈ A.auxiliaryJordanCircle.outside) ∨
      (plus ∈ A.auxiliaryJordanCircle.outside ∧
        minus ∈ A.auxiliaryJordanCircle.inside)) at hsides
  have he : e ≠ 0 := by
    exact sub_ne_zero.mpr (Q.adjacent_ne X.polygonEdge).symm
  have hplusNe : plus ≠ K.vertex i := by
    intro h
    have hzero : delta • e = 0 := by
      have h' := congrArg (fun x => x - K.vertex i) h
      simpa [plus] using h'
    rcases smul_eq_zero.mp hzero with hdeltaZero | heZero
    · exact hdelta.ne' hdeltaZero
    · exact he heZero
  have hminusNe : minus ≠ K.vertex i := by
    intro h
    have hzero : delta • e = 0 := by
      have h' : K.vertex i - delta • e = K.vertex i := by
        simpa [minus] using h
      exact sub_eq_self.mp h'
    rcases smul_eq_zero.mp hzero with hdeltaZero | heZero
    · exact hdelta.ne' hdeltaZero
    · exact he heZero
  have hmidpoint : midpoint ℝ plus minus = K.vertex i := by
    simpa [plus, minus] using
      (midpoint_add_sub (ℝ) (K.vertex i) (delta • e))
  have hplusMinus : plus ≠ minus := by
    intro h
    have hminusEq : minus = K.vertex i := by
      simpa [h] using hmidpoint
    exact hplusNe (h.trans hminusEq)
  have hiBetween : K.vertex i ∈ openSegment ℝ plus minus := by
    rw [← hmidpoint]
    exact midpoint_mem_openSegment _ _
  have hplusKCarrier : plus ∈ K.carrier := by
    rw [hcarrier]
    exact Q.edgeSegment_subset_carrier X.polygonEdge hplusQEdge
  have hminusKCarrier : minus ∈ K.carrier := by
    rw [hcarrier]
    exact Q.edgeSegment_subset_carrier X.polygonEdge hminusQEdge
  have hplusIncident :
      plus ∈ K.edgeSegment i ∪ K.edgeSegment (i - 1) := by
    apply K.mem_incident_edge_of_mem_carrier_of_dist_lt
      hseparation3 hplusKCarrier
    simpa only [Metric.mem_ball, dist_comm] using hplusBall
  have hminusIncident :
      minus ∈ K.edgeSegment i ∪ K.edgeSegment (i - 1) := by
    apply K.mem_incident_edge_of_mem_carrier_of_dist_lt
      hseparation3 hminusKCarrier
    simpa only [Metric.mem_ball, dist_comm] using hminusBall
  have hnotBothOutgoing :
      ¬(plus ∈ K.edgeSegment i ∧ minus ∈ K.edgeSegment i) := by
    rintro ⟨hplus, hminus⟩
    exact endpoint_not_mem_openSegment_of_mem_segment (K.adjacent_ne i)
      hplusMinus hplus hminus hiBetween
  have hnotBothIncoming :
      ¬(plus ∈ K.edgeSegment (i - 1) ∧
        minus ∈ K.edgeSegment (i - 1)) := by
    rintro ⟨hplus, hminus⟩
    have hne : K.vertex i ≠ K.vertex (i - 1) := by
      have := K.adjacent_ne (i - 1)
      simpa using this.symm
    apply endpoint_not_mem_openSegment_of_mem_segment hne
      hplusMinus _ _ hiBetween
    · simpa only [PolygonalCircle.edgeSegment, sub_add_cancel,
        segment_symm] using hplus
    · simpa only [PolygonalCircle.edgeSegment, sub_add_cancel,
        segment_symm] using hminus
  have hplusNeNext : plus ≠ K.vertex (i + 1) := by
    intro h
    have hnear : dist (K.vertex i) (K.vertex (i + 1)) < 3 * eps := by
      simpa only [Metric.mem_ball, h, dist_comm] using hplusBall
    nlinarith [hlength i]
  have hminusNeNext : minus ≠ K.vertex (i + 1) := by
    intro h
    have hnear : dist (K.vertex i) (K.vertex (i + 1)) < 3 * eps := by
      simpa only [Metric.mem_ball, h, dist_comm] using hminusBall
    nlinarith [hlength i]
  have hplusNePrev : plus ≠ K.vertex (i - 1) := by
    intro h
    have hnear : dist (K.vertex (i - 1)) (K.vertex i) < 3 * eps := by
      simpa only [Metric.mem_ball, h] using hplusBall
    have hfar := hlength (i - 1)
    simp only [sub_add_cancel] at hfar
    nlinarith
  have hminusNePrev : minus ≠ K.vertex (i - 1) := by
    intro h
    have hnear : dist (K.vertex (i - 1)) (K.vertex i) < 3 * eps := by
      simpa only [Metric.mem_ball, h] using hminusBall
    have hfar := hlength (i - 1)
    simp only [sub_add_cancel] at hfar
    nlinarith
  have labels_ne_of_opposite {x y : Plane} {a b : Bool}
      (hx : x ∈ A.auxiliaryJordanCircle.inside ↔ a = true)
      (hy : y ∈ A.auxiliaryJordanCircle.inside ↔ b = true)
      (hopposite :
        (x ∈ A.auxiliaryJordanCircle.inside ∧
            y ∈ A.auxiliaryJordanCircle.outside) ∨
          (x ∈ A.auxiliaryJordanCircle.outside ∧
            y ∈ A.auxiliaryJordanCircle.inside)) : a ≠ b := by
    intro hab
    rcases hopposite with ⟨hxInside, hyOutside⟩ | ⟨hxOutside, hyInside⟩
    · have hyInside' : y ∈ A.auxiliaryJordanCircle.inside :=
        hy.mpr (hab.symm.trans (hx.mp hxInside))
      exact Set.disjoint_left.mp
        A.auxiliaryJordanCircle.inside_disjoint_outside
          hyInside' hyOutside
    · have hxInside' : x ∈ A.auxiliaryJordanCircle.inside :=
        hx.mpr (hab.trans (hy.mp hyInside))
      exact Set.disjoint_left.mp
        A.auxiliaryJordanCircle.inside_disjoint_outside
          hxInside' hxOutside
  rcases hplusIncident with hplusOut | hplusIn <;>
      rcases hminusIncident with hminusOut | hminusIn
  · exact False.elim (hnotBothOutgoing ⟨hplusOut, hminusOut⟩)
  · have hplusOpen : plus ∈
        openSegment ℝ (K.vertex i) (K.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right hplusNe.symm
        hplusNeNext.symm hplusOut
    have hminusOpen : minus ∈
        openSegment ℝ (K.vertex (i - 1)) (K.vertex ((i - 1) + 1)) :=
      mem_openSegment_of_ne_left_right hminusNePrev.symm
        (by simpa only [sub_add_cancel] using hminusNe.symm)
        (by simpa only [PolygonalCircle.edgeSegment] using hminusIn)
    have hne := labels_ne_of_opposite
      (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hplusOpen)
      (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices (i - 1) hminusOpen)
      hsides
    exact fun h => hne h.symm
  · have hminusOpen : minus ∈
        openSegment ℝ (K.vertex i) (K.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right hminusNe.symm
        hminusNeNext.symm hminusOut
    have hplusOpen : plus ∈
        openSegment ℝ (K.vertex (i - 1)) (K.vertex ((i - 1) + 1)) :=
      mem_openSegment_of_ne_left_right hplusNePrev.symm
        (by simpa only [sub_add_cancel] using hplusNe.symm)
        (by simpa only [PolygonalCircle.edgeSegment] using hplusIn)
    exact labels_ne_of_opposite
      (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices (i - 1) hplusOpen)
      (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hminusOpen)
      hsides
  · exact False.elim (hnotBothIncoming ⟨hplusIn, hminusIn⟩)

end AccessibleAngularArc
end JordanCircle

end Schoenflies
