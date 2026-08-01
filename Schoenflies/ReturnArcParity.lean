import Schoenflies.ReturnArcFrames
import Schoenflies.AuxiliaryTransverseIntersections
import Schoenflies.ReturnPathParity
import Schoenflies.RefinedSeparatorFrame
import Schoenflies.RefinedEdgeSides

/-!
# Crossing parity for an explicit inside return arc

This is the finite crossing half of Moise 9.5, generalized from the original
chosen return path to the stable `InsideReturnArc` interface.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc
namespace InsideReturnArc

variable {J : JordanCircle} {A : J.AccessibleAngularArc}

/-- At a generic frame/return intersection, a short move along the polygon
edge crosses the two sides of the explicit auxiliary Jordan circle. -/
theorem exists_points_opposite_auxiliarySides_in_ball
    (R : A.InsideReturnArc) (Q : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    {p : Plane}
    (X : R.carrierBrokenLine.TransverseIntersection Q p)
    {radius : ℝ} (hRadius : 0 < radius) :
    ∃ delta : ℝ, 0 < delta ∧
      let e := Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge
      (p + delta • e) ∈ ball p radius ∧
      (p - delta • e) ∈ ball p radius ∧
      (p + delta • e) ∈ Q.edgeSegment X.polygonEdge ∧
      (p - delta • e) ∈ Q.edgeSegment X.polygonEdge ∧
      (((p + delta • e) ∈ R.auxiliaryJordanCircle.inside ∧
          (p - delta • e) ∈ R.auxiliaryJordanCircle.outside) ∨
        ((p + delta • e) ∈ R.auxiliaryJordanCircle.outside ∧
          (p - delta • e) ∈ R.auxiliaryJordanCircle.inside)) := by
  have hpQ : p ∈ Q.carrier :=
    Q.edgeSegment_subset_carrier X.polygonEdge X.mem_polygonEdge
  have hpNotArc : p ∉ A.curveArcPlane := by
    intro hpArc
    have hpInterior := hArcInside hpArc
    have hpCompl : p ∈ Q.carrierᶜ := by
      rw [← Q.interior_union_exterior]
      exact Or.inl hpInterior
    exact hpCompl hpQ
  have hArcNhds : A.curveArcPlaneᶜ ∈ nhds p :=
    A.curveArcPlane_isCompact.isClosed.isOpen_compl.mem_nhds hpNotArc
  obtain ⟨rArc, hrArc, hballArc⟩ := Metric.mem_nhds_iff.mp hArcNhds
  let bdir : Plane :=
    R.carrierBrokenLine.data.vertex X.brokenEdge.succ -
      R.carrierBrokenLine.data.vertex X.brokenEdge.castSucc
  obtain ⟨rReturn, hrReturn, hlocalReturn⟩ :=
    resolvedBrokenLine_exists_local_determinantLine
      R.sourceBrokenLine.data X.brokenEdge X.mem_open_brokenEdge
  change ball p rReturn ∩ R.carrierBrokenLine.data.segmentCarrier =
    ball p rReturn ∩ determinantLine p bdir at hlocalReturn
  obtain ⟨rEdge, hrEdge, hlineSegment⟩ :=
    exists_ball_inter_determinantLine_subset_segment
      (Q.adjacent_ne X.polygonEdge) X.mem_open_polygonEdge
  let r : ℝ := min (min (min rArc rReturn) rEdge) radius
  have hr : 0 < r :=
    lt_min (lt_min (lt_min hrArc hrReturn) hrEdge) hRadius
  have hrArcLe : r ≤ rArc :=
    (min_le_left _ _).trans <| (min_le_left _ _).trans (min_le_left _ _)
  have hrReturnLe : r ≤ rReturn :=
    (min_le_left _ _).trans <| (min_le_left _ _).trans (min_le_right _ _)
  have hrEdgeLe : r ≤ rEdge :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hrRadiusLe : r ≤ radius := min_le_right _ _
  have hlocalAux : ball p r ∩ R.auxiliaryJordanCircle.carrier =
      ball p r ∩ determinantLine p bdir := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxBall, hxAux⟩
      rw [R.carrier_auxiliaryJordanCircle] at hxAux
      rcases hxAux with hxArc | hxReturn
      · exact False.elim <|
          hballArc (ball_subset_ball hrArcLe hxBall) hxArc
      · have hxCarrier : x ∈
            R.carrierBrokenLine.data.segmentCarrier := by
          rw [R.segmentCarrier_carrierBrokenLine_eq_range]
          exact hxReturn
        have hxLocal : x ∈ ball p rReturn ∩
            R.carrierBrokenLine.data.segmentCarrier :=
          ⟨ball_subset_ball hrReturnLe hxBall, hxCarrier⟩
        rw [hlocalReturn] at hxLocal
        exact ⟨hxBall, hxLocal.2⟩
    · rintro x ⟨hxBall, hxLine⟩
      have hxLocal : x ∈ ball p rReturn ∩ determinantLine p bdir :=
        ⟨ball_subset_ball hrReturnLe hxBall, hxLine⟩
      rw [← hlocalReturn] at hxLocal
      refine ⟨hxBall, ?_⟩
      rw [R.carrier_auxiliaryJordanCircle]
      exact Or.inr <| by
        rw [← R.segmentCarrier_carrierBrokenLine_eq_range]
        exact hxLocal.2
  have htransverse : planeDet
      (Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge) bdir ≠ 0 := by
    intro hzero
    apply X.transverse
    rw [planeDet_swap, hzero, neg_zero]
  obtain ⟨delta, hdelta, hplusBall, hminusBall, hsides⟩ :=
    R.auxiliaryJordanCircle.local_transverse_points_opposite_in_ball hr
      (by
        rw [R.carrier_auxiliaryJordanCircle]
        exact Or.inr <| by
          rw [← R.segmentCarrier_carrierBrokenLine_eq_range]
          exact Set.mem_iUnion.mpr ⟨X.brokenEdge, X.mem_brokenEdge⟩)
      hlocalAux htransverse
  let e := Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge
  have hplusLine : p + delta • e ∈ determinantLine p e := by
    simp [determinantLine, planeDet]
    ring
  have hminusLine : p - delta • e ∈ determinantLine p e := by
    simp [determinantLine, planeDet]
    ring
  have hplusEdge : p + delta • e ∈ Q.edgeSegment X.polygonEdge :=
    hlineSegment ⟨ball_subset_ball hrEdgeLe hplusBall, hplusLine⟩
  have hminusEdge : p - delta • e ∈ Q.edgeSegment X.polygonEdge :=
    hlineSegment ⟨ball_subset_ball hrEdgeLe hminusBall, hminusLine⟩
  exact ⟨delta, hdelta, ball_subset_ball hrRadiusLe hplusBall,
    ball_subset_ball hrRadiusLe hminusBall, hplusEdge, hminusEdge, hsides⟩

/-- A transverse crossing changes polygonal side in every parameter interval
around its explicit return-path parameter. -/
theorem exists_path_parameters_opposite_polygonSides_between
    (R : A.InsideReturnArc) (Q : PolygonalCircle) {p : Plane}
    (X : R.carrierBrokenLine.TransverseIntersection Q p)
    {a t b : unitInterval} (htp : R.path t = p)
    (hat : a < t) (htb : t < b) :
    ∃ l u : unitInterval,
      a < l ∧ l < t ∧ t < u ∧ u < b ∧
      (((R.path l ∈ Q.interiorRegion) ∧
          (R.path u ∈ Q.exteriorRegion)) ∨
        ((R.path l ∈ Q.exteriorRegion) ∧
          (R.path u ∈ Q.interiorRegion))) := by
  have hpQ : p ∈ Q.carrier :=
    Q.edgeSegment_subset_carrier X.polygonEdge X.mem_polygonEdge
  obtain ⟨rQ, hrQ, hlocalQ⟩ :=
    polygonalCircle_exists_local_determinantLine Q X.mem_open_polygonEdge
  have hlocalQJordan : ball p rQ ∩ Q.toJordanCircle.carrier =
      ball p rQ ∩ determinantLine p
        (Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge) := by
    simpa using hlocalQ
  let e : Plane :=
    R.carrierBrokenLine.data.vertex X.brokenEdge.succ -
      R.carrierBrokenLine.data.vertex X.brokenEdge.castSucc
  obtain ⟨rReturn, hrReturn, hlocalReturn⟩ :=
    resolvedBrokenLine_exists_local_determinantLine
      R.sourceBrokenLine.data X.brokenEdge X.mem_open_brokenEdge
  change ball p rReturn ∩ R.carrierBrokenLine.data.segmentCarrier =
    ball p rReturn ∩ determinantLine p e at hlocalReturn
  have hlocalPath : ball p rReturn ∩ range R.path =
      ball p rReturn ∩ determinantLine p e := by
    rw [← R.segmentCarrier_carrierBrokenLine_eq_range]
    exact hlocalReturn
  obtain ⟨l, u, hal, hlt, htu, hub, hsides⟩ :=
    Q.toJordanCircle.exists_ordered_points_opposite_sides_between
      R.path.continuous R.path_injective hat htb htp hrQ
      (by rw [Q.carrier_toJordanCircle]; exact hpQ)
      hlocalQJordan hrReturn hlocalPath X.transverse
  refine ⟨l, u, hal, hlt, htu, hub, ?_⟩
  simpa only [Q.inside_toJordanCircle, Q.outside_toJordanCircle] using hsides

/-- Generic position gives a finite set of ordered side-changing parameters
on an explicit return path. -/
theorem exists_ordered_path_crossingTimes
    (R : A.InsideReturnArc) (Q : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hfinite : (Q.carrier ∩ range R.path).Finite)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0) :
    ∃ T : Finset unitInterval,
      (∀ t, t ∈ T ↔ R.path t ∈ Q.carrier) ∧
      ∀ t ∈ T,
        (⊥ : unitInterval) < t ∧ t < (⊤ : unitInterval) ∧
        ∀ a b : unitInterval, a < t → t < b →
          ∃ l u : unitInterval,
            a < l ∧ l < t ∧ t < u ∧ u < b ∧
            (((R.path l ∈ Q.interiorRegion) ∧
                (R.path u ∈ Q.exteriorRegion)) ∨
              ((R.path l ∈ Q.exteriorRegion) ∧
                (R.path u ∈ Q.interiorRegion))) := by
  let crossingTimes : Set unitInterval := R.path ⁻¹' Q.carrier
  have hpreimageEq : crossingTimes =
      R.path ⁻¹' (Q.carrier ∩ range R.path) := by
    ext t
    simp only [crossingTimes, mem_preimage, mem_inter_iff, mem_range]
    constructor
    · intro ht
      exact ⟨ht, t, rfl⟩
    · exact fun ht => ht.1
  have hcrossingTimesFinite : crossingTimes.Finite := by
    rw [hpreimageEq]
    exact hfinite.preimage R.path_injective.injOn
  let T : Finset unitInterval := hcrossingTimesFinite.toFinset
  refine ⟨T, ?_, ?_⟩
  · intro t
    simp only [T, Set.Finite.mem_toFinset, crossingTimes, mem_preimage]
  · intro t htT
    have htCarrier : R.path t ∈ Q.carrier := by
      simpa only [T, Set.Finite.mem_toFinset, crossingTimes, mem_preimage]
        using htT
    have htBroken : R.path t ∈
        R.carrierBrokenLine.data.segmentCarrier := by
      rw [R.segmentCarrier_carrierBrokenLine_eq_range]
      exact ⟨t, rfl⟩
    obtain ⟨X⟩ :=
      R.carrierBrokenLine.exists_transverseIntersection_of_generic
        Q hpolygonVertices hbrokenVertices ⟨htCarrier, htBroken⟩
    have htNotArc : R.path t ∉ A.curveArcPlane := by
      intro htArc
      have htInterior := hArcInside htArc
      have htCompl : R.path t ∈ Q.carrierᶜ := by
        rw [← Q.interior_union_exterior]
        exact Or.inl htInterior
      exact htCompl htCarrier
    have htLower : (⊥ : unitInterval) < t := by
      rw [bot_lt_iff_ne_bot]
      intro ht
      apply htNotArc
      rw [ht]
      change R.path (0 : unitInterval) ∈ A.curveArcPlane
      rw [R.path.source]
      exact A.right_mem_curveArcPlane
    have htUpper : t < (⊤ : unitInterval) := by
      rw [lt_top_iff_ne_top]
      intro ht
      apply htNotArc
      rw [ht]
      change R.path (1 : unitInterval) ∈ A.curveArcPlane
      rw [R.path.target]
      exact A.left_mem_curveArcPlane
    refine ⟨htLower, htUpper, ?_⟩
    intro a b hat htb
    exact R.exists_path_parameters_opposite_polygonSides_between
      Q X rfl hat htb

/-- Crossings before the first middle parameter have odd cardinality. -/
theorem odd_firstTail_crossingTimes
    (R : A.InsideReturnArc) (Q : PolygonalCircle)
    {s t : unitInterval}
    (hspos : (⊥ : unitInterval) < s) (hst : s < t)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hMiddleExterior : R.path '' Icc s t ⊆ Q.exteriorRegion)
    (T : Finset unitInterval)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hordered : ∀ u ∈ T,
      (⊥ : unitInterval) < u ∧ u < (⊤ : unitInterval) ∧
      ∀ a b : unitInterval, a < u → u < b →
        ∃ l v : unitInterval,
          a < l ∧ l < u ∧ u < v ∧ v < b ∧
          (((R.path l ∈ Q.interiorRegion) ∧
              (R.path v ∈ Q.exteriorRegion)) ∨
            ((R.path l ∈ Q.exteriorRegion) ∧
              (R.path v ∈ Q.interiorRegion)))) :
    Odd ((T.filter fun u => u < s).card) := by
  classical
  let firstT : Finset unitInterval := T.filter fun u => u < s
  let side : unitInterval → Bool := fun u =>
    decide (R.path u ∈ Q.interiorRegion)
  have hzeroInside : R.path (⊥ : unitInterval) ∈ Q.interiorRegion := by
    change R.path (0 : unitInterval) ∈ Q.interiorRegion
    rw [R.path.source]
    exact hArcInside A.right_mem_curveArcPlane
  have hsExterior : R.path s ∈ Q.exteriorRegion :=
    hMiddleExterior ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩
  have hsNotCarrier : R.path s ∉ Q.carrier := by
    intro hsCarrier
    exact Set.disjoint_left.mp Q.disjoint_carrier_exteriorRegion
      hsCarrier hsExterior
  have hsNotInside : R.path s ∉ Q.interiorRegion := by
    intro hsInside
    exact Set.disjoint_left.mp Q.disjoint_interior_exterior
      hsInside hsExterior
  have hend : side (⊥ : unitInterval) ≠ side s := by
    simp only [side, hzeroInside, decide_true, hsNotInside, decide_false]
    decide
  apply odd_card_of_ordered_local_side_changes firstT side hspos.le
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    exact ⟨(hordered u hu'.1).1, hu'.2⟩
  · intro x y hx0 hxy hys hfree
    have havoid : ∀ u ∈ Icc x y,
        R.path u ∉ Q.toJordanCircle.carrier := by
      intro u huInterval huCarrierJordan
      have huCarrier : R.path u ∈ Q.carrier := by
        rwa [Q.carrier_toJordanCircle] at huCarrierJordan
      have huT : u ∈ T := (hT u).mpr huCarrier
      have huLeS : u ≤ s := huInterval.2.trans hys
      have huNeS : u ≠ s := by
        intro hus
        subst u
        exact hsNotCarrier huCarrier
      have huLtS : u < s := lt_of_le_of_ne huLeS huNeS
      exact hfree u (Finset.mem_filter.mpr ⟨huT, huLtS⟩) huInterval
    rcases Q.toJordanCircle.interval_image_same_side R.path.continuous
        hxy havoid with hinside | houtside
    · have hxInside : R.path x ∈ Q.interiorRegion := by
        simpa only [Q.inside_toJordanCircle] using hinside.1
      have hyInside : R.path y ∈ Q.interiorRegion := by
        simpa only [Q.inside_toJordanCircle] using hinside.2
      simp only [side, hxInside, hyInside, decide_true]
    · have hxOutside : R.path x ∈ Q.exteriorRegion := by
        simpa only [Q.outside_toJordanCircle] using houtside.1
      have hyOutside : R.path y ∈ Q.exteriorRegion := by
        simpa only [Q.outside_toJordanCircle] using houtside.2
      have hxNotInside : R.path x ∉ Q.interiorRegion := by
        intro hxInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hxInside hxOutside
      have hyNotInside : R.path y ∉ Q.interiorRegion := by
        intro hyInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hyInside hyOutside
      simp only [side, hxNotInside, hyNotInside, decide_false]
  · intro u hu x y hxu huy
    have huT : u ∈ T := (Finset.mem_filter.mp hu).1
    obtain ⟨l, v, hxl, hlu, huv, hvy, hsides⟩ :=
      (hordered u huT).2.2 x y hxu huy
    refine ⟨l, v, hxl, hlu, huv, hvy, ?_⟩
    rcases hsides with hsides | hsides
    · have hvNotInside : R.path v ∉ Q.interiorRegion := by
        intro hvInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hvInside hsides.2
      simp only [side, hsides.1, decide_true, hvNotInside, decide_false]
      decide
    · have hlNotInside : R.path l ∉ Q.interiorRegion := by
        intro hlInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hlInside hsides.1
      simp only [side, hlNotInside, decide_false, hsides.2, decide_true]
      decide
  · exact hend

/-- Refine the separator at every crossing of an explicit return path. -/
theorem exists_intersectionVertexRefinement
    (R : A.InsideReturnArc) (Q : PolygonalCircle)
    (hfinite : (Q.carrier ∩ range R.path).Finite) :
    ∃ K : PolygonalCircle,
      K.carrier = Q.carrier ∧
      K.interiorRegion = Q.interiorRegion ∧
      K.exteriorRegion = Q.exteriorRegion ∧
      ∀ p ∈ Q.carrier ∩ range R.path, K.IsVertexPoint p := by
  classical
  let F : Finset Plane := hfinite.toFinset
  have hF : ∀ p ∈ F, p ∈ Q.carrier := by
    intro p hp
    have hp' : p ∈ Q.carrier ∩ range R.path := by
      simpa only [F, Set.Finite.mem_toFinset] using hp
    exact hp'.1
  obtain ⟨K, hcarrier, hvertices⟩ := Q.exists_refinement_vertices F hF
  have hregions := PolygonalCircle.regions_eq_of_carrier_eq hcarrier
  refine ⟨K, hcarrier, hregions.1, hregions.2, ?_⟩
  intro p hp
  apply hvertices p
  simpa only [F, Set.Finite.mem_toFinset]

/-- Refined open edges avoid the explicit auxiliary Jordan circle. -/
theorem refined_openEdge_disjoint_auxiliaryCarrier
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (i : ZMod K.n) :
    Disjoint (openSegment ℝ (K.vertex i) (K.vertex (i + 1)))
      R.auxiliaryJordanCircle.carrier := by
  rw [Set.disjoint_left]
  intro p hpOpen hpAuxiliary
  have hpEdge : p ∈ K.edgeSegment i :=
    openSegment_subset_segment ℝ _ _ hpOpen
  have hpKCarrier : p ∈ K.carrier := K.edgeSegment_subset_carrier i hpEdge
  have hpQCarrier : p ∈ Q.carrier := by
    rw [← hcarrier]
    exact hpKCarrier
  rw [R.carrier_auxiliaryJordanCircle] at hpAuxiliary
  rcases hpAuxiliary with hpArc | hpReturn
  · have hpComplement : p ∈ Q.carrierᶜ := by
      rw [← Q.interior_union_exterior]
      exact Or.inl (hArcInside hpArc)
    exact hpComplement hpQCarrier
  · have hpVertex : K.IsVertexPoint p :=
      hvertices p ⟨hpQCarrier, hpReturn⟩
    rcases (hpVertex.mem_edgeSegment_iff i).mp hpEdge with hpLeft | hpRight
    · subst p
      exact K.adjacent_ne i (left_mem_openSegment_iff.mp hpOpen)
    · subst p
      exact K.adjacent_ne i (right_mem_openSegment_iff.mp hpOpen)

/-- Side label of a refined separator edge relative to an explicit auxiliary
Jordan circle. -/
noncomputable def refinedEdgeInside (R : A.InsideReturnArc)
    (K : PolygonalCircle) (i : ZMod K.n) : Bool := by
  classical
  exact decide (refinedEdgeMidpoint K i ∈ R.auxiliaryJordanCircle.inside)

/-- Every point of a crossing-free refined open edge is on the same
auxiliary side as its midpoint. -/
theorem refined_openEdge_same_auxiliarySide
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (i : ZMod K.n) {p : Plane}
    (hp : p ∈ openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :
    ((p ∈ R.auxiliaryJordanCircle.inside ∧
        refinedEdgeMidpoint K i ∈ R.auxiliaryJordanCircle.inside) ∨
      (p ∈ R.auxiliaryJordanCircle.outside ∧
        refinedEdgeMidpoint K i ∈ R.auxiliaryJordanCircle.outside)) := by
  have hdisjoint := R.refined_openEdge_disjoint_auxiliaryCarrier Q K
    hArcInside hcarrier hvertices i
  have hsubset : openSegment ℝ (K.vertex i) (K.vertex (i + 1)) ⊆
      R.auxiliaryJordanCircle.carrierᶜ := by
    intro x hxOpen hxCarrier
    exact Set.disjoint_left.mp hdisjoint hxOpen hxCarrier
  apply R.auxiliaryJordanCircle.preconnected_subset_same_side
    (convex_openSegment (𝕜 := ℝ) (K.vertex i)
      (K.vertex (i + 1))).isPreconnected
    hsubset hp
  exact midpoint_mem_openSegment _ _

/-- Membership in the explicit auxiliary inside is represented by the edge
side label. -/
theorem mem_auxiliaryInside_iff_refinedEdgeInside
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (i : ZMod K.n) {p : Plane}
    (hp : p ∈ openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :
    p ∈ R.auxiliaryJordanCircle.inside ↔
      R.refinedEdgeInside K i = true := by
  classical
  rcases R.refined_openEdge_same_auxiliarySide Q K hArcInside
      hcarrier hvertices i hp with hinside | houtside
  · simp [refinedEdgeInside, hinside.1, hinside.2]
  · have hpNotInside : p ∉ R.auxiliaryJordanCircle.inside := by
      intro hpInside
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside
        hpInside houtside.1
    have hmidNotInside : refinedEdgeMidpoint K i ∉
        R.auxiliaryJordanCircle.inside := by
      intro hmidInside
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside
        hmidInside houtside.2
    simp [refinedEdgeInside, hpNotInside, hmidNotInside]

/-- At a separator vertex away from the auxiliary circle, the two incident
edge labels agree. -/
theorem refined_nonCrossingVertex_same_edgeSide
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (i : ZMod K.n)
    (hiAux : K.vertex i ∉ R.auxiliaryJordanCircle.carrier) :
    R.refinedEdgeInside K (i - 1) = R.refinedEdgeInside K i := by
  classical
  have hclosed : IsClosed R.auxiliaryJordanCircle.carrier := by
    rw [← R.auxiliaryJordanCircle.frontier_inside]
    exact isClosed_frontier
  have hnhds : R.auxiliaryJordanCircle.carrierᶜ ∈ nhds (K.vertex i) :=
    hclosed.isOpen_compl.mem_nhds hiAux
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hprev : K.vertex i ≠ K.vertex (i - 1) := by
    have h := K.adjacent_ne (i - 1)
    simpa only [sub_add_cancel] using h.symm
  have hnext : K.vertex i ≠ K.vertex (i + 1) := K.adjacent_ne i
  obtain ⟨x, hxOpen, hxBall⟩ :=
    exists_mem_openSegment_inter_ball hprev hr
  obtain ⟨y, hyOpen, hyBall⟩ :=
    exists_mem_openSegment_inter_ball hnext hr
  have hxOpenIncoming : x ∈
      openSegment ℝ (K.vertex (i - 1)) (K.vertex ((i - 1) + 1)) := by
    rw [sub_add_cancel, openSegment_symm]
    exact hxOpen
  have hxInside := R.mem_auxiliaryInside_iff_refinedEdgeInside
    Q K hArcInside hcarrier hvertices (i - 1) hxOpenIncoming
  have hyInside := R.mem_auxiliaryInside_iff_refinedEdgeInside
    Q K hArcInside hcarrier hvertices i hyOpen
  have hsame := R.auxiliaryJordanCircle.preconnected_subset_same_side
    (convex_ball (K.vertex i) r).isPreconnected hball hxBall hyBall
  rcases hsame with ⟨hxIn, hyIn⟩ | ⟨hxOut, hyOut⟩
  · exact (hxInside.mp hxIn).trans (hyInside.mp hyIn).symm
  · have hxNotIn : x ∉ R.auxiliaryJordanCircle.inside := by
      intro hxIn
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside hxIn hxOut
    have hyNotIn : y ∉ R.auxiliaryJordanCircle.inside := by
      intro hyIn
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside hyIn hyOut
    have hxFalse : R.refinedEdgeInside K (i - 1) = false :=
      Bool.eq_false_of_not_eq_true fun htrue => hxNotIn (hxInside.mpr htrue)
    have hyFalse : R.refinedEdgeInside K i = false :=
      Bool.eq_false_of_not_eq_true fun htrue => hyNotIn (hyInside.mpr htrue)
    exact hxFalse.trans hyFalse.symm

/-- At a transverse auxiliary crossing, the two incident refined edge labels
are opposite. -/
theorem refined_crossingVertex_changes_edgeSide
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (i : ZMod K.n)
    (hiAux : K.vertex i ∈ R.auxiliaryJordanCircle.carrier) :
    R.refinedEdgeInside K (i - 1) ≠ R.refinedEdgeInside K i := by
  classical
  have hiKCarrier : K.vertex i ∈ K.carrier := K.vertex_mem_carrier i
  have hiQCarrier : K.vertex i ∈ Q.carrier := by
    rw [← hcarrier]
    exact hiKCarrier
  have hiReturn : K.vertex i ∈ range R.path := by
    rw [R.carrier_auxiliaryJordanCircle] at hiAux
    rcases hiAux with hiArc | hiReturn
    · have hiComplement : K.vertex i ∈ Q.carrierᶜ := by
        rw [← Q.interior_union_exterior]
        exact Or.inl (hArcInside hiArc)
      exact False.elim (hiComplement hiQCarrier)
    · exact hiReturn
  have hiBroken : K.vertex i ∈
      R.carrierBrokenLine.data.segmentCarrier := by
    rw [R.segmentCarrier_carrierBrokenLine_eq_range]
    exact hiReturn
  obtain ⟨X⟩ :=
    R.carrierBrokenLine.exists_transverseIntersection_of_generic
      Q hpolygonVertices hbrokenVertices ⟨hiQCarrier, hiBroken⟩
  obtain ⟨eps, heps, hlength, _hedges, hseparation⟩ :=
    K.exists_featureRadius
  have hseparation3 : ∀ a b : ZMod K.n, a ≠ b → a ≠ b + 1 →
      ∀ y ∈ K.edgeSegment b, 3 * eps < dist (K.vertex a) y := by
    intro a b hab habPrev y hy
    have h := hseparation a b hab habPrev y hy
    nlinarith
  obtain ⟨delta, hdelta, hplusBall, hminusBall,
      hplusQEdge, hminusQEdge, hsides⟩ :=
    R.exists_points_opposite_auxiliarySides_in_ball Q hArcInside X
      (radius := 3 * eps) (by positivity)
  let e : Plane :=
    Q.vertex (X.polygonEdge + 1) - Q.vertex X.polygonEdge
  let plus : Plane := K.vertex i + delta • e
  let minus : Plane := K.vertex i - delta • e
  change plus ∈ Metric.ball (K.vertex i) (3 * eps) at hplusBall
  change minus ∈ Metric.ball (K.vertex i) (3 * eps) at hminusBall
  change plus ∈ Q.edgeSegment X.polygonEdge at hplusQEdge
  change minus ∈ Q.edgeSegment X.polygonEdge at hminusQEdge
  change
    ((plus ∈ R.auxiliaryJordanCircle.inside ∧
        minus ∈ R.auxiliaryJordanCircle.outside) ∨
      (plus ∈ R.auxiliaryJordanCircle.outside ∧
        minus ∈ R.auxiliaryJordanCircle.inside)) at hsides
  have he : e ≠ 0 :=
    sub_ne_zero.mpr (Q.adjacent_ne X.polygonEdge).symm
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
      have h := K.adjacent_ne (i - 1)
      simpa using h.symm
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
      (hx : x ∈ R.auxiliaryJordanCircle.inside ↔ a = true)
      (hy : y ∈ R.auxiliaryJordanCircle.inside ↔ b = true)
      (hopposite :
        (x ∈ R.auxiliaryJordanCircle.inside ∧
            y ∈ R.auxiliaryJordanCircle.outside) ∨
          (x ∈ R.auxiliaryJordanCircle.outside ∧
            y ∈ R.auxiliaryJordanCircle.inside)) : a ≠ b := by
    intro hab
    rcases hopposite with
      ⟨hxInside, hyOutside⟩ | ⟨hxOutside, hyInside⟩
    · have hyInside' : y ∈ R.auxiliaryJordanCircle.inside :=
        hy.mpr (hab.symm.trans (hx.mp hxInside))
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside
        hyInside' hyOutside
    · have hxInside' : x ∈ R.auxiliaryJordanCircle.inside :=
        hx.mpr (hab.trans (hy.mp hyInside))
      exact Set.disjoint_left.mp
        R.auxiliaryJordanCircle.inside_disjoint_outside
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
      (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hplusOpen)
      (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
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
      (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices (i - 1) hplusOpen)
      (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hminusOpen)
      hsides
  · exact False.elim (hnotBothIncoming ⟨hplusIn, hminusIn⟩)

/-- A refined separator vertex is on the explicit auxiliary circle exactly
when its incident edge labels change. -/
theorem refinedEdgeSides_ne_iff_crossingVertex
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (i : ZMod K.n) :
    R.refinedEdgeInside K (i - 1) ≠ R.refinedEdgeInside K i ↔
      K.vertex i ∈ R.auxiliaryJordanCircle.carrier := by
  constructor
  · intro hchange
    by_contra hiAux
    exact hchange (R.refined_nonCrossingVertex_same_edgeSide Q K
      hArcInside hcarrier hvertices i hiAux)
  · exact R.refined_crossingVertex_changes_edgeSide Q K hArcInside
      hcarrier hvertices hpolygonVertices hbrokenVertices i

end InsideReturnArc
end AccessibleAngularArc
end JordanCircle
end Schoenflies
