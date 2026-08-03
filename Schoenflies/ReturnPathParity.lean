import Schoenflies.ReturnPathCrossings
import Schoenflies.SideConstancy
import Schoenflies.FiniteCrossingParity

/-!
# Odd crossing parity on an endpoint tail

The selected boundary arc lies inside a finite-position polygonal frame,
whereas the middle of the auxiliary return path lies outside.  Ordered
transverse crossings therefore occur an odd number of times on the first
endpoint tail.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- The crossings before the first middle parameter have odd cardinality.
This is the linear parity half of Moise's cyclic pairing argument. -/
theorem odd_firstTail_crossingTimes
    (A : J.AccessibleAngularArc) (Q : PolygonalCircle)
    {s t : unitInterval}
    (hspos : (⊥ : unitInterval) < s) (hst : s < t)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hMiddleExterior : A.returnPath '' Icc s t ⊆ Q.exteriorRegion)
    (T : Finset unitInterval)
    (hT : ∀ u, u ∈ T ↔ A.returnPath u ∈ Q.carrier)
    (hordered : ∀ u ∈ T,
      (⊥ : unitInterval) < u ∧ u < (⊤ : unitInterval) ∧
      ∀ a b : unitInterval, a < u → u < b →
        ∃ l v : unitInterval,
          a < l ∧ l < u ∧ u < v ∧ v < b ∧
          (((A.returnPath l ∈ Q.interiorRegion) ∧
              (A.returnPath v ∈ Q.exteriorRegion)) ∨
            ((A.returnPath l ∈ Q.exteriorRegion) ∧
              (A.returnPath v ∈ Q.interiorRegion)))) :
    Odd ((T.filter fun u => u < s).card) := by
  classical
  let firstT : Finset unitInterval := T.filter fun u => u < s
  let side : unitInterval → Bool := fun u =>
    decide (A.returnPath u ∈ Q.interiorRegion)
  have hzeroInside : A.returnPath (⊥ : unitInterval) ∈ Q.interiorRegion := by
    change A.returnPath (0 : unitInterval) ∈ Q.interiorRegion
    rw [A.returnPath.source]
    exact hArcInside A.right_mem_curveArcPlane
  have hsExterior : A.returnPath s ∈ Q.exteriorRegion := by
    apply hMiddleExterior
    exact ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩
  have hsNotCarrier : A.returnPath s ∉ Q.carrier := by
    intro hsCarrier
    exact Set.disjoint_left.mp Q.disjoint_carrier_exteriorRegion
      hsCarrier hsExterior
  have hsNotInside : A.returnPath s ∉ Q.interiorRegion := by
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
        A.returnPath u ∉ Q.toJordanCircle.carrier := by
      intro u huInterval huCarrierJordan
      have huCarrier : A.returnPath u ∈ Q.carrier := by
        rwa [Q.carrier_toJordanCircle] at huCarrierJordan
      have huT : u ∈ T := (hT u).mpr huCarrier
      have huLeS : u ≤ s := huInterval.2.trans hys
      have huNeS : u ≠ s := by
        intro hus
        subst u
        exact hsNotCarrier huCarrier
      have huLtS : u < s := lt_of_le_of_ne huLeS huNeS
      have huFirst : u ∈ firstT := Finset.mem_filter.mpr ⟨huT, huLtS⟩
      exact hfree u huFirst huInterval
    rcases Q.toJordanCircle.interval_image_same_side A.returnPath.continuous
        hxy havoid with hinside | houtside
    · have hxInside : A.returnPath x ∈ Q.interiorRegion := by
        simpa only [Q.inside_toJordanCircle] using hinside.1
      have hyInside : A.returnPath y ∈ Q.interiorRegion := by
        simpa only [Q.inside_toJordanCircle] using hinside.2
      simp only [side, hxInside, hyInside, decide_true]
    · have hxOutside : A.returnPath x ∈ Q.exteriorRegion := by
        simpa only [Q.outside_toJordanCircle] using houtside.1
      have hyOutside : A.returnPath y ∈ Q.exteriorRegion := by
        simpa only [Q.outside_toJordanCircle] using houtside.2
      have hxNotInside : A.returnPath x ∉ Q.interiorRegion := by
        intro hxInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hxInside hxOutside
      have hyNotInside : A.returnPath y ∉ Q.interiorRegion := by
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
    · have hvNotInside : A.returnPath v ∉ Q.interiorRegion := by
        intro hvInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hvInside hsides.2
      simp only [side, hsides.1, decide_true, hvNotInside, decide_false]
      decide
    · have hlNotInside : A.returnPath l ∉ Q.interiorRegion := by
        intro hlInside
        exact Set.disjoint_left.mp Q.disjoint_interior_exterior
          hlInside hsides.1
      simp only [side, hlNotInside, decide_false, hsides.2, decide_true]
      decide
  · exact hend

/-- Generic position supplies ordered crossing times, and the endpoint/middle
side information immediately upgrades their first-tail subset to odd
cardinality. -/
theorem exists_ordered_crossingTimes_odd_firstTail
    (A : J.AccessibleAngularArc) (Q : PolygonalCircle)
    {s t : unitInterval}
    (hspos : (⊥ : unitInterval) < s) (hst : s < t)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hMiddleExterior : A.returnPath '' Icc s t ⊆ Q.exteriorRegion)
    (hfinite : (Q.carrier ∩ range A.returnPath).Finite)
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
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0) :
    ∃ T : Finset unitInterval,
      (∀ u, u ∈ T ↔ A.returnPath u ∈ Q.carrier) ∧
      (∀ u ∈ T,
        (⊥ : unitInterval) < u ∧ u < (⊤ : unitInterval) ∧
        ∀ a b : unitInterval, a < u → u < b →
          ∃ l v : unitInterval,
            a < l ∧ l < u ∧ u < v ∧ v < b ∧
            (((A.returnPath l ∈ Q.interiorRegion) ∧
                (A.returnPath v ∈ Q.exteriorRegion)) ∨
              ((A.returnPath l ∈ Q.exteriorRegion) ∧
                (A.returnPath v ∈ Q.interiorRegion)))) ∧
      Odd ((T.filter fun u => u < s).card) := by
  obtain ⟨T, hT, hordered⟩ :=
    A.exists_ordered_returnPath_crossingTimes Q hArcInside hfinite
      hpolygonVertices hbrokenVertices
  exact ⟨T, hT, hordered,
    A.odd_firstTail_crossingTimes Q hspos hst hArcInside
      hMiddleExterior T hT hordered⟩

end AccessibleAngularArc
end JordanCircle

end Schoenflies
