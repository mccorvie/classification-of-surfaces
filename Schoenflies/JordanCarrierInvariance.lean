import Schoenflies.JordanRegions

/-!
# Complementary regions depend only on the Jordan carrier

The Jordan-curve input is parametrized, while polygonal cell fillings are
indexed by a finite polygon having the same point-set carrier.  The bounded
and unbounded complementary components are independent of that choice of
parametrization.
-/

namespace Schoenflies

open Set Function Bornology

namespace JordanCircle

/-- Two Jordan circles with the same carrier have the same bounded region. -/
theorem inside_eq_of_carrier_eq (J K : JordanCircle)
    (hcarrier : J.carrier = K.carrier) :
    J.inside = K.inside := by
  have hx : J.insidePoint ∈ K.carrierᶜ := by
    rw [← hcarrier]
    exact J.insidePoint_mem
  have hbounded :
      IsBounded (connectedComponentIn K.carrierᶜ J.insidePoint) := by
    rw [← hcarrier]
    exact J.inside_bounded
  have hcomponents :=
    JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT
      K.continuous K.injective J.insidePoint hx
      K.insidePoint K.insidePoint_mem hbounded K.inside_bounded
  change connectedComponentIn J.carrierᶜ J.insidePoint =
    connectedComponentIn K.carrierᶜ K.insidePoint
  rw [hcarrier]
  exact hcomponents

/-- Two Jordan circles with the same carrier have the same unbounded region. -/
theorem outside_eq_of_carrier_eq (J K : JordanCircle)
    (hcarrier : J.carrier = K.carrier) :
    J.outside = K.outside := by
  have hinside := J.inside_eq_of_carrier_eq K hcarrier
  apply Set.Subset.antisymm
  · intro x hxJ
    have hxCompl : x ∈ K.carrierᶜ := by
      rw [← hcarrier]
      exact J.outside_subset_compl hxJ
    rcases K.mem_inside_or_outside hxCompl with hxK | hxK
    · exact False.elim <| Set.disjoint_left.mp J.inside_disjoint_outside
        (hinside ▸ hxK) hxJ
    · exact hxK
  · intro x hxK
    have hxCompl : x ∈ J.carrierᶜ := by
      rw [hcarrier]
      exact K.outside_subset_compl hxK
    rcases J.mem_inside_or_outside hxCompl with hxJ | hxJ
    · exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
        (hinside ▸ hxJ) hxK
    · exact hxJ

end JordanCircle

end Schoenflies
