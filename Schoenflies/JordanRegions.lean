import JordanCurve

/-!
# The two regions of a Jordan curve

This file packages the consequences of the Jordan curve theorem needed by the
Schoenflies construction.  For a parametrized Jordan circle it chooses the
bounded and unbounded complementary components and proves that they partition
the complement and have the curve as their common frontier.
-/

namespace Schoenflies

open Metric Set Function Bornology

/-- The plane used throughout this development. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A Jordan circle together with its chosen parametrization. -/
structure JordanCircle where
  parametrization : sphere (0 : Plane) 1 → Plane
  continuous : Continuous parametrization
  injective : Injective parametrization

namespace JordanCircle

variable (J : JordanCircle)

/-- The point-set image of a parametrized Jordan circle. -/
def carrier : Set Plane := range J.parametrization

/-- The parametrization, regarded as a homeomorphism onto the curve. -/
noncomputable def carrierHomeomorph : sphere (0 : Plane) 1 ≃ₜ J.carrier :=
  JordanCurve.jordanCurveHomeo J.parametrization J.continuous J.injective

/-- A chosen point in the bounded complementary component. -/
noncomputable def insidePoint : Plane :=
  (JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT
    J.continuous J.injective).choose

theorem insidePoint_mem : J.insidePoint ∈ J.carrierᶜ :=
  (JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT
    J.continuous J.injective).choose_spec.1

/-- The bounded complementary component of the curve. -/
noncomputable def inside : Set Plane :=
  connectedComponentIn J.carrierᶜ J.insidePoint

theorem inside_bounded : IsBounded J.inside :=
  (JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT
    J.continuous J.injective).choose_spec.2

/-- A chosen point in the unbounded complementary component. -/
noncomputable def outsidePoint : Plane :=
  (JordanCurve.exists_unbounded_component J.parametrization J.continuous).choose

theorem outsidePoint_mem : J.outsidePoint ∈ J.carrierᶜ :=
  (JordanCurve.exists_unbounded_component J.parametrization J.continuous).choose_spec.1

/-- The unbounded complementary component of the curve. -/
noncomputable def outside : Set Plane :=
  connectedComponentIn J.carrierᶜ J.outsidePoint

theorem outside_unbounded : ¬ IsBounded J.outside :=
  (JordanCurve.exists_unbounded_component J.parametrization J.continuous).choose_spec.2

theorem insidePoint_mem_inside : J.insidePoint ∈ J.inside :=
  mem_connectedComponentIn J.insidePoint_mem

theorem outsidePoint_mem_outside : J.outsidePoint ∈ J.outside :=
  mem_connectedComponentIn J.outsidePoint_mem

theorem inside_subset_compl : J.inside ⊆ J.carrierᶜ :=
  connectedComponentIn_subset _ _

theorem outside_subset_compl : J.outside ⊆ J.carrierᶜ :=
  connectedComponentIn_subset _ _

theorem inside_isOpen : IsOpen J.inside :=
  JordanCurve.isOpen_component J.parametrization J.continuous J.insidePoint

theorem outside_isOpen : IsOpen J.outside :=
  JordanCurve.isOpen_component J.parametrization J.continuous J.outsidePoint

theorem inside_isConnected : IsConnected J.inside :=
  isConnected_connectedComponentIn_iff.mpr J.insidePoint_mem

theorem outside_isConnected : IsConnected J.outside :=
  isConnected_connectedComponentIn_iff.mpr J.outsidePoint_mem

theorem inside_ne_outside : J.inside ≠ J.outside := by
  intro h
  apply J.outside_unbounded
  simpa [h] using J.inside_bounded

theorem inside_disjoint_outside : Disjoint J.inside J.outside := by
  rw [Set.disjoint_left]
  intro x hxI hxO
  apply J.inside_ne_outside
  exact (connectedComponentIn_eq hxI).trans (connectedComponentIn_eq hxO).symm

/-- Every point off the curve lies in the bounded or the unbounded component. -/
theorem mem_inside_or_outside {x : Plane} (hx : x ∈ J.carrierᶜ) :
    x ∈ J.inside ∨ x ∈ J.outside := by
  by_cases hb : IsBounded (connectedComponentIn J.carrierᶜ x)
  · left
    have h := JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT
      J.continuous J.injective x hx J.insidePoint J.insidePoint_mem hb J.inside_bounded
    have hmem : x ∈ connectedComponentIn J.carrierᶜ x := mem_connectedComponentIn hx
    simp only [carrier] at hmem
    rw [h] at hmem
    exact hmem
  · right
    have h := JordanCurve.unbounded_component_unique J.parametrization J.continuous
      hb J.outside_unbounded
    have hmem : x ∈ connectedComponentIn J.carrierᶜ x := mem_connectedComponentIn hx
    simp only [carrier] at hmem
    rw [h] at hmem
    exact hmem

theorem inside_union_outside : J.inside ∪ J.outside = J.carrierᶜ := by
  apply Set.Subset.antisymm
  · exact union_subset J.inside_subset_compl J.outside_subset_compl
  · intro x hx
    simpa [mem_union] using J.mem_inside_or_outside hx

theorem frontier_inside : frontier J.inside = J.carrier := by
  apply JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT
    J.continuous J.injective J.insidePoint_mem
  exact ⟨J.outsidePoint, J.outsidePoint_mem, J.inside_ne_outside.symm⟩

theorem frontier_outside : frontier J.outside = J.carrier := by
  apply JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT
    J.continuous J.injective J.outsidePoint_mem
  exact ⟨J.insidePoint, J.insidePoint_mem, J.inside_ne_outside⟩

theorem closure_inside : closure J.inside = J.inside ∪ J.carrier := by
  rw [closure_eq_self_union_frontier, J.frontier_inside]

theorem closure_outside : closure J.outside = J.outside ∪ J.carrier := by
  rw [closure_eq_self_union_frontier, J.frontier_outside]

end JordanCircle

end Schoenflies
