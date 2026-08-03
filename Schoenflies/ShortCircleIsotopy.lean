import Schoenflies.StandardRadialCollars
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue

/-!
# The short isotopy of a circle homeomorphism

If a self-homeomorphism of the circle never sends a point to its antipode,
the principal argument of its angular displacement is continuous.  Its lift
to the real line is strictly increasing, and linear interpolation of that
lift with the identity therefore descends to an isotopy through circle
homeomorphisms.  This is the controlled annular Alexander trick needed by
the shrinking Schoenflies construction.
-/

namespace Schoenflies

open Metric Set Function Filter

noncomputable section

namespace Circle

/-- The multiplicative angular displacement of a circle self-map. -/
def angularDifference (q : Circle ≃ₜ Circle) (z : Circle) : Circle :=
  z⁻¹ * q z

/-- The principal real-valued angular displacement. -/
def shortDisplacement (q : Circle ≃ₜ Circle) (z : Circle) : ℝ :=
  Complex.arg (angularDifference q z : ℂ)

/-- The real lift selected by the principal displacement. -/
def shortLift (q : Circle ≃ₜ Circle) (x : ℝ) : ℝ :=
  x + shortDisplacement q (Circle.exp x)

/-- Linear interpolation of the selected lift with the identity.  At
`t = 0` this is the lift of `q`; at `t = 1` it is the identity. -/
def interpolatedLift (q : Circle ≃ₜ Circle) (t : unitInterval) (x : ℝ) : ℝ :=
  (1 - (t : ℝ)) * shortLift q x + (t : ℝ) * x

/-- The corresponding formula directly on the circle. -/
def shortInterpolationMap (q : Circle ≃ₜ Circle)
    (t : unitInterval) (z : Circle) : Circle :=
  z * Circle.exp ((1 - (t : ℝ)) * shortDisplacement q z)

variable (q : Circle ≃ₜ Circle)
  (hshort : ∀ z : Circle, q z ≠ -z)

include hshort

theorem angularDifference_ne_neg_one (z : Circle) :
    angularDifference q z ≠ -1 := by
  intro h
  have := congrArg (fun w : Circle => z * w) h
  apply hshort z
  simpa [angularDifference, mul_assoc] using this

theorem angularDifference_mem_slitPlane (z : Circle) :
    (angularDifference q z : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  constructor
  · intro harg
    apply angularDifference_ne_neg_one q hshort z
    apply Circle.injective_arg
    simpa using harg
  · exact (angularDifference q z).coe_ne_zero

theorem continuous_shortDisplacement :
    Continuous (shortDisplacement q) := by
  have hdiff : Continuous (angularDifference q) := by
    unfold angularDifference
    exact continuous_inv.mul q.continuous
  rw [continuous_iff_continuousAt]
  intro z
  change ContinuousAt
    (Complex.arg ∘ (fun z : Circle => (angularDifference q z : ℂ))) z
  have harg : ContinuousAt (fun w : Circle => Complex.arg (w : ℂ))
      (angularDifference q z) :=
    (Complex.continuousAt_arg
      (angularDifference_mem_slitPlane q hshort z)).comp
        continuous_subtype_val.continuousAt
  exact harg.comp hdiff.continuousAt

theorem continuous_shortLift : Continuous (shortLift q) := by
  unfold shortLift
  exact continuous_id.add
    ((continuous_shortDisplacement q hshort).comp Circle.exp.continuous)

omit hshort in theorem exp_shortLift (x : ℝ) :
    Circle.exp (shortLift q x) = q (Circle.exp x) := by
  rw [shortLift, Circle.exp_add]
  rw [show Circle.exp (shortDisplacement q (Circle.exp x)) =
      angularDifference q (Circle.exp x) by
    exact Circle.exp_arg _]
  simp [angularDifference]

omit hshort in theorem shortDisplacement_exp_add_two_pi (x : ℝ) :
    shortDisplacement q (Circle.exp (x + 2 * Real.pi)) =
      shortDisplacement q (Circle.exp x) := by
  rw [Circle.exp_add_two_pi]

omit hshort in theorem shortLift_add_two_pi (x : ℝ) :
    shortLift q (x + 2 * Real.pi) = shortLift q x + 2 * Real.pi := by
  rw [shortLift, shortLift, shortDisplacement_exp_add_two_pi]
  ring

omit hshort in theorem injective_shortLift : Injective (shortLift q) := by
  intro x y hxy
  have hexp : Circle.exp x = Circle.exp y := by
    apply q.injective
    rw [← exp_shortLift q x, ← exp_shortLift q y, hxy]
  have hdisp : shortDisplacement q (Circle.exp x) =
      shortDisplacement q (Circle.exp y) := by rw [hexp]
  unfold shortLift at hxy
  linarith

theorem strictMono_shortLift : StrictMono (shortLift q) := by
  rcases (continuous_shortLift q hshort).strictMono_of_inj
      (injective_shortLift q) with hmono | hanti
  · exact hmono
  · exfalso
    have h := hanti Real.two_pi_pos
    have hper := shortLift_add_two_pi q 0
    rw [zero_add] at hper
    rw [hper] at h
    linarith [Real.pi_pos]

theorem continuous_interpolatedLift (t : unitInterval) :
    Continuous (interpolatedLift q t) := by
  unfold interpolatedLift
  exact continuous_const.mul (continuous_shortLift q hshort) |>.add
    (continuous_const.mul continuous_id)

theorem strictMono_interpolatedLift (t : unitInterval) :
    StrictMono (interpolatedLift q t) := by
  intro x y hxy
  have hq := strictMono_shortLift q hshort hxy
  by_cases ht : (t : ℝ) = 0
  · simpa [interpolatedLift, ht] using hq
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    unfold interpolatedLift
    exact add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left hq.le (sub_nonneg.mpr t.2.2))
      (mul_lt_mul_of_pos_left hxy htpos)

omit hshort in theorem interpolatedLift_add_two_pi (t : unitInterval) (x : ℝ) :
    interpolatedLift q t (x + 2 * Real.pi) =
      interpolatedLift q t x + 2 * Real.pi := by
  rw [interpolatedLift, interpolatedLift,
    shortLift_add_two_pi]
  ring

omit hshort in theorem interpolatedLift_add_int_mul_two_pi
    (t : unitInterval) (x : ℝ) (k : ℤ) :
    interpolatedLift q t (x + (k : ℝ) * (2 * Real.pi)) =
      interpolatedLift q t x + (k : ℝ) * (2 * Real.pi) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      push_cast at ih ⊢
      calc
        interpolatedLift q t (x + ((k : ℝ) + 1) * (2 * Real.pi)) =
            interpolatedLift q t
              ((x + (k : ℝ) * (2 * Real.pi)) + 2 * Real.pi) := by
                congr 1
                ring
        _ = interpolatedLift q t (x + (k : ℝ) * (2 * Real.pi)) +
              2 * Real.pi := interpolatedLift_add_two_pi q t _
        _ = interpolatedLift q t x + ((k : ℝ) + 1) *
              (2 * Real.pi) := by rw [ih]; ring
  | pred k ih =>
      push_cast at ih ⊢
      let a := x + (-(k : ℝ) - 1) * (2 * Real.pi)
      have hstep := interpolatedLift_add_two_pi q t a
      have ha : a + 2 * Real.pi = x + -(k : ℝ) * (2 * Real.pi) := by
        dsimp [a]
        ring
      calc
        interpolatedLift q t (x + (-(k : ℝ) - 1) * (2 * Real.pi)) =
            interpolatedLift q t a := rfl
        _ = interpolatedLift q t (a + 2 * Real.pi) - 2 * Real.pi := by
              linarith
        _ = interpolatedLift q t (x + -(k : ℝ) * (2 * Real.pi)) -
              2 * Real.pi := by rw [ha]
        _ = interpolatedLift q t x + (-(k : ℝ) - 1) *
              (2 * Real.pi) := by rw [ih]; ring

omit hshort in theorem interpolatedLift_lower_bound (t : unitInterval) (x : ℝ) :
    x - Real.pi ≤ interpolatedLift q t x := by
  have harg := Complex.neg_pi_lt_arg
    (angularDifference q (Circle.exp x) : ℂ)
  have hcoef : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have hcoef_le : 1 - (t : ℝ) ≤ 1 := by linarith [t.2.1]
  have hmul₁ := mul_nonneg hcoef (sub_nonneg.mpr harg.le)
  have hmul₂ := mul_nonneg (sub_nonneg.mpr hcoef_le) Real.pi_pos.le
  unfold interpolatedLift shortLift shortDisplacement
  nlinarith

omit hshort in theorem interpolatedLift_upper_bound (t : unitInterval) (x : ℝ) :
    interpolatedLift q t x ≤ x + Real.pi := by
  have harg := Complex.arg_le_pi
    (angularDifference q (Circle.exp x) : ℂ)
  have hcoef : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  have hcoef_le : 1 - (t : ℝ) ≤ 1 := by linarith [t.2.1]
  have hmul₁ := mul_nonneg hcoef (sub_nonneg.mpr harg)
  have hmul₂ := mul_nonneg (sub_nonneg.mpr hcoef_le) Real.pi_pos.le
  unfold interpolatedLift shortLift shortDisplacement
  nlinarith

theorem surjective_interpolatedLift (t : unitInterval) :
    Surjective (interpolatedLift q t) := by
  apply (continuous_interpolatedLift q hshort t).surjective
  · apply tendsto_atTop_mono (interpolatedLift_lower_bound q t)
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-Real.pi) tendsto_id
  · apply tendsto_atBot_mono (interpolatedLift_upper_bound q t)
    exact tendsto_atBot_add_const_right atBot Real.pi tendsto_id

/-- The interpolated lift as an increasing homeomorphism of the real line. -/
def interpolatedLiftHomeomorph (t : unitInterval) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (interpolatedLift q t)
    (strictMono_interpolatedLift q hshort t)
    (surjective_interpolatedLift q hshort t)).toHomeomorph

omit hshort in theorem shortInterpolationMap_exp (t : unitInterval) (x : ℝ) :
    shortInterpolationMap q t (Circle.exp x) =
      Circle.exp (interpolatedLift q t x) := by
  unfold shortInterpolationMap
  rw [show interpolatedLift q t x =
      x + (1 - (t : ℝ)) * shortDisplacement q (Circle.exp x) by
    unfold interpolatedLift shortLift
    ring]
  exact (Circle.exp_add _ _).symm

theorem continuous_shortInterpolationMap :
    Continuous (fun p : unitInterval × Circle =>
      shortInterpolationMap q p.1 p.2) := by
  apply continuous_induced_rng.mpr
  unfold shortInterpolationMap
  have hexp : Continuous (fun p : unitInterval × Circle =>
      Circle.exp ((1 - (p.1 : ℝ)) * shortDisplacement q p.2)) :=
    Circle.exp.continuous.comp <|
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul <|
        (continuous_shortDisplacement q hshort).comp continuous_snd
  exact (continuous_subtype_val.comp continuous_snd).mul
    (continuous_subtype_val.comp hexp)

theorem bijective_shortInterpolationMap (t : unitInterval) :
    Bijective (shortInterpolationMap q t) := by
  constructor
  · intro z w hzw
    obtain ⟨x, rfl⟩ := Circle.exp_surjective z
    obtain ⟨y, rfl⟩ := Circle.exp_surjective w
    rw [shortInterpolationMap_exp q t,
      shortInterpolationMap_exp q t] at hzw
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hzw
    have hperiod := interpolatedLift_add_int_mul_two_pi q t y k
    have hxy : x = y + (k : ℝ) * (2 * Real.pi) :=
      (strictMono_interpolatedLift q hshort t).injective
        (hk.trans hperiod.symm)
    exact Circle.exp_eq_exp.mpr ⟨k, hxy⟩
  · intro z
    obtain ⟨y, rfl⟩ := Circle.exp_surjective z
    obtain ⟨x, hx⟩ := surjective_interpolatedLift q hshort t y
    exact ⟨Circle.exp x, by
      rw [shortInterpolationMap_exp q t, hx]⟩

/-- The short interpolation at a fixed time, bundled as a homeomorphism. -/
def shortInterpolation (t : unitInterval) : Circle ≃ₜ Circle := by
  let e : Circle ≃ Circle := Equiv.ofBijective
    (shortInterpolationMap q t)
    (bijective_shortInterpolationMap q hshort t)
  exact Continuous.homeoOfEquivCompactToT2 (f := e) <| by
    have h := continuous_shortInterpolationMap q hshort
    exact h.comp (continuous_const.prodMk continuous_id)

@[simp] theorem shortInterpolation_apply (t : unitInterval) (z : Circle) :
    shortInterpolation q hshort t z = shortInterpolationMap q t z := rfl

@[simp] theorem shortInterpolation_zero (z : Circle) :
    shortInterpolation q hshort 0 z = q z := by
  rw [shortInterpolation_apply]
  unfold shortInterpolationMap
  change z * Circle.exp ((1 - (0 : ℝ)) * shortDisplacement q z) = q z
  norm_num
  rw [show Circle.exp (shortDisplacement q z) = angularDifference q z by
    exact Circle.exp_arg _]
  simp [angularDifference]

@[simp] theorem shortInterpolation_one (z : Circle) :
    shortInterpolation q hshort 1 z = z := by
  rw [shortInterpolation_apply]
  unfold shortInterpolationMap
  simp

end Circle

end

end Schoenflies
