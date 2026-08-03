import Schoenflies.ShortCircleIsotopy
import Schoenflies.AngularDriftBounds

/-!
# A boundary correction damped across one standard shell

The short circle isotopy is applied in polar coordinates.  The resulting
annulus homeomorphism realizes a prescribed short correction on its inner
boundary and is exactly the identity on its outer boundary.  Conjugating by
the simultaneous triangle gauge gives the corresponding operation on the
standard polygonal shells.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace SphereShortIsotopy

/-- The antipode on the standard Euclidean unit sphere. -/
def antipode (u : sphere (0 : Plane) 1) : sphere (0 : Plane) 1 :=
  ⟨-(u : Plane), by
    rw [mem_sphere, dist_zero_right, norm_neg]
    simpa only [mem_sphere, dist_zero_right] using u.2⟩

@[simp] theorem antipode_val (u : sphere (0 : Plane) 1) :
    (antipode u : Plane) = -(u : Plane) := rfl

/-- Conjugate a unit-sphere map to Mathlib's complex unit circle. -/
def toCircle (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1) :
    Circle ≃ₜ Circle :=
  JordanCurve.Arcs.circleHomeoSphere.trans <|
    q.trans JordanCurve.Arcs.circleHomeoSphere.symm

theorem circleHomeoSphere_neg (z : Circle) :
    JordanCurve.Arcs.circleHomeoSphere (-z) =
      antipode (JordanCurve.Arcs.circleHomeoSphere z) := by
  apply Subtype.ext
  simp only [JordanCurve.Arcs.circleHomeoSphere_coe, antipode_val]
  exact JordanCurve.Arcs.complexLIE.map_neg (z : ℂ)

theorem toCircle_ne_neg
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u) (z : Circle) :
    toCircle q z ≠ -z := by
  intro h
  have h' := congrArg JordanCurve.Arcs.circleHomeoSphere h
  simp only [toCircle, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply] at h'
  rw [circleHomeoSphere_neg] at h'
  exact hshort _ h'

/-- The short isotopy transported to the real Euclidean unit sphere. -/
def interpolation
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u) (t : unitInterval) :
    sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
  JordanCurve.Arcs.circleHomeoSphere.symm.trans <|
    (Circle.shortInterpolation (toCircle q) (toCircle_ne_neg q hshort) t).trans
      JordanCurve.Arcs.circleHomeoSphere

theorem interpolation_apply
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u) (t : unitInterval)
    (u : sphere (0 : Plane) 1) :
    interpolation q hshort t u =
      JordanCurve.Arcs.circleHomeoSphere
        (Circle.shortInterpolationMap (toCircle q) t
          (JordanCurve.Arcs.circleHomeoSphere.symm u)) := by
  rfl

theorem continuous_interpolation_apply
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u) :
    Continuous (fun p : unitInterval × sphere (0 : Plane) 1 =>
      interpolation q hshort p.1 p.2) := by
  apply JordanCurve.Arcs.circleHomeoSphere.continuous.comp
  have h := Circle.continuous_shortInterpolationMap
    (toCircle q) (toCircle_ne_neg q hshort)
  exact h.comp <| continuous_fst.prodMk <|
    JordanCurve.Arcs.circleHomeoSphere.symm.continuous.comp continuous_snd

@[simp] theorem interpolation_zero
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u)
    (u : sphere (0 : Plane) 1) :
    interpolation q hshort 0 u = q u := by
  rw [interpolation_apply]
  rw [← Circle.shortInterpolation_apply (toCircle q)
    (toCircle_ne_neg q hshort)]
  rw [Circle.shortInterpolation_zero]
  simp [toCircle]

@[simp] theorem interpolation_one
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ antipode u)
    (u : sphere (0 : Plane) 1) :
    interpolation q hshort 1 u = u := by
  rw [interpolation_apply]
  rw [← Circle.shortInterpolation_apply (toCircle q)
    (toCircle_ne_neg q hshort)]
  rw [Circle.shortInterpolation_one]
  simp

theorem dist_antipode_self (u : sphere (0 : Plane) 1) :
    dist (antipode u) u = 2 := by
  change dist (-(u : Plane)) (u : Plane) = 2
  rw [dist_eq_norm]
  have hu : ‖(u : Plane)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.2
  rw [show -(u : Plane) - (u : Plane) = (-2 : ℝ) • (u : Plane) by
    module]
  rw [norm_smul, hu, mul_one, Real.norm_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
  norm_num

theorem ne_antipode_of_dist_lt_two
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (h : ∀ u, dist (q u) u < 2) : ∀ u, q u ≠ antipode u := by
  intro u hu
  have := h u
  rw [hu, dist_antipode_self] at this
  exact (lt_irrefl 2 this)

end SphereShortIsotopy

namespace DampedAnnulus

/-- Polar coordinates on a closed round shell bounded away from the origin. -/
def polarHomeomorph (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    StandardPolygonalCollars.roundClosedShell r s ≃ₜ
      sphere (0 : Plane) 1 × Icc r s where
  toFun x := by
    have hnormLe : ‖(x : Plane)‖ ≤ s := by
      simpa only [StandardPolygonalCollars.roundClosedShell, mem_diff,
        mem_closedBall, dist_zero_right] using x.2.1
    have hrLeNorm : r ≤ ‖(x : Plane)‖ := by
      exact le_of_not_gt fun hlt => x.2.2 <| by
        simpa only [mem_ball, dist_zero_right] using hlt
    have hnormPos : 0 < ‖(x : Plane)‖ := hr.trans_le hrLeNorm
    exact (⟨‖(x : Plane)‖⁻¹ • (x : Plane), by
      rw [mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hnormPos,
        inv_mul_cancel₀ hnormPos.ne']⟩,
      ⟨‖(x : Plane)‖, hrLeNorm, hnormLe⟩)
  invFun p := ⟨(p.2 : ℝ) • (p.1 : Plane), by
    have hpNorm : ‖(p.1 : Plane)‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using p.1.2
    have hpPos : 0 < (p.2 : ℝ) := hr.trans_le p.2.2.1
    constructor
    · rw [mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hpPos.le, hpNorm, mul_one]
      exact p.2.2.2
    · intro hball
      rw [mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hpPos.le, hpNorm, mul_one] at hball
      exact (not_lt_of_ge p.2.2.1) hball⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    have hrLeNorm : r ≤ ‖(x : Plane)‖ := by
      exact le_of_not_gt fun hlt => x.2.2 <| by
        simpa only [mem_ball, dist_zero_right] using hlt
    have hnormNe : ‖(x : Plane)‖ ≠ 0 := (hr.trans_le hrLeNorm).ne'
    rw [smul_smul, mul_inv_cancel₀ hnormNe, one_smul]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      have hpNorm : ‖(p.1 : Plane)‖ = 1 := by
        simpa only [mem_sphere, dist_zero_right] using p.1.2
      have hpPos : 0 < (p.2 : ℝ) := hr.trans_le p.2.2.1
      rw [norm_smul, Real.norm_of_nonneg hpPos.le, hpNorm, mul_one,
        smul_smul, inv_mul_cancel₀ hpPos.ne', one_smul]
    · apply Subtype.ext
      dsimp only
      have hpNorm : ‖(p.1 : Plane)‖ = 1 := by
        simpa only [mem_sphere, dist_zero_right] using p.1.2
      have hpPos : 0 < (p.2 : ℝ) := hr.trans_le p.2.2.1
      rw [norm_smul, Real.norm_of_nonneg hpPos.le, hpNorm, mul_one]
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      exact (continuous_norm.comp continuous_subtype_val).inv₀
        (fun x hx => by
          have hrLeNorm : r ≤ ‖(x : Plane)‖ := by
            exact le_of_not_gt fun hlt => x.2.2 <| by
              simpa only [mem_ball, dist_zero_right] using hlt
          exact (hr.trans_le hrLeNorm).ne' hx) |>.smul continuous_subtype_val
    · exact (continuous_norm.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

/-- Normalize a shell radius to the unit interval. -/
def shellTime (r s : ℝ) (hrs : r < s) (x : Icc r s) : unitInterval :=
  ⟨((x : ℝ) - r) / (s - r), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr x.2.1) (sub_nonneg.mpr hrs.le)
    · rw [div_le_one (sub_pos.mpr hrs)]
      linarith [x.2.2]⟩

theorem continuous_shellTime (r s : ℝ) (hrs : r < s) :
    Continuous (shellTime r s hrs) := by
  apply continuous_induced_rng.mpr
  unfold shellTime
  fun_prop

@[simp] theorem shellTime_left (r s : ℝ) (hrs : r < s) :
    shellTime r s hrs ⟨r, le_rfl, hrs.le⟩ = 0 := by
  apply Subtype.ext
  simp [shellTime]

@[simp] theorem shellTime_right (r s : ℝ) (hrs : r < s) :
    shellTime r s hrs ⟨s, hrs.le, le_rfl⟩ = 1 := by
  apply Subtype.ext
  change (s - r) / (s - r) = 1
  exact div_self (sub_ne_zero.mpr hrs.ne')

/-- The polar-coordinate formula for damping `q` to the identity. -/
def polarMap
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hrs : r < s)
    (p : sphere (0 : Plane) 1 × Icc r s) :
    sphere (0 : Plane) 1 × Icc r s :=
  (SphereShortIsotopy.interpolation q hshort (shellTime r s hrs p.2) p.1,
    p.2)

set_option maxHeartbeats 800000 in
theorem continuous_polarMap
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hrs : r < s) :
    Continuous (polarMap q hshort r s hrs) := by
  change Continuous (fun p : sphere (0 : Plane) 1 × Icc r s =>
    (SphereShortIsotopy.interpolation q hshort
      (shellTime r s hrs p.2) p.1, p.2))
  apply Continuous.prodMk
  · have ht : Continuous (fun p : sphere (0 : Plane) 1 × Icc r s =>
        shellTime r s hrs p.2) :=
      (continuous_shellTime r s hrs).comp continuous_snd
    have hp : Continuous (fun p : sphere (0 : Plane) 1 × Icc r s =>
        (shellTime r s hrs p.2, p.1)) := ht.prodMk continuous_fst
    change Continuous
      ((fun p : unitInterval × sphere (0 : Plane) 1 =>
          SphereShortIsotopy.interpolation q hshort p.1 p.2) ∘
        (fun p : sphere (0 : Plane) 1 × Icc r s =>
          (shellTime r s hrs p.2, p.1)))
    exact (SphereShortIsotopy.continuous_interpolation_apply q hshort).comp hp
  · exact continuous_snd

theorem bijective_polarMap
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hrs : r < s) :
    Bijective (polarMap q hshort r s hrs) := by
  let inv : sphere (0 : Plane) 1 × Icc r s →
      sphere (0 : Plane) 1 × Icc r s := fun p =>
    ((SphereShortIsotopy.interpolation q hshort
      (shellTime r s hrs p.2)).symm p.1, p.2)
  refine ⟨?_, ?_⟩
  · exact (show LeftInverse inv (polarMap q hshort r s hrs) by
      intro p
      apply Prod.ext
      · exact (SphereShortIsotopy.interpolation q hshort
          (shellTime r s hrs p.2)).symm_apply_apply p.1
      · rfl).injective
  · exact (show RightInverse inv (polarMap q hshort r s hrs) by
      intro p
      apply Prod.ext
      · exact (SphereShortIsotopy.interpolation q hshort
          (shellTime r s hrs p.2)).apply_symm_apply p.1
      · rfl).surjective

/-- The damped angular correction as a homeomorphism in polar coordinates. -/
def polarHomeomorphAdjustment
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hrs : r < s) :
    sphere (0 : Plane) 1 × Icc r s ≃ₜ
      sphere (0 : Plane) 1 × Icc r s := by
  let e := Equiv.ofBijective (polarMap q hshort r s hrs)
    (bijective_polarMap q hshort r s hrs)
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (continuous_polarMap q hshort r s hrs)

@[simp] theorem polarHomeomorphAdjustment_apply
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hrs : r < s)
    (p : sphere (0 : Plane) 1 × Icc r s) :
    polarHomeomorphAdjustment q hshort r s hrs p =
      polarMap q hshort r s hrs p := rfl

/-- Regard the inner round sphere as the inner boundary of a round shell. -/
def innerSphereInRoundShell (r s : ℝ) (hrs : r ≤ s)
    (y : sphere (0 : Plane) r) :
    StandardPolygonalCollars.roundClosedShell r s :=
  ⟨y, by
    have hy : ‖(y : Plane)‖ = r := by
      simpa only [mem_sphere, dist_zero_right] using y.2
    constructor
    · simpa only [mem_closedBall, dist_zero_right, hy] using hrs
    · simpa only [mem_ball, dist_zero_right, hy] using (lt_irrefl r)⟩

@[simp] theorem innerSphereInRoundShell_val
    (r s : ℝ) (hrs : r ≤ s) (y : sphere (0 : Plane) r) :
    (innerSphereInRoundShell r s hrs y : Plane) = y := rfl

/-- Regard the outer round sphere as the outer boundary of a round shell. -/
def outerSphereInRoundShell (r s : ℝ) (hrs : r ≤ s)
    (y : sphere (0 : Plane) s) :
    StandardPolygonalCollars.roundClosedShell r s :=
  ⟨y, by
    have hy : ‖(y : Plane)‖ = s := by
      simpa only [mem_sphere, dist_zero_right] using y.2
    constructor
    · simpa only [mem_closedBall, dist_zero_right, hy] using (le_refl s)
    · intro h
      rw [mem_ball, dist_zero_right, hy] at h
      exact (not_lt_of_ge hrs) h⟩

@[simp] theorem outerSphereInRoundShell_val
    (r s : ℝ) (hrs : r ≤ s) (y : sphere (0 : Plane) s) :
    (outerSphereInRoundShell r s hrs y : Plane) = y := rfl

theorem polarHomeomorph_apply_inner
    (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (y : sphere (0 : Plane) r) :
    polarHomeomorph r s hr hrs (innerSphereInRoundShell r s hrs y) =
      ((RadialBoundaryAdjustment.sphereScale r hr).symm y,
        ⟨r, le_rfl, hrs⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    have hy : ‖(y : Plane)‖ = r := by
      simpa only [mem_sphere, dist_zero_right] using y.2
    change ‖(y : Plane)‖⁻¹ • (y : Plane) = r⁻¹ • (y : Plane)
    rw [hy]
  · apply Subtype.ext
    change ‖(y : Plane)‖ = r
    simpa only [mem_sphere, dist_zero_right] using y.2

theorem polarHomeomorph_apply_outer
    (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s)
    (y : sphere (0 : Plane) s) :
    polarHomeomorph r s hr hrs (outerSphereInRoundShell r s hrs y) =
      (⟨s⁻¹ • (y : Plane), by
          have hs : 0 < s := hr.trans_le hrs
          rw [mem_sphere, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_inv, abs_of_pos hs]
          have hy : ‖(y : Plane)‖ = s := by
            simpa only [mem_sphere, dist_zero_right] using y.2
          rw [hy, inv_mul_cancel₀ hs.ne']⟩,
        ⟨s, hrs, le_rfl⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    have hy : ‖(y : Plane)‖ = s := by
      simpa only [mem_sphere, dist_zero_right] using y.2
    change ‖(y : Plane)‖⁻¹ • (y : Plane) = s⁻¹ • (y : Plane)
    rw [hy]
  · apply Subtype.ext
    change ‖(y : Plane)‖ = s
    simpa only [mem_sphere, dist_zero_right] using y.2

/-- A short angular correction on the inner round sphere, damped to the
identity on the outer sphere. -/
def roundShellAdjustment
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) :
    StandardPolygonalCollars.roundClosedShell r s ≃ₜ
      StandardPolygonalCollars.roundClosedShell r s :=
  (polarHomeomorph r s hr hrs.le).trans <|
    (polarHomeomorphAdjustment q hshort r s hrs).trans
      (polarHomeomorph r s hr hrs.le).symm

/-- The damped shell correction realizes `q` exactly on the inner sphere. -/
theorem roundShellAdjustment_apply_inner
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s)
    (y : sphere (0 : Plane) r) :
    (roundShellAdjustment q hshort r s hr hrs
        (innerSphereInRoundShell r s hrs.le y) : Plane) =
      r • (q ((RadialBoundaryAdjustment.sphereScale r hr).symm y) : Plane) := by
  rw [roundShellAdjustment]
  simp only [Homeomorph.trans_apply, polarHomeomorphAdjustment_apply,
    polarMap, polarHomeomorph_apply_inner, shellTime_left,
    SphereShortIsotopy.interpolation_zero]
  rfl

/-- The damped shell correction is exactly the identity on the outer sphere. -/
theorem roundShellAdjustment_apply_outer
    (q : sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1)
    (hshort : ∀ u, q u ≠ SphereShortIsotopy.antipode u)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s)
    (y : sphere (0 : Plane) s) :
    (roundShellAdjustment q hshort r s hr hrs
        (outerSphereInRoundShell r s hrs.le y) : Plane) = y := by
  rw [roundShellAdjustment]
  simp only [Homeomorph.trans_apply, polarHomeomorphAdjustment_apply,
    polarMap, polarHomeomorph_apply_outer, shellTime_right,
    SphereShortIsotopy.interpolation_one]
  have hy : ‖(y : Plane)‖ = s := by
    simpa only [mem_sphere, dist_zero_right] using y.2
  have hs : 0 < s := hr.trans hrs
  change s • (s⁻¹ • (y : Plane)) = (y : Plane)
  rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

end DampedAnnulus

namespace StandardPolygonalCollars

/-- Transport a self-homeomorphism of the `n`th standard polygonal carrier
to the Euclidean unit sphere. -/
def unitBoundaryCorrection (n : ℕ)
    (q : (disk n).carrier ≃ₜ (disk n).carrier) :
    sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
  (RadialBoundaryAdjustment.sphereScale (radius n) (radius_pos n)).trans <|
    (((diskCarrierToSphere n).symm.trans
      (q.trans (diskCarrierToSphere n))).trans
        (RadialBoundaryAdjustment.sphereScale
          (radius n) (radius_pos n)).symm)

/-- The same carrier correction in the master angular coordinate used by the
Moise drift estimates. -/
def angularBoundaryCorrection (n : ℕ)
    (q : (disk n).carrier ≃ₜ (disk n).carrier) :
    sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
  JordanCircle.InitialAngularArcs.sphereToMasterHomeomorph.trans <|
    (diskBoundaryHomeomorph n).trans <|
      q.trans <|
        (diskBoundaryHomeomorph n).symm.trans
          JordanCircle.InitialAngularArcs.sphereToMasterHomeomorph.symm

/-- Convert the gauge-rescaling direction used by `shellToRoundClosedShell`
to the master angular coordinate. -/
def gaugeToAngular (n : ℕ) :
    sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
  (RadialBoundaryAdjustment.sphereScale (radius n) (radius_pos n)).trans <|
    (diskCarrierToSphere n).symm.trans <|
      (diskBoundaryHomeomorph n).symm.trans
        JordanCircle.InitialAngularArcs.sphereToMasterHomeomorph.symm

/-- Polar coordinates on a standard polygonal shell whose angular component
is exactly the master coordinate used by the boundary-drift theorem. -/
def shellToAngularPolar (n : ℕ) :
    PolygonalCircle.closedShell (disk n) (disk (n + 1)) ≃ₜ
      sphere (0 : Plane) 1 × Icc (radius n) (radius (n + 1)) :=
  (shellToRoundClosedShell n).trans <|
    (DampedAnnulus.polarHomeomorph
      (radius n) (radius (n + 1)) (radius_pos n) (radius_lt_succ n).le).trans <|
      (gaugeToAngular n).prodCongr (Homeomorph.refl _)

theorem shellToAngularPolar_apply_innerCarrier (n : ℕ)
    (x : (disk n).carrier) :
    shellToAngularPolar n (innerCarrierInClosedShell n x) =
      (JordanCircle.InitialAngularArcs.normalizedTargetBoundaryPoint n x,
        ⟨radius n, le_rfl, (radius_lt_succ n).le⟩) := by
  rw [shellToAngularPolar]
  simp only [Homeomorph.trans_apply]
  let y : sphere (0 : Plane) (radius n) := diskCarrierToSphere n x
  have hsource :
      shellToRoundClosedShell n (innerCarrierInClosedShell n x) =
        DampedAnnulus.innerSphereInRoundShell
          (radius n) (radius (n + 1)) (radius_lt_succ n).le y := by
    apply Subtype.ext
    rfl
  rw [hsource, DampedAnnulus.polarHomeomorph_apply_inner]
  apply Prod.ext
  · apply Subtype.ext
    simp only [Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_apply,
      gaugeToAngular, JordanCircle.InitialAngularArcs.normalizedTargetBoundaryPoint,
      Homeomorph.trans_apply, Homeomorph.apply_symm_apply, y]
    rw [(diskCarrierToSphere n).symm_apply_apply]
  · rfl

theorem shellToAngularPolar_apply_outerCarrier (n : ℕ)
    (x : (disk (n + 1)).carrier) :
    (shellToAngularPolar n (outerCarrierInClosedShell n x)).2 =
      ⟨radius (n + 1), (radius_lt_succ n).le, le_rfl⟩ := by
  rw [shellToAngularPolar]
  simp only [Homeomorph.trans_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
    Homeomorph.refl_apply]
  let y : sphere (0 : Plane) (radius (n + 1)) :=
    diskCarrierToSphere (n + 1) x
  have hsource :
      shellToRoundClosedShell n (outerCarrierInClosedShell n x) =
        DampedAnnulus.outerSphereInRoundShell
          (radius n) (radius (n + 1)) (radius_lt_succ n).le y := by
    apply Subtype.ext
    rfl
  rw [hsource, DampedAnnulus.polarHomeomorph_apply_outer]
  rfl

/-- Extend a short inner-carrier correction across one standard polygonal
shell while damping it to the identity on the outer carrier. -/
def dampedStandardShellBoundaryAdjustment (n : ℕ)
    (q : (disk n).carrier ≃ₜ (disk n).carrier)
    (hshort : ∀ u, angularBoundaryCorrection n q u ≠
      SphereShortIsotopy.antipode u) :
    PolygonalCircle.closedShell (disk n) (disk (n + 1)) ≃ₜ
      PolygonalCircle.closedShell (disk n) (disk (n + 1)) :=
  (shellToAngularPolar n).trans <|
    (DampedAnnulus.polarHomeomorphAdjustment
      (angularBoundaryCorrection n q) hshort
      (radius n) (radius (n + 1)) (radius_lt_succ n)).trans
    (shellToAngularPolar n).symm

/-- The damped standard-shell adjustment realizes the requested map exactly
on its inner polygonal carrier. -/
theorem dampedStandardShellBoundaryAdjustment_apply_innerCarrier
    (n : ℕ) (q : (disk n).carrier ≃ₜ (disk n).carrier)
    (hshort : ∀ u, angularBoundaryCorrection n q u ≠
      SphereShortIsotopy.antipode u)
    (x : (disk n).carrier) :
    (dampedStandardShellBoundaryAdjustment n q hshort
        (innerCarrierInClosedShell n x) : Plane) = q x := by
  have hEq :
      dampedStandardShellBoundaryAdjustment n q hshort
          (innerCarrierInClosedShell n x) =
        innerCarrierInClosedShell n (q x) := by
    apply (shellToAngularPolar n).injective
    rw [dampedStandardShellBoundaryAdjustment]
    simp only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
      DampedAnnulus.polarHomeomorphAdjustment_apply,
      DampedAnnulus.polarMap, shellToAngularPolar_apply_innerCarrier,
      DampedAnnulus.shellTime_left, SphereShortIsotopy.interpolation_zero]
    apply Prod.ext
    · simp only [angularBoundaryCorrection,
        JordanCircle.InitialAngularArcs.normalizedTargetBoundaryPoint,
        Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    · rfl
  exact congrArg Subtype.val hEq

/-- The damped standard-shell adjustment is exactly the identity on its
outer polygonal carrier. -/
theorem dampedStandardShellBoundaryAdjustment_apply_outerCarrier
    (n : ℕ) (q : (disk n).carrier ≃ₜ (disk n).carrier)
    (hshort : ∀ u, angularBoundaryCorrection n q u ≠
      SphereShortIsotopy.antipode u)
    (x : (disk (n + 1)).carrier) :
    (dampedStandardShellBoundaryAdjustment n q hshort
        (outerCarrierInClosedShell n x) : Plane) = x := by
  have hEq :
      dampedStandardShellBoundaryAdjustment n q hshort
          (outerCarrierInClosedShell n x) =
        outerCarrierInClosedShell n x := by
    apply (shellToAngularPolar n).injective
    rw [dampedStandardShellBoundaryAdjustment]
    simp only [Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
      DampedAnnulus.polarHomeomorphAdjustment_apply, DampedAnnulus.polarMap]
    have hr := shellToAngularPolar_apply_outerCarrier n x
    rw [hr, DampedAnnulus.shellTime_right,
      SphereShortIsotopy.interpolation_one]
    apply Prod.ext
    · rfl
    · exact hr.symm
  exact congrArg Subtype.val hEq

end StandardPolygonalCollars

end

end Schoenflies
