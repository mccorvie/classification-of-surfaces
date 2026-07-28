/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.DiskSquare
import ClassificationOfSurfaces.SphereCarrierGeometry
import ClassificationOfSurfaces.WeightedCircle

/-!
# The one-sided-degenerate P2 disk model

The ordinary P2 model glues two polygons along a marked side, with at least one old side on
each child.  Cancellation in the Gallier--Xu normalization also uses the limiting case in which
one child is a monogon.  This file supplies a concrete model for that case.

The local target is a polynomial teardrop.  The map

`z ↦ (1 - z) ^ 2`

is injective on the closed unit disk: translating by `1` puts the disk in a closed half-plane,
on which squaring has no nontrivial antipodal pair.  Its image is star-shaped at the cusp.  A
scaled copy receives the monogon, while the other child fills the collar between that copy and
the full teardrop.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace P2DegenerateDisk

/-- Every polygon cell has the closed-unit-disk norm bound. -/
theorem norm_le_one {n : ℕ} (z : PolygonCell n) :
    ‖z.val‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using z.property

/-- The polynomial disk used as the target of the degenerate two-child gluing. -/
def teardropMap {n : ℕ} (z : PolygonCell n) : ℂ :=
  (1 - z.val) ^ 2

theorem continuous_teardropMap {n : ℕ} :
    Continuous (teardropMap : PolygonCell n → ℂ) := by
  unfold teardropMap
  fun_prop

/-- A point of the closed unit disk with real part `1` is the cusp point `1`. -/
theorem eq_one_of_re_eq_one {n : ℕ} (z : PolygonCell n)
    (hre : z.val.re = 1) :
    z.val = 1 := by
  have hnorm : Complex.normSq z.val ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  apply Complex.ext
  · simpa using hre
  · simp only [Complex.one_im]
    rw [Complex.normSq_apply] at hnorm
    nlinarith

/-- Squaring after translation by `1` is injective on the closed unit disk. -/
theorem teardropMap_injective {n m : ℕ}
    {z : PolygonCell n} {w : PolygonCell m}
    (h : teardropMap z = teardropMap w) :
    z.val = w.val := by
  let u : ℂ := 1 - z.val
  let v : ℂ := 1 - w.val
  have hprod : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
      _ = 0 := by
        dsimp [u, v, teardropMap] at h ⊢
        rw [h]
        ring
  rcases mul_eq_zero.mp hprod with huv | huv
  · dsimp [u, v] at huv
    linear_combination -huv
  · have hsum : z.val + w.val = 2 := by
      dsimp [u, v] at huv
      calc
        z.val + w.val =
            2 - ((1 - z.val) + (1 - w.val)) := by ring
        _ = 2 := by rw [huv, sub_zero]
    have hzre : z.val.re ≤ 1 :=
      (Complex.re_le_norm z.val).trans (norm_le_one z)
    have hwre : w.val.re ≤ 1 :=
      (Complex.re_le_norm w.val).trans (norm_le_one w)
    have hsumre := congrArg Complex.re hsum
    change z.val.re + w.val.re = 2 at hsumre
    have hzre_eq : z.val.re = 1 := by linarith
    have hwre_eq : w.val.re = 1 := by linarith
    rw [eq_one_of_re_eq_one z hzre_eq,
      eq_one_of_re_eq_one w hwre_eq]

/-- The teardrop image, equipped with the subspace topology inherited from the plane. -/
abbrev Teardrop :=
  Set.range (teardropMap : PolygonCell 1 → ℂ)

/-- The polynomial map as a map into its exact range. -/
def toTeardrop (z : PolygonCell 1) : Teardrop :=
  ⟨teardropMap z, ⟨z, rfl⟩⟩

theorem continuous_toTeardrop :
    Continuous toTeardrop := by
  exact continuous_induced_rng.2 continuous_teardropMap

theorem toTeardrop_bijective :
    Function.Bijective toTeardrop := by
  constructor
  · intro z w h
    apply PolygonCell.ext
    exact teardropMap_injective (congrArg Subtype.val h)
  · rintro ⟨x, z, rfl⟩
    exact ⟨z, rfl⟩

/-- The closed disk is homeomorphic to its polynomial teardrop image. -/
noncomputable def teardropHomeomorph :
    PolygonCell 1 ≃ₜ Teardrop :=
  IsHomeomorph.homeomorph toTeardrop
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_toTeardrop, toTeardrop_bijective⟩)

@[simp]
theorem teardropHomeomorph_apply_val (z : PolygonCell 1) :
    (teardropHomeomorph z).val = teardropMap z :=
  by
    simp [teardropHomeomorph, toTeardrop]

/-- Contracting the translated disk toward its cusp stays in the translated disk. -/
theorem one_sub_smul_mem_closedBall
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(1 : ℂ) - s * (1 - z.val)‖ ≤ 1 := by
  have hconvex :
      (1 : ℂ) - s * (1 - z.val) =
        (1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val := by
    ring
  rw [hconvex]
  calc
    ‖(1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val‖ ≤
        ‖(1 - (s : ℂ)) * (1 : ℂ)‖ +
          ‖(s : ℂ) * z.val‖ :=
      norm_add_le _ _
    _ = (1 - s) + s * ‖z.val‖ := by
      rw [norm_mul, norm_mul, norm_one, mul_one]
      have hsub :
          (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hs1)]
    _ ≤ 1 := by
      have hz := norm_le_one z
      nlinarith

/-- Every radial contraction of a teardrop point is again a teardrop point. -/
theorem smul_teardropMap_mem_range
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s : ℂ) * teardropMap z ∈
      Set.range (teardropMap : PolygonCell 1 → ℂ) := by
  let r : ℝ := Real.sqrt s
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := by
    simpa [r] using hs1
  let w : PolygonCell 1 :=
    ⟨(1 : ℂ) - r * (1 - z.val), by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        one_sub_smul_mem_closedBall z hr0 hr1⟩
  refine ⟨w, ?_⟩
  unfold teardropMap
  dsimp [w, r]
  have hsqrt : (Real.sqrt s) ^ 2 = s :=
    Real.sq_sqrt hs0
  have hsqrtC : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast hsqrt
  rw [show (1 : ℂ) -
      ((1 : ℂ) - (Real.sqrt s : ℂ) * (1 - z.val)) =
        (Real.sqrt s : ℂ) * (1 - z.val) by ring]
  rw [mul_pow, hsqrtC]

/-! ## The monogon and collar maps -/

/-- The monogon occupies the inner radial half of the teardrop. -/
noncomputable def monogonMap (z : PolygonCell 1) : ℂ :=
  (((2 : ℝ)⁻¹ : ℝ) : ℂ) * teardropMap z

theorem continuous_monogonMap :
    Continuous monogonMap := by
  unfold monogonMap
  exact continuous_const.mul continuous_teardropMap

/-- Half of a teardrop point is still in the full teardrop. -/
theorem monogonMap_mem_teardrop (z : PolygonCell 1) :
    monogonMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  unfold monogonMap
  exact smul_teardropMap_mem_range
    (s := (2 : ℝ)⁻¹) z (by norm_num) (by norm_num)

/-- The nonnegative height of the upper circular boundary above a fixed real coordinate. -/
noncomputable def chordHeight (z : PolygonCell 2) : ℝ :=
  Real.sqrt (1 - z.val.re ^ 2)

theorem re_sq_le_one (z : PolygonCell 2) :
    z.val.re ^ 2 ≤ 1 := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  nlinarith [sq_nonneg z.val.im]

theorem chordHeight_nonneg (z : PolygonCell 2) :
    0 ≤ chordHeight z :=
  Real.sqrt_nonneg _

theorem chordHeight_sq (z : PolygonCell 2) :
    chordHeight z ^ 2 = 1 - z.val.re ^ 2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr (re_sq_le_one z))

theorem neg_chordHeight_le_im (z : PolygonCell 2) :
    -chordHeight z ≤ z.val.im := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im + chordHeight z)]

theorem im_le_chordHeight (z : PolygonCell 2) :
    z.val.im ≤ chordHeight z := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im - chordHeight z)]

/-- The lower unit-circle point on the vertical chord through a digon point, squared so that the
two chord endpoints sweep the teardrop boundary once. -/
noncomputable def collarCircleValue (z : PolygonCell 2) : ℂ :=
  ((z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I) ^ 2

theorem collarCircleValue_norm (z : PolygonCell 2) :
    ‖collarCircleValue z‖ = 1 := by
  let a : ℂ :=
    (z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I
  have haSq : Complex.normSq a = 1 := by
    rw [Complex.normSq_apply]
    simp only [a, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, sub_zero, Complex.sub_im,
      Complex.mul_im, Complex.I_im, mul_one, add_zero,
      zero_sub]
    nlinarith [chordHeight_sq z]
  have haNorm : ‖a‖ = 1 := by
    have hnorm0 := norm_nonneg a
    rw [Complex.normSq_eq_norm_sq] at haSq
    nlinarith
  change ‖a ^ 2‖ = 1
  rw [norm_pow, haNorm]
  norm_num

/-- The collar's boundary-direction point, bundled as a point of the unit disk. -/
noncomputable def collarCirclePoint (z : PolygonCell 2) :
    PolygonCell 1 :=
  ⟨collarCircleValue z, by
    simp [Metric.mem_closedBall, dist_zero_right,
      collarCircleValue_norm z]⟩

theorem continuous_chordHeight :
    Continuous chordHeight := by
  unfold chordHeight
  fun_prop

theorem continuous_collarCircleValue :
    Continuous collarCircleValue := by
  unfold collarCircleValue
  apply Continuous.pow
  apply Continuous.sub
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp PolygonCell.continuous_val)
  · exact
      (Complex.continuous_ofReal.comp continuous_chordHeight).mul
        continuous_const

theorem continuous_collarCirclePoint :
    Continuous collarCirclePoint :=
  continuous_induced_rng.2 continuous_collarCircleValue

/-- The teardrop boundary value of the collar direction has an exact quadratic factor. -/
theorem teardropMap_collarCirclePoint
    (z : PolygonCell 2) :
    teardropMap (collarCirclePoint z) =
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 *
        collarCircleValue z := by
  let x : ℝ := z.val.re
  let s : ℝ := chordHeight z
  let a : ℂ := (x : ℂ) - (s : ℂ) * Complex.I
  have hcircleR : x ^ 2 + s ^ 2 = 1 := by
    dsimp [x, s]
    nlinarith [chordHeight_sq z]
  have hcircleC : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    exact_mod_cast hcircleR
  have hone : (1 : ℂ) - a ^ 2 =
      2 * Complex.I * (s : ℂ) * a := by
    apply Complex.ext
    · simp [a, pow_two]
      nlinarith [hcircleR]
    · simp [a, pow_two]
      ring
  have hI : (2 * Complex.I : ℂ) ^ 2 = -4 := by
    calc
      (2 * Complex.I : ℂ) ^ 2 =
          4 * (Complex.I * Complex.I) := by ring
      _ = -4 := by rw [Complex.I_mul_I]; ring
  change (1 - a ^ 2) ^ 2 =
    (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2
  rw [hone]
  calc
    (2 * Complex.I * (s : ℂ) * a) ^ 2 =
        (2 * Complex.I) ^ 2 * (s : ℂ) ^ 2 * a ^ 2 := by ring
    _ = (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2 := by rw [hI]

/-- The digon fills the radial collar between the half-size and full teardrop boundaries. -/
noncomputable def collarMap (z : PolygonCell 2) : ℂ :=
  let s := chordHeight z
  collarCircleValue z *
    ((s * z.val.im - 3 * s ^ 2 : ℝ) : ℂ)

theorem continuous_collarMap :
    Continuous collarMap := by
  unfold collarMap
  apply continuous_collarCircleValue.mul
  apply Complex.continuous_ofReal.comp
  exact
    (continuous_chordHeight.mul
      (Complex.continuous_im.comp PolygonCell.continuous_val)).sub
        (continuous_const.mul (continuous_chordHeight.pow 2))

/-- Away from the two chord tips, the collar map is a radial teardrop value with scale in
`[1/2, 1]`. -/
theorem collarMap_eq_smul_teardropMap
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    collarMap z =
      (((3 * chordHeight z ^ 2 -
          chordHeight z * z.val.im) /
            (4 * chordHeight z ^ 2) : ℝ) : ℂ) *
        teardropMap (collarCirclePoint z) := by
  let s : ℝ := chordHeight z
  let y : ℝ := z.val.im
  have hscalar :
      s * y - 3 * s ^ 2 =
        ((3 * s ^ 2 - s * y) / (4 * s ^ 2)) *
          (-4) * s ^ 2 := by
    have hs' : s ≠ 0 := by simpa [s] using hs
    field_simp [hs']
    ring
  have hscalarC :
      ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
        (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
          (-4 : ℂ) * (s : ℂ) ^ 2 := by
    exact_mod_cast hscalar
  rw [teardropMap_collarCirclePoint]
  unfold collarMap
  change
    collarCircleValue z *
        ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
      (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
        ((-4 : ℂ) * (s : ℂ) ^ 2 * collarCircleValue z)
  rw [hscalarC]
  ring

theorem collarScale_nonneg
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    0 ≤ (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := im_le_chordHeight z
  apply div_nonneg
  · nlinarith
  · positivity

theorem collarScale_le_one
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) ≤ 1 := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := neg_chordHeight_le_im z
  rw [div_le_one (by positivity)]
  nlinarith

theorem collarMap_mem_teardrop (z : PolygonCell 2) :
    collarMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  by_cases hs : chordHeight z = 0
  · refine ⟨⟨1, by simp [Metric.mem_closedBall]⟩, ?_⟩
    simp [collarMap, hs, teardropMap]
  · rw [collarMap_eq_smul_teardropMap z hs]
    exact smul_teardropMap_mem_range
      (collarCirclePoint z)
      (collarScale_nonneg z hs)
      (collarScale_le_one z hs)

/-! ## Exact compatibility on the fresh seam -/

/-- On the upper circular boundary of the digon, the collar meets the half-size teardrop
occupied by the monogon. -/
theorem collarMap_eq_monogonMap_collarCirclePoint_of_im_eq
    (z : PolygonCell 2) (hy : z.val.im = chordHeight z) :
    collarMap z = monogonMap (collarCirclePoint z) := by
  unfold collarMap monogonMap
  rw [teardropMap_collarCirclePoint]
  rw [hy]
  norm_num
  ring

/-- Side zero of the digon is the upper semicircle with its usual angle parameter. -/
theorem side_zero_digon_val (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ) := by
  change
    (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 2) t) : ℂ) =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ)
  congr 2
  unfold PolygonCell.sideAngle
  norm_num
  ring

/-- The imaginary coordinate on side zero of the digon. -/
theorem side_zero_digon_im (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val.im =
      Real.sin (Real.pi * (t : ℝ)) := by
  rw [side_zero_digon_val]
  exact Complex.exp_ofReal_mul_I_im _

/-- The chord height agrees with the imaginary coordinate on the upper digon side. -/
theorem chordHeight_side_zero_digon (t : unitInterval) :
    chordHeight (PolygonCell.side (0 : Fin 2) t) =
      Real.sin (Real.pi * (t : ℝ)) := by
  let z : PolygonCell 2 := PolygonCell.side (0 : Fin 2) t
  let θ : ℝ := Real.pi * (t : ℝ)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le t.property.1
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos, t.property.2]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hre : z.val.re = Real.cos θ := by
    dsimp [z, θ]
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have him : z.val.im = Real.sin θ := by
    simpa [z, θ] using side_zero_digon_im t
  have hs := chordHeight_sq z
  have htrig := Real.sin_sq_add_cos_sq θ
  rw [hre] at hs
  have hheight0 := chordHeight_nonneg z
  change chordHeight z = Real.sin θ
  nlinarith

/-- Squaring the lower endpoint of an upper digon chord gives the corresponding monogon
boundary point. -/
theorem collarCirclePoint_side_zero_digon_symm (t : unitInterval) :
    collarCirclePoint
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) =
      PolygonCell.side (0 : Fin 1) t := by
  apply PolygonCell.ext
  let u : unitInterval := unitInterval.symm t
  let θ : ℝ := Real.pi * (u : ℝ)
  have hheight :
      chordHeight (PolygonCell.side (0 : Fin 2) u) =
        Real.sin θ := by
    simpa [θ] using chordHeight_side_zero_digon u
  have hre :
      (PolygonCell.side (0 : Fin 2) u : PolygonCell 2).val.re =
        Real.cos θ := by
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have ha :
      ((Real.cos θ : ℂ) -
          (Real.sin θ : ℂ) * Complex.I) =
        (Circle.exp (-θ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul,
        mul_one, add_zero, zero_sub, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  change collarCircleValue
      (PolygonCell.side (0 : Fin 2) u) =
    (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val
  unfold collarCircleValue
  rw [hheight, hre, ha]
  change ((Circle.exp (-θ) : ℂ) ^ 2) =
    (Circle.exp (PolygonCell.sideAngle (0 : Fin 1) t) : ℂ)
  rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  dsimp [θ, u]
  simp only [PolygonCell.sideAngle, Fin.val_zero, Nat.cast_one,
    div_one, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul]
  ring

/-- The analytic child map respects the exact reversed fresh-side parameter used by P2. -/
theorem monogonMap_fresh_seam (t : unitInterval) :
    monogonMap (PolygonCell.side (0 : Fin 1) t) =
      collarMap
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) := by
  symm
  rw [collarMap_eq_monogonMap_collarCirclePoint_of_im_eq,
    collarCirclePoint_side_zero_digon_symm]
  rw [side_zero_digon_im]
  exact (chordHeight_side_zero_digon (unitInterval.symm t)).symm

end P2DegenerateDisk

end LeanEval.Topology.ClassificationOfSurfaces
