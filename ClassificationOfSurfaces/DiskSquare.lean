/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.RepresentativeCarrier
import ClassificationOfSurfaces.WeightedCircle
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# A square model for polygon cells

This file supplies the geometric cut-and-paste model used by Gallier--Xu P2.  The closed unit
square is treated as a convex disk.  Its boundary is parameterized explicitly by radial
projection of the Euclidean circle, and an arbitrary homeomorphism from the circle to the
frontier of a bounded convex disk is extended across `PolygonCell`.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex
open Metric Bornology Filter Set
open scoped Topology

namespace DiskSquare

/-- The sup norm of a complex number, used as the gauge of the centered square. -/
def maxAbs (z : ℂ) : ℝ :=
  max |z.re| |z.im|

@[simp]
theorem maxAbs_zero : maxAbs 0 = 0 := by
  simp [maxAbs]

theorem maxAbs_nonneg (z : ℂ) : 0 ≤ maxAbs z :=
  le_max_of_le_left (abs_nonneg z.re)

theorem abs_re_le_maxAbs (z : ℂ) : |z.re| ≤ maxAbs z :=
  le_max_left _ _

theorem abs_im_le_maxAbs (z : ℂ) : |z.im| ≤ maxAbs z :=
  le_max_right _ _

theorem maxAbs_eq_zero_iff {z : ℂ} : maxAbs z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Complex.ext
    · have hre : |z.re| = 0 :=
        le_antisymm (abs_re_le_maxAbs z |>.trans_eq h) (abs_nonneg _)
      simpa using abs_eq_zero.mp hre
    · have him : |z.im| = 0 :=
        le_antisymm (abs_im_le_maxAbs z |>.trans_eq h) (abs_nonneg _)
      simpa using abs_eq_zero.mp him
  · rintro rfl
    exact maxAbs_zero

theorem maxAbs_pos {z : ℂ} (hz : z ≠ 0) : 0 < maxAbs z :=
  (maxAbs_nonneg z).lt_of_ne fun h ↦ hz ((maxAbs_eq_zero_iff.mp h.symm))

theorem maxAbs_le_norm (z : ℂ) : maxAbs z ≤ ‖z‖ := by
  apply max_le
  · exact abs_re_le_norm z
  · exact abs_im_le_norm z

theorem maxAbs_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    maxAbs (c • z) = c * maxAbs z := by
  simp only [maxAbs, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    abs_mul, abs_of_nonneg hc]
  by_cases h : |z.re| ≤ |z.im|
  · rw [max_eq_right h,
      max_eq_right (mul_le_mul_of_nonneg_left h hc)]
  · have h' : |z.im| ≤ |z.re| := le_of_not_ge h
    rw [max_eq_left h',
      max_eq_left (mul_le_mul_of_nonneg_left h' hc)]

theorem maxAbs_add_le (z w : ℂ) :
    maxAbs (z + w) ≤ maxAbs z + maxAbs w := by
  apply max_le
  · change |z.re + w.re| ≤ maxAbs z + maxAbs w
    exact (abs_add_le _ _).trans
      (add_le_add (abs_re_le_maxAbs z) (abs_re_le_maxAbs w))
  · change |z.im + w.im| ≤ maxAbs z + maxAbs w
    exact (abs_add_le _ _).trans
      (add_le_add (abs_im_le_maxAbs z) (abs_im_le_maxAbs w))

theorem maxAbs_div_of_pos (z : ℂ) {r : ℝ} (hr : 0 < r) :
    maxAbs (z / r) = maxAbs z / r := by
  simp only [maxAbs, Complex.div_ofReal_re, Complex.div_ofReal_im,
    abs_div, abs_of_pos hr, max_div_div_right hr.le]

theorem norm_le_sqrtTwo_mul_maxAbs (z : ℂ) :
    ‖z‖ ≤ Real.sqrt 2 * maxAbs z := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (maxAbs_nonneg _))]
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow]
  have hre := abs_re_le_maxAbs z
  have him := abs_im_le_maxAbs z
  have hreSq : z.re ^ 2 ≤ maxAbs z ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.re) (maxAbs_nonneg z)).2 hre
  have himSq : z.im ^ 2 ≤ maxAbs z ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) (maxAbs_nonneg z)).2 him
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- The centered closed unit square. -/
def square : Set ℂ :=
  {z | maxAbs z ≤ 1}

/-- The geometric boundary of the centered square. -/
def boundary : Set ℂ :=
  {z | maxAbs z = 1}

theorem continuous_maxAbs : Continuous maxAbs := by
  unfold maxAbs
  exact (Complex.continuous_re.abs.max Complex.continuous_im.abs)

theorem isClosed_square : IsClosed square := by
  exact isClosed_le continuous_maxAbs continuous_const

theorem zero_mem_square : (0 : ℂ) ∈ square := by
  simp [square]

theorem ball_zero_one_subset_square :
    Metric.ball (0 : ℂ) 1 ⊆ square := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact (maxAbs_le_norm z).trans hz.le

theorem square_mem_nhds_zero : square ∈ nhds (0 : ℂ) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
    ball_zero_one_subset_square

theorem convex_square : Convex ℝ square := by
  intro x hx y hy a b ha hb hab
  change maxAbs x ≤ 1 at hx
  change maxAbs y ≤ 1 at hy
  change maxAbs (a • x + b • y) ≤ 1
  calc
    maxAbs (a • x + b • y) ≤ maxAbs (a • x) + maxAbs (b • y) :=
      maxAbs_add_le _ _
    _ = a * maxAbs x + b * maxAbs y := by
      rw [maxAbs_smul_of_nonneg a ha, maxAbs_smul_of_nonneg b hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

theorem isBounded_square : IsBounded square := by
  apply Metric.isBounded_iff_subset_closedBall 0 |>.2
  refine ⟨Real.sqrt 2, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_sqrtTwo_mul_maxAbs z).trans
    (mul_le_of_le_one_right (Real.sqrt_nonneg 2) hz)

theorem interior_square_nonempty : (interior square).Nonempty := by
  refine ⟨0, ?_⟩
  exact mem_interior_iff_mem_nhds.mpr square_mem_nhds_zero

theorem interior_square :
    interior square = {z | maxAbs z < 1} := by
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hnot
    have hzMem : z ∈ square :=
      (interior_subset : interior square ⊆ square) hz
    have hzSquare : maxAbs z ≤ 1 := hzMem
    have hEq : maxAbs z = 1 :=
      le_antisymm hzSquare (le_of_not_gt hnot)
    have hscale : ∀ ε : ℝ, 0 < ε →
        (1 + ε) • z ∉ square := by
      intro ε hε
      change ¬maxAbs ((1 + ε) • z) ≤ 1
      have hpos : 0 ≤ 1 + ε := by linarith
      rw [maxAbs_smul_of_nonneg (1 + ε) hpos, hEq]
      linarith
    have hopen : square ∈ nhds z :=
      mem_interior_iff_mem_nhds.mp hz
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp hopen
    let δ : ℝ := min (ε / (2 * ‖z‖)) (1 / 2)
    have hzNorm : 0 < ‖z‖ := by
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        simp at hEq
      exact norm_pos_iff.mpr hz0
    have hδ : 0 < δ := by
      exact lt_min (div_pos hε (by positivity)) (by norm_num)
    have hdist : dist ((1 + δ) • z) z < ε := by
      rw [dist_eq, add_smul, one_smul,
        show z + δ • z - z = δ • z by abel, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ]
      have hδle : δ ≤ ε / (2 * ‖z‖) := min_le_left _ _
      have hnorm : δ * ‖z‖ ≤ ε / 2 := by
        calc
          δ * ‖z‖ ≤ (ε / (2 * ‖z‖)) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hδle (norm_nonneg _)
          _ = ε / 2 := by field_simp
      linarith
    exact hscale δ hδ (hball hdist)
  · intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hpre :
        {w : ℂ | maxAbs w < 1} ∈ nhds z :=
      (isOpen_lt continuous_maxAbs continuous_const).mem_nhds hz
    exact Filter.mem_of_superset hpre fun w hw ↦ by
      change maxAbs w ≤ 1
      exact hw.le

theorem frontier_square :
    frontier square = boundary := by
  rw [frontier, isClosed_square.closure_eq, interior_square]
  ext z
  simp only [square, boundary, Set.mem_diff, Set.mem_setOf_eq, not_lt]
  constructor
  · exact fun h ↦ le_antisymm h.1 h.2
  · intro h
    exact ⟨h.le, h.ge⟩

/-- Radial projection of a nonzero point to the square boundary. -/
noncomputable def radialToBoundary (z : ℂ) (hz : z ≠ 0) : ℂ :=
  z / maxAbs z

theorem radialToBoundary_maxAbs (z : ℂ) (hz : z ≠ 0) :
    maxAbs (radialToBoundary z hz) = 1 := by
  have hm : 0 < maxAbs z := maxAbs_pos hz
  unfold radialToBoundary
  rw [maxAbs_div_of_pos z hm]
  exact div_self hm.ne'

/-- The radial homeomorphism from the Euclidean unit circle to the centered square boundary. -/
noncomputable def circleBoundaryHomeomorph : Circle ≃ₜ boundary where
  toFun z := ⟨radialToBoundary z z.coe_ne_zero,
    radialToBoundary_maxAbs z z.coe_ne_zero⟩
  invFun z :=
    ⟨z.1 / ‖z.1‖, by
      have hz0 : z.1 ≠ 0 := by
        intro h
        have := z.2
        simp [boundary, h, maxAbs] at this
      have hnorm : ‖z.1 / (‖z.1‖ : ℂ)‖ = 1 := by
        rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr hz0)]
      simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hnorm⟩
  left_inv := by
    intro z
    apply Circle.ext
    change
      (radialToBoundary (z : ℂ) z.coe_ne_zero) /
          ‖radialToBoundary (z : ℂ) z.coe_ne_zero‖ =
        z
    have hm : 0 < maxAbs (z : ℂ) := maxAbs_pos z.coe_ne_zero
    have hnorm :
        ‖radialToBoundary (z : ℂ) z.coe_ne_zero‖ =
          1 / maxAbs (z : ℂ) := by
      rw [radialToBoundary, norm_div, norm_real, Real.norm_eq_abs,
        abs_of_pos hm, z.norm_coe]
    rw [hnorm, radialToBoundary]
    push_cast
    field_simp [hm.ne']
  right_inv := by
    intro z
    apply Subtype.ext
    have hz0 : z.1 ≠ 0 := by
      intro hz
      have := z.2
      simp [boundary, hz, maxAbs] at this
    have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hz0
    have hm : maxAbs z.1 = 1 := z.2
    change
      (z.1 / (‖z.1‖ : ℂ)) /
          (maxAbs (z.1 / (‖z.1‖ : ℂ)) : ℂ) =
        z.1
    have hmax :
        maxAbs (z.1 / ‖z.1‖) = 1 / ‖z.1‖ := by
      rw [maxAbs_div_of_pos z.1 hn, hm]
    rw [hmax]
    push_cast
    field_simp [hn.ne']
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : Circle ↦ (z : ℂ) / maxAbs (z : ℂ))
    exact continuous_subtype_val.div₀
      (Complex.continuous_ofReal.comp
        (continuous_maxAbs.comp continuous_subtype_val))
      fun z ↦ Complex.ofReal_ne_zero.mpr
        (maxAbs_pos (Circle.coe_ne_zero z)).ne'
  continuous_invFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : boundary ↦ z.1 / ‖z.1‖)
    exact continuous_subtype_val.div₀
      (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
      fun z ↦ Complex.ofReal_ne_zero.mpr <| by
        intro h
        have hz0 : z.1 = 0 := norm_eq_zero.mp h
        have := z.2
        simp [boundary, hz0, maxAbs] at this

@[simp]
theorem circleBoundaryHomeomorph_val (z : Circle) :
    (circleBoundaryHomeomorph z).1 =
      radialToBoundary z z.coe_ne_zero :=
  rfl

/-! ## Extending a chosen square-boundary parameterization -/

theorem exists_squareAmbientHomeomorph :
    ∃ h : ℂ ≃ₜ ℂ,
      h '' square = Metric.closedBall 0 1 ∧
      h '' boundary = Metric.sphere 0 1 := by
  obtain ⟨h, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      convex_square interior_square_nonempty isBounded_square
  refine ⟨h, ?_, ?_⟩
  · simpa only [isClosed_square.closure_eq] using hclosure
  · simpa only [frontier_square] using hfrontier

/-- A fixed ambient straightening of the centered square to the Euclidean unit disk. -/
noncomputable def squareAmbientHomeomorph : ℂ ≃ₜ ℂ :=
  Classical.choose exists_squareAmbientHomeomorph

theorem squareAmbientHomeomorph_image_square :
    squareAmbientHomeomorph '' square = Metric.closedBall 0 1 :=
  (Classical.choose_spec exists_squareAmbientHomeomorph).1

theorem squareAmbientHomeomorph_image_boundary :
    squareAmbientHomeomorph '' boundary = Metric.sphere 0 1 :=
  (Classical.choose_spec exists_squareAmbientHomeomorph).2

/-- Restrict the fixed ambient straightening to the closed square. -/
noncomputable def squareCellHomeomorph (n : ℕ) :
    square ≃ₜ PolygonCell n where
  toFun z :=
    ⟨squareAmbientHomeomorph z.1, by
      rw [← squareAmbientHomeomorph_image_square]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨squareAmbientHomeomorph.symm z.val, by
      have hz :
          squareAmbientHomeomorph
              (squareAmbientHomeomorph.symm z.val) ∈
            squareAmbientHomeomorph '' square := by
        rw [squareAmbientHomeomorph_image_square]
        simpa using z.property
      rcases hz with ⟨w, hw, heq⟩
      exact squareAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact squareAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact squareAmbientHomeomorph.apply_symm_apply z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.symm.continuous.comp PolygonCell.continuous_val

/-- The fixed square straightening restricted to its frontier. -/
noncomputable def boundaryCircleHomeomorph :
    boundary ≃ₜ Circle where
  toFun z :=
    ⟨squareAmbientHomeomorph z.1, by
      change squareAmbientHomeomorph z.1 ∈ Metric.sphere 0 1
      rw [← squareAmbientHomeomorph_image_boundary]
      exact ⟨z.1, z.2, rfl⟩⟩
  invFun z :=
    ⟨squareAmbientHomeomorph.symm z, by
      have hz :
          squareAmbientHomeomorph (squareAmbientHomeomorph.symm z) ∈
            squareAmbientHomeomorph '' boundary := by
        rw [squareAmbientHomeomorph_image_boundary]
        simpa [Submonoid.unitSphere] using z.property
      rcases hz with ⟨w, hw, heq⟩
      exact squareAmbientHomeomorph.injective heq.symm ▸ hw⟩
  left_inv := by
    intro z
    apply Subtype.ext
    exact squareAmbientHomeomorph.symm_apply_apply z.1
  right_inv := by
    intro z
    apply Circle.ext
    exact squareAmbientHomeomorph.apply_symm_apply z
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact squareAmbientHomeomorph.symm.continuous.comp continuous_subtype_val

/-- Include the square frontier into the closed square. -/
def boundaryInclusion : C(boundary, square) where
  toFun z := ⟨z.1, z.2.le⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

@[simp]
theorem squareCellHomeomorph_boundary (n : ℕ) (z : boundary) :
    squareCellHomeomorph n (boundaryInclusion z) =
      PolygonCell.ofCircle n (boundaryCircleHomeomorph z) := by
  apply PolygonCell.ext
  rfl

/-- Extend any selected parameterization of the square frontier across a polygon cell. -/
noncomputable def cellSquareHomeomorph {n : ℕ}
    (b : Circle ≃ₜ boundary) :
    PolygonCell n ≃ₜ square :=
  (PolygonCell.radialHomeomorph
      (b.trans boundaryCircleHomeomorph)).trans
    (squareCellHomeomorph n).symm

/-- The convex extension agrees exactly with the prescribed boundary parameterization. -/
@[simp]
theorem cellSquareHomeomorph_ofCircle {n : ℕ}
    (b : Circle ≃ₜ boundary) (z : Circle) :
    cellSquareHomeomorph b (PolygonCell.ofCircle n z) =
      boundaryInclusion (b z) := by
  apply (squareCellHomeomorph n).injective
  rw [cellSquareHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, PolygonCell.radialHomeomorph_ofCircle,
    squareCellHomeomorph_boundary]
  rfl

/-! ## A distinguished polygon side on the right side of the square -/

/-- Boundary weights for a polygon whose final side is distinguished. -/
def finalSideWeights (l : ℕ) : List ℕ :=
  List.replicate l 3 ++ [l]

/-- Boundary weights for a polygon whose first side is distinguished. -/
def firstSideWeights (r : ℕ) : List ℕ :=
  r :: List.replicate r 3

@[simp]
theorem finalSideWeights_length (l : ℕ) :
    (finalSideWeights l).length = l + 1 := by
  simp [finalSideWeights]

@[simp]
theorem firstSideWeights_length (r : ℕ) :
    (firstSideWeights r).length = r + 1 := by
  simp [firstSideWeights]

@[simp]
theorem finalSideWeights_sum (l : ℕ) :
    (finalSideWeights l).sum = 4 * l := by
  simp [finalSideWeights]
  omega

@[simp]
theorem firstSideWeights_sum (r : ℕ) :
    (firstSideWeights r).sum = 4 * r := by
  simp [firstSideWeights]
  omega

theorem finalSideWeights_positive {l : ℕ} (hl : 0 < l) :
    WeightedCircle.Positive (finalSideWeights l) := by
  intro w hw
  simp only [finalSideWeights, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hw
  rcases hw with ⟨_hl, rfl⟩ | rfl <;> omega

theorem firstSideWeights_positive {r : ℕ} (hr : 0 < r) :
    WeightedCircle.Positive (firstSideWeights r) := by
  intro w hw
  simp only [firstSideWeights, List.mem_cons, List.mem_replicate] at hw
  rcases hw with rfl | ⟨_hr, rfl⟩ <;> omega

theorem finalSideWeights_ne_nil {l : ℕ} (hl : 0 < l) :
    finalSideWeights l ≠ [] := by
  simpa only [List.ne_nil_iff_length_pos, finalSideWeights_length] using
    Nat.succ_pos l

theorem firstSideWeights_ne_nil {r : ℕ} (hr : 0 < r) :
    firstSideWeights r ≠ [] := by
  simp [firstSideWeights]

/-- Rotate the circle counterclockwise by `π / 4`. -/
noncomputable def quarterRotation : Circle ≃ₜ Circle :=
  Homeomorph.mulLeft (Circle.exp (Real.pi / 4))

/-- Put the final side of an `(l+1)`-gon on the right side of the square. -/
noncomputable def finalSideBoundaryHomeomorph (l : ℕ) (hl : 0 < l) :
    Circle ≃ₜ boundary :=
  (WeightedCircle.circleHomeomorph
      (finalSideWeights l) (finalSideWeights_positive hl)
      (finalSideWeights_ne_nil hl)).trans
    (quarterRotation.trans circleBoundaryHomeomorph)

/-- Put the first side of an `(r+1)`-gon on the same square side, but with reversed traversal. -/
noncomputable def firstSideBoundaryHomeomorph (r : ℕ) (hr : 0 < r) :
    Circle ≃ₜ boundary :=
  (WeightedCircle.circleHomeomorph
      (firstSideWeights r) (firstSideWeights_positive hr)
      (firstSideWeights_ne_nil hr)).trans
    ((Homeomorph.inv Circle).trans
      (quarterRotation.trans circleBoundaryHomeomorph))

theorem abs_sin_le_cos_of_mem_Icc
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    |Real.sin θ| ≤ Real.cos θ := by
  have hquarter : Real.pi / 4 ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hhalf : -(Real.pi / 2) ≤ -(Real.pi / 4) := by
    linarith [Real.pi_pos]
  by_cases hnonneg : 0 ≤ θ
  · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      hnonneg (hθ.2.trans (by linarith [Real.pi_pos])))]
    rw [← Real.sin_pi_div_two_sub]
    have horder : θ ≤ Real.pi / 2 - θ := by
      linear_combination 2 * hθ.2
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · exact horder
  · have hθnonpos : θ ≤ 0 := le_of_not_ge hnonneg
    have hsinNonpos : Real.sin θ ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hθnonpos
        (by linarith [hθ.1, Real.pi_pos])
    have hsin :
        |Real.sin θ| = Real.sin (-θ) := by
      rw [Real.sin_neg, abs_of_nonpos hsinNonpos]
    rw [hsin, ← Real.cos_neg θ]
    rw [← Real.sin_pi_div_two_sub]
    have hnegLe : -θ ≤ Real.pi / 4 := by
      linarith [hθ.1]
    have horder : -θ ≤ Real.pi / 2 - (-θ) := by
      linear_combination 2 * hnegLe
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · exact horder

theorem radialToBoundary_re_eq_one_of_angle
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) :
    (radialToBoundary (Circle.exp θ) (Circle.exp θ).coe_ne_zero).re = 1 := by
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩
  have hmax :
      maxAbs (Circle.exp θ : ℂ) = Real.cos θ := by
    simp only [maxAbs, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, abs_of_nonneg hcos]
    exact max_eq_left (abs_sin_le_cos_of_mem_Icc hθ)
  have hcosPos : 0 < Real.cos θ := by
    have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
    have hcosQuarter : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 :=
      Real.cos_pi_div_four
    by_cases hθnonneg : 0 ≤ θ
    · have hle : θ ≤ Real.pi / 4 := hθ.2
      exact (hcosQuarter ▸ hsqrt).trans_le
        (Real.cos_le_cos_of_nonneg_of_le_pi hθnonneg
          (by linarith [Real.pi_pos]) hle)
    · have hneg : 0 ≤ -θ := by linarith
      have hle : -θ ≤ Real.pi / 4 := by linarith [hθ.1]
      rw [← Real.cos_neg θ]
      exact (hcosQuarter ▸ hsqrt).trans_le
        (Real.cos_le_cos_of_nonneg_of_le_pi hneg
          (by linarith [Real.pi_pos]) hle)
  unfold radialToBoundary
  rw [Complex.div_ofReal_re, hmax]
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  exact div_self hcosPos.ne'

theorem finalSideWeights_take_last (l : ℕ) :
    (finalSideWeights l).take l = List.replicate l 3 := by
  simp [finalSideWeights]

@[simp]
theorem finalSideWeights_get_last (l : ℕ) :
    (finalSideWeights l).get
        ⟨l, by simp only [finalSideWeights_length]; omega⟩ = l := by
  simp [finalSideWeights]

@[simp]
theorem firstSideWeights_get_zero (r : ℕ) :
    (firstSideWeights r).get
        ⟨0, by simp only [firstSideWeights_length]; omega⟩ = r := by
  simp [firstSideWeights]

theorem finalSideWeightedCircle_apply
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    WeightedCircle.circleHomeomorph
        (finalSideWeights l) (finalSideWeights_positive hl)
        (finalSideWeights_ne_nil hl)
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      Circle.exp
        (2 * Real.pi / (4 * l) *
          (3 * l + l * (t : ℝ))) := by
  let i :
      Fin (finalSideWeights l).length :=
    ⟨l, by simp only [finalSideWeights_length]; omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (finalSideWeights l) (finalSideWeights_positive hl)
      (finalSideWeights_ne_nil hl) i t
  rw [show PolygonCell.sideAngle (Fin.last l) t =
      2 * Real.pi / (finalSideWeights l).length *
        ((i : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [Fin.val_last, i, finalSideWeights_length]
    ring] 
  rw [h]
  congr 1
  simp only [finalSideWeights_sum, finalSideWeights_get_last,
    i, Fin.getElem_fin, finalSideWeights_take_last, List.sum_replicate,
    nsmul_eq_mul]
  push_cast
  ring

theorem firstSideWeightedCircle_apply
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    WeightedCircle.circleHomeomorph
        (firstSideWeights r) (firstSideWeights_positive hr)
        (firstSideWeights_ne_nil hr)
        (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      Circle.exp
        (2 * Real.pi / (4 * r) * (r * (t : ℝ))) := by
  let i :
      Fin (firstSideWeights r).length :=
    ⟨0, by simp only [firstSideWeights_length]; omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (firstSideWeights r) (firstSideWeights_positive hr)
      (firstSideWeights_ne_nil hr) i t
  rw [show PolygonCell.sideAngle (0 : Fin (r + 1)) t =
      2 * Real.pi / (firstSideWeights r).length *
        ((i : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, i,
      firstSideWeights_length]
    ring]
  rw [h]
  congr 1
  simp only [firstSideWeights_sum, firstSideWeights_get_zero,
    i, Fin.getElem_fin, List.take_zero, List.sum_nil, Nat.cast_zero,
    zero_add]
  push_cast
  ring

theorem finalSideBoundaryHomeomorph_apply
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    finalSideBoundaryHomeomorph l hl
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      circleBoundaryHomeomorph
        (Circle.exp
          (-(Real.pi / 4) + Real.pi / 2 * (t : ℝ))) := by
  change
    circleBoundaryHomeomorph
        (quarterRotation
          (WeightedCircle.circleHomeomorph
            (finalSideWeights l) (finalSideWeights_positive hl)
            (finalSideWeights_ne_nil hl)
            (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)))) =
      _
  rw [finalSideWeightedCircle_apply l hl t]
  apply congrArg circleBoundaryHomeomorph
  change
    Circle.exp (Real.pi / 4) *
        Circle.exp
          (2 * Real.pi / (4 * l) *
            (3 * l + l * (t : ℝ))) =
      Circle.exp
        (-(Real.pi / 4) + Real.pi / 2 * (t : ℝ))
  rw [← Circle.exp_add]
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  have hlReal : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp [hlReal]
  ring

theorem firstSideBoundaryHomeomorph_apply
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    firstSideBoundaryHomeomorph r hr
        (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      circleBoundaryHomeomorph
        (Circle.exp
          (Real.pi / 4 - Real.pi / 2 * (t : ℝ))) := by
  change
    circleBoundaryHomeomorph
        (quarterRotation
          ((Homeomorph.inv Circle)
            (WeightedCircle.circleHomeomorph
              (firstSideWeights r) (firstSideWeights_positive hr)
              (firstSideWeights_ne_nil hr)
              (Circle.exp
                (PolygonCell.sideAngle (0 : Fin (r + 1)) t))))) =
      _
  rw [firstSideWeightedCircle_apply r hr t]
  apply congrArg circleBoundaryHomeomorph
  change
    Circle.exp (Real.pi / 4) *
        (Circle.exp
          (2 * Real.pi / (4 * r) * (r * (t : ℝ))))⁻¹ =
      Circle.exp
        (Real.pi / 4 - Real.pi / 2 * (t : ℝ))
  rw [← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrReal]
  ring

/-- The two fresh sides have exactly the same point of the local square after reversing the
right-child parameter. -/
theorem finalSide_eq_firstSide_symm
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) (t : unitInterval) :
    finalSideBoundaryHomeomorph l hl
        (Circle.exp (PolygonCell.sideAngle (Fin.last l) t)) =
      firstSideBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1))
            (unitInterval.symm t))) := by
  rw [finalSideBoundaryHomeomorph_apply,
    firstSideBoundaryHomeomorph_apply]
  apply congrArg circleBoundaryHomeomorph
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  simp only [unitInterval.coe_symm_eq, Int.cast_zero, zero_mul, add_zero]
  ring

theorem finalSideBoundaryHomeomorph_re
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    (finalSideBoundaryHomeomorph l hl
      (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))).1.re = 1 := by
  rw [finalSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  apply radialToBoundary_re_eq_one_of_angle
  constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]

theorem firstSideBoundaryHomeomorph_re
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (firstSideBoundaryHomeomorph r hr
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin (r + 1)) t))).1.re = 1 := by
  rw [firstSideBoundaryHomeomorph_apply]
  rw [circleBoundaryHomeomorph_val]
  apply radialToBoundary_re_eq_one_of_angle
  constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]

/-- Square model for the selected child of a nondegenerate P2 split. -/
noncomputable def finalSideCellHomeomorph (l : ℕ) (hl : 0 < l) :
    PolygonCell (l + 1) ≃ₜ square :=
  cellSquareHomeomorph (finalSideBoundaryHomeomorph l hl)

/-- Square model for the right child of a nondegenerate P2 split. -/
noncomputable def firstSideCellHomeomorph (r : ℕ) (hr : 0 < r) :
    PolygonCell (r + 1) ≃ₜ square :=
  cellSquareHomeomorph (firstSideBoundaryHomeomorph r hr)

@[simp]
theorem finalSideCellHomeomorph_side
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    finalSideCellHomeomorph l hl
        (PolygonCell.side (Fin.last l) t) =
      boundaryInclusion
        (finalSideBoundaryHomeomorph l hl
          (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))) := by
  exact cellSquareHomeomorph_ofCircle
    (finalSideBoundaryHomeomorph l hl)
    (Circle.exp (PolygonCell.sideAngle (Fin.last l) t))

@[simp]
theorem firstSideCellHomeomorph_side
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    firstSideCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1)) t) =
      boundaryInclusion
        (firstSideBoundaryHomeomorph r hr
          (Circle.exp
            (PolygonCell.sideAngle (0 : Fin (r + 1)) t))) := by
  exact cellSquareHomeomorph_ofCircle
    (firstSideBoundaryHomeomorph r hr)
    (Circle.exp (PolygonCell.sideAngle (0 : Fin (r + 1)) t))

theorem finalSideCell_eq_firstSideCell_symm
    (l r : ℕ) (hl : 0 < l) (hr : 0 < r) (t : unitInterval) :
    (finalSideCellHomeomorph l hl
        (PolygonCell.side (Fin.last l) t)).1 =
      (firstSideCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1))
          (unitInterval.symm t))).1 := by
  rw [finalSideCellHomeomorph_side, firstSideCellHomeomorph_side]
  exact congrArg (fun z : boundary ↦ z.1)
    (finalSide_eq_firstSide_symm l r hl hr t)

theorem finalSideCellHomeomorph_side_re
    (l : ℕ) (hl : 0 < l) (t : unitInterval) :
    (finalSideCellHomeomorph l hl
      (PolygonCell.side (Fin.last l) t)).1.re = 1 := by
  rw [finalSideCellHomeomorph_side]
  exact finalSideBoundaryHomeomorph_re l hl t

theorem firstSideCellHomeomorph_side_re
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (firstSideCellHomeomorph r hr
      (PolygonCell.side (0 : Fin (r + 1)) t)).1.re = 1 := by
  rw [firstSideCellHomeomorph_side]
  exact firstSideBoundaryHomeomorph_re r hr t

/-! ## Gluing two square models along their right sides -/

/-- Place a local square as the left half of the outer square. -/
noncomputable def leftPlacement : C(square, square) where
  toFun z :=
    ⟨Complex.mk ((z.1.re - 1) / 2) z.1.im, by
      change max |(z.1.re - 1) / 2| |z.1.im| ≤ 1
      have hre := abs_re_le_maxAbs z.1 |>.trans z.2
      have him := abs_im_le_maxAbs z.1 |>.trans z.2
      rw [abs_le] at hre him
      apply max_le
      · rw [abs_le]
        constructor <;> linarith [hre.1, hre.2]
      · exact (abs_le.mpr him)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : square ↦
      Complex.mk ((z.1.re - 1) / 2) z.1.im)
    have hre : Continuous (fun z : square ↦ (z.1.re - 1) / 2) := by
      fun_prop
    have him : Continuous (fun z : square ↦ z.1.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    convert
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul
          (continuous_const : Continuous (fun _ : square ↦ Complex.I))) using 1
    funext z
    apply Complex.ext <;> simp

/-- Place a local square, reflected horizontally, as the right half of the outer square. -/
noncomputable def rightPlacement : C(square, square) where
  toFun z :=
    ⟨Complex.mk ((1 - z.1.re) / 2) z.1.im, by
      change max |(1 - z.1.re) / 2| |z.1.im| ≤ 1
      have hre := abs_re_le_maxAbs z.1 |>.trans z.2
      have him := abs_im_le_maxAbs z.1 |>.trans z.2
      rw [abs_le] at hre him
      apply max_le
      · rw [abs_le]
        constructor <;> linarith [hre.1, hre.2]
      · exact (abs_le.mpr him)⟩
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : square ↦
      Complex.mk ((1 - z.1.re) / 2) z.1.im)
    have hre : Continuous (fun z : square ↦ (1 - z.1.re) / 2) := by
      fun_prop
    have him : Continuous (fun z : square ↦ z.1.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    convert
      (Complex.continuous_ofReal.comp hre).add
        ((Complex.continuous_ofReal.comp him).mul
          (continuous_const : Continuous (fun _ : square ↦ Complex.I))) using 1
    funext z
    apply Complex.ext <;> simp

@[simp]
theorem leftPlacement_re (z : square) :
    (leftPlacement z).1.re = (z.1.re - 1) / 2 :=
  rfl

@[simp]
theorem leftPlacement_im (z : square) :
    (leftPlacement z).1.im = z.1.im :=
  rfl

@[simp]
theorem rightPlacement_re (z : square) :
    (rightPlacement z).1.re = (1 - z.1.re) / 2 :=
  rfl

@[simp]
theorem rightPlacement_im (z : square) :
    (rightPlacement z).1.im = z.1.im :=
  rfl

theorem leftPlacement_injective : Function.Injective leftPlacement := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have hre := congrArg (fun q : square ↦ q.1.re) h
    simp only [leftPlacement_re] at hre
    linarith
  · simpa only [leftPlacement_im] using
      congrArg (fun q : square ↦ q.1.im) h

theorem rightPlacement_injective : Function.Injective rightPlacement := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have hre := congrArg (fun q : square ↦ q.1.re) h
    simp only [rightPlacement_re] at hre
    linarith
  · simpa only [rightPlacement_im] using
      congrArg (fun q : square ↦ q.1.im) h

theorem leftPlacement_re_nonpos (z : square) :
    (leftPlacement z).1.re ≤ 0 := by
  have hre := abs_re_le_maxAbs z.1 |>.trans z.2
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (le_trans (le_abs_self _) hre)) (by norm_num)

theorem rightPlacement_re_nonneg (z : square) :
    0 ≤ (rightPlacement z).1.re := by
  have hre := abs_re_le_maxAbs z.1 |>.trans z.2
  exact div_nonneg (sub_nonneg.mpr (le_trans (le_abs_self _) hre))
    (by norm_num)

/-- The two placements agree on their common local right side. -/
theorem leftPlacement_eq_rightPlacement_of_re_eq_one
    (z w : square) (hreZ : z.1.re = 1) (hreW : w.1.re = 1)
    (him : z.1.im = w.1.im) :
    leftPlacement z = rightPlacement w := by
  apply Subtype.ext
  apply Complex.ext <;> simp [hreZ, hreW, him]

theorem exists_leftPlacement_of_re_nonpos
    (z : square) (hz : z.1.re ≤ 0) :
    ∃ w : square, leftPlacement w = z := by
  let w : ℂ := Complex.mk (2 * z.1.re + 1) z.1.im
  have hw : w ∈ square := by
    change max |2 * z.1.re + 1| |z.1.im| ≤ 1
    have hre := abs_re_le_maxAbs z.1 |>.trans z.2
    have him := abs_im_le_maxAbs z.1 |>.trans z.2
    rw [abs_le] at hre him
    apply max_le
    · rw [abs_le]
      constructor <;> linarith [hre.1, hz]
    · exact abs_le.mpr him
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply Complex.ext <;> simp [w] <;> ring

theorem exists_rightPlacement_of_re_nonneg
    (z : square) (hz : 0 ≤ z.1.re) :
    ∃ w : square, rightPlacement w = z := by
  let w : ℂ := Complex.mk (1 - 2 * z.1.re) z.1.im
  have hw : w ∈ square := by
    change max |1 - 2 * z.1.re| |z.1.im| ≤ 1
    have hre := abs_re_le_maxAbs z.1 |>.trans z.2
    have him := abs_im_le_maxAbs z.1 |>.trans z.2
    rw [abs_le] at hre him
    apply max_le
    · rw [abs_le]
      constructor <;> linarith [hre.2, hz]
    · exact abs_le.mpr him
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply Complex.ext <;> simp [w] <;> ring

theorem leftPlacement_or_rightPlacement (z : square) :
    (∃ w : square, leftPlacement w = z) ∨
      (∃ w : square, rightPlacement w = z) := by
  rcases le_total z.1.re 0 with h | h
  · exact Or.inl (exists_leftPlacement_of_re_nonpos z h)
  · exact Or.inr (exists_rightPlacement_of_re_nonneg z h)

/-! ## Gluing two square disks along their distinguished sides -/

/-- The disjoint union of the two local square disks. -/
abbrev SquarePair :=
  Sum square square

/--
The generating seam relation: the right side of the left local square is glued, point for
point, to the right side of the horizontally reflected right local square.
-/
inductive SeamGenerator : SquarePair → SquarePair → Prop
  | glue (z w : square) (hz : z.1.re = 1) (hw : w.1.re = 1)
      (him : z.1.im = w.1.im) :
      SeamGenerator (.inl z) (.inr w)

/-- The equivalence relation generated by the common side of the two square disks. -/
abbrev seamSetoid : Setoid SquarePair :=
  Relation.EqvGen.setoid SeamGenerator

/-- The topological quotient obtained by gluing the two local square disks along the seam. -/
abbrev SquareGluing :=
  Quotient seamSetoid

/-- Merge the two local squares into the left and right halves of one outer square. -/
noncomputable def squarePairMerge : SquarePair → square :=
  Sum.elim leftPlacement rightPlacement

theorem continuous_squarePairMerge :
    Continuous squarePairMerge :=
  leftPlacement.continuous.sumElim rightPlacement.continuous

theorem squarePairMerge_eq_of_seamGenerator
    {x y : SquarePair} (hxy : SeamGenerator x y) :
    squarePairMerge x = squarePairMerge y := by
  cases hxy with
  | glue z w hz hw him =>
      exact leftPlacement_eq_rightPlacement_of_re_eq_one z w hz hw him

/-- The merge map is constant on the equivalence closure of the seam relation. -/
theorem squarePairMerge_respects
    {x y : SquarePair} (hxy : Relation.EqvGen SeamGenerator x y) :
    squarePairMerge x = squarePairMerge y := by
  induction hxy with
  | rel _ _ h => exact squarePairMerge_eq_of_seamGenerator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem square_re_le_one (z : square) :
    z.1.re ≤ 1 :=
  (le_abs_self z.1.re).trans (abs_re_le_maxAbs z.1 |>.trans z.2)

/-- Equality between opposite merged summands can only occur on the declared seam. -/
theorem squarePairMerge_eqvGen_inl_inr
    (z w : square)
    (hzw : squarePairMerge (.inl z) = squarePairMerge (.inr w)) :
    Relation.EqvGen SeamGenerator (.inl z) (.inr w) := by
  have hre := congrArg (fun q : square ↦ q.1.re) hzw
  have hz : z.1.re = 1 := by
    simp only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_re, rightPlacement_re] at hre
    linarith [square_re_le_one z, square_re_le_one w]
  have hw : w.1.re = 1 := by
    simp only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_re, rightPlacement_re] at hre
    linarith [square_re_le_one z, square_re_le_one w]
  have him : z.1.im = w.1.im := by
    simpa only [squarePairMerge, Sum.elim_inl, Sum.elim_inr,
      leftPlacement_im, rightPlacement_im] using
        congrArg (fun q : square ↦ q.1.im) hzw
  exact Relation.EqvGen.rel _ _
    (SeamGenerator.glue z w hz hw him)

/--
No identifications are hidden by the planar merge: equality after merging is exactly generated
by equality inside one summand and the declared seam relation.
-/
theorem squarePairMerge_eqvGen_of_eq
    {x y : SquarePair} (hxy : squarePairMerge x = squarePairMerge y) :
    Relation.EqvGen SeamGenerator x y := by
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          have hzw : z = w := leftPlacement_injective hxy
          subst w
          exact Relation.EqvGen.refl _
      | inr w =>
          exact squarePairMerge_eqvGen_inl_inr z w hxy
  | inr z =>
      cases y with
      | inl w =>
          exact Relation.EqvGen.symm _ _
            (squarePairMerge_eqvGen_inl_inr w z hxy.symm)
      | inr w =>
          have hzw : z = w := rightPlacement_injective hxy
          subst w
          exact Relation.EqvGen.refl _

/-- The continuous map induced on the quotient by merging the two local squares. -/
noncomputable def squareGluingMap : C(SquareGluing, square) where
  toFun :=
    Quotient.lift squarePairMerge fun _ _ hxy ↦ squarePairMerge_respects hxy
  continuous_toFun :=
    continuous_squarePairMerge.quotient_lift fun _ _ hxy ↦
      squarePairMerge_respects hxy

@[simp]
theorem squareGluingMap_mk (x : SquarePair) :
    squareGluingMap (@Quotient.mk'' SquarePair seamSetoid x) =
      squarePairMerge x :=
  rfl

theorem squareGluingMap_injective :
    Function.Injective squareGluingMap := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
          apply Quotient.sound
          apply squarePairMerge_eqvGen_of_eq
          simpa only [squareGluingMap_mk] using hqr

theorem squareGluingMap_surjective :
    Function.Surjective squareGluingMap := by
  intro z
  rcases leftPlacement_or_rightPlacement z with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine ⟨@Quotient.mk'' SquarePair seamSetoid (.inl w), ?_⟩
    change leftPlacement w = z
    exact hw
  · refine ⟨@Quotient.mk'' SquarePair seamSetoid (.inr w), ?_⟩
    change rightPlacement w = z
    exact hw

theorem isCompact_square : IsCompact square :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_square, isBounded_square⟩

/-- Gluing two square disks along the selected sides is again a closed disk. -/
noncomputable def squareGluingHomeomorph : SquareGluing ≃ₜ square := by
  letI : CompactSpace square :=
    isCompact_iff_compactSpace.mp isCompact_square
  let e : SquareGluing ≃ square :=
    Equiv.ofBijective squareGluingMap
      ⟨squareGluingMap_injective, squareGluingMap_surjective⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) squareGluingMap.continuous

@[simp]
theorem squareGluingHomeomorph_apply (q : SquareGluing) :
    squareGluingHomeomorph q = squareGluingMap q :=
  rfl

end DiskSquare

end LeanEval.Topology.ClassificationOfSurfaces
