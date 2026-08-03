import Schoenflies.TransverseIntersections

/-!
# Ordered crossings of an injective path

The local determinant calculation says that a transverse straight arc meets
the two complementary regions of a Jordan circle on opposite sides.  For the
finite parity argument we need the stronger, ordered version: the two points
can be chosen before and after the intersection in the parameter order of an
injective path.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle

/-- An injective path which is locally straight and transverse to a locally
straight Jordan circle changes complementary regions at the crossing, in any
prescribed parameter interval around that crossing. -/
theorem exists_ordered_points_opposite_sides_between
    (J : JordanCircle) {f : unitInterval → Plane}
    {a t b : unitInterval}
    {p d e : Plane} {rJ rPath : ℝ}
    (hfContinuous : Continuous f) (hfInjective : Injective f)
    (hat : a < t) (htb : t < b)
    (hft : f t = p)
    (hrJ : 0 < rJ) (hpJ : p ∈ J.carrier)
    (hlocalJ : ball p rJ ∩ J.carrier =
      ball p rJ ∩ determinantLine p d)
    (hrPath : 0 < rPath)
    (hlocalPath : ball p rPath ∩ range f =
      ball p rPath ∩ determinantLine p e)
    (htransverse : planeDet e d ≠ 0) :
    ∃ l u : unitInterval, a < l ∧ l < t ∧ t < u ∧ u < b ∧
      (((f l ∈ J.inside) ∧ (f u ∈ J.outside)) ∨
        ((f l ∈ J.outside) ∧ (f u ∈ J.inside))) := by
  let r : ℝ := min rJ rPath
  have hr : 0 < r := lt_min hrJ hrPath
  have hballNhds : ball p r ∈ nhds (f t) := by
    rw [hft]
    exact ball_mem_nhds p hr
  have hpreimageNhds : f ⁻¹' ball p r ∈ nhds t :=
    hfContinuous.continuousAt hballNhds
  have hboundedNhds :
      f ⁻¹' ball p r ∩ Ioo a b ∈ nhds t :=
    Filter.inter_mem hpreimageNhds (Ioo_mem_nhds hat htb)
  obtain ⟨l₀, u₀, htIoo, hIoo⟩ :=
    (mem_nhds_iff_exists_Ioo_subset'
      ⟨a, hat⟩ ⟨b, htb⟩).mp hboundedNhds
  obtain ⟨l, hl₀, hlt⟩ := exists_between htIoo.1
  obtain ⟨u, htu, hu₀⟩ := exists_between htIoo.2
  have hintervalBall : ∀ z ∈ Icc l u, f z ∈ ball p r := by
    intro z hz
    exact (hIoo ⟨hl₀.trans_le hz.1, hz.2.trans_lt hu₀⟩).1
  have hal : a < l :=
    (hIoo ⟨hl₀, hlt.trans htIoo.2⟩).2.1
  have hub : u < b :=
    (hIoo ⟨htIoo.1.trans htu, hu₀⟩).2.2
  have hintervalPathLine : ∀ z ∈ Icc l u,
      f z ∈ determinantLine p e := by
    intro z hz
    have hzPath : f z ∈ ball p rPath ∩ range f :=
      ⟨ball_subset_ball (min_le_right _ _) (hintervalBall z hz),
        ⟨z, rfl⟩⟩
    rw [hlocalPath] at hzPath
    exact hzPath.2
  have he : e ≠ 0 := by
    intro he
    apply htransverse
    simp [he, planeDet]
  obtain ⟨k, hek⟩ : ∃ k : Fin 2, e k ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_ne_iff] at hall
    apply he
    ext k
    exact hall k
  let c : unitInterval → ℝ := fun z ↦ f z k
  have hcContinuous : Continuous c := by
    fun_prop
  have hcInjective : Set.InjOn c (Icc l u) := by
    intro x hx y hy hxy
    apply hfInjective
    obtain ⟨sx, hsx⟩ := exists_smul_eq_of_planeDet_eq_zero he
      (hintervalPathLine x hx)
    obtain ⟨sy, hsy⟩ := exists_smul_eq_of_planeDet_eq_zero he
      (hintervalPathLine y hy)
    have hsxCoord := congrArg (fun z : Plane ↦ z k) hsx
    have hsyCoord := congrArg (fun z : Plane ↦ z k) hsy
    have hs : sx = sy := by
      change f x k = f y k at hxy
      change sx * e k = f x k - p k at hsxCoord
      change sy * e k = f y k - p k at hsyCoord
      apply (mul_left_cancel₀ hek)
      linarith
    apply sub_left_inj.mp
    rw [← hsx, ← hsy, hs]
  have hlu : l ≤ u := (hlt.trans htu).le
  have hlMem : l ∈ Icc l u := ⟨le_rfl, hlu⟩
  have htMem : t ∈ Icc l u := ⟨hlt.le, htu.le⟩
  have huMem : u ∈ Icc l u := ⟨hlu, le_rfl⟩
  have hcoordinateOrder :
      (c l < c t ∧ c t < c u) ∨ (c u < c t ∧ c t < c l) := by
    rcases hcContinuous.continuousOn.strictMonoOn_of_injOn_Icc'
        hlu hcInjective with hmono | hanti
    · exact Or.inl ⟨hmono hlMem htMem hlt, hmono htMem huMem htu⟩
    · exact Or.inr ⟨hanti htMem huMem htu, hanti hlMem htMem hlt⟩
  have hlLine := hintervalPathLine l hlMem
  have huLine := hintervalPathLine u huMem
  obtain ⟨sl, hsl⟩ := exists_smul_eq_of_planeDet_eq_zero he hlLine
  obtain ⟨su, hsu⟩ := exists_smul_eq_of_planeDet_eq_zero he huLine
  have hslCoord := congrArg (fun z : Plane ↦ z k) hsl
  have hsuCoord := congrArg (fun z : Plane ↦ z k) hsu
  have hct : c t = p k := by simp only [c, hft]
  have hslEq : sl * e k = c l - c t := by
    change sl * e k = f l k - f t k
    simpa [hft] using hslCoord
  have hsuEq : su * e k = c u - c t := by
    change su * e k = f u k - f t k
    simpa [hft] using hsuCoord
  have hscalarProduct : sl * su < 0 := by
    rcases hcoordinateOrder with hmono | hanti
    · rcases lt_or_gt_of_ne hek with hekNeg | hekPos
      · have hslPos : 0 < sl := by nlinarith [hslEq]
        have hsuNeg : su < 0 := by nlinarith [hsuEq]
        exact mul_neg_of_pos_of_neg hslPos hsuNeg
      · have hslNeg : sl < 0 := by nlinarith [hslEq]
        have hsuPos : 0 < su := by nlinarith [hsuEq]
        exact mul_neg_of_neg_of_pos hslNeg hsuPos
    · rcases lt_or_gt_of_ne hek with hekNeg | hekPos
      · have hslNeg : sl < 0 := by nlinarith [hslEq]
        have hsuPos : 0 < su := by nlinarith [hsuEq]
        exact mul_neg_of_neg_of_pos hslNeg hsuPos
      · have hslPos : 0 < sl := by nlinarith [hslEq]
        have hsuNeg : su < 0 := by nlinarith [hsuEq]
        exact mul_neg_of_pos_of_neg hslPos hsuNeg
  have hlDet : planeDet (f l - p) d = sl * planeDet e d := by
    rw [← hsl]
    exact planeDet_smul_left sl e d
  have huDet : planeDet (f u - p) d = su * planeDet e d := by
    rw [← hsu]
    exact planeDet_smul_left su e d
  have hdetProduct :
      planeDet (f l - p) d * planeDet (f u - p) d < 0 := by
    rw [hlDet, huDet]
    calc
      (sl * planeDet e d) * (su * planeDet e d) =
          (sl * su) * (planeDet e d * planeDet e d) := by ring
      _ < 0 := mul_neg_of_neg_of_pos hscalarProduct
        (mul_self_pos.mpr htransverse)
  have hlBallJ : f l ∈ ball p rJ :=
    ball_subset_ball (min_le_left _ _) (hintervalBall l hlMem)
  have huBallJ : f u ∈ ball p rJ :=
    ball_subset_ball (min_le_left _ _) (hintervalBall u huMem)
  have hsides := J.local_lineSide_dichotomy hrJ hpJ hlocalJ
  rcases (mul_neg_iff.mp hdetProduct) with hposNeg | hnegPos
  · have hlPos : f l ∈ positiveLineSide p d := hposNeg.1
    have huNeg : f u ∈ negativeLineSide p d := hposNeg.2
    rcases hsides with horder | horder
    · exact ⟨l, u, hal, hlt, htu, hub, Or.inl
        ⟨horder.1 ⟨hlBallJ, hlPos⟩, horder.2 ⟨huBallJ, huNeg⟩⟩⟩
    · exact ⟨l, u, hal, hlt, htu, hub, Or.inr
        ⟨horder.1 ⟨hlBallJ, hlPos⟩, horder.2 ⟨huBallJ, huNeg⟩⟩⟩
  · have hlNeg : f l ∈ negativeLineSide p d := hnegPos.1
    have huPos : f u ∈ positiveLineSide p d := hnegPos.2
    rcases hsides with horder | horder
    · exact ⟨l, u, hal, hlt, htu, hub, Or.inr
        ⟨horder.2 ⟨hlBallJ, hlNeg⟩, horder.1 ⟨huBallJ, huPos⟩⟩⟩
    · exact ⟨l, u, hal, hlt, htu, hub, Or.inl
        ⟨horder.2 ⟨hlBallJ, hlNeg⟩, horder.1 ⟨huBallJ, huPos⟩⟩⟩

/-- The unbounded-neighborhood form of
`exists_ordered_points_opposite_sides_between`. -/
theorem exists_ordered_points_opposite_sides
    (J : JordanCircle) {f : unitInterval → Plane} {t : unitInterval}
    {p d e : Plane} {rJ rPath : ℝ}
    (hfContinuous : Continuous f) (hfInjective : Injective f)
    (htLower : (⊥ : unitInterval) < t)
    (htUpper : t < (⊤ : unitInterval))
    (hft : f t = p)
    (hrJ : 0 < rJ) (hpJ : p ∈ J.carrier)
    (hlocalJ : ball p rJ ∩ J.carrier =
      ball p rJ ∩ determinantLine p d)
    (hrPath : 0 < rPath)
    (hlocalPath : ball p rPath ∩ range f =
      ball p rPath ∩ determinantLine p e)
    (htransverse : planeDet e d ≠ 0) :
    ∃ l u : unitInterval, l < t ∧ t < u ∧
      (((f l ∈ J.inside) ∧ (f u ∈ J.outside)) ∨
        ((f l ∈ J.outside) ∧ (f u ∈ J.inside))) := by
  obtain ⟨l, u, _hlower, hlt, htu, _hupper, hsides⟩ :=
    J.exists_ordered_points_opposite_sides_between
      hfContinuous hfInjective htLower htUpper hft hrJ hpJ hlocalJ
      hrPath hlocalPath htransverse
  exact ⟨l, u, hlt, htu, hsides⟩

end JordanCircle

end Schoenflies
