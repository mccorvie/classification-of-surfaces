import Schoenflies.TwoArcJordan

/-!
# Path representatives of the two arcs of a Jordan circle

The Jordan-curve split theorem supplies its arcs as closed sets
homeomorphic to `unitInterval`.  Finite annulus arguments need actual
injective `Path`s with exact ranges.  This file provides that conversion and
packages the two complementary boundary paths of a Jordan circle.
-/

namespace Schoenflies

open Metric Set Function

noncomputable section

namespace JordanArcPaths

variable {X : Type*} [TopologicalSpace X]

/-- Read a path in a subtype as an ambient path. -/
def subtypeValPath {A : Set X} {x y : A} (p : Path x y) :
    Path (x : X) (y : X) where
  toFun t := (p t : X)
  continuous_toFun := continuous_subtype_val.comp p.continuous
  source' := congrArg Subtype.val p.source
  target' := congrArg Subtype.val p.target

theorem subtypeValPath_injective {A : Set X} {x y : A}
    (p : Path x y) (hp : Injective p) :
    Injective (subtypeValPath p) := by
  intro s t hst
  apply hp
  exact Subtype.ext hst

theorem range_subtypeValPath {A : Set X} {x y : A}
    (p : Path x y) :
    range (subtypeValPath p) =
      ((fun z : A => (z : X)) '' range p) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨p t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- Orient a homeomorphism from a closed arc to the unit interval from its
chosen zero endpoint to its chosen one endpoint. -/
private def pathOfEndpointHomeomorph {A : Set X} (e : A ≃ₜ unitInterval)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : e ⟨x, hx⟩ = 0) (hy1 : e ⟨y, hy⟩ = 1) : Path x y where
  toFun t := (e.symm t : A)
  continuous_toFun := continuous_subtype_val.comp e.symm.continuous
  source' := by
    have h : e.symm 0 = (⟨x, hx⟩ : A) := by
      rw [← hx0, e.symm_apply_apply]
    exact congrArg Subtype.val h
  target' := by
    have h : e.symm 1 = (⟨y, hy⟩ : A) := by
      rw [← hy1, e.symm_apply_apply]
    exact congrArg Subtype.val h

private theorem pathOfEndpointHomeomorph_injective
    {A : Set X} (e : A ≃ₜ unitInterval)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : e ⟨x, hx⟩ = 0) (hy1 : e ⟨y, hy⟩ = 1) :
    Injective (pathOfEndpointHomeomorph e hx hy hx0 hy1) := by
  intro s t hst
  exact e.symm.injective (Subtype.ext hst)

private theorem range_pathOfEndpointHomeomorph
    {A : Set X} (e : A ≃ₜ unitInterval)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : e ⟨x, hx⟩ = 0) (hy1 : e ⟨y, hy⟩ = 1) :
    range (pathOfEndpointHomeomorph e hx hy hx0 hy1) = A := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact (e.symm t).2
  · intro hz
    refine ⟨e ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)

/-- A closed arc homeomorphic to the interval, with two distinct designated
endpoints mapping as a set to `{0,1}`, admits an injective path with exactly
that arc as its range. -/
theorem exists_injectivePath_of_arcHomeomorph {A : Set X}
    (e : A ≃ₜ unitInterval) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y)
    (hend : ({e ⟨x, hx⟩, e ⟨y, hy⟩} : Set unitInterval) = {0, 1}) :
    ∃ p : Path x y, Injective p ∧ range p = A := by
  have hxEnd : e ⟨x, hx⟩ = 0 ∨ e ⟨x, hx⟩ = 1 := by
    have : e ⟨x, hx⟩ ∈ ({0, 1} : Set unitInterval) := by
      rw [← hend]
      exact Set.mem_insert _ _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hyEnd : e ⟨y, hy⟩ = 0 ∨ e ⟨y, hy⟩ = 1 := by
    have : e ⟨y, hy⟩ ∈ ({0, 1} : Set unitInterval) := by
      rw [← hend]
      exact Set.mem_insert_iff.mpr (Or.inr rfl)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hvaluesNe : e ⟨x, hx⟩ ≠ e ⟨y, hy⟩ := by
    intro h
    have hsub : (⟨x, hx⟩ : A) = ⟨y, hy⟩ := e.injective h
    exact hxy (congrArg Subtype.val hsub)
  rcases hxEnd with hx0 | hx1
  · have hy1 : e ⟨y, hy⟩ = 1 := hyEnd.resolve_left <| by
      intro hy0
      exact hvaluesNe (hx0.trans hy0.symm)
    let p := pathOfEndpointHomeomorph e hx hy hx0 hy1
    exact ⟨p, pathOfEndpointHomeomorph_injective e hx hy hx0 hy1,
      range_pathOfEndpointHomeomorph e hx hy hx0 hy1⟩
  · have hy0 : e ⟨y, hy⟩ = 0 := hyEnd.resolve_right <| by
      intro hy1
      exact hvaluesNe (hx1.trans hy1.symm)
    let q := pathOfEndpointHomeomorph e hy hx hy0 hx1
    refine ⟨q.symm, ?_, ?_⟩
    · exact (pathOfEndpointHomeomorph_injective e hy hx hy0 hx1).comp
        unitInterval.symm_bijective.injective
    · rw [Path.symm_range]
      exact range_pathOfEndpointHomeomorph e hy hx hy0 hx1

end JordanArcPaths

namespace JordanCircle

variable (J : JordanCircle)

/-- Two oppositely oriented injective paths which are precisely the two
closed boundary arcs between `x` and `y`. -/
structure TwoBoundaryArcPaths (x y : Plane) where
  first : Path x y
  second : Path y x
  first_injective : Injective first
  second_injective : Injective second
  cover : range first ∪ range second = J.carrier
  overlap : range first ∩ range second = {x, y}

/-- The set-theoretic two-arc split of a Jordan circle can always be upgraded
to exact embedded paths in the ambient plane. -/
theorem exists_twoBoundaryArcPaths {x y : Plane}
    (hx : x ∈ J.carrier) (hy : y ∈ J.carrier) (hxy : x ≠ y) :
    Nonempty (J.TwoBoundaryArcPaths x y) := by
  let xs : sphere (0 : Plane) 1 :=
    J.carrierHomeomorph.symm ⟨x, hx⟩
  let ys : sphere (0 : Plane) 1 :=
    J.carrierHomeomorph.symm ⟨y, hy⟩
  have hxs : J.carrierHomeomorph xs = (⟨x, hx⟩ : J.carrier) := by
    exact J.carrierHomeomorph.apply_symm_apply ⟨x, hx⟩
  have hys : J.carrierHomeomorph ys = (⟨y, hy⟩ : J.carrier) := by
    exact J.carrierHomeomorph.apply_symm_apply ⟨y, hy⟩
  have hxsys : xs ≠ ys := by
    intro h
    apply hxy
    exact congrArg Subtype.val (hxs.symm.trans <| h ▸ hys)
  have hxsVal : J.parametrization xs = x := congrArg Subtype.val hxs
  have hysVal : J.parametrization ys = y := congrArg Subtype.val hys
  have hperiod : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨alpha, halpha⟩ := JordanCurve.Arcs.param_surjective xs
  obtain ⟨betaZero, hbetaZero⟩ := JordanCurve.Arcs.param_surjective ys
  let beta : ℝ := toIocMod hperiod alpha betaZero
  have hbetaMem : beta ∈ Set.Ioc alpha (alpha + 2 * Real.pi) :=
    toIocMod_mem_Ioc hperiod alpha betaZero
  have hparamBeta : JordanCurve.Arcs.param beta = ys := by
    have hz : betaZero - beta =
        (toIocDiv hperiod alpha betaZero : ℤ) • (2 * Real.pi) :=
      self_sub_toIocMod hperiod alpha betaZero
    rw [zsmul_eq_mul] at hz
    have hsame : JordanCurve.Arcs.param beta =
        JordanCurve.Arcs.param betaZero := by
      rw [JordanCurve.Arcs.param_eq_iff]
      exact ⟨-(toIocDiv hperiod alpha betaZero), by
        push_cast
        linarith⟩
    rw [hsame, hbetaZero]
  have hbetaLt : beta < alpha + 2 * Real.pi := by
    rcases lt_or_eq_of_le hbetaMem.2 with hlt | heq
    · exact hlt
    · exfalso
      apply hxsys
      rw [← hparamBeta, heq, JordanCurve.Arcs.param_periodic, halpha]
  have hlengthFirst : beta - alpha < 2 * Real.pi := by linarith
  have hlengthSecond :
      (alpha + 2 * Real.pi) - beta < 2 * Real.pi := by
    linarith [hbetaMem.1]
  have hSphereCover :
      (JordanCurve.Arcs.param '' Set.Icc alpha beta) ∪
          (JordanCurve.Arcs.param ''
            Set.Icc beta (alpha + 2 * Real.pi)) = Set.univ := by
    rw [← Set.image_union,
      Set.Icc_union_Icc_eq_Icc hbetaMem.1.le hbetaLt.le,
      JordanCurve.Arcs.param_periodic.image_Icc hperiod alpha,
      JordanCurve.Arcs.param_surjective.range_eq]
  have hSphereOverlap :
      (JordanCurve.Arcs.param '' Set.Icc alpha beta) ∩
          (JordanCurve.Arcs.param ''
            Set.Icc beta (alpha + 2 * Real.pi)) = {xs, ys} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩
      have hst : JordanCurve.Arcs.param s =
          JordanCurve.Arcs.param t := hsz.trans htz.symm
      obtain ⟨m, hm⟩ := JordanCurve.Arcs.param_eq_iff.mp hst
      have heq : s - t = (m : ℝ) * (2 * Real.pi) := by
        linarith
      have hmUpper : (m : ℝ) ≤ 0 := by
        have hmul : (m : ℝ) * (2 * Real.pi) ≤
            0 * (2 * Real.pi) := by
          rw [zero_mul, ← heq]
          linarith [hs.2, ht.1]
        exact le_of_mul_le_mul_right hmul hperiod
      have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by
        have hmul : (-1 : ℝ) * (2 * Real.pi) ≤
            (m : ℝ) * (2 * Real.pi) := by
          rw [neg_one_mul, ← heq]
          linarith [hs.1, ht.2]
        exact le_of_mul_le_mul_right hmul hperiod
      have hmCases : m = 0 ∨ m = -1 := by
        have hm0 : m ≤ (0 : ℤ) := by exact_mod_cast hmUpper
        have hm1 : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
        omega
      rcases hmCases with hmZero | hmNegOne
      · right
        have hstEq : s = t := by
          rw [hmZero] at hm
          push_cast at hm
          linarith
        have hsBeta : s = beta :=
          le_antisymm hs.2 (by rw [hstEq]; exact ht.1)
        rw [← hsz, hsBeta, hparamBeta]
      · left
        have hstEq : s = t - 2 * Real.pi := by
          rw [hmNegOne] at hm
          push_cast at hm
          linarith
        have hsAlpha : s = alpha :=
          le_antisymm (by rw [hstEq]; linarith [ht.2]) hs.1
        rw [← hsz, hsAlpha, halpha]
    · rintro (rfl | rfl)
      · exact ⟨
          ⟨alpha, ⟨le_rfl, hbetaMem.1.le⟩, halpha⟩,
          ⟨alpha + 2 * Real.pi, ⟨hbetaLt.le, le_rfl⟩, by
            rw [JordanCurve.Arcs.param_periodic]
            exact halpha⟩⟩
      · exact ⟨
          ⟨beta, ⟨hbetaMem.1.le, le_rfl⟩, hparamBeta⟩,
          ⟨beta, ⟨le_rfl, hbetaLt.le⟩, hparamBeta⟩⟩
  let f : ℝ → Plane :=
    fun theta => J.parametrization (JordanCurve.Arcs.param theta)
  have hf : Continuous f :=
    J.continuous.comp JordanCurve.Arcs.continuous_param
  have hfAlpha : f alpha = x := by
    dsimp [f]
    rw [halpha, hxsVal]
  have hfBeta : f beta = y := by
    dsimp [f]
    rw [hparamBeta, hysVal]
  have hfPeriod : f (alpha + 2 * Real.pi) = x := by
    dsimp [f]
    rw [JordanCurve.Arcs.param_periodic, halpha, hxsVal]
  let pRaw : Path (f alpha) (f beta) := (Path.segment alpha beta).map hf
  let qRaw : Path (f beta) (f (alpha + 2 * Real.pi)) :=
    (Path.segment beta (alpha + 2 * Real.pi)).map hf
  let p : Path x y := pRaw.cast hfAlpha.symm hfBeta.symm
  let q : Path y x := qRaw.cast hfBeta.symm hfPeriod.symm
  have hpInjective : Injective p := by
    intro s t hst
    have hfst : f (Path.segment alpha beta s) =
        f (Path.segment alpha beta t) := by
      simpa only [p, pRaw, Path.cast_coe, Path.map_coe,
        Function.comp_apply] using hst
    have hparam : JordanCurve.Arcs.param
          (Path.segment alpha beta s) =
        JordanCurve.Arcs.param (Path.segment alpha beta t) :=
      J.injective hfst
    have hsMem : Path.segment alpha beta s ∈ Set.Icc alpha beta := by
      rw [← segment_eq_Icc hbetaMem.1.le, ← Path.range_segment]
      exact ⟨s, rfl⟩
    have htMem : Path.segment alpha beta t ∈ Set.Icc alpha beta := by
      rw [← segment_eq_Icc hbetaMem.1.le, ← Path.range_segment]
      exact ⟨t, rfl⟩
    exact Path.segment_injective_of_ne hbetaMem.1.ne <|
      JordanCurve.Arcs.param_injOn hlengthFirst hsMem htMem hparam
  have hqInjective : Injective q := by
    intro s t hst
    have hfst : f (Path.segment beta (alpha + 2 * Real.pi) s) =
        f (Path.segment beta (alpha + 2 * Real.pi) t) := by
      simpa only [q, qRaw, Path.cast_coe, Path.map_coe,
        Function.comp_apply] using hst
    have hparam : JordanCurve.Arcs.param
          (Path.segment beta (alpha + 2 * Real.pi) s) =
        JordanCurve.Arcs.param
          (Path.segment beta (alpha + 2 * Real.pi) t) :=
      J.injective hfst
    have hsMem : Path.segment beta (alpha + 2 * Real.pi) s ∈
        Set.Icc beta (alpha + 2 * Real.pi) := by
      rw [← segment_eq_Icc hbetaLt.le, ← Path.range_segment]
      exact ⟨s, rfl⟩
    have htMem : Path.segment beta (alpha + 2 * Real.pi) t ∈
        Set.Icc beta (alpha + 2 * Real.pi) := by
      rw [← segment_eq_Icc hbetaLt.le, ← Path.range_segment]
      exact ⟨t, rfl⟩
    exact Path.segment_injective_of_ne hbetaLt.ne <|
      JordanCurve.Arcs.param_injOn hlengthSecond
        hsMem htMem hparam
  have hpRange : range p =
      J.parametrization ''
        (JordanCurve.Arcs.param '' Set.Icc alpha beta) := by
    change range pRaw = _
    rw [show (pRaw : unitInterval → Plane) =
        f ∘ Path.segment alpha beta from Path.map_coe _ _]
    rw [Set.range_comp, Path.range_segment,
      segment_eq_Icc hbetaMem.1.le, ← Set.image_image]
  have hqRange : range q =
      J.parametrization '' (JordanCurve.Arcs.param ''
        Set.Icc beta (alpha + 2 * Real.pi)) := by
    change range qRaw = _
    rw [show (qRaw : unitInterval → Plane) =
        f ∘ Path.segment beta (alpha + 2 * Real.pi) from Path.map_coe _ _]
    rw [Set.range_comp, Path.range_segment,
      segment_eq_Icc hbetaLt.le, ← Set.image_image]
  refine ⟨{
    first := p
    second := q
    first_injective := hpInjective
    second_injective := hqInjective
    cover := ?_
    overlap := ?_ }⟩
  · rw [hpRange, hqRange, ← Set.image_union, hSphereCover,
      Set.image_univ]
    rfl
  · rw [hpRange, hqRange, ← Set.image_inter J.injective,
      hSphereOverlap, Set.image_insert_eq, Set.image_singleton,
      hxsVal, hysVal]

end JordanCircle

end

end Schoenflies
