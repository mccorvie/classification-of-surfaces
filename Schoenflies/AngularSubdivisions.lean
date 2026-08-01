import Schoenflies.AccessHairs

/-!
# Contracting angular subdivisions

This is a quantitative version of Moise 9.3.  An accessible angular arc is
split at an accessible point in its middle third.  Iterating the operation
gives nested finite binary subdivisions, and every descendant has angular
width at most `(2/3)^n` times the width of its ancestor.
-/

namespace Schoenflies

open Metric Set Function Real

namespace JordanCircle

variable (J : JordanCircle)

/-- A short angular lift of an arc of the Jordan circle whose endpoints are
linearly accessible from the inside. -/
structure AccessibleAngularArc where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  width_lt_turn : right - left < 2 * π
  left_accessible :
    J.carrierHomeomorph (JordanCurve.Arcs.param left) ∈ J.insideAccessibleCarrier
  right_accessible :
    J.carrierHomeomorph (JordanCurve.Arcs.param right) ∈ J.insideAccessibleCarrier

namespace AccessibleAngularArc

variable {J : JordanCircle}

def width (A : J.AccessibleAngularArc) : ℝ := A.right - A.left

theorem width_pos (A : J.AccessibleAngularArc) : 0 < A.width := by
  exact sub_pos.mpr A.left_lt_right

/-- The open middle third in which the next accessible mark is selected. -/
def middleThird (A : J.AccessibleAngularArc) : Set ℝ :=
  Ioo (A.left + A.width / 3) (A.right - A.width / 3)

theorem middleThird_nonempty (A : J.AccessibleAngularArc) : A.middleThird.Nonempty := by
  rw [middleThird, nonempty_Ioo]
  dsimp [middleThird, width]
  linarith [A.left_lt_right]

theorem middleThird_bounds (A : J.AccessibleAngularArc) :
    A.left + A.width / 3 < A.right - A.width / 3 := by
  dsimp [width]
  linarith [A.left_lt_right]

/-- A chosen accessible angle in the middle third. -/
noncomputable def splitAngle (A : J.AccessibleAngularArc) : ℝ :=
  Classical.choose (J.exists_insideAccessibleAngle
    A.middleThird_bounds)

theorem splitAngle_mem (A : J.AccessibleAngularArc) :
    A.splitAngle ∈ A.middleThird :=
  (Classical.choose_spec (J.exists_insideAccessibleAngle
    A.middleThird_bounds)).1

theorem splitAngle_accessible (A : J.AccessibleAngularArc) :
    J.carrierHomeomorph (JordanCurve.Arcs.param A.splitAngle) ∈
      J.insideAccessibleCarrier :=
  (Classical.choose_spec (J.exists_insideAccessibleAngle
    A.middleThird_bounds)).2

noncomputable def leftChild (A : J.AccessibleAngularArc) :
    J.AccessibleAngularArc where
  left := A.left
  right := A.splitAngle
  left_lt_right := (lt_add_of_pos_right _
    (div_pos A.width_pos (by norm_num))).trans A.splitAngle_mem.1
  width_lt_turn := by
    have h : A.splitAngle < A.right :=
      A.splitAngle_mem.2.trans_le (sub_le_self _ (div_nonneg A.width_pos.le (by norm_num)))
    linarith [A.width_lt_turn]
  left_accessible := A.left_accessible
  right_accessible := A.splitAngle_accessible

noncomputable def rightChild (A : J.AccessibleAngularArc) :
    J.AccessibleAngularArc where
  left := A.splitAngle
  right := A.right
  left_lt_right := A.splitAngle_mem.2.trans
    (sub_lt_self _ (div_pos A.width_pos (by norm_num)))
  width_lt_turn := by
    have h : A.left < A.splitAngle :=
      (le_add_of_nonneg_right (div_nonneg A.width_pos.le (by norm_num))).trans_lt
        A.splitAngle_mem.1
    linarith [A.width_lt_turn]
  left_accessible := A.splitAngle_accessible
  right_accessible := A.right_accessible

theorem leftChild_width_le (A : J.AccessibleAngularArc) :
    A.leftChild.width ≤ (2 / 3 : ℝ) * A.width := by
  have h := A.splitAngle_mem.2
  change A.splitAngle - A.left ≤ (2 / 3 : ℝ) * (A.right - A.left)
  dsimp [middleThird, width] at h
  linarith

theorem rightChild_width_le (A : J.AccessibleAngularArc) :
    A.rightChild.width ≤ (2 / 3 : ℝ) * A.width := by
  have h := A.splitAngle_mem.1
  change A.right - A.splitAngle ≤ (2 / 3 : ℝ) * (A.right - A.left)
  dsimp [middleThird, width] at h
  linarith

/-- Follow a binary address through the nested subdivision. -/
noncomputable def descendant (A : J.AccessibleAngularArc) :
    List Bool → J.AccessibleAngularArc
  | [] => A
  | false :: bs => A.leftChild.descendant bs
  | true :: bs => A.rightChild.descendant bs

theorem descendant_width_le (A : J.AccessibleAngularArc) (bs : List Bool) :
    (A.descendant bs).width ≤ (2 / 3 : ℝ) ^ bs.length * A.width := by
  induction bs generalizing A with
  | nil => simp [descendant]
  | cons b bs ih =>
      cases b
      · rw [descendant]
        calc
          (A.leftChild.descendant bs).width
              ≤ (2 / 3 : ℝ) ^ bs.length * A.leftChild.width := ih A.leftChild
          _ ≤ (2 / 3 : ℝ) ^ bs.length * ((2 / 3 : ℝ) * A.width) := by
            exact mul_le_mul_of_nonneg_left A.leftChild_width_le
              (pow_nonneg (by norm_num) _)
          _ = (2 / 3 : ℝ) ^ (false :: bs).length * A.width := by
            simp only [List.length_cons, pow_succ]
            ring
      · rw [descendant]
        calc
          (A.rightChild.descendant bs).width
              ≤ (2 / 3 : ℝ) ^ bs.length * A.rightChild.width := ih A.rightChild
          _ ≤ (2 / 3 : ℝ) ^ bs.length * ((2 / 3 : ℝ) * A.width) := by
            exact mul_le_mul_of_nonneg_left A.rightChild_width_le
              (pow_nonneg (by norm_num) _)
          _ = (2 / 3 : ℝ) ^ (true :: bs).length * A.width := by
            simp only [List.length_cons, pow_succ]
            ring

theorem left_le_leftChild_left (A : J.AccessibleAngularArc) :
    A.left ≤ A.leftChild.left := le_rfl

theorem leftChild_right_le_right (A : J.AccessibleAngularArc) :
    A.leftChild.right ≤ A.right := by
  exact (A.splitAngle_mem.2.trans_le
    (sub_le_self _ (div_nonneg A.width_pos.le (by norm_num)))).le

theorem left_le_rightChild_left (A : J.AccessibleAngularArc) :
    A.left ≤ A.rightChild.left := by
  exact ((le_add_of_nonneg_right
    (div_nonneg A.width_pos.le (by norm_num))).trans_lt A.splitAngle_mem.1).le

theorem rightChild_right_le_right (A : J.AccessibleAngularArc) :
    A.rightChild.right ≤ A.right := le_rfl

/-- Every interval occurring in the binary subdivision is contained in its
ancestor interval. -/
theorem descendant_interval_subset (A : J.AccessibleAngularArc) (bs : List Bool) :
    Icc (A.descendant bs).left (A.descendant bs).right ⊆ Icc A.left A.right := by
  induction bs generalizing A with
  | nil => simp [descendant]
  | cons b bs ih =>
      cases b
      · intro t ht
        have hchild := ih A.leftChild ht
        exact ⟨A.left_le_leftChild_left.trans hchild.1,
          hchild.2.trans A.leftChild_right_le_right⟩
      · intro t ht
        have hchild := ih A.rightChild ht
        exact ⟨A.left_le_rightChild_left.trans hchild.1,
          hchild.2.trans A.rightChild_right_le_right⟩

end AccessibleAngularArc

/-- The point of the Jordan curve with lifted angular parameter `t`. -/
noncomputable def curvePoint (t : ℝ) : J.carrier :=
  J.carrierHomeomorph (JordanCurve.Arcs.param t)

theorem continuous_curvePoint : Continuous J.curvePoint :=
  J.carrierHomeomorph.continuous.comp JordanCurve.Arcs.continuous_param

/-- The closed Jordan subarc represented by an accessible angular lift. -/
def AccessibleAngularArc.curveArc (A : J.AccessibleAngularArc) : Set J.carrier :=
  J.curvePoint '' Icc A.left A.right

theorem AccessibleAngularArc.curveArc_isCompact
    (A : J.AccessibleAngularArc) : IsCompact A.curveArc :=
  isCompact_Icc.image J.continuous_curvePoint

theorem AccessibleAngularArc.curveArc_isPreconnected
    (A : J.AccessibleAngularArc) : IsPreconnected A.curveArc :=
  (ordConnected_Icc.isPreconnected.image J.curvePoint
    J.continuous_curvePoint.continuousOn)

theorem AccessibleAngularArc.left_mem_curveArc
    (A : J.AccessibleAngularArc) : J.curvePoint A.left ∈ A.curveArc :=
  ⟨A.left, left_mem_Icc.mpr A.left_lt_right.le, rfl⟩

theorem AccessibleAngularArc.right_mem_curveArc
    (A : J.AccessibleAngularArc) : J.curvePoint A.right ∈ A.curveArc :=
  ⟨A.right, right_mem_Icc.mpr A.left_lt_right.le, rfl⟩

theorem AccessibleAngularArc.descendant_curveArc_subset
    (A : J.AccessibleAngularArc) (bs : List Bool) :
    (A.descendant bs).curveArc ⊆ A.curveArc := by
  exact image_mono (A.descendant_interval_subset bs)

/-- The same closed subarc regarded as a subset of the ambient plane. -/
def AccessibleAngularArc.curveArcPlane (A : J.AccessibleAngularArc) : Set Plane :=
  ((↑) : J.carrier → Plane) '' A.curveArc

theorem AccessibleAngularArc.curveArcPlane_isCompact
    (A : J.AccessibleAngularArc) : IsCompact A.curveArcPlane :=
  A.curveArc_isCompact.image continuous_subtype_val

theorem AccessibleAngularArc.curveArcPlane_isPreconnected
    (A : J.AccessibleAngularArc) : IsPreconnected A.curveArcPlane :=
  A.curveArc_isPreconnected.image _ continuous_subtype_val.continuousOn

theorem AccessibleAngularArc.left_mem_curveArcPlane
    (A : J.AccessibleAngularArc) :
    (J.curvePoint A.left : Plane) ∈ A.curveArcPlane :=
  ⟨J.curvePoint A.left, A.left_mem_curveArc, rfl⟩

theorem AccessibleAngularArc.right_mem_curveArcPlane
    (A : J.AccessibleAngularArc) :
    (J.curvePoint A.right : Plane) ∈ A.curveArcPlane :=
  ⟨J.curvePoint A.right, A.right_mem_curveArc, rfl⟩

theorem AccessibleAngularArc.curveArcPlane_subset_carrier
    (A : J.AccessibleAngularArc) : A.curveArcPlane ⊆ J.carrier := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- Each lifted boundary subarc is genuinely an arc, first intrinsically in
the Jordan curve and then in the ambient plane. -/
noncomputable def AccessibleAngularArc.curveArcHomeomorph
    (A : J.AccessibleAngularArc) : A.curveArc ≃ₜ unitInterval := by
  let S : Set (sphere (0 : Plane) 1) :=
    JordanCurve.Arcs.param '' Icc A.left A.right
  have hset : A.curveArc = J.carrierHomeomorph '' S := by
    ext x
    simp only [curveArc, curvePoint, S, mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨JordanCurve.Arcs.param t, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
  exact (Homeomorph.setCongr hset).trans
    ((J.carrierHomeomorph.image S).symm.trans
      (JordanCurve.Arcs.arcHomeoUnitInterval A.left_lt_right A.width_lt_turn))

noncomputable def AccessibleAngularArc.curveArcPlaneHomeomorph
    (A : J.AccessibleAngularArc) : A.curveArcPlane ≃ₜ unitInterval := by
  letI : CompactSpace A.curveArc :=
    isCompact_iff_compactSpace.mp A.curveArc_isCompact
  let e₀ : A.curveArc ≃ A.curveArcPlane :=
    Equiv.Set.image ((↑) : J.carrier → Plane) A.curveArc Subtype.val_injective
  have he₀ : Continuous e₀ := by
    apply (continuous_induced_rng
      (f := ((↑) : A.curveArcPlane → Plane))).mpr
    convert (continuous_subtype_val.comp
      (continuous_subtype_val : Continuous ((↑) : A.curveArc → J.carrier))) using 1
    ext x
    rfl
  let e : A.curveArc ≃ₜ A.curveArcPlane :=
    Continuous.homeoOfEquivCompactToT2 he₀
  exact e.symm.trans A.curveArcHomeomorph

/-- Maehara's arc theorem, already proved as part of the Jordan-curve
development, applies to every selected boundary subarc. -/
theorem AccessibleAngularArc.isConnected_compl_curveArcPlane
    (A : J.AccessibleAngularArc) : IsConnected A.curveArcPlaneᶜ :=
  JordanCurve.arc_not_separates JordanCurve.Brouwer.brouwerFPT
    A.curveArcPlaneHomeomorph

/-- At one sufficiently deep uniform subdivision level, every parameter arc
has arbitrarily small image.  This is the metric content of Moise 9.3(4).

The theorem is phrased by pairwise distances instead of `diam`, which is the
form consumed by the later collar construction. -/
theorem AccessibleAngularArc.exists_depth_curvePoint_dist_lt
    (A : J.AccessibleAngularArc) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ bs : List Bool, bs.length = N →
      ∀ s ∈ Icc (A.descendant bs).left (A.descendant bs).right,
      ∀ t ∈ Icc (A.descendant bs).left (A.descendant bs).right,
        dist (J.curvePoint s) (J.curvePoint t) < epsilon := by
  have hu : UniformContinuousOn J.curvePoint (Icc A.left A.right) :=
    isCompact_Icc.uniformContinuousOn_of_continuous J.continuous_curvePoint.continuousOn
  obtain ⟨delta, hdelta, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hu) epsilon hepsilon
  have hthreshold : 0 < delta / A.width := div_pos hdelta A.width_pos
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hthreshold
    (show (2 / 3 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro bs hlen s hs t ht
  have hsroot : s ∈ Icc A.left A.right := A.descendant_interval_subset bs hs
  have htroot : t ∈ Icc A.left A.right := A.descendant_interval_subset bs ht
  apply hmod s hsroot t htroot
  have hwidth : (A.descendant bs).width < delta := by
    calc
      (A.descendant bs).width
          ≤ (2 / 3 : ℝ) ^ bs.length * A.width := A.descendant_width_le bs
      _ = (2 / 3 : ℝ) ^ N * A.width := by rw [hlen]
      _ < delta := by
        rw [lt_div_iff₀ A.width_pos] at hN
        simpa [mul_comm] using hN
  rw [Real.dist_eq]
  change |s - t| < delta
  change (A.descendant bs).right - (A.descendant bs).left < delta at hwidth
  rw [abs_lt]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- The uniform smallness conclusion persists at every later subdivision
level, not merely at one selected level. -/
theorem AccessibleAngularArc.eventually_curvePoint_dist_lt
    (A : J.AccessibleAngularArc) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ bs : List Bool, N ≤ bs.length →
      ∀ s ∈ Icc (A.descendant bs).left (A.descendant bs).right,
      ∀ t ∈ Icc (A.descendant bs).left (A.descendant bs).right,
        dist (J.curvePoint s) (J.curvePoint t) < epsilon := by
  have hu : UniformContinuousOn J.curvePoint (Icc A.left A.right) :=
    isCompact_Icc.uniformContinuousOn_of_continuous J.continuous_curvePoint.continuousOn
  obtain ⟨delta, hdelta, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hu) epsilon hepsilon
  have hpow : Filter.Tendsto
      (fun n : ℕ => (2 / 3 : ℝ) ^ n * A.width) Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.mul_const A.width
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 2 / 3 by norm_num)
        (show (2 / 3 : ℝ) < 1 by norm_num)))
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      (2 / 3 : ℝ) ^ n * A.width < delta := by
    exact hpow.eventually_lt_const hdelta
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨N, ?_⟩
  intro bs hlen s hs t ht
  have hsroot : s ∈ Icc A.left A.right := A.descendant_interval_subset bs hs
  have htroot : t ∈ Icc A.left A.right := A.descendant_interval_subset bs ht
  apply hmod s hsroot t htroot
  have hwidth : (A.descendant bs).width < delta :=
    (A.descendant_width_le bs).trans_lt (hN bs.length hlen)
  rw [Real.dist_eq]
  change |s - t| < delta
  change (A.descendant bs).right - (A.descendant bs).left < delta at hwidth
  rw [abs_lt]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- Two initial accessible arcs whose angular lifts make one full turn. -/
structure InitialAngularArcs where
  first : J.AccessibleAngularArc
  second : J.AccessibleAngularArc
  adjacent : first.right = second.left
  closes : second.right = first.left + 2 * π

/-- The contracting subdivision can be initialized by choosing one accessible
mark in each open semicircle. -/
theorem exists_initialAngularArcs : Nonempty J.InitialAngularArcs := by
  obtain ⟨a, ha, haAcc⟩ := J.exists_insideAccessibleAngle
    (show (0 : ℝ) < π by positivity)
  obtain ⟨b, hb, hbAcc⟩ := J.exists_insideAccessibleAngle
    (show π < 2 * π by linarith [pi_pos])
  have hab : a < b := ha.2.trans hb.1
  have hba : b < a + 2 * π := hb.2.trans (lt_add_of_pos_left _ ha.1)
  have haPeriodic : JordanCurve.Arcs.param (a + 2 * π) =
      JordanCurve.Arcs.param a := JordanCurve.Arcs.param_periodic a
  let A : J.AccessibleAngularArc :=
    { left := a
      right := b
      left_lt_right := hab
      width_lt_turn := by linarith [ha.1, hb.2]
      left_accessible := haAcc
      right_accessible := hbAcc }
  let B : J.AccessibleAngularArc :=
    { left := b
      right := a + 2 * π
      left_lt_right := hba
      width_lt_turn := by linarith [ha.2, hb.1]
      left_accessible := hbAcc
      right_accessible := by simpa only [haPeriodic] using haAcc }
  exact ⟨{ first := A, second := B, adjacent := rfl, closes := rfl }⟩

end JordanCircle

end Schoenflies
