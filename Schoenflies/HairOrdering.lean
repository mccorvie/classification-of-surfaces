import Schoenflies.AccessHairs

/-!
# The intrinsic order on a straight access hair

Points of an access hair have a unique affine parameter between its boundary
base and its inside tip.  This elementary order is what Moise 9.6 uses when
two neighboring crosscuts have initially selected different points on their
common retained hair: the point nearer the boundary is retained and the
other crosscut is extended out to it.
-/

namespace Schoenflies

open Metric Set Function AffineMap

namespace JordanCircle
namespace InsideAccessHair

variable {J : JordanCircle} {q : Plane}

private theorem exists_carrierParameter (H : J.InsideAccessHair q)
    (x : H.carrier) :
    ∃ t ∈ Icc (0 : ℝ) 1, lineMap q H.tip t = (x : Plane) := by
  have hx : (x : Plane) ∈ segment ℝ q H.tip := x.2
  rw [segment_eq_image_lineMap] at hx
  exact hx

/-- The unique affine coordinate of a point on a nondegenerate access hair. -/
noncomputable def carrierParameter (H : J.InsideAccessHair q)
    (x : H.carrier) : ℝ :=
  Classical.choose (H.exists_carrierParameter x)

theorem carrierParameter_mem_Icc (H : J.InsideAccessHair q)
    (x : H.carrier) : H.carrierParameter x ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec (H.exists_carrierParameter x)).1

theorem lineMap_carrierParameter (H : J.InsideAccessHair q)
    (x : H.carrier) : lineMap q H.tip (H.carrierParameter x) = x :=
  (Classical.choose_spec (H.exists_carrierParameter x)).2

theorem carrierParameter_injective (H : J.InsideAccessHair q) :
    Injective H.carrierParameter := by
  intro x y hxy
  apply Subtype.ext
  rw [← H.lineMap_carrierParameter x,
    ← H.lineMap_carrierParameter y, hxy]

/-- The boundary base has coordinate zero. -/
@[simp] theorem carrierParameter_base (H : J.InsideAccessHair q) :
    H.carrierParameter ⟨q, H.base_mem⟩ = 0 := by
  apply lineMap_injective ℝ H.tip_ne_base.symm
  rw [H.lineMap_carrierParameter, lineMap_apply_zero]

/-- The inside tip has coordinate one. -/
@[simp] theorem carrierParameter_tip (H : J.InsideAccessHair q) :
    H.carrierParameter ⟨H.tip, H.tip_mem⟩ = 1 := by
  apply lineMap_injective ℝ H.tip_ne_base.symm
  rw [H.lineMap_carrierParameter, lineMap_apply_one]

/-- A point of the hair lying in the Jordan inside is strictly beyond the
boundary base in the affine order. -/
theorem carrierParameter_pos_of_mem_inside
    (H : J.InsideAccessHair q) (hq : q ∈ J.carrier)
    (x : H.carrier) (hx : (x : Plane) ∈ J.inside) :
    0 < H.carrierParameter x := by
  have hxnonneg := (H.carrierParameter_mem_Icc x).1
  exact hxnonneg.lt_of_ne fun hxzero => by
    have hxq : (x : Plane) = q := by
      rw [← H.lineMap_carrierParameter x, ← hxzero, lineMap_apply_zero]
    exact (J.inside_subset_compl hx) (hxq.symm ▸ hq)

/-- Affine coordinates interpolate monotonically along a segment whose
endpoints occur in the given order on one hair. -/
theorem carrierParameter_bounds_of_mem_segment
    (H : J.InsideAccessHair q) (x y : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y)
    {z : Plane} (hz : z ∈ segment ℝ (x : Plane) (y : Plane)) :
    let z' : H.carrier := ⟨z,
      (convex_segment q H.tip).segment_subset x.2 y.2 hz⟩
    H.carrierParameter x ≤ H.carrierParameter z' ∧
      H.carrierParameter z' ≤ H.carrierParameter y := by
  let z' : H.carrier := ⟨z,
    (convex_segment q H.tip).segment_subset x.2 y.2 hz⟩
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, hsz⟩ := hz
  have hcoordinate : H.carrierParameter z' =
      (1 - s) * H.carrierParameter x + s * H.carrierParameter y := by
    apply lineMap_injective ℝ H.tip_ne_base.symm
    rw [H.lineMap_carrierParameter z']
    change z = lineMap q H.tip
      ((1 - s) * H.carrierParameter x + s * H.carrierParameter y)
    rw [← hsz, ← H.lineMap_carrierParameter x,
      ← H.lineMap_carrierParameter y]
    simp only [lineMap_apply_module]
    module
  dsimp only [z']
  rw [hcoordinate]
  constructor <;> nlinarith [hs.1, hs.2]

/-- Initial hair segments are nested according to their affine parameters. -/
theorem baseSegment_subset_of_parameter_le
    (H : J.InsideAccessHair q) (x y : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y) :
    segment ℝ q (x : Plane) ⊆ segment ℝ q (y : Plane) := by
  have hy0 := (H.carrierParameter_mem_Icc y).1
  by_cases hyzero : H.carrierParameter y = 0
  · have hxzero : H.carrierParameter x = 0 :=
      le_antisymm (hxy.trans_eq hyzero) (H.carrierParameter_mem_Icc x).1
    have hxq : (x : Plane) = q := by
      rw [← H.lineMap_carrierParameter x, hxzero, lineMap_apply_zero]
    have hyq : (y : Plane) = q := by
      rw [← H.lineMap_carrierParameter y, hyzero, lineMap_apply_zero]
    simp [hxq, hyq]
  · have hypos : 0 < H.carrierParameter y := lt_of_le_of_ne hy0
      (Ne.symm hyzero)
    apply (convex_segment q (y : Plane)).segment_subset
    · exact left_mem_segment ℝ _ _
    · rw [segment_eq_image_lineMap]
      refine ⟨H.carrierParameter x / H.carrierParameter y, ?_, ?_⟩
      · constructor
        · exact div_nonneg (H.carrierParameter_mem_Icc x).1 hypos.le
        · exact (div_le_one hypos).mpr hxy
      · rw [← H.lineMap_carrierParameter x,
          ← H.lineMap_carrierParameter y,
          lineMap_lineMap_right]
        congr 1
        field_simp [hyzero]

/-- A segment joining two non-base points in their hair order meets the
initial segment to the first point exactly at that first point. -/
theorem segment_inter_baseSegment_eq
    (H : J.InsideAccessHair q) (x y : H.carrier)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y) :
    segment ℝ (x : Plane) (y : Plane) ∩ segment ℝ q (x : Plane) =
      {(x : Plane)} := by
  ext z
  constructor
  · rintro ⟨hzXY, hzQX⟩
    let z' : H.carrier := ⟨z,
      (convex_segment q H.tip).segment_subset x.2 y.2 hzXY⟩
    have hlower : H.carrierParameter x ≤ H.carrierParameter z' :=
      (H.carrierParameter_bounds_of_mem_segment x y hxy hzXY).1
    let q' : H.carrier := ⟨q, H.base_mem⟩
    have hqx : H.carrierParameter q' ≤ H.carrierParameter x := by
      simpa [q'] using (H.carrierParameter_mem_Icc x).1
    have hupper0 :=
      (H.carrierParameter_bounds_of_mem_segment q' x hqx hzQX).2
    have hupper : H.carrierParameter z' ≤ H.carrierParameter x := by
      exact hupper0
    have hzParam : H.carrierParameter z' = H.carrierParameter x :=
      le_antisymm hupper hlower
    have hzx : z' = x := H.carrierParameter_injective hzParam
    exact mem_singleton_iff.mpr (congrArg Subtype.val hzx)
  · intro hz
    have hzx : z = (x : Plane) := mem_singleton_iff.mp hz
    subst z
    exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩

/-- Moving inward from a positive hair point stays in the Jordan inside. -/
theorem segment_subset_inside_of_parameter_le
    (H : J.InsideAccessHair q) (hq : q ∈ J.carrier)
    (x y : H.carrier) (hxInside : (x : Plane) ∈ J.inside)
    (hxy : H.carrierParameter x ≤ H.carrierParameter y) :
    segment ℝ (x : Plane) (y : Plane) ⊆ J.inside := by
  intro z hz
  have hzCarrier : z ∈ H.carrier :=
    (convex_segment q H.tip).segment_subset x.2 y.2 hz
  rcases H.carrier_subset hzCarrier with hzInside | hzBase
  · exact hzInside
  · have hxPos := H.carrierParameter_pos_of_mem_inside hq x hxInside
    let z' : H.carrier := ⟨z, hzCarrier⟩
    have hzLower : H.carrierParameter x ≤ H.carrierParameter z' :=
      (H.carrierParameter_bounds_of_mem_segment x y hxy hz).1
    have hzEqBase : z' = ⟨q, H.base_mem⟩ := by
      apply Subtype.ext
      exact mem_singleton_iff.mp hzBase
    rw [hzEqBase, H.carrierParameter_base] at hzLower
    exact False.elim (not_le_of_gt hxPos hzLower)

/-- Select the shallower of two inside points on a retained hair. -/
noncomputable def shallowerPoint (H : J.InsideAccessHair q)
    (x y : H.carrier) : H.carrier :=
  if H.carrierParameter x ≤ H.carrierParameter y then x else y

theorem shallowerPoint_eq_left_or_right (H : J.InsideAccessHair q)
    (x y : H.carrier) : H.shallowerPoint x y = x ∨
      H.shallowerPoint x y = y := by
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · exact Or.inl (by simp [shallowerPoint, hxy])
  · exact Or.inr (by simp [shallowerPoint, hxy])

theorem shallowerPoint_parameter_le_left (H : J.InsideAccessHair q)
    (x y : H.carrier) :
    H.carrierParameter (H.shallowerPoint x y) ≤
      H.carrierParameter x := by
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · simp [shallowerPoint, hxy]
  · simp [shallowerPoint, hxy, le_of_not_ge hxy]

theorem shallowerPoint_parameter_le_right (H : J.InsideAccessHair q)
    (x y : H.carrier) :
    H.carrierParameter (H.shallowerPoint x y) ≤
      H.carrierParameter y := by
  by_cases hxy : H.carrierParameter x ≤ H.carrierParameter y
  · simp [shallowerPoint, hxy]
  · simp [shallowerPoint, hxy]

end InsideAccessHair
end JordanCircle

end Schoenflies
