import Schoenflies.CyclicLevelAddresses
import Schoenflies.HairOrdering

/-!
# Endpoint hairs retained between consecutive subdivision levels

Moise's Chapter 9 cells use the old crosscut as one side and the chain of
new crosscuts over its children as the opposite side.  The remaining two
sides lie on the old endpoint hairs.  These lemmas record that the recursive
hair family makes those endpoint hairs literally the same objects at the
two levels.
-/

namespace Schoenflies

open Metric Set Function AffineMap

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle}

/-- The leftmost depth-`k` descendant of a level address. -/
def leftmostDescendant {n : ℕ} (a : LevelAddress n) :
    (k : ℕ) → LevelAddress (n + k)
  | 0 => a
  | k + 1 => extendLevelAddress (leftmostDescendant a k) false

/-- The rightmost depth-`k` descendant of a level address. -/
def rightmostDescendant {n : ℕ} (a : LevelAddress n) :
    (k : ℕ) → LevelAddress (n + k)
  | 0 => a
  | k + 1 => extendLevelAddress (rightmostDescendant a k) true

@[simp] theorem levelArc_leftmostDescendant_left
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    (k : ℕ) :
    (I.levelArc (leftmostDescendant a k)).left =
      (I.levelArc a).left := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [leftmostDescendant,
        I.levelArc_extendLevelAddress_false,
        AccessibleAngularArc.leftChild_left, ih]

@[simp] theorem levelArc_rightmostDescendant_right
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    (k : ℕ) :
    (I.levelArc (rightmostDescendant a k)).right =
      (I.levelArc a).right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [rightmostDescendant,
        I.levelArc_extendLevelAddress_true,
        AccessibleAngularArc.rightChild_right, ih]

/-- The left child retains its parent's left endpoint hair. -/
@[simp] theorem levelLeftHair_extendLevelAddress_false_carrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    (I.levelLeftHair (extendLevelAddress a false)).carrier =
      (I.levelLeftHair a).carrier := by
  let oldMark : I.GenerationMark n :=
    ⟨(J.curvePoint (I.levelArc a).left : Plane),
      I.levelArc_left_mem_generationMarks a⟩
  let childMark : I.GenerationMark (n + 1) :=
    ⟨(J.curvePoint
        (I.levelArc (extendLevelAddress a false)).left : Plane),
      I.levelArc_left_mem_generationMarks (extendLevelAddress a false)⟩
  let retainedMark : I.GenerationMark (n + 1) :=
    ⟨oldMark.1, I.generationMarks_mono n oldMark.2⟩
  have hbase :
      (J.curvePoint
          (I.levelArc (extendLevelAddress a false)).left : Plane) =
        (J.curvePoint (I.levelArc a).left : Plane) := by
    rw [I.levelArc_extendLevelAddress_false,
      AccessibleAngularArc.leftChild_left]
  have hmark : childMark = retainedMark := by
    apply Subtype.ext
    exact hbase
  change ((I.generationInsideHairFamily (n + 1)).hair childMark).carrier =
    ((I.generationInsideHairFamily n).hair oldMark).carrier
  rw [hmark]
  exact congrArg InsideAccessHair.carrier
    (I.generationInsideHairFamily_succ_hair n oldMark)

/-- The extreme left endpoint hair is retained across any finite number of
binary refinements. -/
@[simp] theorem levelLeftHair_leftmostDescendant_carrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    (k : ℕ) :
    (I.levelLeftHair (leftmostDescendant a k)).carrier =
      (I.levelLeftHair a).carrier := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [leftmostDescendant,
        I.levelLeftHair_extendLevelAddress_false_carrier,
        ih]

/-- The right child retains its parent's right endpoint hair. -/
@[simp] theorem levelRightHair_extendLevelAddress_true_carrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    (I.levelRightHair (extendLevelAddress a true)).carrier =
      (I.levelRightHair a).carrier := by
  let oldMark : I.GenerationMark n :=
    ⟨(J.curvePoint (I.levelArc a).right : Plane),
      I.levelArc_right_mem_generationMarks a⟩
  let childMark : I.GenerationMark (n + 1) :=
    ⟨(J.curvePoint
        (I.levelArc (extendLevelAddress a true)).right : Plane),
      I.levelArc_right_mem_generationMarks (extendLevelAddress a true)⟩
  let retainedMark : I.GenerationMark (n + 1) :=
    ⟨oldMark.1, I.generationMarks_mono n oldMark.2⟩
  have hbase :
      (J.curvePoint
          (I.levelArc (extendLevelAddress a true)).right : Plane) =
        (J.curvePoint (I.levelArc a).right : Plane) := by
    rw [I.levelArc_extendLevelAddress_true,
      AccessibleAngularArc.rightChild_right]
  have hmark : childMark = retainedMark := by
    apply Subtype.ext
    exact hbase
  change ((I.generationInsideHairFamily (n + 1)).hair childMark).carrier =
    ((I.generationInsideHairFamily n).hair oldMark).carrier
  rw [hmark]
  exact congrArg InsideAccessHair.carrier
    (I.generationInsideHairFamily_succ_hair n oldMark)

/-- The extreme right endpoint hair is retained across any finite number of
binary refinements. -/
@[simp] theorem levelRightHair_rightmostDescendant_carrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    (k : ℕ) :
    (I.levelRightHair (rightmostDescendant a k)).carrier =
      (I.levelRightHair a).carrier := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rightmostDescendant,
        I.levelRightHair_extendLevelAddress_true_carrier,
        ih]

end InitialAngularArcs

namespace InsideAccessHair

variable {J : JordanCircle} {q : Plane}

/-- Distance from the base is the affine hair parameter times the hair
length.  This converts metric collar separation into the order needed to
use the retained hair as an exact polygonal side. -/
theorem dist_base_eq_carrierParameter_mul_dist_tip
    (H : J.InsideAccessHair q) (x : H.carrier) :
    dist q (x : Plane) = H.carrierParameter x * dist q H.tip := by
  rw [← H.lineMap_carrierParameter x]
  simp only [lineMap_apply_module]
  rw [dist_eq_norm, dist_eq_norm]
  have ht0 : 0 ≤ H.carrierParameter x :=
    (H.carrierParameter_mem_Icc x).1
  rw [show q - ((1 - H.carrierParameter x) • q +
      H.carrierParameter x • H.tip) =
      H.carrierParameter x • (q - H.tip) by module]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]

/-- On a nondegenerate retained hair, being metrically closer to the base is
equivalent to having the smaller affine parameter. -/
theorem carrierParameter_lt_of_dist_base_lt
    (H : J.InsideAccessHair q) (x y : H.carrier)
    (hxy : dist q (x : Plane) < dist q (y : Plane)) :
    H.carrierParameter x < H.carrierParameter y := by
  rw [H.dist_base_eq_carrierParameter_mul_dist_tip x,
    H.dist_base_eq_carrierParameter_mul_dist_tip y] at hxy
  have htip : 0 < dist q H.tip := dist_pos.mpr H.tip_ne_base.symm
  nlinarith

end InsideAccessHair
end JordanCircle

end Schoenflies
