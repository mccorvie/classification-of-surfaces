import Schoenflies.MasterParameters

/-!
# Metric bounds for the angular subdivision

The recursive compatibility corrections are controlled on the standard unit
circle.  This file records the elementary estimate that the chord distance
between two angular parameters is at most their lifted angular distance, and
packages the corresponding bounds for equal and adjacent subdivision arcs.
-/

namespace Schoenflies

open Metric Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

/-- Chord distance on the standard unit circle is bounded by lifted angular
distance. -/
theorem dist_arcsParam_le_abs_sub (s t : ℝ) :
    dist (JordanCurve.Arcs.param s) (JordanCurve.Arcs.param t) ≤ |s - t| := by
  change ‖JordanCurve.Arcs.complexLIE (Circle.exp s : ℂ) -
      JordanCurve.Arcs.complexLIE (Circle.exp t : ℂ)‖ ≤ |s - t|
  rw [← JordanCurve.Arcs.complexLIE.map_sub,
    JordanCurve.Arcs.complexLIE.norm_map]
  change ‖Complex.exp (s * Complex.I) -
      Complex.exp (t * Complex.I)‖ ≤ |s - t|
  rw [show Complex.exp (s * Complex.I) - Complex.exp (t * Complex.I) =
      Complex.exp (t * Complex.I) *
        (Complex.exp (Complex.I * (s - t)) - 1) by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast
      ring]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

namespace JordanCircle.InitialAngularArcs

open StandardPolygonalCollars

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The fixed identification of the standard unit circle with the master
triangle boundary. -/
def sphereToMasterHomeomorph :
    sphere (0 : Plane) 1 ≃ₜ standardTriangleCircle.carrier :=
  standardTriangleCircle.toJordanCircle.carrierHomeomorph.trans
    (Homeomorph.setCongr standardTriangleCircle.carrier_toJordanCircle)

@[simp] theorem sphereToMasterHomeomorph_apply
    (u : sphere (0 : Plane) 1) :
    (sphereToMasterHomeomorph u : Plane) =
      standardTriangleCircle.sphereStraightening.symm u := by
  rfl

@[simp] theorem sphereToMasterHomeomorph_apply_param (t : ℝ) :
    (sphereToMasterHomeomorph (JordanCurve.Arcs.param t) : Plane) =
      masterPoint t := by
  rfl

/-- Normalize a point of a radial target carrier back to the unit-circle
angular coordinate used by the master subdivision. -/
def normalizedTargetBoundaryPoint (m : ℕ) (y : (disk m).carrier) :
    sphere (0 : Plane) 1 :=
  sphereToMasterHomeomorph.symm ((diskBoundaryHomeomorph m).symm y)

/-- Membership in a scaled master window becomes membership in the original
angular parameter interval after radial normalization. -/
theorem normalizedTargetBoundaryPoint_mem_paramArc
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (y : (disk m).carrier)
    (hy : (y : Plane) ∈ I.masterArcImage m a) :
    normalizedTargetBoundaryPoint m y ∈
      JordanCurve.Arcs.param ''
        Icc (I.levelArc a).left (I.levelArc a).right := by
  rw [I.masterArcImage_eq_image_Icc] at hy
  obtain ⟨t, ht, hyt⟩ := hy
  refine ⟨t, ht, ?_⟩
  apply sphereToMasterHomeomorph.injective
  simp only [normalizedTargetBoundaryPoint,
    Homeomorph.apply_symm_apply]
  apply (diskBoundaryHomeomorph m).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [diskBoundaryHomeomorph_apply,
    sphereToMasterHomeomorph_apply_param]
  exact hyt

/-- Two angular points in one subdivision arc have chord distance at most
the width of that arc. -/
theorem dist_param_le_width_of_mem_levelArc {n : ℕ}
    (a : LevelAddress n) {s t : ℝ}
    (hs : s ∈ Icc (I.levelArc a).left (I.levelArc a).right)
    (ht : t ∈ Icc (I.levelArc a).left (I.levelArc a).right) :
    dist (JordanCurve.Arcs.param s) (JordanCurve.Arcs.param t) ≤
      (I.levelArc a).width := by
  refine (dist_arcsParam_le_abs_sub s t).trans ?_
  rcases hs with ⟨hsL, hsR⟩
  rcases ht with ⟨htL, htR⟩
  rw [abs_sub_le_iff]
  constructor <;> unfold JordanCircle.AccessibleAngularArc.width <;> linarith

/-- Points in two consecutive subdivision arcs are separated by at most the
sum of their widths.  This formulation also handles the cyclic seam, because
adjacency is stated on the circle rather than by equality of lifted endpoints.
-/
theorem dist_param_le_width_add_width_of_adjacent {n : ℕ}
    {a b : LevelAddress n} (hab : I.LevelAdjacent a b)
    {s t : ℝ}
    (hs : s ∈ Icc (I.levelArc a).left (I.levelArc a).right)
    (ht : t ∈ Icc (I.levelArc b).left (I.levelArc b).right) :
    dist (JordanCurve.Arcs.param s) (JordanCurve.Arcs.param t) ≤
      (I.levelArc a).width + (I.levelArc b).width := by
  have hend : JordanCurve.Arcs.param (I.levelArc a).right =
      JordanCurve.Arcs.param (I.levelArc b).left := by
    apply J.carrierHomeomorph.injective
    exact Subtype.ext hab
  calc
    dist (JordanCurve.Arcs.param s) (JordanCurve.Arcs.param t) ≤
        dist (JordanCurve.Arcs.param s)
            (JordanCurve.Arcs.param (I.levelArc a).right) +
          dist (JordanCurve.Arcs.param (I.levelArc b).left)
            (JordanCurve.Arcs.param t) := by
      rw [hend]
      exact dist_triangle _ _ _
    _ ≤ (I.levelArc a).width + (I.levelArc b).width :=
      add_le_add
        (I.dist_param_le_width_of_mem_levelArc a hs
          (right_mem_Icc.mpr (I.levelArc a).left_lt_right.le))
        (I.dist_param_le_width_of_mem_levelArc b
          (left_mem_Icc.mpr (I.levelArc b).left_lt_right.le) ht)

/-- If one normalized boundary point lies in a level window and another lies
in that window or either cyclic neighbor, their chord distance is bounded by
twice the largest width at that level. -/
theorem dist_normalizedTargetBoundaryPoint_le_two_mul_levelMax
    (m : ℕ) {n : ℕ} (a : LevelAddress n)
    (x y : (disk m).carrier)
    (hx : (x : Plane) ∈ I.masterArcImage m a)
    (hy : (y : Plane) ∈
      I.masterArcImage m (prevLevelAddress n a) ∪
        (I.masterArcImage m a ∪
          I.masterArcImage m (nextLevelAddress n a))) :
    dist (normalizedTargetBoundaryPoint m x)
        (normalizedTargetBoundaryPoint m y) ≤
      2 * ((2 / 3 : ℝ) ^ n * max I.first.width I.second.width) := by
  obtain ⟨s, hs, hsx⟩ :=
    I.normalizedTargetBoundaryPoint_mem_paramArc m a x hx
  rw [← hsx]
  rcases hy with hyPrev | hySelf | hyNext
  · obtain ⟨t, ht, hty⟩ :=
      I.normalizedTargetBoundaryPoint_mem_paramArc m
        (prevLevelAddress n a) y hyPrev
    rw [← hty]
    have hdist := I.dist_param_le_width_add_width_of_adjacent
      (I.levelAdjacent_prevLevelAddress n a) ht hs
    rw [dist_comm]
    exact hdist.trans <| by
      have hp := I.levelArc_width_le (prevLevelAddress n a)
      have ha := I.levelArc_width_le a
      linarith
  · obtain ⟨t, ht, hty⟩ :=
      I.normalizedTargetBoundaryPoint_mem_paramArc m a y hySelf
    rw [← hty]
    have hdist := I.dist_param_le_width_of_mem_levelArc a hs ht
    have ha := I.levelArc_width_le a
    have hB : 0 ≤ (2 / 3 : ℝ) ^ n * max I.first.width I.second.width :=
      (I.levelArc a).width_pos.le.trans ha
    linarith
  · obtain ⟨t, ht, hty⟩ :=
      I.normalizedTargetBoundaryPoint_mem_paramArc m
        (nextLevelAddress n a) y hyNext
    rw [← hty]
    have hdist := I.dist_param_le_width_add_width_of_adjacent
      (I.levelAdjacent_nextLevelAddress n a) hs ht
    have ha := I.levelArc_width_le a
    have hn := I.levelArc_width_le (nextLevelAddress n a)
    linarith

end JordanCircle.InitialAngularArcs

end

end Schoenflies
