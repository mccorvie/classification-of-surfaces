import Schoenflies.JordanRegionBounds
import Schoenflies.SynchronizedPolygonalCircle

/-!
# Shrinking Jordan cells at synchronized collar levels

Each elementary boundary arc and its synchronized polygonal return bound an
auxiliary Jordan cell.  The return estimates and the binary subdivision
estimates imply that the whole closed cell shrinks uniformly, not just its
boundary.
-/

namespace Schoenflies

open Metric Set Function

namespace JordanCircle
namespace InitialAngularArcs
namespace LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

/-- The Jordan circle formed by an elementary wild boundary arc and its
synchronized polygonal return. -/
noncomputable def synchronizedAuxiliaryJordanCircle
    (a : LevelAddress n) : JordanCircle :=
  (F.synchronizedInsideReturnArc a).auxiliaryJordanCircle

@[simp] theorem carrier_synchronizedAuxiliaryJordanCircle
    (a : LevelAddress n) :
    (F.synchronizedAuxiliaryJordanCircle a).carrier =
      (I.levelArc a).curveArcPlane ∪
        range (F.synchronizedReturnPath a) :=
  (F.synchronizedInsideReturnArc a).carrier_auxiliaryJordanCircle

theorem inside_synchronizedAuxiliaryJordanCircle_subset
    (a : LevelAddress n) :
    (F.synchronizedAuxiliaryJordanCircle a).inside ⊆ J.inside :=
  (F.synchronizedInsideReturnArc a).inside_auxiliaryJordanCircle_subset

/-- Metric control of the wild arc and synchronized return controls the
whole closed auxiliary cell. -/
theorem closure_inside_synchronizedAuxiliaryJordanCircle_subset_closedBall
    (a : LevelAddress n) {c : Plane} {rho : ℝ}
    (hArc : (I.levelArc a).curveArcPlane ⊆ closedBall c rho)
    (hReturn : F.synchronizedReturnSet a ⊆ closedBall c rho) :
    closure (F.synchronizedAuxiliaryJordanCircle a).inside ⊆
      closedBall c rho := by
  apply closure_inside_subset_closedBall_of_carrier_subset
    (F.synchronizedAuxiliaryJordanCircle a)
  rw [F.carrier_synchronizedAuxiliaryJordanCircle a]
  exact union_subset hArc
    ((F.range_synchronizedReturnPath_subset a).trans hReturn)

/-- At sufficiently deep complete levels, every closed auxiliary cell lies
in a prescribed ball around the left endpoint of its boundary arc. -/
theorem eventually_closure_inside_synchronizedAuxiliary_subset_ball
    (I : J.InitialAngularArcs) {rho : ℝ} (hrho : 0 < rho) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (F : I.LevelAvoidingJoinFamily n (rho / 4))
        (a : LevelAddress n),
        closure (F.synchronizedAuxiliaryJordanCircle a).inside ⊆
          closedBall (J.curvePoint (I.levelArc a).left : Plane) rho := by
  obtain ⟨Narc, hArc⟩ := I.eventually_levelArc_curvePoint_dist_lt hrho
  obtain ⟨Nreturn, hReturn⟩ :=
    LevelAvoidingJoinFamily.eventually_synchronizedReturnSet_subset_ball
      I hrho
  refine ⟨max Narc Nreturn, ?_⟩
  intro n hn F a
  have hnArc : Narc ≤ n := (le_max_left Narc Nreturn).trans hn
  have hnReturn : Nreturn ≤ n := (le_max_right Narc Nreturn).trans hn
  apply F.closure_inside_synchronizedAuxiliaryJordanCircle_subset_closedBall
  · rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    rw [mem_closedBall]
    exact (hArc n hnArc a t ht (I.levelArc a).left
      (left_mem_Icc.mpr (I.levelArc a).left_lt_right.le)).le
  · exact (hReturn n hnReturn F a).trans ball_subset_closedBall

end LevelAvoidingJoinFamily
end InitialAngularArcs
end JordanCircle

end Schoenflies
