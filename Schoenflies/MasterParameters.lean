import Schoenflies.CyclicTargetCells

/-!
# Master angular parameters of the target boundary

The prescribed boundary correspondence factors through the angular
parametrization of the original Jordan circle: the master boundary point of
a curve point depends only on its angular parameter, through one fixed
homeomorphism of the standard sphere onto the standard triangle boundary.
Consequently all master windows are images of parameter intervals under one
fixed continuous map, and their binary subdivision widths decay
geometrically.  The drift and limit analysis of the recursive boundary
corrections is carried out on these parameters.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace StandardPolygonalCollars

/-- The master boundary point of a parametrized curve point depends only on
the angular parameter, through the fixed straightening of the standard
triangle.  The Jordan parametrization cancels. -/
theorem boundaryPoint_curvePoint (J : JordanCircle) (t : ℝ) :
    boundaryPoint J (J.curvePoint t) =
      standardTriangleCircle.sphereStraightening.symm
        (JordanCurve.Arcs.param t) := by
  unfold boundaryPoint
  rw [show J.curvePoint t = J.carrierHomeomorph (JordanCurve.Arcs.param t)
      from rfl,
    J.carrierHomeomorph.symm_apply_apply]

/-- The fixed master parametrization of the standard triangle boundary. -/
def masterPoint (t : ℝ) : Plane :=
  standardTriangleCircle.sphereStraightening.symm (JordanCurve.Arcs.param t)

theorem continuous_masterPoint : Continuous masterPoint := by
  unfold masterPoint
  fun_prop

@[simp] theorem boundaryPoint_curvePoint_eq_masterPoint
    (J : JordanCircle) (t : ℝ) :
    boundaryPoint J (J.curvePoint t) = masterPoint t :=
  boundaryPoint_curvePoint J t

end StandardPolygonalCollars

end

end Schoenflies
