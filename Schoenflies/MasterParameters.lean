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

/-- The master parametrization at one radial scale. -/
def masterImagePoint (m : ℕ) (t : ℝ) : Plane :=
  homothetyPoint (radius m) (masterPoint t)

theorem continuous_masterImagePoint (m : ℕ) :
    Continuous (masterImagePoint m) := by
  unfold masterImagePoint homothetyPoint
  exact ((continuous_const (y := radius m)).smul
    (continuous_masterPoint.sub continuous_const)).add continuous_const

end StandardPolygonalCollars

namespace JordanCircle.InitialAngularArcs

open StandardPolygonalCollars

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Every scaled master window is the image of its parameter interval under
the fixed scaled master parametrization. -/
theorem masterArcImage_eq_image_Icc (m : ℕ) {k : ℕ}
    (a : LevelAddress k) :
    I.masterArcImage m a =
      masterImagePoint m ''
        Icc (I.levelArc a).left (I.levelArc a).right := by
  unfold masterArcImage
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, ⟨t, htIcc, rfl⟩, hwz⟩ := hz
    have hzw : z = J.curvePoint t := Subtype.ext hwz.symm
    refine ⟨t, htIcc, ?_⟩
    rw [hzw]
    simp only [boundaryPoint_curvePoint_eq_masterPoint]
    rfl
  · rintro ⟨t, htIcc, rfl⟩
    refine ⟨J.curvePoint t, ?_, ?_⟩
    · exact ⟨J.curvePoint t, ⟨t, htIcc, rfl⟩, rfl⟩
    · simp only [boundaryPoint_curvePoint_eq_masterPoint]
      rfl

/-- The angular width of every level arc decays geometrically with the
subdivision depth. -/
theorem levelArc_width_le {k : ℕ} (a : LevelAddress k) :
    (I.levelArc a).width ≤
      (2 / 3 : ℝ) ^ k * max I.first.width I.second.width := by
  have h := (I.rootArc a.1).descendant_width_le (List.ofFn a.2)
  rw [List.length_ofFn] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  cases a.1
  · exact le_max_left _ _
  · exact le_max_right _ _

end JordanCircle.InitialAngularArcs

end

end Schoenflies
