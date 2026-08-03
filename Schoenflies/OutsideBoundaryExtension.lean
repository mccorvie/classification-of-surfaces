import Schoenflies.BallPunctureExterior

/-!
# The unbounded regional Schoenflies homeomorphism

Invert about an inside point, apply the completed bounded-side theorem to the
inverted Jordan circle, delete the point representing infinity, and identify
the resulting punctured ball with the standard exterior.
-/

namespace Schoenflies

open Metric Set Function

noncomputable section

namespace InsideRegionalExtensionData

variable {J : JordanCircle} (E : InsideRegionalExtensionData J)

/-- An inside regional extension sends the open bounded component into the
open unit ball. -/
theorem maps_open (x : J.inside) :
    (E.homeomorph ⟨x, subset_closure x.2⟩ : Plane) ∈
      ball (0 : Plane) 1 := by
  let z := E.homeomorph ⟨x, subset_closure x.2⟩
  by_contra hzball
  have hzsphere : (z : Plane) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere]
    have hzle : dist (z : Plane) 0 ≤ 1 := by
      simpa only [mem_closedBall] using z.2
    have hzge : 1 ≤ dist (z : Plane) 0 := by
      exact not_lt.mp (by simpa only [mem_ball] using hzball)
    exact le_antisymm hzle hzge
  let y : sphere (0 : Plane) 1 := ⟨z, hzsphere⟩
  let c : J.carrier := J.carrierHomeomorph y
  have hc : (c : Plane) ∈ closure J.inside := by
    rw [J.closure_inside]
    exact Or.inr c.2
  have hsame : E.homeomorph ⟨c, hc⟩ = z := by
    apply Subtype.ext
    exact (E.boundary c).trans
      (congrArg Subtype.val (J.carrierHomeomorph.symm_apply_apply y))
  have hxc : (⟨x, subset_closure x.2⟩ : closure J.inside) = ⟨c, hc⟩ :=
    E.homeomorph.injective hsame.symm
  have hxcarrier : (x : Plane) ∈ J.carrier := by
    have hval : (x : Plane) = (c : Plane) := congrArg Subtype.val hxc
    rw [hval]
    exact c.2
  exact (J.inside_subset_compl x.2) hxcarrier

end InsideRegionalExtensionData

namespace JordanCircle

variable (J : JordanCircle)

/-- A fixed initial angular pair for the inverted Jordan circle. -/
noncomputable def invertedInitialAngularArcs :
    J.inverted.InitialAngularArcs :=
  Classical.choice J.inverted.exists_initialAngularArcs

private abbrev KI (J : JordanCircle) := J.invertedInitialAngularArcs

theorem insidePoint_mem_inverted_inside :
    J.insidePoint ∈ J.inverted.inside := by
  rw [J.inverted_inside]
  exact J.insidePoint_mem_invertedOutsideFill

/-- The inversion center as a point of the closed inverted inside. -/
def invertedCenterInClosure : closure J.inverted.inside :=
  ⟨J.insidePoint, subset_closure J.insidePoint_mem_inverted_inside⟩

/-- The image of infinity under the bounded-side homeomorphism of the
inverted curve, as an interior point of the unit ball. -/
noncomputable def invertedCenterInBall : ball (0 : Plane) 1 :=
  ⟨J.KI.shrinkingInsideBallHomeomorph J.invertedCenterInClosure,
    J.KI.shrinkingInsideRegionalExtensionData.maps_open
      ⟨J.insidePoint, J.insidePoint_mem_inverted_inside⟩⟩

/-- Restrict the bounded-side homeomorphism of the inverted curve away from
the point representing infinity. -/
noncomputable def puncturedInvertedInsideToPuncturedBall :
    {x : closure J.inverted.inside // (x : Plane) ≠ J.insidePoint} ≃ₜ
      {y : closedBall (0 : Plane) 1 //
        (y : Plane) ≠ (J.invertedCenterInBall : Plane)} :=
  J.KI.shrinkingInsideBallHomeomorph.subtype fun x => by
    constructor
    · intro hxc hhu
      apply hxc
      let c := J.invertedCenterInClosure
      have heq : J.KI.shrinkingInsideBallHomeomorph x =
          J.KI.shrinkingInsideBallHomeomorph c := by
        apply Subtype.ext
        exact hhu
      exact congrArg (fun z : closure J.inverted.inside => (z : Plane))
        (J.KI.shrinkingInsideBallHomeomorph.injective heq)
    · intro hhu hxc
      apply hhu
      have hEq : x = J.invertedCenterInClosure := by
        apply Subtype.ext
        exact hxc
      rw [hEq]
      change (J.KI.shrinkingInsideBallHomeomorph
        J.invertedCenterInClosure : Plane) =
          (J.KI.shrinkingInsideBallHomeomorph
            J.invertedCenterInClosure : Plane)
      rfl

@[simp] theorem puncturedInvertedInsideToPuncturedBall_apply
    (x : {x : closure J.inverted.inside // (x : Plane) ≠ J.insidePoint}) :
    ((J.puncturedInvertedInsideToPuncturedBall x :
        closedBall (0 : Plane) 1) : Plane) =
      (J.KI.shrinkingInsideBallHomeomorph x : Plane) := rfl

/-- The completed homeomorphism of the original closed outside onto the
standard closed exterior. -/
noncomputable def shrinkingOutsideHomeomorph :
    closure J.outside ≃ₜ ((ball (0 : Plane) 1)ᶜ : Set Plane) :=
  J.outsideToPuncturedInvertedInside |>.trans <|
    J.puncturedInvertedInsideToPuncturedBall |>.trans <|
      BallPuncture.normalizedRecenteringPunctured J.invertedCenterInBall |>.trans
        puncturedClosedBallToExterior

/-- The outside homeomorphism has the same exact parametrized boundary value
as the bounded-side homeomorphism. -/
theorem shrinkingOutsideHomeomorph_boundary (x : J.carrier) :
    (J.shrinkingOutsideHomeomorph
        ⟨x, by rw [J.closure_outside]; exact Or.inr x.2⟩ : Plane) =
      (J.carrierHomeomorph.symm x : Plane) := by
  let xc : closure J.outside :=
    ⟨x, by rw [J.closure_outside]; exact Or.inr x.2⟩
  let p : J.inverted.carrier := J.carrierInversionHomeomorph x
  let pc : closure J.inverted.inside :=
    ⟨p, by rw [J.inverted.closure_inside]; exact Or.inr p.2⟩
  have hpNe : (p : Plane) ≠ J.insidePoint := by
    intro h
    exact J.insidePoint_not_mem_inverted_carrier (h ▸ p.2)
  let pp : {y : closure J.inverted.inside //
      (y : Plane) ≠ J.insidePoint} := ⟨pc, hpNe⟩
  have hinversion : J.outsideToPuncturedInvertedInside xc = pp := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let s : sphere (0 : Plane) 1 := J.inverted.carrierHomeomorph.symm p
  have hbounded : J.KI.shrinkingInsideBallHomeomorph pc =
      ⟨s, sphere_subset_closedBall s.2⟩ := by
    apply Subtype.ext
    exact J.KI.shrinkingInsideBallHomeomorph_boundary p
  let hpBall := J.puncturedInvertedInsideToPuncturedBall pp
  have hpBallEq : (hpBall : closedBall (0 : Plane) 1) =
      ⟨s, sphere_subset_closedBall s.2⟩ := by
    apply Subtype.ext
    change (J.KI.shrinkingInsideBallHomeomorph pp.1 : Plane) = (s : Plane)
    rw [show pp.1 = pc from rfl]
    exact congrArg Subtype.val hbounded
  have hsNeCenter : (s : Plane) ≠
      (J.invertedCenterInBall : Plane) := by
    intro h
    apply hpBall.2
    rw [hpBallEq]
    exact h
  let sp : {y : closedBall (0 : Plane) 1 //
      (y : Plane) ≠ (J.invertedCenterInBall : Plane)} :=
    ⟨⟨s, sphere_subset_closedBall s.2⟩, hsNeCenter⟩
  have hpNested : hpBall = sp := by
    apply Subtype.ext
    exact hpBallEq
  have hnormalized :
      BallPuncture.normalizedRecenteringPunctured J.invertedCenterInBall sp =
        ⟨⟨s, sphere_subset_closedBall s.2⟩, by
          intro h
          have hs := s.2
          rw [h, mem_sphere, dist_self] at hs
          norm_num at hs⟩ := by
    apply Subtype.ext
    exact BallPuncture.normalizedRecentering_boundary
      J.invertedCenterInBall s
  change (puncturedClosedBallToExterior
      (BallPuncture.normalizedRecenteringPunctured J.invertedCenterInBall
        (J.puncturedInvertedInsideToPuncturedBall
          (J.outsideToPuncturedInvertedInside xc))) : Plane) = _
  rw [hinversion, show J.puncturedInvertedInsideToPuncturedBall pp = hpBall
      from rfl, hpNested, hnormalized,
    puncturedClosedBallToExterior_boundary]
  exact congrArg Subtype.val
    (J.inverted_carrierHomeomorph_symm_carrierInversion x)

end JordanCircle

end

end Schoenflies
