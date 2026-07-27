/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Real
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Eval representatives and normal-form indices

The Lean-Eval challenge owns `Complex.ClosedUnitDisc`, `OrientableRel`, and
`NonOrientableRel`; they are imported verbatim from `LeanEval/ChallengeDeps.lean`. This file adds
only the project-owned sphere abbreviation and the index type used by the normal-form reduction.
-/

open scoped Manifold

namespace Complex

/-- The closed unit disk in the complex plane. -/
abbrev ClosedUnitDisc : Type :=
  Metric.closedBall (0 : ℂ) 1

/-- The boundary point `exp (2πir)` on the closed unit disk. -/
noncomputable def ClosedUnitDisc.bdyPtOfReal (r : ℝ) : ClosedUnitDisc :=
  ⟨r.fourierChar, r.fourierChar.2.le⟩

@[simp]
theorem ClosedUnitDisc.norm_bdyPtOfReal (r : ℝ) :
    ‖(ClosedUnitDisc.bdyPtOfReal r : ℂ)‖ = 1 := by
  apply mem_sphere_zero_iff_norm.mp
  exact r.fourierChar.2

end Complex

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex Set

/-- The representative orientable surface of genus `p` with `n` disks removed.

Its boundary word is
`a₁b₁a₁⁻¹b₁⁻¹⋯aₚbₚaₚ⁻¹bₚ⁻¹c₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`.
This declaration is definitionally aligned with the trusted Lean-Eval benchmark. -/
inductive OrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 3 - x) / (4 * p + 3 * n))
  | b (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + 1 + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 4 - x) / (4 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : OrientableRel p n
      (.bdyPtOfReal <| -(3 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| -(3 * i + 3 - x) / (4 * p + 3 * n))

/-- The representative non-orientable surface with `p` crosscaps and `n` disks removed.

Its boundary word is `a₁a₁⋯aₚaₚc₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`.
This declaration is definitionally aligned with the trusted Lean-Eval benchmark. -/
inductive NonOrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : NonOrientableRel p n
      (.bdyPtOfReal <| (2 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| (2 * i + 1 + x) / (2 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : NonOrientableRel p n
      (.bdyPtOfReal <| -(3 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| -(3 * i + 3 - x) / (2 * p + 3 * n))

/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Radius descends through every orientable boundary identification. -/
noncomputable def orientableQuotRadius (p n : ℕ) : Quot (OrientableRel p n) → ℝ :=
  Quot.lift (fun z : ClosedUnitDisc ↦ ‖(z : ℂ)‖) (by
    intro a b hab
    cases hab <;> simp)

/-- Radius descends through every non-orientable boundary identification. -/
noncomputable def nonOrientableQuotRadius (p n : ℕ) : Quot (NonOrientableRel p n) → ℝ :=
  Quot.lift (fun z : ClosedUnitDisc ↦ ‖(z : ℂ)‖) (by
    intro a b hab
    cases hab <;> simp)

/-- None of the orientable representatives collapses to a point: the disk center and boundary
have different radii in the quotient. -/
theorem not_subsingleton_orientableQuot (p n : ℕ) :
    ¬Subsingleton (Quot (OrientableRel p n)) := by
  intro h
  have hcollapse :
      Quot.mk (OrientableRel p n) (0 : ClosedUnitDisc) =
        Quot.mk (OrientableRel p n) (ClosedUnitDisc.bdyPtOfReal 0) :=
    h.elim _ _
  have hradius := congrArg (orientableQuotRadius p n) hcollapse
  norm_num [orientableQuotRadius] at hradius

/-- None of the non-orientable representatives collapses to a point. -/
theorem not_subsingleton_nonOrientableQuot (p n : ℕ) :
    ¬Subsingleton (Quot (NonOrientableRel p n)) := by
  intro h
  have hcollapse :
      Quot.mk (NonOrientableRel p n) (0 : ClosedUnitDisc) =
        Quot.mk (NonOrientableRel p n) (ClosedUnitDisc.bdyPtOfReal 0) :=
    h.elim _ _
  have hradius := congrArg (nonOrientableQuotRadius p n) hcollapse
  norm_num [nonOrientableQuotRadius] at hradius

/-- Definition-faithfulness anchor: the torus representative is not a point. -/
example : ¬Subsingleton (Quot (OrientableRel 1 0)) :=
  not_subsingleton_orientableQuot 1 0

/-- Definition-faithfulness anchor: the projective-plane representative is not a point. -/
example : ¬Subsingleton (Quot (NonOrientableRel 1 0)) :=
  not_subsingleton_nonOrientableQuot 1 0

/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr

end ClassificationOfSurfaces
end Topology
end LeanEval
