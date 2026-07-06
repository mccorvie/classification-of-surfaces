/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Normal-form representatives

The eval statement names two families of quotient spaces. This file owns those names.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Temporary carrier for the polygonal cell model used by the standard representatives.

TODO: replace this with a disk/polygon plus boundary-edge identifications. -/
abbrev SurfaceCellModel (_p _n : ℕ) : Type := PUnit

instance (p n : ℕ) : TopologicalSpace (SurfaceCellModel p n) :=
  inferInstanceAs (TopologicalSpace PUnit)

/-- Placeholder relation for the orientable representative of genus `p` with `n` boundary
components. -/
def OrientableRel (p n : ℕ) : Setoid (SurfaceCellModel p n) := ⊥

/-- Placeholder relation for the non-orientable representative with `p` crosscaps and `n` boundary
components. -/
def NonOrientableRel (p n : ℕ) : Setoid (SurfaceCellModel p n) := ⊥

/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Placeholder homeomorphism from the temporary one-point model to an orientable quotient.

This should disappear once the representative quotients are implemented by actual polygonal
models. -/
noncomputable def orientableRelPUnitHomeomorph (p n : ℕ) :
    PUnit ≃ₜ Quot (OrientableRel p n) where
  toFun := fun _ => Quot.mk (OrientableRel p n) PUnit.unit
  invFun := fun _ => PUnit.unit
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro q
    induction q using Quot.ind with
    | mk a =>
        cases a
        rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- Placeholder homeomorphism from the temporary one-point model to a non-orientable quotient.

This should disappear once the representative quotients are implemented by actual polygonal
models. -/
noncomputable def nonOrientableRelPUnitHomeomorph (p n : ℕ) :
    PUnit ≃ₜ Quot (NonOrientableRel p n) where
  toFun := fun _ => Quot.mk (NonOrientableRel p n) PUnit.unit
  invFun := fun _ => PUnit.unit
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro q
    induction q using Quot.ind with
    | mk a =>
        cases a
        rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr

end ClassificationOfSurfaces
end Topology
end LeanEval
