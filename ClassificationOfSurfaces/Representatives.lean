/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Eval representatives and normal-form indices

The Lean-Eval challenge owns `Complex.ClosedUnitDisc`, `OrientableRel`, and
`NonOrientableRel`; they are imported verbatim from `LeanEval/ChallengeDeps.lean`. This file adds
only the project-owned sphere abbreviation and the index type used by the normal-form reduction.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr

end ClassificationOfSurfaces
end Topology
end LeanEval
