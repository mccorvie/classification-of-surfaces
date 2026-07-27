/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.EvalStatement
import ClassificationOfSurfaces.LeanEval.ChallengeDeps

/-!
# Lean-Eval specification audit

This compile-only audit pins the public theorem to the carrier and relation constants vendored in
`ChallengeDeps.lean`. In particular, the quotient carriers below are `Complex.ClosedUnitDisc`,
not a project-owned substitute.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

#check Complex.ClosedUnitDisc

#check (OrientableRel :
  (p n : ℕ) → Complex.ClosedUnitDisc → Complex.ClosedUnitDisc → Prop)

#check (NonOrientableRel :
  (p n : ℕ) → Complex.ClosedUnitDisc → Complex.ClosedUnitDisc → Prop)

/-- Type-level regression check against the exact conclusion published by Lean-Eval. -/
example (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧
            Nonempty
              (S ≃ₜ Quot
                (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p n))) ∨
          (1 ≤ p ∧
            Nonempty
              (S ≃ₜ Quot
                (LeanEval.Topology.ClassificationOfSurfaces.NonOrientableRel p n))) :=
  topological_classification_of_surfaces S

end ClassificationOfSurfaces
end Topology
end LeanEval
