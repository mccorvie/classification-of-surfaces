import ChallengeDeps
import Submission.ClassificationOfSurfaces.EvalStatement

/-!
# `topological_classification_of_surfaces` submission shim

The proof development is maintained at the repository root.  Run
`python3 port_submission.py` to refresh the generated copy under `Submission/`.
-/

open LeanEval.Topology.ClassificationOfSurfaces
open Complex Set

namespace Submission

theorem classification_of_surfaces (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
    ∃ p n, ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
      (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) :=
  LeanEval.Topology.ClassificationOfSurfaces.classification_of_surfaces S

end Submission
