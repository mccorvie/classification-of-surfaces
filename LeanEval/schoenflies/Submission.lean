import Submission.Schoenflies.Main

/-!
# `schoenflies` submission shim

The proof development is maintained at the repository root.  Run
`python3 port_submission.py` to refresh the generated copy under `Submission/`.
-/

namespace Submission

theorem schoenflies (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' Set.range r = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  exact Schoenflies.schoenflies r _hcont _hinj

end Submission
