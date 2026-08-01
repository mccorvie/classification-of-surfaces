import Mathlib
import Submission.Helpers

/-!
# `schoenflies` submission scaffold

This workspace already has the exact lean-eval shape, but the repository does
not yet contain a proof of the full Schoenflies theorem.  Once a source root is
available, add it to `PROBLEMS` in `port_submission.py` and replace this body
with the same kind of thin delegation used by the other two workspaces.
-/

namespace Submission

theorem schoenflies (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      h '' Set.range r = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  sorry

end Submission
