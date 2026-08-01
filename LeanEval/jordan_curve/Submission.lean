import Submission.JordanCurve

/-!
# `jordan_curve` submission shim

The proof development is maintained at the repository root.  Run
`python3 port_submission.py` to refresh the generated copy under `Submission/`.
-/

namespace Submission

theorem jordan_curve (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Function.Injective r) :
    Nat.card
        (ConnectedComponents ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) =
      2 :=
  _root_.JordanCurve.jordan_curve r _hcont _hinj

end Submission
