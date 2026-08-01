import Schoenflies.FiniteSeparatorSetup
import Schoenflies.RefinedCyclicCuts
import Schoenflies.ReturnPathParity

/-!
# A controlled inside join between the two return-path tails

This is the geometric output of Moise's finite separator and cyclic pairing
argument.  It hides the translated polygon, its generic-position hypotheses,
the intersection-vertex refinement, and the parity bookkeeping behind one
neighborhood-scale statement.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- At every scale, the two short endpoint tails of the polygonal return path
can be joined through the original Jordan inside while remaining in that
scale's neighborhood of the selected boundary arc. -/
theorem exists_controlled_inside_join_between_returnTails
    (A : J.AccessibleAngularArc) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (s t : unitInterval) (p q : Plane),
      (0 : ℝ) < s ∧ (s : ℝ) < t ∧ (t : ℝ) < 1 ∧
        A.returnPath '' Icc (0 : unitInterval) s ⊆
          thickening epsilon A.curveArcPlane ∧
        A.returnPath '' Icc t (1 : unitInterval) ⊆
          thickening epsilon A.curveArcPlane ∧
        p ∈ A.returnPath '' Icc (0 : unitInterval) s ∧
        q ∈ A.returnPath '' Icc t (1 : unitInterval) ∧
        JoinedByBrokenLine
          ((J.inside ∩ thickening epsilon A.curveArcPlane) ∪ {p, q}) p q := by
  obtain ⟨s, t, Q, hspos, hst, htone, hfirstSmall, hlastSmall,
      hQsmall, hArcInside, hMiddleExterior, _hMiddleCompact,
      _hMiddlePreconnected, _hMiddleDisjoint, hfinite, hfirstMeet,
      _hlastMeet, hintersections, hpolygonVertices, hbrokenVertices⟩ :=
    A.exists_finiteSeparatorFrame hepsilon
  obtain ⟨K, hcarrier, _hinterior, _hexterior, hvertices⟩ :=
    A.exists_intersectionVertexRefinement Q hfinite
  have hmeets : (Q.carrier ∩ range A.returnPath).Nonempty := by
    obtain ⟨x, hxQ, u, _hu, hux⟩ := hfirstMeet
    exact ⟨x, hxQ, ⟨u, hux⟩⟩
  obtain ⟨start, hstartPrev, hstart⟩ :=
    A.exists_refined_false_true_transition Q K hArcInside hcarrier
      hvertices hpolygonVertices hbrokenVertices hmeets
  obtain ⟨T, hT, _hordered, hodd⟩ :=
    A.exists_ordered_crossingTimes_odd_firstTail Q hspos hst
      hArcInside hMiddleExterior hfinite hpolygonVertices hbrokenVertices
  let n := K.n - 1
  have hsize : n + 1 = K.n := by
    dsimp [n]
    have hnpos : 0 < K.n := lt_of_lt_of_le (by omega : 0 < 3) K.three_le
    omega
  obtain ⟨p, q, hpFirst, hqLast, hjoin⟩ :=
    A.exists_inside_brokenLine_between_returnTails (n := n) Q K hsize
      hArcInside hcarrier hvertices hpolygonVertices hbrokenVertices
      start hstartPrev hstart T hst hMiddleExterior hT hodd hintersections
  have hjoinControlled : JoinedByBrokenLine
      ((J.inside ∩ thickening epsilon A.curveArcPlane) ∪ {p, q}) p q := by
    apply hjoin.mono
    rintro x (⟨hxAuxInside, hxK⟩ | hxEndpoint)
    · left
      refine ⟨A.inside_auxiliaryJordanCircle_subset hxAuxInside,
        hQsmall ?_⟩
      rw [← hcarrier]
      exact hxK
    · exact Or.inr hxEndpoint
  exact ⟨s, t, p, q, hspos, hst, htone, hfirstSmall, hlastSmall,
    hpFirst, hqLast, hjoinControlled⟩

end AccessibleAngularArc
end JordanCircle

end Schoenflies
