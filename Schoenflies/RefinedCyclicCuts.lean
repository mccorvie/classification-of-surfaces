import Schoenflies.RefinedEdgeSides
import Schoenflies.CyclicCrossingParity

/-!
# Linear cuts of refined separator polygons

These adapters rotate a refined polygon at a chosen outside-to-inside edge
transition.  They identify the abstract crossings used by
`CyclicCrossingParity` with the actual auxiliary-circle vertices.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- The old cyclic edge index represented by a position after cutting at
`start`. -/
def cutEdgeIndex {n : ℕ} (K : PolygonalCircle) (start : ZMod K.n)
    (q : Fin (n + 1)) : ZMod K.n :=
  (q.val : ZMod K.n) + start

/-- Refined auxiliary-inside edge labels, read linearly after a cyclic cut. -/
noncomputable def cutRefinedEdgeSide {n : ℕ}
    (A : J.AccessibleAngularArc) (K : PolygonalCircle)
    (start : ZMod K.n) (q : Fin (n + 1)) : Bool :=
  A.refinedEdgeInside K (cutEdgeIndex K start q)

/-- The polygon vertex represented by a position after a cyclic cut. -/
def cutVertex {n : ℕ} (K : PolygonalCircle) (start : ZMod K.n)
    (q : Fin (n + 1)) : Plane :=
  K.vertex (cutEdgeIndex K start q)

@[simp] theorem cutEdgeIndex_zero {n : ℕ} (K : PolygonalCircle)
    (start : ZMod K.n) :
    cutEdgeIndex (n := n) K start 0 = start := by
  simp [cutEdgeIndex]

theorem cutEdgeIndex_last {n : ℕ} (K : PolygonalCircle)
    (hsize : n + 1 = K.n) (start : ZMod K.n) :
    cutEdgeIndex K start (Fin.last n) = start - 1 := by
  have hzero : (n : ZMod K.n) + 1 = 0 := by
    calc
      (n : ZMod K.n) + 1 = ((n + 1 : ℕ) : ZMod K.n) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = (K.n : ZMod K.n) :=
        congrArg (fun z : ℕ => (z : ZMod K.n)) hsize
      _ = 0 := ZMod.natCast_self K.n
  change (n : ZMod K.n) + start = start - 1
  have hn : (n : ZMod K.n) = -1 := by
    exact eq_neg_of_add_eq_zero_left hzero
  rw [hn]
  abel

/-- The abstract incoming label at a cut position is the label of the actual
preceding polygon edge. -/
theorem incomingLinearSide_cutRefinedEdgeSide {n : ℕ}
    (A : J.AccessibleAngularArc) (K : PolygonalCircle)
    (start : ZMod K.n)
    (hstartPrev : A.refinedEdgeInside K (start - 1) = false)
    (q : Fin (n + 1)) :
    incomingLinearSide (A.cutRefinedEdgeSide K start) q =
      A.refinedEdgeInside K (cutEdgeIndex K start q - 1) := by
  by_cases hq : q.val = 0
  · have hqZero : q = 0 := Fin.ext hq
    subst q
    simpa [cutRefinedEdgeSide] using hstartPrev
  · rw [incomingLinearSide_of_pos _ q (Nat.pos_of_ne_zero hq)]
    have hpred : ((q.val - 1 : ℕ) : ZMod K.n) =
        (q.val : ZMod K.n) - 1 := by
      apply eq_sub_of_add_eq
      calc
        ((q.val - 1 : ℕ) : ZMod K.n) + 1 =
            ((q.val - 1 + 1 : ℕ) : ZMod K.n) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = (q.val : ZMod K.n) := by
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
    change A.refinedEdgeInside K
        (((q.val - 1 : ℕ) : ZMod K.n) + start) =
      A.refinedEdgeInside K ((q.val : ZMod K.n) + start - 1)
    apply congrArg (A.refinedEdgeInside K)
    rw [hpred]
    abel

/-- For a generic refinement, the linear crossing predicate after a cyclic
cut is exactly membership of the represented vertex in the auxiliary circle. -/
theorem isLinearCrossing_cutRefinedEdgeSide_iff {n : ℕ}
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range A.returnPath,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin A.returnCarrierBrokenLine.data.n),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (A.returnCarrierBrokenLine.data.vertex j.succ -
          A.returnCarrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (A.returnCarrierBrokenLine.data.n + 1)),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : A.refinedEdgeInside K (start - 1) = false)
    (q : Fin (n + 1)) :
    IsLinearCrossing (A.cutRefinedEdgeSide K start) q ↔
      cutVertex K start q ∈ A.auxiliaryJordanCircle.carrier := by
  rw [IsLinearCrossing,
    A.incomingLinearSide_cutRefinedEdgeSide K start hstartPrev q]
  change
    A.refinedEdgeInside K (cutEdgeIndex K start q - 1) ≠
        A.refinedEdgeInside K (cutEdgeIndex K start q) ↔
      K.vertex (cutEdgeIndex K start q) ∈
        A.auxiliaryJordanCircle.carrier
  exact A.refinedEdgeSides_ne_iff_crossingVertex Q K hArcInside
    hcarrier hvertices hpolygonVertices hbrokenVertices
      (cutEdgeIndex K start q)

/-- A generic refined separator that meets the return path has a cyclic
outside-to-inside edge transition at which to make the linear cut. -/
theorem exists_refined_false_true_transition
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range A.returnPath,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin A.returnCarrierBrokenLine.data.n),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (A.returnCarrierBrokenLine.data.vertex j.succ -
          A.returnCarrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (A.returnCarrierBrokenLine.data.n + 1)),
      planeDet
        (A.returnCarrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (hmeets : (Q.carrier ∩ range A.returnPath).Nonempty) :
    ∃ start : ZMod K.n,
      A.refinedEdgeInside K (start - 1) = false ∧
        A.refinedEdgeInside K start = true := by
  classical
  obtain ⟨p, hpQ, hpReturn⟩ := hmeets
  obtain ⟨i, hi⟩ := hvertices p ⟨hpQ, hpReturn⟩
  have hiAux : K.vertex i ∈ A.auxiliaryJordanCircle.carrier := by
    rw [hi, A.carrier_auxiliaryJordanCircle]
    exact Or.inr hpReturn
  have hchange := A.refined_crossingVertex_changes_edgeSide Q K
    hArcInside hcarrier hvertices hpolygonVertices hbrokenVertices i hiAux
  have hfalse : ∃ e : ZMod K.n, A.refinedEdgeInside K e = false := by
    by_cases hprev : A.refinedEdgeInside K (i - 1) = false
    · exact ⟨i - 1, hprev⟩
    · have hprevTrue := Bool.eq_true_of_not_eq_false hprev
      have houtNotTrue : A.refinedEdgeInside K i ≠ true :=
        fun houtTrue => hchange (hprevTrue.trans houtTrue.symm)
      exact ⟨i, Bool.eq_false_of_not_eq_true houtNotTrue⟩
  have htrue : ∃ e : ZMod K.n, A.refinedEdgeInside K e = true := by
    by_cases hout : A.refinedEdgeInside K i = true
    · exact ⟨i, hout⟩
    · have houtFalse := Bool.eq_false_of_not_eq_true hout
      have hprevNotFalse : A.refinedEdgeInside K (i - 1) ≠ false :=
        fun hprevFalse => hchange (hprevFalse.trans houtFalse.symm)
      exact ⟨i - 1, Bool.eq_true_of_not_eq_false hprevNotFalse⟩
  exact exists_cyclic_false_true_transition
    (lt_of_lt_of_le (by norm_num : 0 < 3) K.three_le)
    (A.refinedEdgeInside K) hfalse htrue

end AccessibleAngularArc
end JordanCircle

end Schoenflies
