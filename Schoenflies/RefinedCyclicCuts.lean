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

/-- A full linear cut lists every cyclic edge index exactly once. -/
theorem cutEdgeIndex_injective {n : ℕ} (K : PolygonalCircle)
    (hsize : n + 1 = K.n) (start : ZMod K.n) :
    Injective (cutEdgeIndex (n := n) K start) := by
  intro q r hqr
  have hcast : (q.val : ZMod K.n) = (r.val : ZMod K.n) := by
    apply add_right_cancel (b := start)
    exact hqr
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (by omega : q.val < K.n),
    ZMod.val_natCast_of_lt (by omega : r.val < K.n)] at hval
  exact Fin.ext hval

/-- The vertices listed by a full linear cut are pairwise distinct. -/
theorem cutVertex_injective {n : ℕ} (K : PolygonalCircle)
    (hsize : n + 1 = K.n) (start : ZMod K.n) :
    Injective (cutVertex (n := n) K start) := by
  intro q r hqr
  apply cutEdgeIndex_injective K hsize start
  exact K.vertex_injective hqr

/-- A cut vertex is marked when it is the image of one of the selected
first-tail crossing times. -/
noncomputable def cutFirstTailMark {n : ℕ}
    (A : J.AccessibleAngularArc) (K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (q : Fin (n + 1)) : Bool := by
  classical
  exact decide (∃ u ∈ T, u < s ∧ A.returnPath u = cutVertex K start q)

theorem cutFirstTailMark_eq_true_iff {n : ℕ}
    (A : J.AccessibleAngularArc) (K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (q : Fin (n + 1)) :
    A.cutFirstTailMark K start T s q = true ↔
      ∃ u ∈ T, u < s ∧ A.returnPath u = cutVertex K start q := by
  classical
  simp [cutFirstTailMark]

/-- At a cut vertex on the separator, the Boolean mark is exactly geometric
membership in the first endpoint tail. -/
theorem cutFirstTailMark_eq_true_iff_mem_firstTail {n : ℕ}
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ A.returnPath u ∈ Q.carrier)
    (hsNotCarrier : A.returnPath s ∉ Q.carrier)
    (q : Fin (n + 1)) (hqQ : cutVertex K start q ∈ Q.carrier) :
    A.cutFirstTailMark K start T s q = true ↔
      cutVertex K start q ∈
        A.returnPath '' Icc (⊥ : unitInterval) s := by
  constructor
  · intro hmark
    obtain ⟨u, _huT, hus, hu⟩ :=
      (A.cutFirstTailMark_eq_true_iff K start T s q).mp hmark
    exact ⟨u, ⟨bot_le, hus.le⟩, hu⟩
  · rintro ⟨u, huIcc, hu⟩
    have huT : u ∈ T := (hT u).mpr (hu ▸ hqQ)
    have hus : u < s := lt_of_le_of_ne huIcc.2 fun hus => by
      subst u
      exact hsNotCarrier (hu ▸ hqQ)
    exact (A.cutFirstTailMark_eq_true_iff K start T s q).mpr
      ⟨u, huT, hus, hu⟩

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

/-- The odd first-tail count on return-path parameters transfers exactly to
the marked crossings of any full linear cut of the refined polygon. -/
theorem odd_cutFirstTail_crossings {n : ℕ}
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hsize : n + 1 = K.n)
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
    (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ A.returnPath u ∈ Q.carrier)
    (hodd : Odd ((T.filter fun u => u < s).card)) :
    Odd (((linearCrossings (n := n)
      (A.cutRefinedEdgeSide (n := n) K start)).filter
      fun q : Fin (n + 1) =>
        A.cutFirstTailMark (n := n) K start T s q = true).card) := by
  classical
  let D : Finset unitInterval := T.filter fun u => u < s
  let C : Finset (Fin (n + 1)) :=
    (linearCrossings (n := n)
      (A.cutRefinedEdgeSide (n := n) K start)).filter
      fun q => A.cutFirstTailMark (n := n) K start T s q = true
  have hexistsIndex (u : D) :
      ∃ q : Fin (n + 1),
        cutVertex K start q = A.returnPath u := by
    have huT : (u : unitInterval) ∈ T := (Finset.mem_filter.mp u.2).1
    have hpQ : A.returnPath u ∈ Q.carrier := (hT u).mp huT
    obtain ⟨i, hi⟩ := hvertices (A.returnPath u)
      ⟨hpQ, ⟨u, rfl⟩⟩
    let raw : Fin K.n := ⟨(i - start).val, ZMod.val_lt _⟩
    let q : Fin (n + 1) := (finCongr hsize).symm raw
    refine ⟨q, ?_⟩
    rw [← hi]
    apply congrArg K.vertex
    change (q.val : ZMod K.n) + start = i
    have hqval : q.val = (i - start).val := by rfl
    rw [hqval, ZMod.natCast_zmod_val]
    abel
  let timeCutIndex (u : D) : Fin (n + 1) :=
    Classical.choose (hexistsIndex u)
  have timeCutIndex_spec (u : D) :
      cutVertex K start (timeCutIndex u) = A.returnPath u :=
    Classical.choose_spec (hexistsIndex u)
  let f : D → C := fun u =>
    ⟨timeCutIndex u, Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (A.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
          hcarrier hvertices hpolygonVertices hbrokenVertices start
          hstartPrev (timeCutIndex u)).mpr (by
            rw [timeCutIndex_spec u, A.carrier_auxiliaryJordanCircle]
            exact Or.inr ⟨u, rfl⟩)⟩,
      (A.cutFirstTailMark_eq_true_iff K start T s (timeCutIndex u)).mpr
        ⟨u, (Finset.mem_filter.mp u.2).1,
          (Finset.mem_filter.mp u.2).2, (timeCutIndex_spec u).symm⟩⟩⟩
  have hfInjective : Injective f := by
    intro u v huv
    have hindex : timeCutIndex u = timeCutIndex v :=
      congrArg Subtype.val huv
    apply Subtype.ext
    apply A.returnPath_injective
    calc
      A.returnPath u = cutVertex K start (timeCutIndex u) :=
        (timeCutIndex_spec u).symm
      _ = cutVertex K start (timeCutIndex v) := congrArg _ hindex
      _ = A.returnPath v := timeCutIndex_spec v
  have hfSurjective : Surjective f := by
    intro q
    have hmark : A.cutFirstTailMark K start T s q.1 = true :=
      (Finset.mem_filter.mp q.2).2
    obtain ⟨u, huT, hus, huVertex⟩ :=
      (A.cutFirstTailMark_eq_true_iff K start T s q.1).mp hmark
    let uD : D := ⟨u, Finset.mem_filter.mpr ⟨huT, hus⟩⟩
    refine ⟨uD, Subtype.ext ?_⟩
    change timeCutIndex uD = q.1
    apply cutVertex_injective K hsize start
    calc
      cutVertex K start (timeCutIndex uD) = A.returnPath u :=
        timeCutIndex_spec uD
      _ = cutVertex K start q.1 := huVertex
  let E : D ≃ C := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
  have hcard : D.card = C.card := by
    rw [← Fintype.card_coe D, ← Fintype.card_coe C]
    exact Fintype.card_congr E
  change Odd C.card
  rw [← hcard]
  simpa only [D] using hodd

/-- Odd first-tail parity selects one entire auxiliary-inside run of refined
polygon edges whose two crossing endpoints have different tail marks. -/
theorem exists_mixedTail_inside_cutRun {n : ℕ}
    (A : J.AccessibleAngularArc) (Q K : PolygonalCircle)
    (hsize : n + 1 = K.n)
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
    (hstart : A.refinedEdgeInside K start = true)
    (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ A.returnPath u ∈ Q.carrier)
    (hodd : Odd ((T.filter fun u => u < s).card)) :
    ∃ a b : Fin (n + 1),
      a < b ∧
        cutVertex K start a ∈ A.auxiliaryJordanCircle.carrier ∧
        cutVertex K start b ∈ A.auxiliaryJordanCircle.carrier ∧
        A.cutFirstTailMark K start T s a ≠
          A.cutFirstTailMark K start T s b ∧
        A.cutRefinedEdgeSide K start a = true ∧
        A.cutRefinedEdgeSide K start b = false ∧
        ∀ q : Fin (n + 1), a ≤ q → q < b →
          A.cutRefinedEdgeSide K start q = true := by
  have hfirst : A.cutRefinedEdgeSide (n := n) K start 0 = true := by
    simpa [cutRefinedEdgeSide] using hstart
  have hlast : A.cutRefinedEdgeSide (n := n) K start (Fin.last n) = false := by
    change A.refinedEdgeInside K
      (cutEdgeIndex K start (Fin.last n)) = false
    rw [cutEdgeIndex_last K hsize start]
    exact hstartPrev
  have hoddCut := A.odd_cutFirstTail_crossings Q K hsize hArcInside
    hcarrier hvertices hpolygonVertices hbrokenVertices start hstartPrev
      T s hT hodd
  obtain ⟨a, b, hab, haCross, hbCross, hmark,
      haTrue, hbFalse, hrun⟩ :=
    exists_true_run_with_mixed_crossing_marks
      (A.cutRefinedEdgeSide K start)
      (A.cutFirstTailMark K start T s) hfirst hlast hoddCut
  refine ⟨a, b, hab, ?_, ?_, hmark, haTrue, hbFalse, hrun⟩
  · exact (A.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
      hcarrier hvertices hpolygonVertices hbrokenVertices start
      hstartPrev a).mp haCross
  · exact (A.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
      hcarrier hvertices hpolygonVertices hbrokenVertices start
      hstartPrev b).mp hbCross

/-- Every point of a `true` cut run is in the auxiliary inside, except for
the two crossing vertices that bound the run. -/
theorem cutRun_edgePoint_inside_or_endpoint {n : ℕ}
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
    {a b : Fin (n + 1)} (_hab : a < b)
    (hrun : ∀ q : Fin (n + 1), a ≤ q → q < b →
      A.cutRefinedEdgeSide K start q = true) :
    ∀ q : Fin (n + 1), a ≤ q → q < b →
      ∀ x ∈ K.edgeSegment (cutEdgeIndex K start q),
        x = cutVertex K start a ∨ x = cutVertex K start b ∨
          x ∈ A.auxiliaryJordanCircle.inside := by
  have hinteriorVertex (r : Fin (n + 1)) (har : a < r) (hrb : r < b) :
      cutVertex K start r ∈ A.auxiliaryJordanCircle.inside := by
    have hrSide : A.cutRefinedEdgeSide K start r = true :=
      hrun r har.le hrb
    have hrNotCarrier :
        cutVertex K start r ∉ A.auxiliaryJordanCircle.carrier := by
      intro hrCarrier
      have hrCross :=
        (A.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
          hcarrier hvertices hpolygonVertices hbrokenVertices start
          hstartPrev r).mpr hrCarrier
      have hrPos : 0 < r.val := by
        change a.val < r.val at har
        omega
      let rprev : Fin (n + 1) := ⟨r.val - 1, by omega⟩
      have haPrev : a ≤ rprev := by
        change a.val ≤ r.val - 1
        omega
      have hprevB : rprev < b := by
        change r.val - 1 < b.val
        change r.val < b.val at hrb
        omega
      have hprevSide : A.cutRefinedEdgeSide K start rprev = true :=
        hrun rprev haPrev hprevB
      rw [IsLinearCrossing,
        incomingLinearSide_of_pos _ r hrPos] at hrCross
      exact hrCross (hprevSide.trans hrSide.symm)
    let i : ZMod K.n := cutEdgeIndex K start r
    have hopenInside :
        openSegment ℝ (K.vertex i) (K.vertex (i + 1)) ⊆
          A.auxiliaryJordanCircle.inside := by
      intro y hy
      apply (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hy).mpr
      exact hrSide
    have hvClosureOpen : K.vertex i ∈
        closure (openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
    have hvClosureInside : K.vertex i ∈
        closure A.auxiliaryJordanCircle.inside :=
      closure_mono hopenInside hvClosureOpen
    rw [A.auxiliaryJordanCircle.closure_inside] at hvClosureInside
    rcases hvClosureInside with hvInside | hvCarrier
    · exact hvInside
    · exact False.elim (hrNotCarrier hvCarrier)
  intro q haq hqb x hxEdge
  let i : ZMod K.n := cutEdgeIndex K start q
  have hxSegment : x ∈ segment ℝ (K.vertex i) (K.vertex (i + 1)) :=
    hxEdge
  by_cases hxLeft : x = K.vertex i
  · by_cases hqa : q = a
    · left
      subst q
      exact hxLeft
    · right; right
      rw [hxLeft]
      exact hinteriorVertex q (lt_of_le_of_ne haq (Ne.symm hqa)) hqb
  by_cases hxRight : x = K.vertex (i + 1)
  · let qnext : Fin (n + 1) := ⟨q.val + 1, by
        change q.val < b.val at hqb
        omega⟩
    have hindexNext : cutEdgeIndex K start qnext = i + 1 := by
      simp only [cutEdgeIndex, i, qnext]
      push_cast
      abel
    by_cases hnextB : qnext = b
    · right; left
      rw [hxRight, ← hindexNext, hnextB]
      rfl
    · right; right
      rw [hxRight, ← hindexNext]
      apply hinteriorVertex qnext
      · change a.val < q.val + 1
        change a.val ≤ q.val at haq
        omega
      · have hnextLe : qnext ≤ b := by
          change q.val + 1 ≤ b.val
          change q.val < b.val at hqb
          omega
        exact lt_of_le_of_ne hnextLe hnextB
  · right; right
    have hxOpen : x ∈ openSegment ℝ (K.vertex i) (K.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right
        (fun h => hxLeft h.symm) (fun h => hxRight h.symm) hxSegment
    apply (A.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
      hcarrier hvertices i hxOpen).mpr
    exact hrun q haq hqb

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
