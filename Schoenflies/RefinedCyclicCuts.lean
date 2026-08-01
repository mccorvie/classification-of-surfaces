import Schoenflies.RefinedEdgeSides
import Schoenflies.CyclicCrossingParity
import Schoenflies.ReturnArcParity

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

variable {J : JordanCircle} {A : J.AccessibleAngularArc}

namespace InsideReturnArc

/-- The old cyclic edge index represented by a position after cutting at
`start`. -/
def cutEdgeIndex {n : ℕ} (K : PolygonalCircle) (start : ZMod K.n)
    (q : Fin (n + 1)) : ZMod K.n :=
  (q.val : ZMod K.n) + start

/-- Refined auxiliary-inside edge labels, read linearly after a cyclic cut. -/
noncomputable def cutRefinedEdgeSide {n : ℕ}
    (R : A.InsideReturnArc) (K : PolygonalCircle)
    (start : ZMod K.n) (q : Fin (n + 1)) : Bool :=
  R.refinedEdgeInside K (cutEdgeIndex K start q)

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
    (R : A.InsideReturnArc) (K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (q : Fin (n + 1)) : Bool := by
  classical
  exact decide (∃ u ∈ T, u < s ∧ R.path u = cutVertex K start q)

theorem cutFirstTailMark_eq_true_iff {n : ℕ}
    (R : A.InsideReturnArc) (K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (q : Fin (n + 1)) :
    R.cutFirstTailMark K start T s q = true ↔
      ∃ u ∈ T, u < s ∧ R.path u = cutVertex K start q := by
  classical
  simp [cutFirstTailMark]

/-- At a cut vertex on the separator, the Boolean mark is exactly geometric
membership in the first endpoint tail. -/
theorem cutFirstTailMark_eq_true_iff_mem_firstTail {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (start : ZMod K.n) (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hsNotCarrier : R.path s ∉ Q.carrier)
    (q : Fin (n + 1)) (hqQ : cutVertex K start q ∈ Q.carrier) :
    R.cutFirstTailMark K start T s q = true ↔
      cutVertex K start q ∈
        R.path '' Icc (⊥ : unitInterval) s := by
  constructor
  · intro hmark
    obtain ⟨u, _huT, hus, hu⟩ :=
      (R.cutFirstTailMark_eq_true_iff K start T s q).mp hmark
    exact ⟨u, ⟨bot_le, hus.le⟩, hu⟩
  · rintro ⟨u, huIcc, hu⟩
    have huT : u ∈ T := (hT u).mpr (hu ▸ hqQ)
    have hus : u < s := lt_of_le_of_ne huIcc.2 fun hus => by
      subst u
      exact hsNotCarrier (hu ▸ hqQ)
    exact (R.cutFirstTailMark_eq_true_iff K start T s q).mpr
      ⟨u, huT, hus, hu⟩

/-- The abstract incoming label at a cut position is the label of the actual
preceding polygon edge. -/
theorem incomingLinearSide_cutRefinedEdgeSide {n : ℕ}
    (R : A.InsideReturnArc) (K : PolygonalCircle)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    (q : Fin (n + 1)) :
    incomingLinearSide (R.cutRefinedEdgeSide K start) q =
      R.refinedEdgeInside K (cutEdgeIndex K start q - 1) := by
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
    change R.refinedEdgeInside K
        (((q.val - 1 : ℕ) : ZMod K.n) + start) =
      R.refinedEdgeInside K ((q.val : ZMod K.n) + start - 1)
    apply congrArg (R.refinedEdgeInside K)
    rw [hpred]
    abel

/-- For a generic refinement, the linear crossing predicate after a cyclic
cut is exactly membership of the represented vertex in the auxiliary circle. -/
theorem isLinearCrossing_cutRefinedEdgeSide_iff {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    (q : Fin (n + 1)) :
    IsLinearCrossing (R.cutRefinedEdgeSide K start) q ↔
      cutVertex K start q ∈ R.auxiliaryJordanCircle.carrier := by
  rw [IsLinearCrossing,
    R.incomingLinearSide_cutRefinedEdgeSide K start hstartPrev q]
  change
    R.refinedEdgeInside K (cutEdgeIndex K start q - 1) ≠
        R.refinedEdgeInside K (cutEdgeIndex K start q) ↔
      K.vertex (cutEdgeIndex K start q) ∈
        R.auxiliaryJordanCircle.carrier
  exact R.refinedEdgeSides_ne_iff_crossingVertex Q K hArcInside
    hcarrier hvertices hpolygonVertices hbrokenVertices
      (cutEdgeIndex K start q)

/-- The odd first-tail count on return-path parameters transfers exactly to
the marked crossings of any full linear cut of the refined polygon. -/
theorem odd_cutFirstTail_crossings {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hsize : n + 1 = K.n)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hodd : Odd ((T.filter fun u => u < s).card)) :
    Odd (((linearCrossings (n := n)
      (R.cutRefinedEdgeSide (n := n) K start)).filter
      fun q : Fin (n + 1) =>
        R.cutFirstTailMark (n := n) K start T s q = true).card) := by
  classical
  let D : Finset unitInterval := T.filter fun u => u < s
  let C : Finset (Fin (n + 1)) :=
    (linearCrossings (n := n)
      (R.cutRefinedEdgeSide (n := n) K start)).filter
      fun q => R.cutFirstTailMark (n := n) K start T s q = true
  have hexistsIndex (u : D) :
      ∃ q : Fin (n + 1),
        cutVertex K start q = R.path u := by
    have huT : (u : unitInterval) ∈ T := (Finset.mem_filter.mp u.2).1
    have hpQ : R.path u ∈ Q.carrier := (hT u).mp huT
    obtain ⟨i, hi⟩ := hvertices (R.path u)
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
      cutVertex K start (timeCutIndex u) = R.path u :=
    Classical.choose_spec (hexistsIndex u)
  let f : D → C := fun u =>
    ⟨timeCutIndex u, Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (R.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
          hcarrier hvertices hpolygonVertices hbrokenVertices start
          hstartPrev (timeCutIndex u)).mpr (by
            rw [timeCutIndex_spec u, R.carrier_auxiliaryJordanCircle]
            exact Or.inr ⟨u, rfl⟩)⟩,
      (R.cutFirstTailMark_eq_true_iff K start T s (timeCutIndex u)).mpr
        ⟨u, (Finset.mem_filter.mp u.2).1,
          (Finset.mem_filter.mp u.2).2, (timeCutIndex_spec u).symm⟩⟩⟩
  have hfInjective : Injective f := by
    intro u v huv
    have hindex : timeCutIndex u = timeCutIndex v :=
      congrArg Subtype.val huv
    apply Subtype.ext
    apply R.path_injective
    calc
      R.path u = cutVertex K start (timeCutIndex u) :=
        (timeCutIndex_spec u).symm
      _ = cutVertex K start (timeCutIndex v) := congrArg _ hindex
      _ = R.path v := timeCutIndex_spec v
  have hfSurjective : Surjective f := by
    intro q
    have hmark : R.cutFirstTailMark K start T s q.1 = true :=
      (Finset.mem_filter.mp q.2).2
    obtain ⟨u, huT, hus, huVertex⟩ :=
      (R.cutFirstTailMark_eq_true_iff K start T s q.1).mp hmark
    let uD : D := ⟨u, Finset.mem_filter.mpr ⟨huT, hus⟩⟩
    refine ⟨uD, Subtype.ext ?_⟩
    change timeCutIndex uD = q.1
    apply cutVertex_injective K hsize start
    calc
      cutVertex K start (timeCutIndex uD) = R.path u :=
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
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hsize : n + 1 = K.n)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    (hstart : R.refinedEdgeInside K start = true)
    (T : Finset unitInterval) (s : unitInterval)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hodd : Odd ((T.filter fun u => u < s).card)) :
    ∃ a b : Fin (n + 1),
      a < b ∧
        cutVertex K start a ∈ R.auxiliaryJordanCircle.carrier ∧
        cutVertex K start b ∈ R.auxiliaryJordanCircle.carrier ∧
        R.cutFirstTailMark K start T s a ≠
          R.cutFirstTailMark K start T s b ∧
        R.cutRefinedEdgeSide K start a = true ∧
        R.cutRefinedEdgeSide K start b = false ∧
        ∀ q : Fin (n + 1), a ≤ q → q < b →
          R.cutRefinedEdgeSide K start q = true := by
  have hfirst : R.cutRefinedEdgeSide (n := n) K start 0 = true := by
    simpa [cutRefinedEdgeSide] using hstart
  have hlast : R.cutRefinedEdgeSide (n := n) K start (Fin.last n) = false := by
    change R.refinedEdgeInside K
      (cutEdgeIndex K start (Fin.last n)) = false
    rw [cutEdgeIndex_last K hsize start]
    exact hstartPrev
  have hoddCut := R.odd_cutFirstTail_crossings Q K hsize hArcInside
    hcarrier hvertices hpolygonVertices hbrokenVertices start hstartPrev
      T s hT hodd
  obtain ⟨a, b, hab, haCross, hbCross, hmark,
      haTrue, hbFalse, hrun⟩ :=
    exists_true_run_with_mixed_crossing_marks
      (R.cutRefinedEdgeSide K start)
      (R.cutFirstTailMark K start T s) hfirst hlast hoddCut
  refine ⟨a, b, hab, ?_, ?_, hmark, haTrue, hbFalse, hrun⟩
  · exact (R.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
      hcarrier hvertices hpolygonVertices hbrokenVertices start
      hstartPrev a).mp haCross
  · exact (R.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
      hcarrier hvertices hpolygonVertices hbrokenVertices start
      hstartPrev b).mp hbCross

/-- Every point of a `true` cut run is in the auxiliary inside, except for
the two crossing vertices that bound the run. -/
theorem cutRun_edgePoint_inside_or_endpoint {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    {a b : Fin (n + 1)} (_hab : a < b)
    (hrun : ∀ q : Fin (n + 1), a ≤ q → q < b →
      R.cutRefinedEdgeSide K start q = true) :
    ∀ q : Fin (n + 1), a ≤ q → q < b →
      ∀ x ∈ K.edgeSegment (cutEdgeIndex K start q),
        x = cutVertex K start a ∨ x = cutVertex K start b ∨
          x ∈ R.auxiliaryJordanCircle.inside := by
  have hinteriorVertex (r : Fin (n + 1)) (har : a < r) (hrb : r < b) :
      cutVertex K start r ∈ R.auxiliaryJordanCircle.inside := by
    have hrSide : R.cutRefinedEdgeSide K start r = true :=
      hrun r har.le hrb
    have hrNotCarrier :
        cutVertex K start r ∉ R.auxiliaryJordanCircle.carrier := by
      intro hrCarrier
      have hrCross :=
        (R.isLinearCrossing_cutRefinedEdgeSide_iff Q K hArcInside
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
      have hprevSide : R.cutRefinedEdgeSide K start rprev = true :=
        hrun rprev haPrev hprevB
      rw [IsLinearCrossing,
        incomingLinearSide_of_pos _ r hrPos] at hrCross
      exact hrCross (hprevSide.trans hrSide.symm)
    let i : ZMod K.n := cutEdgeIndex K start r
    have hopenInside :
        openSegment ℝ (K.vertex i) (K.vertex (i + 1)) ⊆
          R.auxiliaryJordanCircle.inside := by
      intro y hy
      apply (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
        hcarrier hvertices i hy).mpr
      exact hrSide
    have hvClosureOpen : K.vertex i ∈
        closure (openSegment ℝ (K.vertex i) (K.vertex (i + 1))) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ _ _)
    have hvClosureInside : K.vertex i ∈
        closure R.auxiliaryJordanCircle.inside :=
      closure_mono hopenInside hvClosureOpen
    rw [R.auxiliaryJordanCircle.closure_inside] at hvClosureInside
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
    apply (R.mem_auxiliaryInside_iff_refinedEdgeInside Q K hArcInside
      hcarrier hvertices i hxOpen).mpr
    exact hrun q haq hqb

/-- The two parameter tails separated by a nonempty middle interval have
disjoint images under the injective return path. -/
theorem disjoint_firstTail_lastTail
    (R : A.InsideReturnArc) {s t : unitInterval} (hst : s < t) :
    Disjoint
      (R.path '' Icc (⊥ : unitInterval) s)
      (R.path '' Icc t (⊤ : unitInterval)) := by
  rw [Set.disjoint_left]
  intro x hxFirst hxLast
  obtain ⟨u, hu, hux⟩ := hxFirst
  obtain ⟨v, hv, hvx⟩ := hxLast
  have huv : u = v := R.path_injective (hux.trans hvx.symm)
  subst v
  exact (not_le_of_gt hst) (hv.1.trans hu.2)

/-- Distinct first-tail marks on two auxiliary-circle crossings force the
crossings to lie on opposite endpoint tails of the return path. -/
theorem cutVertices_of_distinct_firstTailMarks_lie_on_opposite_tails
    {n : ℕ} (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hcarrier : K.carrier = Q.carrier) (start : ZMod K.n)
    (T : Finset unitInterval) {s t : unitInterval} (hst : s < t)
    (hMiddleExterior : R.path '' Icc s t ⊆ Q.exteriorRegion)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hintersections :
      Q.carrier ∩ R.auxiliaryJordanCircle.carrier ⊆
        R.path '' Icc (⊥ : unitInterval) s ∪
          R.path '' Icc t (⊤ : unitInterval))
    {a b : Fin (n + 1)}
    (haAux : cutVertex K start a ∈ R.auxiliaryJordanCircle.carrier)
    (hbAux : cutVertex K start b ∈ R.auxiliaryJordanCircle.carrier)
    (hmark : R.cutFirstTailMark K start T s a ≠
      R.cutFirstTailMark K start T s b) :
    ((cutVertex K start a ∈
          R.path '' Icc (⊥ : unitInterval) s ∧
        cutVertex K start b ∈
          R.path '' Icc t (⊤ : unitInterval)) ∨
      (cutVertex K start a ∈
          R.path '' Icc t (⊤ : unitInterval) ∧
        cutVertex K start b ∈
          R.path '' Icc (⊥ : unitInterval) s)) := by
  have hsExterior : R.path s ∈ Q.exteriorRegion :=
    hMiddleExterior ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩
  have hsNotCarrier : R.path s ∉ Q.carrier := by
    intro hsCarrier
    exact Set.disjoint_left.mp Q.disjoint_carrier_exteriorRegion
      hsCarrier hsExterior
  have haQ : cutVertex K start a ∈ Q.carrier := by
    rw [← hcarrier]
    exact K.vertex_mem_carrier (cutEdgeIndex K start a)
  have hbQ : cutVertex K start b ∈ Q.carrier := by
    rw [← hcarrier]
    exact K.vertex_mem_carrier (cutEdgeIndex K start b)
  have haTails := hintersections ⟨haQ, haAux⟩
  have hbTails := hintersections ⟨hbQ, hbAux⟩
  have haMarkIff :=
    R.cutFirstTailMark_eq_true_iff_mem_firstTail Q K start T s
      hT hsNotCarrier a haQ
  have hbMarkIff :=
    R.cutFirstTailMark_eq_true_iff_mem_firstTail Q K start T s
      hT hsNotCarrier b hbQ
  have hdisjoint := R.disjoint_firstTail_lastTail hst
  rcases haTails with haFirst | haLast
  · rcases hbTails with hbFirst | hbLast
    · have haTrue := haMarkIff.mpr haFirst
      have hbTrue := hbMarkIff.mpr hbFirst
      exact False.elim (hmark (haTrue.trans hbTrue.symm))
    · exact Or.inl ⟨haFirst, hbLast⟩
  · rcases hbTails with hbFirst | hbLast
    · exact Or.inr ⟨haLast, hbFirst⟩
    · have haNotFirst : cutVertex K start a ∉
          R.path '' Icc (⊥ : unitInterval) s :=
        fun haFirst => Set.disjoint_left.mp hdisjoint haFirst haLast
      have hbNotFirst : cutVertex K start b ∉
          R.path '' Icc (⊥ : unitInterval) s :=
        fun hbFirst => Set.disjoint_left.mp hdisjoint hbFirst hbLast
      have haFalse : R.cutFirstTailMark K start T s a = false :=
        Bool.eq_false_of_not_eq_true (fun haTrue =>
          haNotFirst (haMarkIff.mp haTrue))
      have hbFalse : R.cutFirstTailMark K start T s b = false :=
        Bool.eq_false_of_not_eq_true (fun hbTrue =>
          hbNotFirst (hbMarkIff.mp hbTrue))
      exact False.elim (hmark (haFalse.trans hbFalse.symm))

/-- A true run in the linear cut is itself a broken-line join through the
auxiliary inside, allowing only its two crossing endpoints on the boundary. -/
theorem joinedByBrokenLine_cutRun {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    {a b : Fin (n + 1)} (hab : a < b)
    (hrun : ∀ q : Fin (n + 1), a ≤ q → q < b →
      R.cutRefinedEdgeSide K start q = true) :
    JoinedByBrokenLine
      ((R.auxiliaryJordanCircle.inside ∩ K.carrier) ∪
        {cutVertex K start a, cutVertex K start b})
      (cutVertex K start a) (cutVertex K start b) := by
  let k := b.val - a.val
  let qAt : Fin (k + 1) → Fin (n + 1) := fun j =>
    ⟨a.val + j.val, by
      change a.val < b.val at hab
      omega⟩
  have hqZero : qAt 0 = a := by
    apply Fin.ext
    simp [qAt]
  have hqLast : qAt (Fin.last k) = b := by
    apply Fin.ext
    simp only [qAt, Fin.val_last, k]
    change a.val < b.val at hab
    omega
  refine ⟨k, (fun j => cutVertex K start (qAt j)), ?_, ?_, ?_⟩
  · change cutVertex K start (qAt 0) = cutVertex K start a
    rw [hqZero]
  · change cutVertex K start (qAt (Fin.last k)) = cutVertex K start b
    rw [hqLast]
  · intro i x hx
    have hqA : a ≤ qAt i.castSucc := by
      change a.val ≤ a.val + i.val
      omega
    have hqB : qAt i.castSucc < b := by
      change a.val + i.val < b.val
      have hi : i.val < b.val - a.val := i.isLt
      omega
    have hindex : cutEdgeIndex K start (qAt i.succ) =
        cutEdgeIndex K start (qAt i.castSucc) + 1 := by
      simp only [cutEdgeIndex, qAt, Fin.val_succ, Fin.val_castSucc]
      push_cast
      abel
    have hxEdge : x ∈ K.edgeSegment
        (cutEdgeIndex K start (qAt i.castSucc)) := by
      rw [PolygonalCircle.edgeSegment]
      simpa only [cutVertex, hindex] using hx
    rcases R.cutRun_edgePoint_inside_or_endpoint Q K hArcInside
        hcarrier hvertices hpolygonVertices hbrokenVertices start hstartPrev
        hab hrun (qAt i.castSucc) hqA hqB x hxEdge with hxa | hxb | hxInside
    · exact Or.inr (by simp [hxa])
    · exact Or.inr (by simp [hxb])
    · exact Or.inl ⟨hxInside,
        K.edgeSegment_subset_carrier
          (cutEdgeIndex K start (qAt i.castSucc)) hxEdge⟩

/-- The odd tail parity package produces a polygonal join through the
auxiliary inside from the first return-path tail to the last one. -/
theorem exists_inside_brokenLine_between_returnTails {n : ℕ}
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hsize : n + 1 = K.n)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (start : ZMod K.n)
    (hstartPrev : R.refinedEdgeInside K (start - 1) = false)
    (hstart : R.refinedEdgeInside K start = true)
    (T : Finset unitInterval) {s t : unitInterval} (hst : s < t)
    (hMiddleExterior : R.path '' Icc s t ⊆ Q.exteriorRegion)
    (hT : ∀ u, u ∈ T ↔ R.path u ∈ Q.carrier)
    (hodd : Odd ((T.filter fun u => u < s).card))
    (hintersections :
      Q.carrier ∩ R.auxiliaryJordanCircle.carrier ⊆
        R.path '' Icc (⊥ : unitInterval) s ∪
          R.path '' Icc t (⊤ : unitInterval)) :
    ∃ p q : Plane,
      p ∈ R.path '' Icc (⊥ : unitInterval) s ∧
        q ∈ R.path '' Icc t (⊤ : unitInterval) ∧
        p ∈ K.carrier ∧ q ∈ K.carrier ∧
        JoinedByBrokenLine
          ((R.auxiliaryJordanCircle.inside ∩ K.carrier) ∪ {p, q}) p q := by
  obtain ⟨a, b, hab, haAux, hbAux, hmark, _haTrue, _hbFalse, hrun⟩ :=
    R.exists_mixedTail_inside_cutRun Q K hsize hArcInside hcarrier
      hvertices hpolygonVertices hbrokenVertices start hstartPrev hstart
      T s hT hodd
  have hopposite :=
    R.cutVertices_of_distinct_firstTailMarks_lie_on_opposite_tails
      Q K hcarrier start T hst hMiddleExterior hT hintersections
      haAux hbAux hmark
  have hjoin := R.joinedByBrokenLine_cutRun Q K hArcInside hcarrier
    hvertices hpolygonVertices hbrokenVertices start hstartPrev hab hrun
  rcases hopposite with ⟨haFirst, hbLast⟩ | ⟨haLast, hbFirst⟩
  · exact ⟨cutVertex K start a, cutVertex K start b,
      haFirst, hbLast,
      K.vertex_mem_carrier (cutEdgeIndex K start a),
      K.vertex_mem_carrier (cutEdgeIndex K start b), hjoin⟩
  · refine ⟨cutVertex K start b, cutVertex K start a,
      hbFirst, haLast,
      K.vertex_mem_carrier (cutEdgeIndex K start b),
      K.vertex_mem_carrier (cutEdgeIndex K start a), ?_⟩
    simpa only [Set.pair_comm] using hjoin.symm

/-- A generic refined separator that meets the return path has a cyclic
outside-to-inside edge transition at which to make the linear cut. -/
theorem exists_refined_false_true_transition
    (R : A.InsideReturnArc) (Q K : PolygonalCircle)
    (hArcInside : A.curveArcPlane ⊆ Q.interiorRegion)
    (hcarrier : K.carrier = Q.carrier)
    (hvertices : ∀ p ∈ Q.carrier ∩ range R.path,
      K.IsVertexPoint p)
    (hpolygonVertices : ∀ (i : ZMod Q.n)
        (j : Fin R.carrierBrokenLine.data.n),
      planeDet
        (R.carrierBrokenLine.data.vertex j.castSucc - Q.vertex i)
        (R.carrierBrokenLine.data.vertex j.succ -
          R.carrierBrokenLine.data.vertex j.castSucc) ≠ 0)
    (hbrokenVertices : ∀ (i : ZMod Q.n)
        (j : Fin (R.carrierBrokenLine.data.n + 1)),
      planeDet
        (R.carrierBrokenLine.data.vertex j - Q.vertex i)
        (Q.vertex (i + 1) - Q.vertex i) ≠ 0)
    (hmeets : (Q.carrier ∩ range R.path).Nonempty) :
    ∃ start : ZMod K.n,
      R.refinedEdgeInside K (start - 1) = false ∧
        R.refinedEdgeInside K start = true := by
  classical
  obtain ⟨p, hpQ, hpReturn⟩ := hmeets
  obtain ⟨i, hi⟩ := hvertices p ⟨hpQ, hpReturn⟩
  have hiAux : K.vertex i ∈ R.auxiliaryJordanCircle.carrier := by
    rw [hi, R.carrier_auxiliaryJordanCircle]
    exact Or.inr hpReturn
  have hchange := R.refined_crossingVertex_changes_edgeSide Q K
    hArcInside hcarrier hvertices hpolygonVertices hbrokenVertices i hiAux
  have hfalse : ∃ e : ZMod K.n, R.refinedEdgeInside K e = false := by
    by_cases hprev : R.refinedEdgeInside K (i - 1) = false
    · exact ⟨i - 1, hprev⟩
    · have hprevTrue := Bool.eq_true_of_not_eq_false hprev
      have houtNotTrue : R.refinedEdgeInside K i ≠ true :=
        fun houtTrue => hchange (hprevTrue.trans houtTrue.symm)
      exact ⟨i, Bool.eq_false_of_not_eq_true houtNotTrue⟩
  have htrue : ∃ e : ZMod K.n, R.refinedEdgeInside K e = true := by
    by_cases hout : R.refinedEdgeInside K i = true
    · exact ⟨i, hout⟩
    · have houtFalse := Bool.eq_false_of_not_eq_true hout
      have hprevNotFalse : R.refinedEdgeInside K (i - 1) ≠ false :=
        fun hprevFalse => hchange (hprevFalse.trans houtFalse.symm)
      exact ⟨i - 1, Bool.eq_true_of_not_eq_false hprevNotFalse⟩
  exact exists_cyclic_false_true_transition
    (lt_of_lt_of_le (by norm_num : 0 < 3) K.three_le)
    (R.refinedEdgeInside K) hfalse htrue

end InsideReturnArc
end AccessibleAngularArc
end JordanCircle

end Schoenflies
