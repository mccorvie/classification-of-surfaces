import Schoenflies.ControlledJordanArcPaths
import Schoenflies.PolygonalJordanCircle
import Schoenflies.PolygonalSubarcs

/-!
# Comparing intrinsic and polygonal boundary arcs

After two points of a polygonal circle have been made vertices, the two
intrinsic Jordan arcs between them are exactly the two cyclic edge arcs of
the polygon, up to swapping the two choices.  The proper-chord development
in Chapter 2 proves the corresponding statements only when both edge arcs
contain at least two edges.  Annular crosscuts can end at adjacent polygon
vertices, so this file supplies the endpoint-adjacent version as well.
-/

open Set Function

noncomputable section

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise
namespace PolygonalCircle

open ProperChord

variable (J : PolygonalCircle)

private theorem natCast_injective_of_lt {n m l : ℕ} [NeZero n]
    (hm : m < n) (hl : l < n)
    (h : (m : ZMod n) = (l : ZMod n)) : m = l := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hl] at hv

theorem endpoints_mem_forwardArc_of_pos {k : ℕ}
    (hkpos : 0 < k) (_hk : k < J.n) :
    J.vertex 0 ∈ forwardArc (J := J) k ∧
      J.vertex (k : ZMod J.n) ∈ forwardArc (J := J) k := by
  constructor
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, hkpos⟩, ?_⟩
    simpa only [edgeSegment, Fin.val_zero, Nat.cast_zero] using
      (left_mem_segment ℝ (J.vertex 0) (J.vertex ((0 : ZMod J.n) + 1)))
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    change J.vertex (k : ZMod J.n) ∈
      J.edgeSegment ((k - 1 : ℕ) : ZMod J.n)
    apply (J.vertex_mem_edgeSegment_iff (k : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mpr
    right
    calc
      (k : ZMod J.n) = ((k - 1 + 1 : ℕ) : ZMod J.n) := by
        congr 1
        omega
      _ = ((k - 1 : ℕ) : ZMod J.n) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]

theorem endpoints_mem_backwardArc_of_pos {k : ℕ}
    (hkpos : 0 < k) (hk : k < J.n) :
    J.vertex 0 ∈ backwardArc (J := J) k ∧
      J.vertex (k : ZMod J.n) ∈ backwardArc (J := J) k := by
  let R := J.rotate (k : ZMod J.n)
  have hlenpos : 0 < J.n - k := by omega
  have hlenlt : J.n - k < R.n := by
    change J.n - k < J.n
    omega
  have hends := R.endpoints_mem_forwardArc_of_pos hlenpos hlenlt
  have hzero : R.vertex 0 = J.vertex (k : ZMod J.n) := by
    change J.vertex ((0 : ZMod J.n) + (k : ZMod J.n)) = _
    rw [zero_add]
  have hlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = J.vertex 0 := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) +
      (k : ZMod J.n)) = J.vertex 0
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel hk.le]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
  exact ⟨by simpa only [backwardArc, hlast] using hends.2,
    by simpa only [backwardArc, hzero] using hends.1⟩

theorem isClosed_forwardArc (k : ℕ) :
    IsClosed (forwardArc (J := J) k) := by
  exact isClosed_iUnion_of_finite fun i : Fin k => J.isClosed_edgeSegment i

theorem isClosed_backwardArc (k : ℕ) :
    IsClosed (backwardArc (J := J) k) := by
  exact (J.rotate (k : ZMod J.n)).isClosed_forwardArc (J.n - k)

/-- The cyclic edge arcs meet only at their endpoints, including when one
of the arcs consists of a single polygon edge. -/
theorem forwardArc_inter_backwardArc_of_pos {k : ℕ}
    (hkpos : 0 < k) (hk : k < J.n) :
    forwardArc (J := J) k ∩ backwardArc (J := J) k =
      {J.vertex 0, J.vertex (k : ZMod J.n)} := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxF, hxB⟩
    simp only [forwardArc, Set.mem_iUnion] at hxF
    simp only [backwardArc, forwardArc, Set.mem_iUnion] at hxB
    obtain ⟨m, hm⟩ := hxF
    obtain ⟨l, hl⟩ := hxB
    let a := m.val
    let b := l.val + k
    have ha : a < k := m.isLt
    have hb0 : k ≤ b := by dsimp [b]; omega
    have hbn : b < J.n := by dsimp [b]; omega
    have hm' : x ∈ J.edgeSegment (a : ZMod J.n) := by
      simpa [a] using hm
    have hrot := rotate_edgeSegment_nat (J := J) (k := k) (m := l.val)
      hk (by omega)
    have hlOld : x ∈ J.edgeSegment (b : ZMod J.n) := by
      have hl' : x ∈ (J.rotate (k : ZMod J.n)).edgeSegment
          (l.val : ZMod J.n) := by
        exact hl
      rw [hrot] at hl'
      have hidx : (l.val : ZMod J.n) + (k : ZMod J.n) =
          (b : ZMod J.n) := by
        dsimp [b]
        rw [Nat.cast_add]
      rwa [hidx] at hl'
    have hab : (a : ZMod J.n) ≠ (b : ZMod J.n) := by
      intro heq
      have := natCast_injective_of_lt (by omega : a < J.n) hbn heq
      omega
    have hxEnds := J.edgeSegment_inter_subset_endpoints hab ⟨hm', hlOld⟩
    rcases hxEnds with hxa | hxa
    · have hvertexB : J.vertex (a : ZMod J.n) ∈
          J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff (a : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · exact (hab heq).elim
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt (by omega : a < J.n), ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          have ha0 : a = 0 := by omega
          left
          calc
            x = J.vertex (a : ZMod J.n) := hxa
            _ = J.vertex (0 : ZMod J.n) := by rw [ha0]; simp
    · have ha1 : a + 1 < J.n := by omega
      rw [Set.mem_singleton_iff] at hxa
      have hcast : (a : ZMod J.n) + 1 = (a + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast] at hxa
      have hvertexB : J.vertex ((a + 1 : ℕ) : ZMod J.n) ∈
          J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff ((a + 1 : ℕ) : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · have habNat := natCast_injective_of_lt ha1 hbn heq
        have haLast : a + 1 = k := by omega
        right
        calc
          x = J.vertex ((a + 1 : ℕ) : ZMod J.n) := hxa
          _ = J.vertex (k : ZMod J.n) := by rw [haLast]
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt ha1, ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          omega
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(J.endpoints_mem_forwardArc_of_pos hkpos hk).1,
        (J.endpoints_mem_backwardArc_of_pos hkpos hk).1⟩
    · exact ⟨(J.endpoints_mem_forwardArc_of_pos hkpos hk).2,
        (J.endpoints_mem_backwardArc_of_pos hkpos hk).2⟩

end PolygonalCircle
end LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise
open PolygonalCircle.ProperChord

namespace JordanCircle.TwoBoundaryArcPaths

variable {J K : JordanCircle} {x y : Plane}

/-- Transport a boundary split between Jordan-circle presentations with the
same point-set carrier. -/
def congrCarrier (S : J.TwoBoundaryArcPaths x y)
    (hcarrier : K.carrier = J.carrier) : K.TwoBoundaryArcPaths x y where
  first := S.first
  second := S.second
  first_injective := S.first_injective
  second_injective := S.second_injective
  cover := by rw [hcarrier]; exact S.cover
  overlap := S.overlap

@[simp] theorem congrCarrier_first (S : J.TwoBoundaryArcPaths x y)
    (hcarrier : K.carrier = J.carrier) :
    (S.congrCarrier hcarrier).first = S.first := rfl

@[simp] theorem congrCarrier_second (S : J.TwoBoundaryArcPaths x y)
    (hcarrier : K.carrier = J.carrier) :
    (S.congrCarrier hcarrier).second = S.second := rfl

end JordanCircle.TwoBoundaryArcPaths

namespace PolygonalCircle

private theorem range_subset_of_interior_image_subset
    {x y : Plane} (p : Path x y)
    {C : Set Plane} (hx : x ∈ C) (hy : y ∈ C)
    (hinter : p '' Set.Ioo (0 : unitInterval) 1 ⊆ C) :
    range p ⊆ C := by
  rintro z ⟨t, rfl⟩
  by_cases ht0 : t = 0
  · subst t
    simpa only [p.source] using hx
  by_cases ht1 : t = 1
  · subst t
    simpa only [p.target] using hy
  apply hinter
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · exact bot_lt_iff_ne_bot.mpr ht0
  · exact lt_top_iff_ne_top.mpr ht1

private theorem path_interior_image_avoids_endpoints
    {x y : Plane} (p : Path x y) (hp : Injective p) :
    (p '' Set.Ioo (0 : unitInterval) 1) ∩ ({x, y} : Set Plane) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨z, ⟨⟨t, ht, rfl⟩, hz⟩⟩
  rcases hz with hzx | hzy
  · have ht0 : t = 0 := hp (by simpa only [p.source] using hzx)
    exact (ne_of_gt ht.1) ht0
  · rw [Set.mem_singleton_iff] at hzy
    have ht1 : t = 1 := hp (by simpa only [p.target] using hzy)
    exact (ne_of_lt ht.2) ht1

private theorem backwardArc_sdiff_forwardArc_nonempty
    (P : PolygonalCircle) {k : ℕ} (hkpos : 0 < k) (hk : k < P.n) :
    (backwardArc (J := P) k \ forwardArc (J := P) k).Nonempty := by
  let R := P.rotate (k : ZMod P.n)
  let z : Plane := midpoint ℝ (R.vertex 0) (R.vertex 1)
  have hzOpen : z ∈ openSegment ℝ (R.vertex 0) (R.vertex 1) :=
    midpoint_mem_openSegment _ _
  have hzSegment : z ∈ R.edgeSegment 0 := by
    change z ∈ segment ℝ (R.vertex 0) (R.vertex (0 + 1))
    simpa only [zero_add] using
      (openSegment_subset_segment ℝ _ _ hzOpen)
  have hzNotVertex : ¬ R.IsVertexPoint z := by
    intro hzVertex
    rcases (hzVertex.mem_edgeSegment_iff (0 : ZMod R.n)).mp hzSegment with
      hz0 | hz1
    · have hmid : midpoint ℝ (R.vertex 0) (R.vertex 1) = R.vertex 0 := by
        simpa only [z] using hz0
      apply R.adjacent_ne 0
      simpa only [zero_add] using (midpoint_eq_left_iff ℝ).mp hmid
    · have hmid : midpoint ℝ (R.vertex 0) (R.vertex 1) = R.vertex 1 := by
        simpa only [z, zero_add] using hz1
      apply R.adjacent_ne 0
      simpa only [zero_add] using (midpoint_eq_right_iff ℝ).mp hmid
  have hlenpos : 0 < P.n - k := by omega
  have hzBackward : z ∈ backwardArc (J := P) k := by
    simp only [backwardArc, forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, hlenpos⟩, ?_⟩
    simpa only [Fin.val_zero, Nat.cast_zero] using hzSegment
  refine ⟨z, hzBackward, ?_⟩
  intro hzForward
  have hzEnds : z ∈
      ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
    rw [← P.forwardArc_inter_backwardArc_of_pos hkpos hk]
    exact ⟨hzForward, hzBackward⟩
  rcases hzEnds with hz0 | hzk
  · apply hzNotVertex
    refine ⟨((P.n - k : ℕ) : ZMod R.n), ?_⟩
    change P.vertex (((P.n - k : ℕ) : ZMod P.n) +
      (k : ZMod P.n)) = z
    have hsum : ((P.n - k : ℕ) : ZMod P.n) + (k : ZMod P.n) = 0 := by
      calc
        ((P.n - k : ℕ) : ZMod P.n) + (k : ZMod P.n) =
            ((P.n - k + k : ℕ) : ZMod P.n) := by rw [Nat.cast_add]
        _ = (P.n : ℕ) := by rw [Nat.sub_add_cancel hk.le]
        _ = 0 := ZMod.natCast_self P.n
    rw [hsum, hz0]
  · apply hzNotVertex
    rw [Set.mem_singleton_iff] at hzk
    refine ⟨0, ?_⟩
    change P.vertex ((0 : ZMod P.n) + (k : ZMod P.n)) = z
    simpa only [zero_add] using hzk.symm

private theorem forwardArc_sdiff_backwardArc_nonempty
    (P : PolygonalCircle) {k : ℕ} (hkpos : 0 < k) (hk : k < P.n) :
    (forwardArc (J := P) k \ backwardArc (J := P) k).Nonempty := by
  let z : Plane := midpoint ℝ (P.vertex 0) (P.vertex 1)
  have hzOpen : z ∈ openSegment ℝ (P.vertex 0) (P.vertex 1) :=
    midpoint_mem_openSegment _ _
  have hzSegment : z ∈ P.edgeSegment 0 := by
    change z ∈ segment ℝ (P.vertex 0) (P.vertex (0 + 1))
    simpa only [zero_add] using
      (openSegment_subset_segment ℝ _ _ hzOpen)
  have hzNotVertex : ¬ P.IsVertexPoint z := by
    intro hzVertex
    rcases (hzVertex.mem_edgeSegment_iff (0 : ZMod P.n)).mp hzSegment with
      hz0 | hz1
    · have hmid : midpoint ℝ (P.vertex 0) (P.vertex 1) = P.vertex 0 := by
        simpa only [z] using hz0
      apply P.adjacent_ne 0
      simpa only [zero_add] using (midpoint_eq_left_iff ℝ).mp hmid
    · have hmid : midpoint ℝ (P.vertex 0) (P.vertex 1) = P.vertex 1 := by
        simpa only [z, zero_add] using hz1
      apply P.adjacent_ne 0
      simpa only [zero_add] using (midpoint_eq_right_iff ℝ).mp hmid
  have hzForward : z ∈ forwardArc (J := P) k := by
    simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, hkpos⟩, ?_⟩
    simpa only [Fin.val_zero, Nat.cast_zero] using hzSegment
  refine ⟨z, hzForward, ?_⟩
  intro hzBackward
  have hzEnds : z ∈
      ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
    rw [← P.forwardArc_inter_backwardArc_of_pos hkpos hk]
    exact ⟨hzForward, hzBackward⟩
  rcases hzEnds with hz0 | hzk
  · apply hzNotVertex
    refine ⟨0, hz0.symm⟩
  · rw [Set.mem_singleton_iff] at hzk
    apply hzNotVertex
    exact ⟨(k : ZMod P.n), hzk.symm⟩

/-- Once the endpoints are polygon vertices `0` and `k`, an arbitrary
intrinsic two-arc split is exactly the forward/backward polygonal split, up
to exchanging the two paths. -/
theorem twoBoundaryArcPaths_eq_forward_backward
    (P : PolygonalCircle) {k : ℕ} (hkpos : 0 < k) (hk : k < P.n)
    (S : P.toJordanCircle.TwoBoundaryArcPaths
      (P.vertex 0) (P.vertex (k : ZMod P.n))) :
    (range S.first = forwardArc (J := P) k ∧
        range S.second = backwardArc (J := P) k) ∨
      (range S.first = backwardArc (J := P) k ∧
        range S.second = forwardArc (J := P) k) := by
  let F := forwardArc (J := P) k
  let B := backwardArc (J := P) k
  have hFclosed : IsClosed F := P.isClosed_forwardArc k
  have hBclosed : IsClosed B := P.isClosed_backwardArc k
  have hFB : F ∩ B = {P.vertex 0, P.vertex (k : ZMod P.n)} :=
    P.forwardArc_inter_backwardArc_of_pos hkpos hk
  have hFends : P.vertex 0 ∈ F ∧ P.vertex (k : ZMod P.n) ∈ F :=
    P.endpoints_mem_forwardArc_of_pos hkpos hk
  have hBends : P.vertex 0 ∈ B ∧ P.vertex (k : ZMod P.n) ∈ B :=
    P.endpoints_mem_backwardArc_of_pos hkpos hk
  have hfirstCarrier : range S.first ⊆ P.carrier := by
    intro z hz
    rw [← P.carrier_toJordanCircle, ← S.cover]
    exact Or.inl hz
  have hsecondCarrier : range S.second ⊆ P.carrier := by
    intro z hz
    rw [← P.carrier_toJordanCircle, ← S.cover]
    exact Or.inr hz
  have hcanonicalCover : F ∪ B = P.carrier := by
    exact forwardArc_union_backwardArc hk
  have hsplitCover : range S.first ∪ range S.second = P.carrier := by
    simpa only [P.carrier_toJordanCircle] using S.cover
  have hfirstInteriorPreconnected :
      IsPreconnected (S.first '' Set.Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image S.first S.first.continuous.continuousOn
  have hfirstInteriorCover :
      S.first '' Set.Ioo (0 : unitInterval) 1 ⊆ F ∪ B := by
    rintro z ⟨t, ht, rfl⟩
    rw [hcanonicalCover]
    exact hfirstCarrier ⟨t, rfl⟩
  have hfirstInteriorDisjoint :
      (S.first '' Set.Ioo (0 : unitInterval) 1) ∩ (F ∩ B) = ∅ := by
    rw [hFB]
    exact path_interior_image_avoids_endpoints S.first S.first_injective
  have hfirstInteriorCases :
      S.first '' Set.Ioo (0 : unitInterval) 1 ⊆ F ∨
        S.first '' Set.Ioo (0 : unitInterval) 1 ⊆ B :=
    isPreconnected_iff_subset_of_disjoint_closed.mp
      hfirstInteriorPreconnected F B hFclosed hBclosed
        hfirstInteriorCover hfirstInteriorDisjoint
  have hsecondInteriorPreconnected :
      IsPreconnected (S.second '' Set.Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image S.second S.second.continuous.continuousOn
  have hsecondInteriorCover :
      S.second '' Set.Ioo (0 : unitInterval) 1 ⊆ F ∪ B := by
    rintro z ⟨t, ht, rfl⟩
    rw [hcanonicalCover]
    exact hsecondCarrier ⟨t, rfl⟩
  have hsecondInteriorDisjoint :
      (S.second '' Set.Ioo (0 : unitInterval) 1) ∩ (F ∩ B) = ∅ := by
    rw [hFB, Set.pair_comm]
    exact path_interior_image_avoids_endpoints S.second S.second_injective
  have hsecondInteriorCases :
      S.second '' Set.Ioo (0 : unitInterval) 1 ⊆ F ∨
        S.second '' Set.Ioo (0 : unitInterval) 1 ⊆ B :=
    isPreconnected_iff_subset_of_disjoint_closed.mp
      hsecondInteriorPreconnected F B hFclosed hBclosed
        hsecondInteriorCover hsecondInteriorDisjoint
  have hsplit_of_mem_carrier {z : Plane} (hz : z ∈ P.carrier) :
      z ∈ range S.first ∨ z ∈ range S.second := by
    have : z ∈ range S.first ∪ range S.second := by
      rw [hsplitCover]
      exact hz
    exact this
  rcases hfirstInteriorCases with hfirstF | hfirstB
  · have hfirstSub : range S.first ⊆ F :=
      range_subset_of_interior_image_subset S.first
        hFends.1 hFends.2 hfirstF
    have hsecondB : S.second '' Set.Ioo (0 : unitInterval) 1 ⊆ B := by
      rcases hsecondInteriorCases with hsecondF | hsecondB
      · exfalso
        have hsecondSub : range S.second ⊆ F :=
          range_subset_of_interior_image_subset S.second
            hFends.2 hFends.1 hsecondF
        obtain ⟨z, hzB, hzNotF⟩ := backwardArc_sdiff_forwardArc_nonempty
          P hkpos hk
        have hzSplit := hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inr hzB))
        exact hzNotF (hzSplit.elim (fun hz => hfirstSub hz)
          (fun hz => hsecondSub hz))
      · exact hsecondB
    have hsecondSub : range S.second ⊆ B :=
      range_subset_of_interior_image_subset S.second
        hBends.2 hBends.1 hsecondB
    left
    constructor
    · apply Set.Subset.antisymm hfirstSub
      intro z hzF
      rcases hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inl hzF)) with hzFirst | hzSecond
      · exact hzFirst
      · have hzEnds : z ∈
            ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
          rw [← hFB]
          exact ⟨hzF, hsecondSub hzSecond⟩
        rcases hzEnds with rfl | rfl
        · exact Path.source_mem_range S.first
        · exact Path.target_mem_range S.first
    · apply Set.Subset.antisymm hsecondSub
      intro z hzB
      rcases hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inr hzB)) with hzFirst | hzSecond
      · have hzEnds : z ∈
            ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
          rw [← hFB]
          exact ⟨hfirstSub hzFirst, hzB⟩
        rcases hzEnds with rfl | rfl
        · exact Path.target_mem_range S.second
        · exact Path.source_mem_range S.second
      · exact hzSecond
  · have hfirstSub : range S.first ⊆ B :=
      range_subset_of_interior_image_subset S.first
        hBends.1 hBends.2 hfirstB
    have hsecondF : S.second '' Set.Ioo (0 : unitInterval) 1 ⊆ F := by
      rcases hsecondInteriorCases with hsecondF | hsecondB
      · exact hsecondF
      · exfalso
        have hsecondSub : range S.second ⊆ B :=
          range_subset_of_interior_image_subset S.second
            hBends.2 hBends.1 hsecondB
        obtain ⟨z, hzF, hzNotB⟩ := forwardArc_sdiff_backwardArc_nonempty
          P hkpos hk
        have hzSplit := hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inl hzF))
        exact hzNotB (hzSplit.elim (fun hz => hfirstSub hz)
          (fun hz => hsecondSub hz))
    have hsecondSub : range S.second ⊆ F :=
      range_subset_of_interior_image_subset S.second
        hFends.2 hFends.1 hsecondF
    right
    constructor
    · apply Set.Subset.antisymm hfirstSub
      intro z hzB
      rcases hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inr hzB)) with hzFirst | hzSecond
      · exact hzFirst
      · have hzEnds : z ∈
            ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
          rw [← hFB]
          exact ⟨hsecondSub hzSecond, hzB⟩
        rcases hzEnds with rfl | rfl
        · exact Path.source_mem_range S.first
        · exact Path.target_mem_range S.first
    · apply Set.Subset.antisymm hsecondSub
      intro z hzF
      rcases hsplit_of_mem_carrier
          (hcanonicalCover.le (Or.inl hzF)) with hzFirst | hzSecond
      · have hzEnds : z ∈
            ({P.vertex 0, P.vertex (k : ZMod P.n)} : Set Plane) := by
          rw [← hFB]
          exact ⟨hzF, hfirstSub hzFirst⟩
        rcases hzEnds with rfl | rfl
        · exact Path.target_mem_range S.second
        · exact Path.source_mem_range S.second
      · exact hzSecond

/-- Refine and rotate a polygonal presentation at the endpoints of an
intrinsic boundary split.  In the resulting presentation the split has the
exact forward/backward finite-edge description. -/
theorem exists_normalization_twoBoundaryArcPaths
    (P : PolygonalCircle) {x y : Plane} (hxy : x ≠ y)
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y) :
    ∃ R : PolygonalCircle, ∃ k : ℕ,
      R.carrier = P.carrier ∧
      R.vertex 0 = x ∧
      R.vertex (k : ZMod R.n) = y ∧
      0 < k ∧ k < R.n ∧
      ((range S.first = forwardArc (J := R) k ∧
          range S.second = backwardArc (J := R) k) ∨
        (range S.first = backwardArc (J := R) k ∧
          range S.second = forwardArc (J := R) k)) := by
  classical
  have hxP : x ∈ P.carrier := by
    rw [← P.carrier_toJordanCircle, ← S.cover]
    exact Or.inl (Path.source_mem_range S.first)
  have hyP : y ∈ P.carrier := by
    rw [← P.carrier_toJordanCircle, ← S.cover]
    exact Or.inl (Path.target_mem_range S.first)
  let E : Finset Plane := {x, y}
  obtain ⟨K, hKP, hvertices⟩ := P.exists_refinement_vertices E (by
    intro z hz
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxP
    · exact hyP)
  obtain ⟨ix, hix⟩ := hvertices x (by simp [E])
  obtain ⟨iy, hiy⟩ := hvertices y (by simp [E])
  let R := K.rotate ix
  let l : ZMod K.n := iy - ix
  let k : ℕ := l.val
  have hkcast : (k : ZMod K.n) = l := ZMod.natCast_zmod_val l
  have hRzero : R.vertex 0 = x := by
    change K.vertex ((0 : ZMod K.n) + ix) = x
    simpa only [zero_add] using hix
  have hRk : R.vertex (k : ZMod R.n) = y := by
    change K.vertex ((k : ZMod K.n) + ix) = y
    rw [hkcast]
    change K.vertex ((iy - ix) + ix) = y
    rw [sub_add_cancel, hiy]
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    apply hxy
    rw [← hRzero, ← hRk, hkzero]
    simp only [Nat.cast_zero]
  have hklt : k < R.n := by
    exact l.val_lt
  have hRP : R.carrier = P.carrier := by
    exact (K.rotate_carrier ix).trans hKP
  have hJordanCarrier : R.toJordanCircle.carrier =
      P.toJordanCircle.carrier := by
    simpa only [R.carrier_toJordanCircle, P.carrier_toJordanCircle]
      using hRP
  let S₀ : R.toJordanCircle.TwoBoundaryArcPaths x y :=
    S.congrCarrier hJordanCarrier
  let T : R.toJordanCircle.TwoBoundaryArcPaths
      (R.vertex 0) (R.vertex (k : ZMod R.n)) :=
    S₀.cast hRzero.symm hRk.symm
  have hcomparison := twoBoundaryArcPaths_eq_forward_backward R hkpos hklt T
  refine ⟨R, k, hRP, hRzero, hRk, hkpos, hklt, ?_⟩
  simpa only [T, S₀, JordanCircle.TwoBoundaryArcPaths.range_cast_first,
    JordanCircle.TwoBoundaryArcPaths.range_cast_second,
    JordanCircle.TwoBoundaryArcPaths.congrCarrier_first,
    JordanCircle.TwoBoundaryArcPaths.congrCarrier_second] using hcomparison

end PolygonalCircle

end Schoenflies
