import Schoenflies.CyclicLevelEdges

/-!
# A synchronized collar level as a polygonal circle

The synchronized crosscuts at one sufficiently fine level form a cyclic
family of embedded polygonal arcs.  This file packages all of their resolved
straight edges as the `PolygonalCircle` consumed by polygonal Schoenflies.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace InitialAngularArcs
namespace LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

theorem edgeSegment_inter_of_same_block_succ
    (a : LevelAddress n)
    (i j : Fin (F.synchronizedCrosscutCarrierLine a).data.n)
    (hij : i.val + 1 = j.val) :
    F.edgeSegment ⟨a, i⟩ ∩ F.edgeSegment ⟨a, j⟩ =
      {F.edgeFinish ⟨a, i⟩} := by
  let B := (F.synchronizedCrosscutLine a).data
  have hi : i.val + 1 < B.resolvedWalk.length := by
    have := j.isLt
    simpa [B, synchronizedCrosscutCarrierLine,
      SimpleBrokenLine.carrierBrokenLine] using (hij.symm ▸ this)
  have h := B.resolvedSegment_consecutive_inter i hi
  have hj : (⟨i.val + 1, hi⟩ : Fin B.resolvedWalk.length) = j :=
    Fin.ext hij
  subst j
  simpa [B, edgeSegment, edgeStart, edgeFinish,
    synchronizedCrosscutCarrierLine,
    SimpleBrokenLine.carrierBrokenLine,
    BrokenLineData.resolvedBrokenLine] using h

theorem leftSynchronizedPoint_mem_edgeSegment_iff
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    F.leftSynchronizedPoint a ∈ F.edgeSegment ⟨a, i⟩ ↔
      i.val = 0 := by
  let B := (F.synchronizedCrosscutLine a).data
  have h := B.resolvedVertex_zero_mem_segment_iff i
  have h' : (F.synchronizedCrosscutCarrierLine a).data.vertex 0 ∈
      F.edgeSegment ⟨a, i⟩ ↔ i.val = 0 := by
    convert h using 1
    all_goals simp [B, edgeSegment, edgeStart, edgeFinish,
      synchronizedCrosscutCarrierLine,
      SimpleBrokenLine.carrierBrokenLine,
      BrokenLineData.resolvedBrokenLine]
    all_goals rfl
  constructor
  · intro hx
    apply h'.mp
    convert hx using 1
    exact (F.synchronizedCrosscutCarrierLine a).start_eq
  · intro hi
    convert h'.mpr hi using 1
    exact (F.synchronizedCrosscutCarrierLine a).start_eq.symm

theorem rightSynchronizedPoint_mem_edgeSegment_iff
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    F.rightSynchronizedPoint a ∈ F.edgeSegment ⟨a, i⟩ ↔
      i.val + 1 = (F.synchronizedCrosscutCarrierLine a).data.n := by
  let B := (F.synchronizedCrosscutLine a).data
  have h := B.resolvedVertex_last_mem_segment_iff i
  have h' : (F.synchronizedCrosscutCarrierLine a).data.vertex
        (Fin.last (F.synchronizedCrosscutCarrierLine a).data.n) ∈
      F.edgeSegment ⟨a, i⟩ ↔
        i.val + 1 = (F.synchronizedCrosscutCarrierLine a).data.n := by
    convert h using 1
    all_goals simp [B, edgeSegment, edgeStart, edgeFinish,
      synchronizedCrosscutCarrierLine,
      SimpleBrokenLine.carrierBrokenLine,
      BrokenLineData.resolvedBrokenLine]
  constructor
  · intro hx
    apply h'.mp
    convert hx using 1
    exact (F.synchronizedCrosscutCarrierLine a).finish_eq
  · intro hi
    convert h'.mpr hi using 1
    exact (F.synchronizedCrosscutCarrierLine a).finish_eq.symm

/-- Any two resolved edges which are consecutive in the global collar order
meet exactly at their common endpoint. -/
theorem edgeSegment_inter_of_edgeAdjacent (hn : 1 ≤ n)
    (e f : F.LevelEdgeAddress) (hef : F.EdgeAdjacent e f) :
    F.edgeSegment e ∩ F.edgeSegment f = {F.edgeFinish e} := by
  rcases e with ⟨a, i⟩
  rcases f with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    have hvertices :
        (F.synchronizedCrosscutCarrierLine a).data.vertex i.succ =
          (F.synchronizedCrosscutCarrierLine a).data.vertex j.castSucc :=
      hef
    have hindices :=
      (F.synchronizedCrosscutCarrierLine a).vertex_injective hvertices
    have hij : i.val + 1 = j.val := by
      simpa using congrArg Fin.val hindices
    exact F.edgeSegment_inter_of_same_block_succ a i j hij
  · have hiRange : F.edgeFinish ⟨a, i⟩ ∈
        range (F.synchronizedCrosscutPath a) :=
      edgeSegment_subset_crosscutRange (F := F) ⟨a, i⟩
        (edgeFinish_mem_edgeSegment (F := F) ⟨a, i⟩)
    have hjRange : F.edgeStart ⟨b, j⟩ ∈
        range (F.synchronizedCrosscutPath b) :=
      edgeSegment_subset_crosscutRange (F := F) ⟨b, j⟩
        (edgeStart_mem_edgeSegment (F := F) ⟨b, j⟩)
    have hcommon : F.edgeFinish ⟨a, i⟩ ∈
        range (F.synchronizedCrosscutPath a) ∩
          range (F.synchronizedCrosscutPath b) :=
      ⟨hiRange, hef ▸ hjRange⟩
    have hbNext : b = nextLevelAddress n a := by
      by_contra hb
      by_cases ha : a = nextLevelAddress n b
      · have hreverse : F.edgeFinish ⟨a, i⟩ ∈
            range (F.synchronizedCrosscutPath b) ∩
              range (F.synchronizedCrosscutPath
                (nextLevelAddress n b)) := by
          subst a
          exact ⟨hcommon.2, hcommon.1⟩
        rw [F.range_synchronizedCrosscutPath_inter_next hn b] at hreverse
        exact (edgeStart_ne_rightSynchronizedPoint (F := F) ⟨b, j⟩)
          (hef.symm.trans (mem_singleton_iff.mp hreverse))
      · have hdis := F.disjoint_range_synchronizedCrosscutPath_of_nonadjacent
            a b hab hb ha
        exact Set.disjoint_left.mp hdis hcommon.1 hcommon.2
    subst b
    have hfinish : F.edgeFinish ⟨a, i⟩ =
        F.rightSynchronizedPoint a := by
      rw [F.range_synchronizedCrosscutPath_inter_next hn a] at hcommon
      exact mem_singleton_iff.mp hcommon
    apply Set.Subset.antisymm
    · intro x hx
      have hxRange : x ∈ range (F.synchronizedCrosscutPath a) ∩
          range (F.synchronizedCrosscutPath
            (nextLevelAddress n a)) :=
        ⟨edgeSegment_subset_crosscutRange (F := F) ⟨a, i⟩ hx.1,
          edgeSegment_subset_crosscutRange (F := F)
            ⟨nextLevelAddress n a, j⟩ hx.2⟩
      rw [F.range_synchronizedCrosscutPath_inter_next hn a] at hxRange
      rw [mem_singleton_iff, hfinish]
      exact mem_singleton_iff.mp hxRange
    · intro x hx
      have hxEq : x = F.edgeFinish ⟨a, i⟩ := mem_singleton_iff.mp hx
      subst x
      exact ⟨edgeFinish_mem_edgeSegment (F := F) ⟨a, i⟩, by
        rw [hef]
        exact edgeStart_mem_edgeSegment (F := F)
          ⟨nextLevelAddress n a, j⟩⟩

theorem edgeSegment_inter_next (hn : 1 ≤ n)
    (e : F.LevelEdgeAddress) :
    F.edgeSegment e ∩ F.edgeSegment (nextLevelEdge F e) =
      {F.edgeFinish e} :=
  F.edgeSegment_inter_of_edgeAdjacent hn e (nextLevelEdge F e)
    (edgeAdjacent_nextLevelEdge (F := F) e)

theorem disjoint_edgeSegment_of_same_block_nonadjacent
    (hn : 1 ≤ n) (a : LevelAddress n)
    (i j : Fin (F.synchronizedCrosscutCarrierLine a).data.n)
    (hij : i ≠ j)
    (hijNext : (⟨a, j⟩ : F.LevelEdgeAddress) ≠
      nextLevelEdge F ⟨a, i⟩)
    (hjiNext : (⟨a, i⟩ : F.LevelEdgeAddress) ≠
      nextLevelEdge F ⟨a, j⟩) :
    Disjoint (F.edgeSegment ⟨a, i⟩) (F.edgeSegment ⟨a, j⟩) := by
  have hijSucc : i.val + 1 ≠ j.val := by
    intro hs
    apply hijNext
    apply (edgeAdjacent_iff_eq_next (F := F) hn ⟨a, i⟩ ⟨a, j⟩).mp
    apply congrArg (F.synchronizedCrosscutCarrierLine a).data.vertex
    apply Fin.ext
    exact hs
  have hjiSucc : j.val + 1 ≠ i.val := by
    intro hs
    apply hjiNext
    apply (edgeAdjacent_iff_eq_next (F := F) hn ⟨a, j⟩ ⟨a, i⟩).mp
    apply congrArg (F.synchronizedCrosscutCarrierLine a).data.vertex
    apply Fin.ext
    exact hs
  let B := (F.synchronizedCrosscutLine a).data
  have hdis := B.resolvedSegment_disjoint_of_not_close
    i j hij hijSucc hjiSucc
  simpa [B, edgeSegment, edgeStart, edgeFinish,
    synchronizedCrosscutCarrierLine,
    SimpleBrokenLine.carrierBrokenLine,
    BrokenLineData.resolvedBrokenLine] using hdis

/-- Globally nonadjacent resolved collar edges are disjoint. -/
theorem disjoint_edgeSegment_of_nonadjacent (hn : 1 ≤ n)
    (e f : F.LevelEdgeAddress) (hef : e ≠ f)
    (heNext : e ≠ nextLevelEdge F f)
    (hfNext : f ≠ nextLevelEdge F e) :
    Disjoint (F.edgeSegment e) (F.edgeSegment f) := by
  rcases e with ⟨a, i⟩
  rcases f with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    apply F.disjoint_edgeSegment_of_same_block_nonadjacent hn a i j
    · intro hij
      apply hef
      cases hij
      rfl
    · exact hfNext
    · exact heNext
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hiRange : x ∈ range (F.synchronizedCrosscutPath a) :=
      edgeSegment_subset_crosscutRange (F := F) ⟨a, i⟩ hxi
    have hjRange : x ∈ range (F.synchronizedCrosscutPath b) :=
      edgeSegment_subset_crosscutRange (F := F) ⟨b, j⟩ hxj
    by_cases hbNext : b = nextLevelAddress n a
    · subst b
      have hxInter : x ∈ range (F.synchronizedCrosscutPath a) ∩
          range (F.synchronizedCrosscutPath (nextLevelAddress n a)) :=
        ⟨hiRange, hjRange⟩
      rw [F.range_synchronizedCrosscutPath_inter_next hn a] at hxInter
      have hxRight : x = F.rightSynchronizedPoint a :=
        mem_singleton_iff.mp hxInter
      have hiLastVal : i.val + 1 =
          (F.synchronizedCrosscutCarrierLine a).data.n :=
        (F.rightSynchronizedPoint_mem_edgeSegment_iff a i).mp
          (hxRight ▸ hxi)
      have hjZero : j.val = 0 :=
        (F.leftSynchronizedPoint_mem_edgeSegment_iff
          (nextLevelAddress n a) j).mp (by
            rw [← F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
            exact hxRight ▸ hxj)
      have hiLast : i = F.lastEdgeIndex a := by
        apply Fin.ext
        simp [lastEdgeIndex]
        omega
      have hjFirst : j = F.firstEdgeIndex (nextLevelAddress n a) := by
        apply Fin.ext
        simpa [firstEdgeIndex] using hjZero
      subst i
      subst j
      apply hfNext
      exact (edgeAdjacent_iff_eq_next (F := F) hn _ _).mp
        (F.edgeBlock_bridge (I.levelAdjacent_nextLevelAddress n a))
    · by_cases haNext : a = nextLevelAddress n b
      · subst a
        have hxInter : x ∈ range (F.synchronizedCrosscutPath b) ∩
            range (F.synchronizedCrosscutPath
              (nextLevelAddress n b)) := ⟨hjRange, hiRange⟩
        rw [F.range_synchronizedCrosscutPath_inter_next hn b] at hxInter
        have hxRight : x = F.rightSynchronizedPoint b :=
          mem_singleton_iff.mp hxInter
        have hjLastVal : j.val + 1 =
            (F.synchronizedCrosscutCarrierLine b).data.n :=
          (F.rightSynchronizedPoint_mem_edgeSegment_iff b j).mp
            (hxRight ▸ hxj)
        have hiZero : i.val = 0 :=
          (F.leftSynchronizedPoint_mem_edgeSegment_iff
            (nextLevelAddress n b) i).mp (by
              rw [← F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint b]
              exact hxRight ▸ hxi)
        have hjLast : j = F.lastEdgeIndex b := by
          apply Fin.ext
          simp [lastEdgeIndex]
          omega
        have hiFirst : i = F.firstEdgeIndex (nextLevelAddress n b) := by
          apply Fin.ext
          simpa [firstEdgeIndex] using hiZero
        subst j
        subst i
        apply heNext
        exact (edgeAdjacent_iff_eq_next (F := F) hn _ _).mp
          (F.edgeBlock_bridge (I.levelAdjacent_nextLevelAddress n b))
      · exact Set.disjoint_left.mp
          (F.disjoint_range_synchronizedCrosscutPath_of_nonadjacent
            a b hab hbNext haNext) hiRange hjRange

theorem edgeSegment_inter_eq_empty_of_nonadjacent (hn : 1 ≤ n)
    (e f : F.LevelEdgeAddress) (hef : e ≠ f)
    (heNext : e ≠ nextLevelEdge F f)
    (hfNext : f ≠ nextLevelEdge F e) :
    F.edgeSegment e ∩ F.edgeSegment f = ∅ :=
  Set.disjoint_iff_inter_eq_empty.mp
    (F.disjoint_edgeSegment_of_nonadjacent hn e f hef heNext hfNext)

theorem zmod_add_one_val {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (i : ZMod m) :
    (i + 1).val = if i.val + 1 < m then i.val + 1 else 0 := by
  have hone : (1 : ZMod m).val = 1 := by
    letI : Fact (1 < m) := ⟨by omega⟩
    exact ZMod.val_one m
  rw [ZMod.val_add, hone]
  split_ifs with hi
  · exact Nat.mod_eq_of_lt hi
  · have heq : i.val + 1 = m := by
      have := i.val_lt
      omega
    rw [heq, Nat.mod_self]

theorem zmod_add_one_fin_eq_cyclicSuccIndex
    (l : List α) [NeZero l.length]
    (hne : l ≠ []) (hm : 3 ≤ l.length) (i : ZMod l.length) :
    (⟨(i + 1).val, (i + 1).val_lt⟩ : Fin l.length) =
      cyclicSuccIndex l hne ⟨i.val, i.val_lt⟩ := by
  apply Fin.ext
  change (i + 1).val =
    (cyclicSuccIndex l hne ⟨i.val, i.val_lt⟩).val
  rw [zmod_add_one_val hm]
  unfold cyclicSuccIndex
  split_ifs with hi
  · rfl
  · rfl

/-- The edge address read at a modular list index. -/
noncomputable def cyclicEdgeAddress [NeZero F.orderedLevelEdges.length]
    (i : ZMod F.orderedLevelEdges.length) : F.LevelEdgeAddress :=
  F.orderedLevelEdgeEquiv ⟨i.val, i.val_lt⟩

theorem cyclicEdgeAddress_injective
    [NeZero F.orderedLevelEdges.length] :
    Function.Injective F.cyclicEdgeAddress := by
  intro i j hij
  apply ZMod.val_injective
  have hfin := F.orderedLevelEdgeEquiv.injective hij
  exact congrArg Fin.val hfin

theorem cyclicEdgeAddress_add_one
    [NeZero F.orderedLevelEdges.length]
    (hthree : 3 ≤ F.orderedLevelEdges.length)
    (i : ZMod F.orderedLevelEdges.length) :
    F.cyclicEdgeAddress (i + 1) =
      nextLevelEdge F (F.cyclicEdgeAddress i) := by
  let q := F.orderedLevelEdgeEquiv
  change q ⟨(i + 1).val, (i + 1).val_lt⟩ =
    q (cyclicSuccIndex F.orderedLevelEdges
      F.orderedLevelEdges_nonempty
      (q.symm (q ⟨i.val, i.val_lt⟩)))
  rw [q.symm_apply_apply]
  exact congrArg q (zmod_add_one_fin_eq_cyclicSuccIndex
    F.orderedLevelEdges F.orderedLevelEdges_nonempty hthree i)

theorem cyclicEdge_segment
    [NeZero F.orderedLevelEdges.length]
    (hthree : 3 ≤ F.orderedLevelEdges.length)
    (i : ZMod F.orderedLevelEdges.length) :
    segment ℝ (F.edgeStart (F.cyclicEdgeAddress i))
        (F.edgeStart (F.cyclicEdgeAddress (i + 1))) =
      F.edgeSegment (F.cyclicEdgeAddress i) := by
  rw [F.cyclicEdgeAddress_add_one hthree]
  rw [← edgeFinish_eq_edgeStart_next (F := F)]
  rfl

/-- A complete synchronized inner collar level, viewed as one polygonal
simple closed curve. -/
noncomputable def synchronizedPolygonalCircle (hn : 1 ≤ n) :
    PolygonalCircle := by
  let m := F.orderedLevelEdges.length
  have hthree : 3 ≤ m := F.orderedLevelEdges_three_le hn
  letI : NeZero m := ⟨by omega⟩
  exact
    { n := m
      three_le := hthree
      vertex := fun i => F.edgeStart (F.cyclicEdgeAddress i)
      adjacent_ne := by
        intro i hEq
        have haddr := F.edgeStart_injective hn hEq
        rw [F.cyclicEdgeAddress_add_one hthree] at haddr
        exact (F.nextLevelEdge_ne hn _) haddr.symm
      consecutive_inter := by
        intro i
        rw [F.cyclicEdge_segment hthree]
        rw [show i + 2 = (i + 1) + 1 by ring,
          F.cyclicEdge_segment hthree]
        have h := F.edgeSegment_inter_next hn
          (F.cyclicEdgeAddress i)
        rw [F.cyclicEdgeAddress_add_one hthree]
        simpa [F.edgeFinish_eq_edgeStart_next,
          F.cyclicEdgeAddress_add_one hthree] using h
      nonadjacent_disjoint := by
        intro i j hij hiPrev hjNext
        rw [F.cyclicEdge_segment hthree,
          F.cyclicEdge_segment hthree]
        apply F.edgeSegment_inter_eq_empty_of_nonadjacent hn
        · intro haddr
          exact hij (F.cyclicEdgeAddress_injective haddr)
        · intro haddr
          apply hiPrev
          apply F.cyclicEdgeAddress_injective
          rw [F.cyclicEdgeAddress_add_one hthree]
          exact haddr
        · intro haddr
          apply hjNext
          apply F.cyclicEdgeAddress_injective
          rw [F.cyclicEdgeAddress_add_one hthree]
          exact haddr }

theorem cyclicEdgeAddress_surjective
    [NeZero F.orderedLevelEdges.length] :
    Function.Surjective F.cyclicEdgeAddress := by
  intro e
  let q := F.orderedLevelEdgeEquiv
  let i : Fin F.orderedLevelEdges.length := q.symm e
  let z : ZMod F.orderedLevelEdges.length := i.val
  refine ⟨z, ?_⟩
  change q ⟨z.val, z.val_lt⟩ = e
  rw [← q.apply_symm_apply e]
  apply congrArg q
  apply Fin.ext
  change z.val = i.val
  rw [show z.val = i.val % F.orderedLevelEdges.length by
    simp [z, ZMod.val_natCast]]
  exact Nat.mod_eq_of_lt i.isLt

theorem iUnion_edgeSegment_eq_iUnion_crosscutRange :
    (⋃ e : F.LevelEdgeAddress, F.edgeSegment e) =
      ⋃ a : LevelAddress n, range (F.synchronizedCrosscutPath a) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr
      ⟨e.1, F.edgeSegment_subset_crosscutRange e hxe⟩
  · intro x hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
    have hxCarrier : x ∈
        (F.synchronizedCrosscutCarrierLine a).data.segmentCarrier := by
      rw [F.segmentCarrier_synchronizedCrosscutCarrierLine_eq_range a]
      exact hxa
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxCarrier
    exact Set.mem_iUnion.mpr ⟨⟨a, i⟩, hxi⟩

/-- The polygonal collar has exactly the union of the synchronized inner
crosscuts as its point-set carrier. -/
theorem carrier_synchronizedPolygonalCircle (hn : 1 ≤ n) :
    (F.synchronizedPolygonalCircle hn).carrier =
      ⋃ a : LevelAddress n, range (F.synchronizedCrosscutPath a) := by
  rw [← F.iUnion_edgeSegment_eq_iUnion_crosscutRange]
  have hthree : 3 ≤ F.orderedLevelEdges.length :=
    F.orderedLevelEdges_three_le hn
  letI : NeZero F.orderedLevelEdges.length := ⟨by omega⟩
  change (⋃ i : ZMod F.orderedLevelEdges.length,
      segment ℝ (F.edgeStart (F.cyclicEdgeAddress i))
        (F.edgeStart (F.cyclicEdgeAddress (i + 1)))) =
    ⋃ e : F.LevelEdgeAddress, F.edgeSegment e
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨F.cyclicEdgeAddress i, by
      rw [← F.cyclicEdge_segment hthree]
      exact hxi⟩
  · intro x hx
    obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := F.cyclicEdgeAddress_surjective e
    subst e
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [F.cyclicEdge_segment hthree]
    exact hxe

theorem carrier_synchronizedPolygonalCircle_subset_inside (hn : 1 ≤ n) :
    (F.synchronizedPolygonalCircle hn).carrier ⊆ J.inside := by
  rw [F.carrier_synchronizedPolygonalCircle hn]
  intro x hx
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
  exact F.synchronizedCrosscutSet_subset_inside a
    (F.range_synchronizedCrosscutPath_subset a hxa)

/-- The entire polygonal disk bounded by the synchronized collar lies in
the original Jordan inside, not merely its boundary. -/
theorem closedRegion_synchronizedPolygonalCircle_subset_inside
    (hn : 1 ≤ n) :
    (F.synchronizedPolygonalCircle hn).closedRegion ⊆ J.inside := by
  let P := F.synchronizedPolygonalCircle hn
  have hcarrier : P.toJordanCircle.carrier ⊆ J.inside ∪ J.carrier := by
    rw [P.carrier_toJordanCircle]
    exact (F.carrier_synchronizedPolygonalCircle_subset_inside hn).trans
      Set.subset_union_left
  have hinterior : P.interiorRegion ⊆ J.inside := by
    rw [← P.inside_toJordanCircle]
    exact J.inside_subset_inside_of_carrier_subset P.toJordanCircle hcarrier
  rw [P.closedRegion_eq_union]
  exact Set.union_subset hinterior
    (F.carrier_synchronizedPolygonalCircle_subset_inside hn)

end LevelAvoidingJoinFamily
end InitialAngularArcs
end JordanCircle

end Schoenflies
