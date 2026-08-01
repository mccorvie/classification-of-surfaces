import Schoenflies.FiniteCrossingParity

/-!
# Pairing crossings of a cyclic Boolean edge labelling

Cutting a cyclic edge labelling immediately after a `false` edge turns its
crossing vertices into a linearly ordered alternating sequence.  Consecutive
pairs in that sequence are precisely the endpoints of the `true` edge runs.
This is the finite combinatorial core of Moise's separator extraction.
-/

namespace Schoenflies

open Set

/-- The side immediately before a vertex in a linearly cut cyclic edge list.
At vertex `0` the omitted final edge is stipulated to have label `false`. -/
def incomingLinearSide {n : ℕ} (side : Fin (n + 1) → Bool)
    (i : Fin (n + 1)) : Bool :=
  if hi : i.val = 0 then false else side ⟨i.val - 1, by omega⟩

/-- A vertex at which the incoming and outgoing labels differ. -/
def IsLinearCrossing {n : ℕ} (side : Fin (n + 1) → Bool)
    (i : Fin (n + 1)) : Prop :=
  incomingLinearSide side i ≠ side i

/-- The finite set of label-changing vertices in the linear cut. -/
noncomputable def linearCrossings {n : ℕ} (side : Fin (n + 1) → Bool) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (IsLinearCrossing side)

@[simp] theorem incomingLinearSide_zero {n : ℕ}
    (side : Fin (n + 1) → Bool) :
    incomingLinearSide side 0 = false := by
  simp [incomingLinearSide]

theorem incomingLinearSide_of_pos {n : ℕ}
    (side : Fin (n + 1) → Bool) (i : Fin (n + 1))
    (hi : 0 < i.val) :
    incomingLinearSide side i = side ⟨i.val - 1, by omega⟩ := by
  simp [incomingLinearSide, hi.ne']

/-- If an interval contains no crossing after its left endpoint, its edge
label is constant. -/
theorem side_eq_of_no_linearCrossing_between {n : ℕ}
    (side : Fin (n + 1) → Bool) {a b : Fin (n + 1)} (hab : a ≤ b)
    (hnone : ∀ q ∈ linearCrossings side, a < q → q ≤ b → False) :
    side a = side b := by
  have habVal : a.val ≤ b.val := hab
  have hstep : ∀ (k : ℕ) (hk : a.val + k ≤ b.val),
      side a = side ⟨a.val + k, lt_of_le_of_lt hk b.isLt⟩ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkPrev : a.val + k ≤ b.val := by omega
        have ih' := ih hkPrev
        let q : Fin (n + 1) := ⟨a.val + k + 1, by omega⟩
        have hqNot : q ∉ linearCrossings side := by
          intro hq
          exact hnone q hq (by change a.val < a.val + k + 1; omega)
            (by change a.val + k + 1 ≤ b.val; omega)
        have hqNoChange : incomingLinearSide side q = side q := by
          apply not_ne_iff.mp
          simpa only [linearCrossings, Finset.mem_filter,
            Finset.mem_univ, true_and, IsLinearCrossing] using hqNot
        have hqPos : 0 < q.val := by
          change 0 < a.val + k + 1
          omega
        have hnext :
            side ⟨a.val + k, lt_of_le_of_lt hkPrev b.isLt⟩ = side q := by
          rw [incomingLinearSide_of_pos side q hqPos] at hqNoChange
          simpa only [q, Nat.add_sub_cancel] using hqNoChange
        exact ih'.trans hnext
  have h := hstep (b.val - a.val) (by omega)
  have heq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin (n + 1)) = b := by
    apply Fin.ext
    simp only
    omega
  rwa [heq] at h

/-- The ordered crossing sequence begins at zero, alternates its outgoing
edge labels, and ends with a `false` label. -/
theorem exists_ordered_linearCrossings {n : ℕ}
    (side : Fin (n + 1) → Bool)
    (hfirst : side 0 = true) (hlast : side (Fin.last n) = false) :
    ∃ (m : ℕ) (hcard : (linearCrossings side).card = m + 1),
      let crossing := (linearCrossings side).orderEmbOfFin hcard
      crossing 0 = 0 ∧
        (∀ j : Fin m,
          side (crossing j.castSucc) ≠ side (crossing j.succ)) ∧
        side (crossing (Fin.last m)) = false := by
  classical
  let C := linearCrossings side
  have hzeroC : (0 : Fin (n + 1)) ∈ C := by
    simp only [C, linearCrossings, Finset.mem_filter, Finset.mem_univ,
      true_and, IsLinearCrossing, incomingLinearSide_zero, hfirst,
      ne_eq]
    decide
  have hcardPos : 0 < C.card := Finset.card_pos.mpr ⟨0, hzeroC⟩
  obtain ⟨m, hcard⟩ : ∃ m, C.card = m + 1 := by
    exact ⟨C.card - 1, by omega⟩
  let crossing : Fin (m + 1) ↪o Fin (n + 1) := C.orderEmbOfFin hcard
  have hcrossingMem (j : Fin (m + 1)) : crossing j ∈ C :=
    C.orderEmbOfFin_mem hcard j
  have hcrossingZero : crossing 0 = 0 := by
    have hzeroRange : (0 : Fin (n + 1)) ∈ Set.range crossing := by
      rw [C.range_orderEmbOfFin hcard]
      exact hzeroC
    obtain ⟨j, hj⟩ := hzeroRange
    apply le_antisymm
    · have hle := crossing.monotone (Fin.zero_le j)
      simpa only [hj] using hle
    · exact Fin.zero_le _
  let crossingSide : Fin (m + 1) → Bool := fun j => side (crossing j)
  have hchange : ∀ j : Fin m,
      crossingSide j.castSucc ≠ crossingSide j.succ := by
    intro j
    let p : Fin (n + 1) := crossing j.castSucc
    let q : Fin (n + 1) := crossing j.succ
    have hpq : p < q := crossing.strictMono Fin.castSucc_lt_succ
    have hqPos : 0 < q.val := by
      change p.val < q.val at hpq
      omega
    let qprev : Fin (n + 1) := ⟨q.val - 1, by omega⟩
    have hpPrev : p ≤ qprev := by
      change p.val ≤ q.val - 1
      omega
    have hprevQ : qprev < q := by
      change q.val - 1 < q.val
      omega
    have hconstant : side p = side qprev := by
      apply side_eq_of_no_linearCrossing_between side hpPrev
      intro r hrC hpr hrPrev
      have hrRange : r ∈ Set.range crossing := by
        rw [C.range_orderEmbOfFin hcard]
        exact hrC
      obtain ⟨u, rfl⟩ := hrRange
      have hju : j.castSucc < u := by
        apply crossing.lt_iff_lt.mp
        simpa only [p] using hpr
      have huj : u < j.succ := by
        apply crossing.lt_iff_lt.mp
        have := hrPrev.trans_lt hprevQ
        simpa only [q] using this
      change j.val < u.val at hju
      change u.val < j.val + 1 at huj
      omega
    have hqCrossing : IsLinearCrossing side q := by
      have := hcrossingMem j.succ
      simpa only [C, linearCrossings, Finset.mem_filter,
        Finset.mem_univ, true_and] using this
    rw [IsLinearCrossing,
      incomingLinearSide_of_pos side q hqPos] at hqCrossing
    change side p ≠ side q
    exact fun hpqSide => hqCrossing (hconstant.symm.trans hpqSide)
  have hlastCrossingSide : crossingSide (Fin.last m) = false := by
    let p : Fin (n + 1) := crossing (Fin.last m)
    have hpLast : p ≤ Fin.last n := Fin.le_last p
    have hconstant : side p = side (Fin.last n) := by
      apply side_eq_of_no_linearCrossing_between side hpLast
      intro r hrC hpr _hrLast
      have hrRange : r ∈ Set.range crossing := by
        rw [C.range_orderEmbOfFin hcard]
        exact hrC
      obtain ⟨u, rfl⟩ := hrRange
      have huLast : u ≤ Fin.last m := Fin.le_last u
      exact (not_lt_of_ge (crossing.monotone huLast)) hpr
    exact hconstant.trans hlast
  exact ⟨m, hcard, hcrossingZero, hchange, hlastCrossingSide⟩

/-- If the cut begins with a `true` edge and ends with a `false` edge, the
number of crossings (including the stipulated `false`-to-`true` crossing at
zero) is even. -/
theorem even_card_linearCrossings {n : ℕ}
    (side : Fin (n + 1) → Bool)
    (hfirst : side 0 = true) (hlast : side (Fin.last n) = false) :
    Even (linearCrossings side).card := by
  classical
  obtain ⟨m, hcard, hzero, hchange, hlastCrossing⟩ :=
    exists_ordered_linearCrossings side hfirst hlast
  let crossing := (linearCrossings side).orderEmbOfFin hcard
  let crossingSide : Fin (m + 1) → Bool := fun j => side (crossing j)
  have hfirstCrossing : crossingSide 0 = true := by
    simp only [crossingSide, crossing, hzero, hfirst]
  have hend : crossingSide 0 ≠ crossingSide (Fin.last m) := by
    rw [hfirstCrossing]
    change true ≠ side (crossing (Fin.last m))
    rw [hlastCrossing]
    decide
  obtain ⟨k, hk⟩ := odd_of_alternating_end_ne crossingSide hchange hend
  refine ⟨k + 1, ?_⟩
  rw [hcard]
  omega

/-- If an odd number of marked crossings occur, one `true` run has one
marked and one unmarked endpoint.  The whole half-open edge interval from
the first endpoint to the second retains label `true`. -/
theorem exists_true_run_with_mixed_crossing_marks {n : ℕ}
    (side mark : Fin (n + 1) → Bool)
    (hfirst : side 0 = true) (hlast : side (Fin.last n) = false)
    (hodd : Odd (((linearCrossings side).filter
      fun i => mark i = true).card)) :
    ∃ a b : Fin (n + 1),
      a < b ∧ IsLinearCrossing side a ∧ IsLinearCrossing side b ∧
        mark a ≠ mark b ∧ side a = true ∧ side b = false ∧
        ∀ k : Fin (n + 1), a ≤ k → k < b → side k = true := by
  classical
  let C := linearCrossings side
  obtain ⟨m, hcard, hzero, hchange, hlastCrossing⟩ :=
    exists_ordered_linearCrossings side hfirst hlast
  let crossing : Fin (m + 1) ↪o Fin (n + 1) := C.orderEmbOfFin hcard
  let crossingSide : Fin (m + 1) → Bool := fun j => side (crossing j)
  let crossingMark : Fin (m + 1) → Bool := fun j => mark (crossing j)
  have hfirstCrossing : crossingSide 0 = true := by
    change side (((linearCrossings side).orderEmbOfFin hcard) 0) = true
    rw [hzero, hfirst]
  let orderedMarkedEquiv :
      {j : Fin (m + 1) // crossingMark j = true} ≃
        {i : C // mark i.1 = true} :=
    (C.orderIsoOfFin hcard).toEquiv.subtypeEquiv (by
      intro j
      change crossingMark j = true ↔
        mark ((C.orderIsoOfFin hcard j).1) = true
      simp only [crossingMark, crossing,
        C.coe_orderIsoOfFin_apply hcard j])
  let filteredMarkedEquiv :
      {i : C // mark i.1 = true} ≃
        {i : Fin (n + 1) // i ∈ C.filter fun q => mark q = true} :=
    { toFun := fun i => ⟨i.1.1, Finset.mem_filter.mpr ⟨i.1.2, i.2⟩⟩
      invFun := fun i => ⟨⟨i.1, (Finset.mem_filter.mp i.2).1⟩,
        (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  have hoddOrdered :
      Odd (Fintype.card {j : Fin (m + 1) // crossingMark j = true}) := by
    rw [Fintype.card_congr (orderedMarkedEquiv.trans filteredMarkedEquiv),
      Fintype.card_coe]
    simpa only [C] using hodd
  obtain ⟨pairs, hpairs⟩ := even_card_linearCrossings side hfirst hlast
  have hsize : m + 1 = pairs * 2 := by
    rw [← hcard]
    omega
  let castPairs : Fin (pairs * 2) ≃ Fin (m + 1) :=
    finCongr hsize.symm
  let pairedMark : Fin (pairs * 2) → Bool := fun j => crossingMark (castPairs j)
  let castMarkedEquiv :
      {j : Fin (pairs * 2) // pairedMark j = true} ≃
        {j : Fin (m + 1) // crossingMark j = true} :=
    castPairs.subtypeEquiv (by intro j; rfl)
  have hoddPaired :
      Odd (Fintype.card {j : Fin (pairs * 2) // pairedMark j = true}) := by
    rw [Fintype.card_congr castMarkedEquiv]
    exact hoddOrdered
  obtain ⟨j, hj⟩ := exists_mixed_pair_of_odd_true_count pairedMark hoddPaired
  let ja : Fin (m + 1) :=
    castPairs (finProdFinEquiv (j, (0 : Fin 2)))
  let jb : Fin (m + 1) :=
    castPairs (finProdFinEquiv (j, (1 : Fin 2)))
  have hjVal : ja.val = 2 * j.val := by
    simp only [ja, castPairs, finCongr, Equiv.coe_fn_mk]
    simp [finProdFinEquiv]
  have hjbVal : jb.val = ja.val + 1 := by
    simp only [jb, ja, castPairs, finCongr, Equiv.coe_fn_mk]
    simp [finProdFinEquiv]
    omega
  have hjab : ja < jb := by
    change ja.val < jb.val
    omega
  let a : Fin (n + 1) := crossing ja
  let b : Fin (n + 1) := crossing jb
  have hab : a < b := crossing.strictMono hjab
  have haCrossing : IsLinearCrossing side a := by
    have haMem : a ∈ C := C.orderEmbOfFin_mem hcard ja
    simpa only [C, linearCrossings, Finset.mem_filter,
      Finset.mem_univ, true_and] using haMem
  have hbCrossing : IsLinearCrossing side b := by
    have hbMem : b ∈ C := C.orderEmbOfFin_mem hcard jb
    simpa only [C, linearCrossings, Finset.mem_filter,
      Finset.mem_univ, true_and] using hbMem
  have haTrue : side a = true := by
    have halt := alternating_value crossingSide hchange ja
    rw [hfirstCrossing, hjVal, toggleN_two_mul] at halt
    exact halt
  have hbFalse : side b = false := by
    have hne : side a ≠ side b := by
      let q : Fin m := ⟨ja.val, by
        have hlt : ja.val + 1 < m + 1 := by
          rw [← hjbVal]
          exact jb.isLt
        omega⟩
      have hqCast : q.castSucc = ja := by
        apply Fin.ext
        rfl
      have hqSucc : q.succ = jb := by
        apply Fin.ext
        simpa only [Fin.val_succ, q] using hjbVal.symm
      simpa only [crossingSide, a, b, hqCast, hqSucc] using hchange q
    cases hba : side b <;> simp_all
  have hmark : mark a ≠ mark b := by
    simpa only [pairedMark, ja, jb, crossingMark, a, b] using hj
  refine ⟨a, b, hab, haCrossing, hbCrossing, hmark, haTrue, hbFalse, ?_⟩
  intro k hak hkb
  have hconstant : side a = side k := by
    apply side_eq_of_no_linearCrossing_between side hak
    intro r hrC har hrk
    have hrRange : r ∈ Set.range crossing := by
      rw [C.range_orderEmbOfFin hcard]
      exact hrC
    obtain ⟨u, rfl⟩ := hrRange
    have hjau : ja < u := by
      apply crossing.lt_iff_lt.mp
      simpa only [a] using har
    have hujb : u < jb := by
      apply crossing.lt_iff_lt.mp
      exact (hrk.trans_lt hkb)
    change ja.val < u.val at hjau
    change u.val < jb.val at hujb
    omega
  exact hconstant.symm.trans haTrue

end Schoenflies
