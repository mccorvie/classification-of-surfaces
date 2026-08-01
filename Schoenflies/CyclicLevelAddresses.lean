import Schoenflies.LevelGenerationMarks
import Mathlib.Data.List.Chain
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn

/-!
# Cyclic ordering of binary level addresses

The finite crosscut construction may enumerate level arcs arbitrarily, but
assembling the collar requires their boundary order.  Here the two children
of every address are listed left-to-right, recursively, starting with the
two initial arcs.
-/

namespace Schoenflies

open Set Function

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

theorem descendant_append (A : J.AccessibleAngularArc)
    (xs ys : List Bool) :
    A.descendant (xs ++ ys) = (A.descendant xs).descendant ys := by
  induction xs generalizing A with
  | nil => rfl
  | cons b xs ih =>
      cases b <;> simp only [List.cons_append, descendant] <;>
        exact ih _

end AccessibleAngularArc

namespace InitialAngularArcs

variable {J : JordanCircle}

/-- Append one final left/right choice to a depth-`n` address. -/
def extendLevelAddress {n : ℕ} (a : LevelAddress n) (b : Bool) :
    LevelAddress (n + 1) :=
  ⟨a.1, Fin.append a.2 (fun _ : Fin 1 => b)⟩

theorem ofFn_extendLevelAddress {n : ℕ} (a : LevelAddress n) (b : Bool) :
    List.ofFn (extendLevelAddress a b).2 = List.ofFn a.2 ++ [b] := by
  change List.ofFn (Fin.append a.2 (fun _ : Fin 1 => b)) =
    List.ofFn a.2 ++ [b]
  rw [List.ofFn_fin_append]
  simp

@[simp] theorem levelArc_extendLevelAddress_false
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    I.levelArc (extendLevelAddress a false) = (I.levelArc a).leftChild := by
  rw [levelArc, ofFn_extendLevelAddress,
    AccessibleAngularArc.descendant_append]
  rfl

@[simp] theorem levelArc_extendLevelAddress_true
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    I.levelArc (extendLevelAddress a true) = (I.levelArc a).rightChild := by
  rw [levelArc, ofFn_extendLevelAddress,
    AccessibleAngularArc.descendant_append]
  rfl

/-- Consecutive level addresses have matching boundary endpoints. -/
def LevelAdjacent (I : J.InitialAngularArcs) {n : ℕ}
    (a b : LevelAddress n) : Prop :=
  (J.curvePoint (I.levelArc a).right : Plane) =
    (J.curvePoint (I.levelArc b).left : Plane)

theorem levelAdjacent_children (I : J.InitialAngularArcs)
    {n : ℕ} (a : LevelAddress n) :
    I.LevelAdjacent (extendLevelAddress a false)
      (extendLevelAddress a true) := by
  simp [LevelAdjacent]

theorem levelAdjacent_extended_of_levelAdjacent
    (I : J.InitialAngularArcs) {n : ℕ} {a b : LevelAddress n}
    (hab : I.LevelAdjacent a b) :
    I.LevelAdjacent (extendLevelAddress a true)
      (extendLevelAddress b false) := by
  simpa [LevelAdjacent] using hab

theorem extendLevelAddress_eq_iff {n : ℕ}
    {a c : LevelAddress n} {b d : Bool} :
    extendLevelAddress a b = extendLevelAddress c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hroot : a.1 = c.1 :=
      congrArg (fun z : LevelAddress (n + 1) => z.1) h
    have hbits : (extendLevelAddress a b).2 =
        (extendLevelAddress c d).2 :=
      congrArg (fun z : LevelAddress (n + 1) => z.2) h
    have hpref : a.2 = c.2 := by
      funext i
      have hi := congrFun hbits (Fin.castAdd 1 i)
      simpa [extendLevelAddress] using hi
    have hlast := congrFun hbits (Fin.natAdd n (0 : Fin 1))
    have hbd : b = d := by
      simpa [extendLevelAddress] using hlast
    exact ⟨Prod.ext hroot hpref, hbd⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem extendLevelAddress_parent_eq_of_eq {n : ℕ}
    {a c : LevelAddress n} {b d : Bool}
    (h : extendLevelAddress a b = extendLevelAddress c d) : a = c :=
  (extendLevelAddress_eq_iff.mp h).1

/-- Replace every address by its left and right children. -/
def refineLevelAddresses {n : ℕ} (l : List (LevelAddress n)) :
    List (LevelAddress (n + 1)) :=
  l.flatMap fun a =>
    [extendLevelAddress a false, extendLevelAddress a true]

theorem isChain_refineLevelAddresses
    (I : J.InitialAngularArcs) {n : ℕ} (l : List (LevelAddress n))
    (hchain : l.IsChain I.LevelAdjacent) :
    (refineLevelAddresses l).IsChain I.LevelAdjacent := by
  induction hchain with
  | nil => exact List.isChain_nil
  | singleton a =>
      simpa [refineLevelAddresses] using I.levelAdjacent_children a
  | @cons_cons a b l hab htail ih =>
      have hchildren :
          ([extendLevelAddress a false, extendLevelAddress a true] :
            List (LevelAddress (n + 1))).IsChain I.LevelAdjacent := by
        simpa using I.levelAdjacent_children a
      rw [refineLevelAddresses, List.flatMap_cons]
      change ([extendLevelAddress a false, extendLevelAddress a true] ++
        refineLevelAddresses (b :: l)).IsChain I.LevelAdjacent
      apply hchildren.append ih
      simpa [refineLevelAddresses] using
        I.levelAdjacent_extended_of_levelAdjacent hab

theorem nodup_refineLevelAddresses {n : ℕ}
    (l : List (LevelAddress n)) (hnodup : l.Nodup) :
    (refineLevelAddresses l).Nodup := by
  rw [refineLevelAddresses, List.nodup_flatMap]
  constructor
  · intro a _ha
    simp [extendLevelAddress_eq_iff]
  · apply hnodup.imp
    intro a c hac
    change List.Disjoint
      [extendLevelAddress a false, extendLevelAddress a true]
      [extendLevelAddress c false, extendLevelAddress c true]
    rw [List.disjoint_iff_ne]
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      intro h <;>
      exact hac (extendLevelAddress_parent_eq_of_eq h)

/-- All addresses at a depth, in their positive boundary order. -/
noncomputable def orderedLevelAddresses :
    (n : ℕ) → List (LevelAddress n)
  | 0 => [(false, fun i => Fin.elim0 i),
      (true, fun i => Fin.elim0 i)]
  | n + 1 => refineLevelAddresses (orderedLevelAddresses n)

theorem orderedLevelAddresses_isChain (I : J.InitialAngularArcs) :
    ∀ n : ℕ, (orderedLevelAddresses n).IsChain I.LevelAdjacent := by
  intro n
  induction n with
  | zero =>
      simpa [orderedLevelAddresses, LevelAdjacent, levelArc, rootArc,
        AccessibleAngularArc.descendant] using
        congrArg (fun t => (J.curvePoint t : Plane)) I.adjacent
  | succ n ih =>
      exact I.isChain_refineLevelAddresses (orderedLevelAddresses n) ih

theorem orderedLevelAddresses_nodup :
    ∀ n : ℕ, (orderedLevelAddresses n).Nodup := by
  intro n
  induction n with
  | zero => simp [orderedLevelAddresses]
  | succ n ih =>
      exact nodup_refineLevelAddresses (orderedLevelAddresses n) ih

theorem length_refineLevelAddresses {n : ℕ}
    (l : List (LevelAddress n)) :
    (refineLevelAddresses l).length = 2 * l.length := by
  simp [refineLevelAddresses, Nat.mul_comm]

theorem orderedLevelAddresses_length :
    ∀ n : ℕ, (orderedLevelAddresses n).length = 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp [orderedLevelAddresses]
  | succ n ih =>
      rw [orderedLevelAddresses, length_refineLevelAddresses, ih]
      ring

theorem levelAddress_card (n : ℕ) :
    Fintype.card (LevelAddress n) = 2 ^ (n + 1) := by
  simp [Fintype.card_prod]
  rw [pow_succ]
  ring

/-- The ordered list contains every level address exactly once. -/
theorem mem_orderedLevelAddresses (n : ℕ) (a : LevelAddress n) :
    a ∈ orderedLevelAddresses n := by
  classical
  have hcard : (orderedLevelAddresses n).toFinset.card =
      Fintype.card (LevelAddress n) := by
    rw [List.toFinset_card_of_nodup (orderedLevelAddresses_nodup n),
      orderedLevelAddresses_length, levelAddress_card]
  have huniv : (orderedLevelAddresses n).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have : a ∈ (orderedLevelAddresses n).toFinset := by
    rw [huniv]
    exact Finset.mem_univ a
  simpa using this

theorem orderedLevelAddresses_nonempty (n : ℕ) :
    orderedLevelAddresses n ≠ [] := by
  induction n with
  | zero => simp [orderedLevelAddresses]
  | succ n ih =>
      cases h : orderedLevelAddresses n with
      | nil => exact (ih h).elim
      | cons a l => simp [orderedLevelAddresses, refineLevelAddresses, h]

@[simp] theorem head_refineLevelAddresses {n : ℕ}
    (a : LevelAddress n) (l : List (LevelAddress n)) :
    (refineLevelAddresses (a :: l)).head (by
      simp [refineLevelAddresses]) = extendLevelAddress a false := by
  simp [refineLevelAddresses]

@[simp] theorem getLast_refineLevelAddresses {n : ℕ}
    (a : LevelAddress n) (l : List (LevelAddress n)) :
    (refineLevelAddresses (a :: l)).getLast (by
      simp [refineLevelAddresses]) =
      extendLevelAddress ((a :: l).getLast (by simp)) true := by
  induction l generalizing a with
  | nil => simp [refineLevelAddresses]
  | cons b l ih =>
      simp only [refineLevelAddresses, List.flatMap_cons]
      rw [List.getLast_append_of_ne_nil]
      · simpa [refineLevelAddresses] using ih b
      · simp

/-- The last level arc closes back onto the first one. -/
theorem orderedLevelAddresses_closes (I : J.InitialAngularArcs) :
    ∀ n : ℕ,
      I.LevelAdjacent
        ((orderedLevelAddresses n).getLast
          (orderedLevelAddresses_nonempty n))
        ((orderedLevelAddresses n).head
          (orderedLevelAddresses_nonempty n)) := by
  intro n
  induction n with
  | zero =>
      change (J.curvePoint I.second.right : Plane) =
        (J.curvePoint I.first.left : Plane)
      apply congrArg Subtype.val
      change J.carrierHomeomorph
          (JordanCurve.Arcs.param I.second.right) =
        J.carrierHomeomorph (JordanCurve.Arcs.param I.first.left)
      rw [I.closes, JordanCurve.Arcs.param_periodic]
  | succ n ih =>
      cases h : orderedLevelAddresses n with
      | nil => exact ((orderedLevelAddresses_nonempty n) h).elim
      | cons a l =>
          change I.LevelAdjacent
            ((refineLevelAddresses (orderedLevelAddresses n)).getLast _)
            ((refineLevelAddresses (orderedLevelAddresses n)).head _)
          simpa [h] using I.levelAdjacent_extended_of_levelAdjacent ih

/-- The equivalence obtained by reading the complete ordered list. -/
noncomputable def orderedLevelAddressEquiv (n : ℕ) :
    Fin (orderedLevelAddresses n).length ≃ LevelAddress n :=
  (orderedLevelAddresses_nodup n).getEquivOfForallMemList
    (orderedLevelAddresses n) (mem_orderedLevelAddresses n)

@[simp] theorem orderedLevelAddressEquiv_apply (n : ℕ)
    (i : Fin (orderedLevelAddresses n).length) :
    orderedLevelAddressEquiv n i = (orderedLevelAddresses n).get i := rfl

/-- Successor modulo the length of a nonempty list. -/
def cyclicSuccIndex {α : Type*} (l : List α) (hne : l ≠ [])
    (i : Fin l.length) : Fin l.length :=
  if h : i.val + 1 < l.length then
    ⟨i.val + 1, h⟩
  else
    ⟨0, List.length_pos_iff_ne_nil.mpr hne⟩

theorem cyclicSuccIndex_ne {α : Type*} (l : List α) (hne : l ≠ [])
    (hlen : 1 < l.length) (i : Fin l.length) :
    cyclicSuccIndex l hne i ≠ i := by
  unfold cyclicSuccIndex
  split_ifs with h
  · intro heq
    have := congrArg Fin.val heq
    simp at this
  · intro heq
    have hiZero : i.val = 0 := by
      simpa using congrArg Fin.val heq.symm
    omega

/-- The next address in positive cyclic boundary order. -/
noncomputable def nextLevelAddress (n : ℕ) (a : LevelAddress n) :
    LevelAddress n :=
  let e := orderedLevelAddressEquiv n
  e (cyclicSuccIndex (orderedLevelAddresses n)
    (orderedLevelAddresses_nonempty n) (e.symm a))

theorem nextLevelAddress_ne (n : ℕ) (a : LevelAddress n) :
    nextLevelAddress n a ≠ a := by
  let e := orderedLevelAddressEquiv n
  let i := e.symm a
  have hi : e i = a := e.apply_symm_apply a
  intro hnext
  have heq : e (cyclicSuccIndex (orderedLevelAddresses n)
      (orderedLevelAddresses_nonempty n) i) = e i := by
    exact hnext.trans hi.symm
  have hlen : 1 < (orderedLevelAddresses n).length := by
    rw [orderedLevelAddresses_length]
    exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  exact (cyclicSuccIndex_ne (orderedLevelAddresses n)
    (orderedLevelAddresses_nonempty n) hlen i) (e.injective heq)

/-- Successive addresses in the ordered list, including the wraparound
pair, have matching boundary endpoints. -/
theorem levelAdjacent_nextLevelAddress (I : J.InitialAngularArcs)
    (n : ℕ) (a : LevelAddress n) :
    I.LevelAdjacent a (nextLevelAddress n a) := by
  let l := orderedLevelAddresses n
  let e := orderedLevelAddressEquiv n
  let i : Fin l.length := e.symm a
  have hi : e i = a := e.apply_symm_apply a
  have hrel : I.LevelAdjacent (e i)
      (e (cyclicSuccIndex l (orderedLevelAddresses_nonempty n) i)) := by
    by_cases hsucc : i.val + 1 < l.length
    · have hchain := (I.orderedLevelAddresses_isChain n).getElem i.val hsucc
      simpa [e, l, cyclicSuccIndex, hsucc] using hchain
    · have hlastVal : i.val = l.length - 1 := by
        have hle : l.length ≤ i.val + 1 := Nat.le_of_not_gt hsucc
        omega
      have hiLast : i = ⟨l.length - 1, by
          have := i.isLt
          omega⟩ := Fin.ext hlastVal
      have hclose := I.orderedLevelAddresses_closes n
      have hlastGet : l.get i =
          l.getLast (orderedLevelAddresses_nonempty n) := by
        rw [hiLast]
        exact List.get_length_sub_one _
      have hnextGet :
          l.get (cyclicSuccIndex l (orderedLevelAddresses_nonempty n) i) =
            l.head (orderedLevelAddresses_nonempty n) := by
        rw [cyclicSuccIndex, dif_neg hsucc]
        exact (List.head_eq_getElem_zero
          (orderedLevelAddresses_nonempty n)).symm
      change I.LevelAdjacent (l.get i)
        (l.get (cyclicSuccIndex l (orderedLevelAddresses_nonempty n) i))
      rw [hlastGet, hnextGet]
      exact hclose
  simpa [nextLevelAddress, e, i, hi] using hrel

end InitialAngularArcs
end JordanCircle

end Schoenflies
