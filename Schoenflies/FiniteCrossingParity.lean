import Schoenflies.SideConstancy

/-!
# Finite crossing parity

The geometric argument eventually produces a Boolean side label for each gap
between successive crossings.  This file records the elementary parity fact
that a label toggled `n` times returns to its initial value exactly when `n`
is even.
-/

namespace Schoenflies

/-- Toggle a Boolean value a prescribed number of times. -/
def toggleN (b : Bool) : ℕ → Bool
  | 0 => b
  | n + 1 => !(toggleN b n)

@[simp] theorem toggleN_zero (b : Bool) : toggleN b 0 = b := rfl

@[simp] theorem toggleN_succ (b : Bool) (n : ℕ) :
    toggleN b (n + 1) = !(toggleN b n) := rfl

theorem toggleN_two_mul (b : Bool) (k : ℕ) :
    toggleN b (2 * k) = b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.mul_succ]
      simp only [toggleN_succ, Bool.not_not, ih]

theorem toggleN_two_mul_add_one (b : Bool) (k : ℕ) :
    toggleN b (2 * k + 1) = !b := by
  simp only [toggleN_succ, toggleN_two_mul]

theorem toggleN_eq_self_iff_even (b : Bool) (n : ℕ) :
    toggleN b n = b ↔ Even n := by
  constructor
  · intro h
    rcases n.even_or_odd' with ⟨k, hk | hk⟩
    · exact ⟨k, by omega⟩
    · rw [hk, toggleN_two_mul_add_one] at h
      exact False.elim ((Bool.not_eq_self b).mp h)
  · rintro ⟨k, hk⟩
    have hn : n = 2 * k := by omega
    rw [hn, toggleN_two_mul]

/-- Values in a finite sequence with every adjacent pair unequal are obtained
by repeatedly toggling the first value. -/
theorem alternating_value {n : ℕ} (c : Fin (n + 1) → Bool)
    (hchange : ∀ i : Fin n, c i.castSucc ≠ c i.succ) :
    ∀ i : Fin (n + 1), c i = toggleN (c 0) i.val := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have hnot : c i.succ = !(c i.castSucc) :=
        Bool.eq_not_of_ne (hchange i).symm
      rw [hnot, ih]
      rfl

/-- If an alternating gap sequence has equal first and last labels, the
number of crossings is even. -/
theorem even_of_alternating_end_eq {n : ℕ}
    (c : Fin (n + 1) → Bool)
    (hchange : ∀ i : Fin n, c i.castSucc ≠ c i.succ)
    (hend : c 0 = c (Fin.last n)) : Even n := by
  have hlast := alternating_value c hchange (Fin.last n)
  have htoggle : toggleN (c 0) n = c 0 := by
    exact (hend.trans (by simpa using hlast)).symm
  exact (toggleN_eq_self_iff_even (c 0) n).mp htoggle

/-- If an alternating gap sequence has different first and last labels, the
number of crossings is odd. -/
theorem odd_of_alternating_end_ne {n : ℕ}
    (c : Fin (n + 1) → Bool)
    (hchange : ∀ i : Fin n, c i.castSucc ≠ c i.succ)
    (hend : c 0 ≠ c (Fin.last n)) : Odd n := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have htoggle := (toggleN_eq_self_iff_even (c 0) n).mpr heven
  have hlast := alternating_value c hchange (Fin.last n)
  apply hend
  calc
    c 0 = toggleN (c 0) n := htoggle.symm
    _ = c (Fin.last n) := by simpa using hlast.symm

end Schoenflies
