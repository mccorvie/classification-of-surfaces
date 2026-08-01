import Schoenflies.CyclicLevelAddresses

/-!
# Endpoint incidence for a complete subdivision level

The right endpoints of the elementary arcs at one level are all distinct as
points of the Jordan circle.  Consequently a right endpoint is incident only
to its own arc and to the next arc in cyclic order.
-/

namespace Schoenflies

open Set Function

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- At a fixed depth, the lifted right endpoint remembers the complete
binary address. -/
theorem descendant_right_injective_of_length
    (A : J.AccessibleAngularArc) :
    ∀ {bs cs : List Bool}, bs.length = cs.length →
      (A.descendant bs).right = (A.descendant cs).right → bs = cs := by
  intro bs
  induction bs generalizing A with
  | nil =>
      intro cs hlen _hendpoint
      cases cs with
      | nil => rfl
      | cons c cs => simp at hlen
  | cons b bs ih =>
      intro cs hlen hendpoint
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have htail : bs.length = cs.length := Nat.succ.inj hlen
          cases b <;> cases c
          · simp only [descendant] at hendpoint
            exact congrArg (List.cons false)
              (ih A.leftChild htail hendpoint)
          · have hleft : (A.leftChild.descendant bs).right ≤
                A.splitAngle := by
              have hmem := A.leftChild.descendant_interval_subset bs
                (right_mem_Icc.mpr
                  (A.leftChild.descendant bs).left_lt_right.le)
              simpa using hmem.2
            have hright : A.splitAngle <
                (A.rightChild.descendant cs).right := by
              have hmem := A.rightChild.descendant_interval_subset cs
                (left_mem_Icc.mpr
                  (A.rightChild.descendant cs).left_lt_right.le)
              have hsplit : A.splitAngle ≤
                  (A.rightChild.descendant cs).left := by
                simpa using hmem.1
              exact hsplit.trans_lt
                (A.rightChild.descendant cs).left_lt_right
            exact False.elim ((hleft.trans_lt hright).ne hendpoint)
          · have hleft : (A.leftChild.descendant cs).right ≤
                A.splitAngle := by
              have hmem := A.leftChild.descendant_interval_subset cs
                (right_mem_Icc.mpr
                  (A.leftChild.descendant cs).left_lt_right.le)
              simpa using hmem.2
            have hright : A.splitAngle <
                (A.rightChild.descendant bs).right := by
              have hmem := A.rightChild.descendant_interval_subset bs
                (left_mem_Icc.mpr
                  (A.rightChild.descendant bs).left_lt_right.le)
              have hsplit : A.splitAngle ≤
                  (A.rightChild.descendant bs).left := by
                simpa using hmem.1
              exact hsplit.trans_lt
                (A.rightChild.descendant bs).left_lt_right
            exact False.elim ((hleft.trans_lt hright).ne hendpoint.symm)
          · simp only [descendant] at hendpoint
            exact congrArg (List.cons true)
              (ih A.rightChild htail hendpoint)

/-- A descendant's right endpoint can never wrap back to the left endpoint
of its parent arc. -/
theorem curvePoint_descendant_right_ne_parent_left
    (A : J.AccessibleAngularArc) (bs : List Bool) :
    (J.curvePoint (A.descendant bs).right : Plane) ≠
      (J.curvePoint A.left : Plane) := by
  intro hplane
  have hcurve : J.curvePoint (A.descendant bs).right =
      J.curvePoint A.left := Subtype.ext hplane
  have hparam : JordanCurve.Arcs.param (A.descendant bs).right =
      JordanCurve.Arcs.param A.left :=
    J.carrierHomeomorph.injective hcurve
  have hrightMem : (A.descendant bs).right ∈ Icc A.left A.right :=
    A.descendant_interval_subset bs
      (right_mem_Icc.mpr (A.descendant bs).left_lt_right.le)
  have hleftMem : A.left ∈ Icc A.left A.right :=
    left_mem_Icc.mpr A.left_lt_right.le
  have hangle := JordanCurve.Arcs.param_injOn A.width_lt_turn
    hrightMem hleftMem hparam
  have hdescLeft : A.left ≤ (A.descendant bs).left :=
    (A.descendant_interval_subset bs
      (left_mem_Icc.mpr (A.descendant bs).left_lt_right.le)).1
  exact (hdescLeft.trans_lt (A.descendant bs).left_lt_right).ne hangle.symm

/-- Dually, a descendant's left endpoint never reaches the right endpoint
of its parent arc. -/
theorem curvePoint_descendant_left_ne_parent_right
    (A : J.AccessibleAngularArc) (bs : List Bool) :
    (J.curvePoint (A.descendant bs).left : Plane) ≠
      (J.curvePoint A.right : Plane) := by
  intro hplane
  have hcurve : J.curvePoint (A.descendant bs).left =
      J.curvePoint A.right := Subtype.ext hplane
  have hparam : JordanCurve.Arcs.param (A.descendant bs).left =
      JordanCurve.Arcs.param A.right :=
    J.carrierHomeomorph.injective hcurve
  have hleftMem : (A.descendant bs).left ∈ Icc A.left A.right :=
    A.descendant_interval_subset bs
      (left_mem_Icc.mpr (A.descendant bs).left_lt_right.le)
  have hrightMem : A.right ∈ Icc A.left A.right :=
    right_mem_Icc.mpr A.left_lt_right.le
  have hangle := JordanCurve.Arcs.param_injOn A.width_lt_turn
    hleftMem hrightMem hparam
  have hdescRight : (A.descendant bs).right ≤ A.right :=
    (A.descendant_interval_subset bs
      (right_mem_Icc.mpr (A.descendant bs).left_lt_right.le)).2
  exact ((A.descendant bs).left_lt_right.trans_le hdescRight).ne hangle

end AccessibleAngularArc

namespace InitialAngularArcs

variable {J : JordanCircle}

/-- The right boundary point of an elementary level arc determines its
address. -/
theorem levelRightPoint_injective (I : J.InitialAngularArcs) {n : ℕ} :
    Injective (fun a : LevelAddress n =>
      (J.curvePoint (I.levelArc a).right : Plane)) := by
  intro a c hpoint
  change (J.curvePoint (I.levelArc a).right : Plane) =
    (J.curvePoint (I.levelArc c).right : Plane) at hpoint
  cases ha : a.1 <;> cases hc : c.1
  · have hcurve : J.curvePoint (I.levelArc a).right =
        J.curvePoint (I.levelArc c).right := Subtype.ext hpoint
    have hparam := J.carrierHomeomorph.injective hcurve
    have haMem0 := I.first.descendant_interval_subset (List.ofFn a.2)
      (right_mem_Icc.mpr
        (I.first.descendant (List.ofFn a.2)).left_lt_right.le)
    have hcMem0 := I.first.descendant_interval_subset (List.ofFn c.2)
      (right_mem_Icc.mpr
        (I.first.descendant (List.ofFn c.2)).left_lt_right.le)
    have hangle := JordanCurve.Arcs.param_injOn I.first.width_lt_turn
      (by simpa [levelArc, rootArc, ha] using haMem0)
      (by simpa [levelArc, rootArc, hc] using hcMem0) hparam
    have hbits : a.2 = c.2 := List.ofFn_injective
      (I.first.descendant_right_injective_of_length
        (by simp) (by simpa [levelArc, rootArc, ha, hc] using hangle))
    exact Prod.ext (ha.trans hc.symm) hbits
  · have hxFirst : (J.curvePoint (I.levelArc a).right : Plane) ∈
        I.first.curveArcPlane :=
      I.first.descendant_curveArcPlane_subset (List.ofFn a.2)
        (by simpa [levelArc, rootArc, ha] using
          (I.levelArc a).right_mem_curveArcPlane)
    have hxSecond : (J.curvePoint (I.levelArc a).right : Plane) ∈
        I.second.curveArcPlane := by
      rw [hpoint]
      exact I.second.descendant_curveArcPlane_subset (List.ofFn c.2)
        (by simpa [levelArc, rootArc, hc] using
          (I.levelArc c).right_mem_curveArcPlane)
    have hx := congrArg
      (fun S : Set Plane =>
        (J.curvePoint (I.levelArc a).right : Plane) ∈ S)
      I.first_inter_second_curveArcPlane |>.mp ⟨hxFirst, hxSecond⟩
    rcases hx with hxLeft | hxRight
    · exact False.elim <| I.first.curvePoint_descendant_right_ne_parent_left
        (List.ofFn a.2) (by
          simpa [levelArc, rootArc, ha] using hxLeft)
    · have hcLeft :
          (J.curvePoint (I.levelArc c).right : Plane) =
            (J.curvePoint I.second.left : Plane) := by
          rw [← hpoint, mem_singleton_iff.mp hxRight, I.adjacent]
      exact False.elim <| I.second.curvePoint_descendant_right_ne_parent_left
        (List.ofFn c.2) (by
          simpa [levelArc, rootArc, hc] using hcLeft)
  · have hxFirst : (J.curvePoint (I.levelArc c).right : Plane) ∈
        I.first.curveArcPlane :=
      I.first.descendant_curveArcPlane_subset (List.ofFn c.2)
        (by simpa [levelArc, rootArc, hc] using
          (I.levelArc c).right_mem_curveArcPlane)
    have hxSecond : (J.curvePoint (I.levelArc c).right : Plane) ∈
        I.second.curveArcPlane := by
      rw [← hpoint]
      exact I.second.descendant_curveArcPlane_subset (List.ofFn a.2)
        (by simpa [levelArc, rootArc, ha] using
          (I.levelArc a).right_mem_curveArcPlane)
    have hx := congrArg
      (fun S : Set Plane =>
        (J.curvePoint (I.levelArc c).right : Plane) ∈ S)
      I.first_inter_second_curveArcPlane |>.mp ⟨hxFirst, hxSecond⟩
    rcases hx with hxLeft | hxRight
    · exact False.elim <| I.first.curvePoint_descendant_right_ne_parent_left
        (List.ofFn c.2) (by
          simpa [levelArc, rootArc, hc] using hxLeft)
    · have haLeft :
          (J.curvePoint (I.levelArc a).right : Plane) =
            (J.curvePoint I.second.left : Plane) := by
          rw [hpoint, mem_singleton_iff.mp hxRight, I.adjacent]
      exact False.elim <| I.second.curvePoint_descendant_right_ne_parent_left
        (List.ofFn a.2) (by
          simpa [levelArc, rootArc, ha] using haLeft)
  · have hcurve : J.curvePoint (I.levelArc a).right =
        J.curvePoint (I.levelArc c).right := Subtype.ext hpoint
    have hparam := J.carrierHomeomorph.injective hcurve
    have haMem0 := I.second.descendant_interval_subset (List.ofFn a.2)
      (right_mem_Icc.mpr
        (I.second.descendant (List.ofFn a.2)).left_lt_right.le)
    have hcMem0 := I.second.descendant_interval_subset (List.ofFn c.2)
      (right_mem_Icc.mpr
        (I.second.descendant (List.ofFn c.2)).left_lt_right.le)
    have hangle := JordanCurve.Arcs.param_injOn I.second.width_lt_turn
      (by simpa [levelArc, rootArc, ha] using haMem0)
      (by simpa [levelArc, rootArc, hc] using hcMem0) hparam
    have hbits : a.2 = c.2 := List.ofFn_injective
      (I.second.descendant_right_injective_of_length
        (by simp) (by simpa [levelArc, rootArc, ha, hc] using hangle))
    exact Prod.ext (ha.trans hc.symm) hbits

/-- The generation mark represented by the right endpoint of a level arc. -/
noncomputable def levelRightMark (I : J.InitialAngularArcs) {n : ℕ}
    (a : LevelAddress n) : I.GenerationMark n :=
  ⟨(J.curvePoint (I.levelArc a).right : Plane),
    I.levelArc_right_mem_generationMarks a⟩

/-- The analogous left endpoint mark. -/
noncomputable def levelLeftMark (I : J.InitialAngularArcs) {n : ℕ}
    (a : LevelAddress n) : I.GenerationMark n :=
  ⟨(J.curvePoint (I.levelArc a).left : Plane),
    I.levelArc_left_mem_generationMarks a⟩

theorem levelRightMark_injective (I : J.InitialAngularArcs) {n : ℕ} :
    Injective (I.levelRightMark : LevelAddress n → I.GenerationMark n) := by
  intro a c h
  apply I.levelRightPoint_injective
  exact congrArg (fun m : I.GenerationMark n => (m.1 : Plane)) h

theorem levelLeftMark_eq_levelRightMark_prev
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    I.levelLeftMark a = I.levelRightMark (prevLevelAddress n a) := by
  apply Subtype.ext
  exact (I.levelAdjacent_prevLevelAddress n a).symm

theorem levelLeftMark_injective (I : J.InitialAngularArcs) {n : ℕ} :
    Injective (I.levelLeftMark : LevelAddress n → I.GenerationMark n) := by
  intro a c hmarks
  have hprev : prevLevelAddress n a = prevLevelAddress n c :=
    I.levelRightMark_injective <| by
      rw [← I.levelLeftMark_eq_levelRightMark_prev a,
        ← I.levelLeftMark_eq_levelRightMark_prev c]
      exact hmarks
  have hnext := congrArg (nextLevelAddress n) hprev
  simpa using hnext

theorem levelLeftPoint_injective (I : J.InitialAngularArcs) {n : ℕ} :
    Injective (fun a : LevelAddress n =>
      (J.curvePoint (I.levelArc a).left : Plane)) := by
  intro a c hpoint
  apply I.levelLeftMark_injective
  exact Subtype.ext hpoint

theorem levelRightPoint_eq_levelRightPoint_iff
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n) :
    (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc c).right : Plane) ↔
      a = c :=
  I.levelRightPoint_injective.eq_iff

theorem levelRightPoint_eq_levelLeftPoint_iff
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n) :
    (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc c).left : Plane) ↔
      c = nextLevelAddress n a := by
  constructor
  · intro h
    have hmarks : I.levelRightMark a = I.levelLeftMark c :=
      Subtype.ext h
    have haPrev : a = prevLevelAddress n c :=
      I.levelRightMark_injective
        (hmarks.trans (I.levelLeftMark_eq_levelRightMark_prev c))
    calc
      c = nextLevelAddress n (prevLevelAddress n c) := by simp
      _ = nextLevelAddress n a := congrArg (nextLevelAddress n) haPrev.symm
  · rintro rfl
    exact I.levelAdjacent_nextLevelAddress n a

theorem levelRightPoint_ne_levelLeftPoint_of_ne_next
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (h : c ≠ nextLevelAddress n a) :
    (J.curvePoint (I.levelArc a).right : Plane) ≠
      (J.curvePoint (I.levelArc c).left : Plane) :=
  fun heq => h ((I.levelRightPoint_eq_levelLeftPoint_iff a c).mp heq)

theorem levelRightPoint_ne_levelRightPoint_of_ne
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (h : a ≠ c) :
    (J.curvePoint (I.levelArc a).right : Plane) ≠
      (J.curvePoint (I.levelArc c).right : Plane) :=
  fun heq => h ((I.levelRightPoint_eq_levelRightPoint_iff a c).mp heq)

/-- Retained hairs based at two different right endpoint marks are disjoint. -/
theorem disjoint_levelRightHairs_of_ne
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (h : a ≠ c) :
    Disjoint (I.levelRightHair a).carrier
      (I.levelRightHair c).carrier := by
  apply (I.generationInsideHairFamily n).pairwise_disjoint
  intro hmarks
  exact h (I.levelRightMark_injective hmarks)

theorem disjoint_levelLeftHairs_of_ne
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (h : a ≠ c) :
    Disjoint (I.levelLeftHair a).carrier
      (I.levelLeftHair c).carrier := by
  apply (I.generationInsideHairFamily n).pairwise_disjoint
  intro hmarks
  exact h (I.levelLeftMark_injective hmarks)

/-- A right endpoint hair is disjoint from a left endpoint hair unless those
endpoints form the corresponding cyclic junction. -/
theorem disjoint_levelRightHair_levelLeftHair_of_ne_next
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (h : c ≠ nextLevelAddress n a) :
    Disjoint (I.levelRightHair a).carrier
      (I.levelLeftHair c).carrier := by
  apply (I.generationInsideHairFamily n).pairwise_disjoint
  intro hmarks
  have hpoint :
      (J.curvePoint (I.levelArc a).right : Plane) =
        (J.curvePoint (I.levelArc c).left : Plane) :=
    congrArg (fun m : I.GenerationMark n => (m.1 : Plane)) hmarks
  exact h ((I.levelRightPoint_eq_levelLeftPoint_iff a c).mp hpoint)

end InitialAngularArcs
end JordanCircle

end Schoenflies
