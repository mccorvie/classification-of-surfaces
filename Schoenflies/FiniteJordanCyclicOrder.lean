import Schoenflies.FiniteJordanArcOrder
import Schoenflies.TwoBoundaryArcRigidity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# A canonical cyclic order on finitely many Jordan-circle marks

The earlier finite-order lemma selected a positive neighbor independently at
each starting mark.  That is enough to construct one collar cell, but it does
not expose the coherence needed to assemble all the cells.  Here the marks
are sorted once, using angular lifts based at a fixed root.  Conjugating
`finRotate` by that enumeration gives an actual cyclic permutation of the
marks.
-/

namespace Schoenflies

open Set Function

noncomputable section

namespace JordanCircle

/-- A finite injective family of at least two marked points on a Jordan
circle. -/
structure FiniteMarking (J : JordanCircle) (ι : Type*) [Fintype ι] where
  point : ι → Plane
  point_mem : ∀ i, point i ∈ J.carrier
  point_injective : Injective point
  two_le_card : 2 ≤ Fintype.card ι

namespace FiniteMarking

variable {J : JordanCircle} {ι : Type*} [Fintype ι]
  (M : J.FiniteMarking ι)

private theorem card_pos (M : J.FiniteMarking ι) :
    0 < Fintype.card ι := by
  exact lt_of_lt_of_le (by norm_num) M.two_le_card

private def firstIndex (M : J.FiniteMarking ι) :
    Fin (Fintype.card ι) :=
  ⟨0, M.card_pos⟩

private def lastIndex (M : J.FiniteMarking ι) :
    Fin (Fintype.card ι) :=
  ⟨Fintype.card ι - 1, Nat.sub_lt M.card_pos (by norm_num)⟩

private theorem finRotate_lastIndex {N : ℕ} (hN : 0 < N) :
    finRotate N ⟨N - 1, Nat.sub_lt hN (by norm_num)⟩ =
      (⟨0, hN⟩ : Fin N) := by
  cases N with
  | zero => simp at hN
  | succ n =>
      have hlast : (⟨n + 1 - 1, Nat.sub_lt hN (by norm_num)⟩ :
          Fin (n + 1)) = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [hlast, finRotate_last]
      rfl

private theorem lt_finRotate_of_val_lt_last {N : ℕ} (hN : 0 < N)
    (i : Fin N) (hi : i.val < N - 1) : i < finRotate N i := by
  cases N with
  | zero => simp at hN
  | succ n =>
      apply (lt_finRotate_iff_ne_last i).mpr
      intro hlast
      have hval := congrArg Fin.val hlast
      simp only [Fin.val_last] at hval
      omega

private theorem no_index_between_finRotate_of_val_lt_last
    {N : ℕ} (hN : 0 < N) (i : Fin N) (hi : i.val < N - 1) :
    ∀ j : Fin N, ¬(i < j ∧ j < finRotate N i) := by
  cases N with
  | zero => simp at hN
  | succ n =>
      have hiLast : i ≠ Fin.last n := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_last] at hval
        omega
      have hrotate := coe_finRotate_of_ne_last hiLast
      intro j hj
      rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val] at hj
      omega

/-- A marked point, regarded as a point of the Jordan carrier. -/
def carrierPoint (a : ι) : J.carrier :=
  ⟨M.point a, M.point_mem a⟩

theorem carrierPoint_injective : Injective M.carrierPoint := by
  intro a b h
  exact M.point_injective (congrArg Subtype.val h)

/-- A fixed cut point used only to linearize the cyclic order. -/
noncomputable def root : ι :=
  Classical.choice <| Fintype.card_pos_iff.mp (by
    exact lt_of_lt_of_le (by norm_num) M.two_le_card)

/-- The angular lift of a mark in the one-turn interval based at `root`. -/
noncomputable def angleKey (a : ι) : ℝ :=
  J.cyclicLift (M.carrierPoint M.root) (M.carrierPoint a)

theorem angleKey_injective : Injective M.angleKey := by
  intro a b hab
  have h := congrArg J.angularPoint hab
  have hpoint : (M.carrierPoint a : Plane) = M.carrierPoint b := by
    simpa only [angleKey, J.angularPoint_cyclicLift] using h
  exact M.point_injective hpoint

@[reducible] private noncomputable def indexLinearOrder : LinearOrder ι :=
  LinearOrder.lift' M.angleKey M.angleKey_injective

/-- Increasing enumeration of all marks by the root-based angular key. -/
noncomputable def enumeration : Fin (Fintype.card ι) ≃ ι := by
  letI := M.indexLinearOrder
  exact (Fintype.orderIsoFinOfCardEq ι rfl).toEquiv

theorem angleKey_enumeration_strictMono :
    StrictMono fun i : Fin (Fintype.card ι) =>
      M.angleKey (M.enumeration i) := by
  letI := M.indexLinearOrder
  intro i j hij
  exact (Fintype.orderIsoFinOfCardEq ι rfl).strictMono hij

theorem angleKey_le_of_index_le {a b : ι}
    (h : M.enumeration.symm a ≤ M.enumeration.symm b) :
    M.angleKey a ≤ M.angleKey b := by
  simpa using M.angleKey_enumeration_strictMono.monotone h

theorem angleKey_lt_of_index_lt {a b : ι}
    (h : M.enumeration.symm a < M.enumeration.symm b) :
    M.angleKey a < M.angleKey b := by
  simpa using M.angleKey_enumeration_strictMono h

theorem angularPoint_angleKey (a : ι) :
    J.angularPoint (M.angleKey a) = M.point a := by
  exact J.angularPoint_cyclicLift
    (M.carrierPoint M.root) (M.carrierPoint a)

theorem angularPoint_angleKey_add_period (a : ι) :
    J.angularPoint (M.angleKey a + 2 * Real.pi) = M.point a := by
  rw [J.angularPoint_periodic]
  exact M.angularPoint_angleKey a

theorem angleKey_root :
    M.angleKey M.root =
      J.angularRepresentative (M.carrierPoint M.root) + 2 * Real.pi := by
  simp [angleKey, JordanCircle.cyclicLift]

theorem angularRepresentative_root_lt_angleKey (a : ι) :
    J.angularRepresentative (M.carrierPoint M.root) < M.angleKey a :=
  (J.cyclicLift_mem_Ioc
    (M.carrierPoint M.root) (M.carrierPoint a)).1

theorem angleKey_lt_root {a : ι} (ha : a ≠ M.root) :
    M.angleKey a < M.angleKey M.root := by
  rw [M.angleKey_root]
  exact J.cyclicLift_lt_add_period (M.carrierPoint_injective.ne ha.symm)

theorem enumeration_index_le_root (i : Fin (Fintype.card ι)) :
    i ≤ M.enumeration.symm M.root := by
  by_contra h
  have hrootLt : M.enumeration.symm M.root < i := lt_of_not_ge h
  have hkeyLt := M.angleKey_enumeration_strictMono hrootLt
  have hroot : M.enumeration (M.enumeration.symm M.root) = M.root :=
    M.enumeration.apply_symm_apply M.root
  have hiNe : M.enumeration i ≠ M.root := by
    intro hi
    have heq := M.enumeration.injective (hi.trans hroot.symm)
    rw [heq] at hrootLt
    exact (lt_irrefl _ hrootLt)
  change M.angleKey (M.enumeration (M.enumeration.symm M.root)) <
    M.angleKey (M.enumeration i) at hkeyLt
  rw [hroot] at hkeyLt
  exact (lt_asymm hkeyLt (M.angleKey_lt_root hiNe)).elim

theorem enumeration_symm_root_eq_lastIndex :
    M.enumeration.symm M.root = M.lastIndex := by
  apply Fin.ext
  have hle := M.enumeration_index_le_root M.lastIndex
  have hrootLt := (M.enumeration.symm M.root).isLt
  change Fintype.card ι - 1 ≤ (M.enumeration.symm M.root).val at hle
  change (M.enumeration.symm M.root).val = Fintype.card ι - 1
  omega

/-- The cyclic successor permutation, obtained by rotating the increasing
enumeration by one place. -/
noncomputable def successorEquiv : Equiv.Perm ι :=
  M.enumeration.symm.trans <|
    (finRotate (Fintype.card ι)).trans M.enumeration

/-- The next marked point in positive angular order. -/
noncomputable def successor (a : ι) : ι :=
  M.successorEquiv a

/-- The preceding marked point in positive angular order. -/
noncomputable def predecessor (a : ι) : ι :=
  M.successorEquiv.symm a

theorem successor_bijective : Bijective M.successor :=
  M.successorEquiv.bijective

theorem successor_injective : Injective M.successor :=
  M.successor_bijective.injective

theorem successor_surjective : Surjective M.successor :=
  M.successor_bijective.surjective

@[simp] theorem predecessor_successor (a : ι) :
    M.predecessor (M.successor a) = a :=
  M.successorEquiv.symm_apply_apply a

@[simp] theorem successor_predecessor (a : ι) :
    M.successor (M.predecessor a) = a :=
  M.successorEquiv.apply_symm_apply a

theorem enumeration_symm_successor (a : ι) :
    M.enumeration.symm (M.successor a) =
      finRotate (Fintype.card ι) (M.enumeration.symm a) := by
  simp [successor, successorEquiv]

theorem enumeration_symm_successor_root :
    M.enumeration.symm (M.successor M.root) = M.firstIndex := by
  rw [M.enumeration_symm_successor,
    M.enumeration_symm_root_eq_lastIndex]
  convert finRotate_lastIndex M.card_pos using 1 <;>
    apply Fin.ext <;> rfl

theorem enumeration_symm_lt_successor {a : ι} (ha : a ≠ M.root) :
    M.enumeration.symm a < M.enumeration.symm (M.successor a) := by
  rw [M.enumeration_symm_successor]
  apply lt_finRotate_of_val_lt_last M.card_pos
  have hle := M.enumeration_index_le_root (M.enumeration.symm a)
  rw [M.enumeration_symm_root_eq_lastIndex] at hle
  have hne : M.enumeration.symm a ≠ M.lastIndex := by
    rw [← M.enumeration_symm_root_eq_lastIndex]
    exact fun h => ha (M.enumeration.symm.injective h)
  change (M.enumeration.symm a).val ≤ Fintype.card ι - 1 at hle
  change (M.enumeration.symm a).val < Fintype.card ι - 1
  by_contra h
  apply hne
  apply Fin.ext
  change (M.enumeration.symm a).val = Fintype.card ι - 1
  omega

theorem no_enumeration_index_between_successor {a : ι}
    (ha : a ≠ M.root) (i : Fin (Fintype.card ι)) :
    ¬(M.enumeration.symm a < i ∧
      i < M.enumeration.symm (M.successor a)) := by
  rw [M.enumeration_symm_successor]
  apply no_index_between_finRotate_of_val_lt_last M.card_pos
  have hle := M.enumeration_index_le_root (M.enumeration.symm a)
  rw [M.enumeration_symm_root_eq_lastIndex] at hle
  have hne : M.enumeration.symm a ≠ M.lastIndex := by
    rw [← M.enumeration_symm_root_eq_lastIndex]
    exact fun h => ha (M.enumeration.symm.injective h)
  change (M.enumeration.symm a).val ≤ Fintype.card ι - 1 at hle
  change (M.enumeration.symm a).val < Fintype.card ι - 1
  by_contra h
  apply hne
  apply Fin.ext
  change (M.enumeration.symm a).val = Fintype.card ι - 1
  omega

theorem angleKey_lt_successor {a : ι} (ha : a ≠ M.root) :
    M.angleKey a < M.angleKey (M.successor a) := by
  simpa using M.angleKey_enumeration_strictMono
    (M.enumeration_symm_lt_successor ha)

private theorem finRotate_ne_of_two_le {N : ℕ} (hN : 2 ≤ N)
    (i : Fin N) : finRotate N i ≠ i := by
  cases N with
  | zero =>
      omega
  | succ n =>
      have hn : 0 < n := by
        omega
      by_cases hi : i = Fin.last n
      · rw [hi, finRotate_last]
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_last] at hval
        omega
      · exact ne_of_gt ((lt_finRotate_iff_ne_last i).mpr hi)

private theorem finRotate_sq_ne_of_three_le {N : ℕ} (hN : 3 ≤ N)
    (i : Fin N) : finRotate N (finRotate N i) ≠ i := by
  cases N with
  | zero => omega
  | succ n =>
      have hn : 2 ≤ n := by
        omega
      by_cases hi : i = Fin.last n
      · rw [hi, finRotate_last, finRotate_apply_zero]
        intro h
        have hval := congrArg Fin.val h
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega), Fin.val_last] at hval
        omega
      · have hfirst : (finRotate (n + 1) i : ℕ) = i + 1 :=
          coe_finRotate_of_ne_last hi
        by_cases hnext : finRotate (n + 1) i = Fin.last n
        · rw [hnext, finRotate_last]
          intro h
          have hval := congrArg Fin.val h
          have hnextVal := congrArg Fin.val hnext
          simp only [Fin.val_zero, Fin.val_last] at hval hnextVal
          omega
        · have hsecond :
              (finRotate (n + 1) (finRotate (n + 1) i) : ℕ) =
                (finRotate (n + 1) i : ℕ) + 1 :=
            coe_finRotate_of_ne_last hnext
          intro h
          have hval := congrArg Fin.val h
          omega

theorem successor_ne (a : ι) : M.successor a ≠ a := by
  intro h
  have hindex := congrArg M.enumeration.symm h
  rw [M.enumeration_symm_successor] at hindex
  exact finRotate_ne_of_two_le M.two_le_card
    (M.enumeration.symm a) hindex

theorem successor_successor_ne (hcard : 3 ≤ Fintype.card ι)
    (a : ι) : M.successor (M.successor a) ≠ a := by
  intro h
  have hindex := congrArg M.enumeration.symm h
  rw [M.enumeration_symm_successor,
    M.enumeration_symm_successor] at hindex
  exact finRotate_sq_ne_of_three_le hcard
    (M.enumeration.symm a) hindex

/-- The start angle for the positively oriented arc from a mark to its
successor. -/
noncomputable def successorStartAngle (a : ι) : ℝ :=
  M.angleKey a

/-- The end angle for the positively oriented successor arc.  At the root
the increasing enumeration wraps, so the successor key is lifted by one
additional period. -/
noncomputable def successorEndAngle (a : ι) : ℝ :=
  by
    classical
    exact if a = M.root then
      M.angleKey (M.successor a) + 2 * Real.pi
    else
      M.angleKey (M.successor a)

theorem angularPoint_successorStartAngle (a : ι) :
    J.angularPoint (M.successorStartAngle a) = M.point a :=
  M.angularPoint_angleKey a

theorem angularPoint_successorEndAngle (a : ι) :
    J.angularPoint (M.successorEndAngle a) =
      M.point (M.successor a) := by
  by_cases ha : a = M.root
  · rw [successorEndAngle, if_pos ha]
    exact M.angularPoint_angleKey_add_period (M.successor a)
  · rw [successorEndAngle, if_neg ha]
    exact M.angularPoint_angleKey (M.successor a)

theorem successorStartAngle_lt_endAngle (a : ι) :
    M.successorStartAngle a < M.successorEndAngle a := by
  by_cases ha : a = M.root
  · subst a
    rw [successorStartAngle, successorEndAngle, if_pos rfl,
      M.angleKey_root]
    have hlow :=
      M.angularRepresentative_root_lt_angleKey (M.successor M.root)
    linarith
  · rw [successorStartAngle, successorEndAngle, if_neg ha]
    exact M.angleKey_lt_successor ha

theorem successorEndAngle_lt_startAngle_add_period (a : ι) :
    M.successorEndAngle a <
      M.successorStartAngle a + 2 * Real.pi := by
  by_cases ha : a = M.root
  · subst a
    rw [successorStartAngle, successorEndAngle, if_pos rfl]
    have hsuccNe : M.successor M.root ≠ M.root :=
      M.successor_ne M.root
    linarith [M.angleKey_lt_root hsuccNe]
  · rw [successorStartAngle, successorEndAngle, if_neg ha]
    have hsuccLe : M.angleKey (M.successor a) ≤ M.angleKey M.root := by
      by_cases hs : M.successor a = M.root
      · rw [hs]
      · exact (M.angleKey_lt_root hs).le
    rw [M.angleKey_root] at hsuccLe
    have haLower := M.angularRepresentative_root_lt_angleKey a
    linarith

/-- The positive successor arc contains no third mark.  The complementary
arc therefore contains every remaining mark.  Unlike the earlier local
choice theorem, these successor pairs come from one cyclic permutation. -/
theorem exists_successor_twoBoundaryArcPaths (a : ι) :
  ∃ S : J.TwoBoundaryArcPaths (M.point a) (M.point (M.successor a)),
      range S.first = J.parametrization ''
          (JordanCurve.Arcs.param '' Set.Icc
            (M.successorStartAngle a) (M.successorEndAngle a)) ∧
        ∀ c : ι, c ≠ a → c ≠ M.successor a →
          M.point c ∈ range S.second := by
  let alpha := M.successorStartAngle a
  let beta := M.successorEndAngle a
  obtain ⟨S₀, hfirst₀, hsecond₀⟩ :=
    J.exists_twoBoundaryArcPaths_of_angles
      (M.successorStartAngle_lt_endAngle a)
      (M.successorEndAngle_lt_startAngle_add_period a)
  let S := S₀.cast (M.angularPoint_successorStartAngle a)
    (M.angularPoint_successorEndAngle a)
  have hsecond : range S.second = J.parametrization ''
      (JordanCurve.Arcs.param '' Set.Icc beta
        (alpha + 2 * Real.pi)) := by
    simpa [S, alpha, beta] using hsecond₀
  refine ⟨S, ?_, ?_⟩
  · simpa [S, alpha, beta] using hfirst₀
  intro c hca hcsucc
  rw [hsecond]
  by_cases ha : a = M.root
  · subst a
    let theta := M.angleKey c + 2 * Real.pi
    have hsuccIndex : M.enumeration.symm (M.successor M.root) =
        M.firstIndex := M.enumeration_symm_successor_root
    have hfirstLe : M.enumeration.symm (M.successor M.root) ≤
        M.enumeration.symm c := by
      rw [hsuccIndex]
      change M.firstIndex.val ≤ (M.enumeration.symm c).val
      simp [firstIndex]
    have hkeyLower : M.angleKey (M.successor M.root) ≤
        M.angleKey c := M.angleKey_le_of_index_le hfirstLe
    have hkeyUpper : M.angleKey c < M.angleKey M.root := by
      exact M.angleKey_lt_root hca
    have htheta : theta ∈ Set.Icc beta (alpha + 2 * Real.pi) := by
      dsimp [theta, alpha, beta, successorStartAngle, successorEndAngle]
      rw [if_pos rfl]
      constructor <;> linarith
    refine ⟨JordanCurve.Arcs.param theta, ⟨theta, htheta, rfl⟩, ?_⟩
    exact M.angularPoint_angleKey_add_period c
  · have hraSucc := M.enumeration_symm_lt_successor ha
    have hrootUpper :=
      M.enumeration_index_le_root (M.enumeration.symm c)
    by_cases hsuccC :
        M.enumeration.symm (M.successor a) ≤ M.enumeration.symm c
    · have hkeyLower : M.angleKey (M.successor a) ≤ M.angleKey c :=
        M.angleKey_le_of_index_le hsuccC
      have hkeyRoot : M.angleKey c ≤ M.angleKey M.root :=
        M.angleKey_le_of_index_le hrootUpper
      have haLower := M.angularRepresentative_root_lt_angleKey a
      have htheta : M.angleKey c ∈
          Set.Icc beta (alpha + 2 * Real.pi) := by
        dsimp [alpha, beta, successorStartAngle, successorEndAngle]
        rw [if_neg ha]
        rw [M.angleKey_root] at hkeyRoot
        constructor <;> linarith
      refine ⟨JordanCurve.Arcs.param (M.angleKey c),
        ⟨M.angleKey c, htheta, rfl⟩, ?_⟩
      exact M.angularPoint_angleKey c
    · have hcSucc : M.enumeration.symm c <
          M.enumeration.symm (M.successor a) := lt_of_not_ge hsuccC
      have hcLeA : M.enumeration.symm c ≤ M.enumeration.symm a := by
        by_contra hnot
        have haC : M.enumeration.symm a < M.enumeration.symm c :=
          lt_of_not_ge hnot
        exact M.no_enumeration_index_between_successor ha
          (M.enumeration.symm c) ⟨haC, hcSucc⟩
      have hcNeA : M.enumeration.symm c ≠ M.enumeration.symm a := by
        intro h
        exact hca (M.enumeration.symm.injective h)
      have hcA : M.enumeration.symm c < M.enumeration.symm a :=
        lt_of_le_of_ne hcLeA hcNeA
      have hkeyUpper : M.angleKey c < M.angleKey a :=
        M.angleKey_lt_of_index_lt hcA
      have hsuccRoot : M.angleKey (M.successor a) ≤
          M.angleKey M.root := by
        by_cases hsroot : M.successor a = M.root
        · rw [hsroot]
        · exact (M.angleKey_lt_root hsroot).le
      have hcLower := M.angularRepresentative_root_lt_angleKey c
      rw [M.angleKey_root] at hsuccRoot
      let theta := M.angleKey c + 2 * Real.pi
      have htheta : theta ∈ Set.Icc beta (alpha + 2 * Real.pi) := by
        dsimp [theta, alpha, beta, successorStartAngle, successorEndAngle]
        rw [if_neg ha]
        constructor <;> linarith
      refine ⟨JordanCurve.Arcs.param theta, ⟨theta, htheta, rfl⟩, ?_⟩
      exact M.angularPoint_angleKey_add_period c

/-- A fixed complementary-arc presentation for each canonical successor
pair. -/
noncomputable def successorBoundarySplit (a : ι) :
    J.TwoBoundaryArcPaths (M.point a) (M.point (M.successor a)) :=
  Classical.choose (M.exists_successor_twoBoundaryArcPaths a)

/-- Every third mark lies on the complementary side of the canonical
successor split. -/
theorem other_point_mem_successorBoundarySplit_second (a : ι) :
    ∀ c : ι, c ≠ a → c ≠ M.successor a →
      M.point c ∈ range (M.successorBoundarySplit a).second :=
  (Classical.choose_spec (M.exists_successor_twoBoundaryArcPaths a)).2

/-- The canonical successor path is the positive angular interval between a
mark and its successor. -/
theorem range_successorBoundarySplit_first (a : ι) :
    range (M.successorBoundarySplit a).first = J.parametrization ''
      (JordanCurve.Arcs.param '' Set.Icc
        (M.successorStartAngle a) (M.successorEndAngle a)) :=
  (Classical.choose_spec (M.exists_successor_twoBoundaryArcPaths a)).1

/-- The positive arcs between cyclically consecutive marks cover the whole
Jordan carrier. -/
theorem carrier_subset_iUnion_successorBoundarySplit_first :
    J.carrier ⊆ ⋃ a : ι, range (M.successorBoundarySplit a).first := by
  classical
  intro x hx
  let X : J.carrier := ⟨x, hx⟩
  let theta := J.cyclicLift (M.carrierPoint M.root) X
  have hthetaLower :
      J.angularRepresentative (M.carrierPoint M.root) < theta :=
    (J.cyclicLift_mem_Ioc (M.carrierPoint M.root) X).1
  have hthetaUpper : theta ≤ M.angleKey M.root := by
    rw [M.angleKey_root]
    exact (J.cyclicLift_mem_Ioc (M.carrierPoint M.root) X).2
  have hthetaPoint : J.angularPoint theta = x := by
    exact J.angularPoint_cyclicLift (M.carrierPoint M.root) X
  have hfirstEq : M.enumeration M.firstIndex = M.successor M.root := by
    apply M.enumeration.symm.injective
    rw [M.enumeration_symm_successor_root]
    simp only [Equiv.symm_apply_apply]
  by_cases hfirst :
      M.angleKey (M.enumeration M.firstIndex) ≤ theta
  · let eligible : Finset ι :=
        Finset.univ.filter fun a => M.angleKey a ≤ theta
    have heligible : eligible.Nonempty := by
      refine ⟨M.enumeration M.firstIndex, ?_⟩
      simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfirst
    obtain ⟨a, ha, hamax⟩ :=
      Finset.exists_max_image eligible M.angleKey heligible
    have hastart : M.successorStartAngle a ≤ theta := by
      change M.angleKey a ≤ theta
      exact (Finset.mem_filter.mp ha).2
    have haend : theta ≤ M.successorEndAngle a := by
      by_cases haroot : a = M.root
      · subst a
        exact hthetaUpper.trans
          (M.successorStartAngle_lt_endAngle M.root).le
      · rw [successorEndAngle, if_neg haroot]
        by_contra hnot
        have hsuccessorEligible : M.successor a ∈ eligible := by
          simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
          exact le_of_not_ge hnot
        have hmax := hamax (M.successor a) hsuccessorEligible
        exact (not_lt_of_ge hmax) (M.angleKey_lt_successor haroot)
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [M.range_successorBoundarySplit_first]
    refine ⟨JordanCurve.Arcs.param theta,
      ⟨theta, ⟨hastart, haend⟩, rfl⟩, ?_⟩
    exact hthetaPoint
  · apply Set.mem_iUnion.mpr
    refine ⟨M.root, ?_⟩
    rw [M.range_successorBoundarySplit_first]
    let theta' := theta + 2 * Real.pi
    have hstart : M.successorStartAngle M.root ≤ theta' := by
      dsimp only [successorStartAngle, theta']
      rw [M.angleKey_root]
      linarith
    have hend : theta' ≤ M.successorEndAngle M.root := by
      dsimp only [theta', successorEndAngle]
      rw [if_pos rfl, ← hfirstEq]
      have hlt : theta < M.angleKey (M.enumeration M.firstIndex) :=
        lt_of_not_ge hfirst
      linarith
    refine ⟨JordanCurve.Arcs.param theta',
      ⟨theta', ⟨hstart, hend⟩, rfl⟩, ?_⟩
    change J.angularPoint theta' = x
    dsimp only [theta']
    rw [J.angularPoint_periodic]
    exact hthetaPoint

theorem point_mem_successorBoundarySplit_first_iff (a c : ι) :
    M.point c ∈ range (M.successorBoundarySplit a).first ↔
      c = a ∨ c = M.successor a := by
  constructor
  · intro hc
    by_cases hca : c = a
    · exact Or.inl hca
    by_cases hcsucc : c = M.successor a
    · exact Or.inr hcsucc
    have hcSecond := M.other_point_mem_successorBoundarySplit_second
      a c hca hcsucc
    have hcEnds : M.point c ∈
        ({M.point a, M.point (M.successor a)} : Set Plane) := by
      rw [← (M.successorBoundarySplit a).overlap]
      exact ⟨hc, hcSecond⟩
    rcases hcEnds with h | h
    · exact False.elim (hca (M.point_injective h))
    · exact False.elim
        (hcsucc (M.point_injective (Set.mem_singleton_iff.mp h)))
  · intro h
    rcases h with h | h
    · rw [h]
      exact Path.source_mem_range (M.successorBoundarySplit a).first
    · rw [h]
      exact Path.target_mem_range (M.successorBoundarySplit a).first

/-- Any coherently labelled family of endpoint-free successor arcs has
pairwise overlaps only at endpoints of the first arc.  The paths themselves
may have been chosen independently. -/
theorem successorSplitFamily_first_inter_subset_endpoints
    (hcard : 3 ≤ Fintype.card ι)
    (T : ∀ a : ι,
      J.TwoBoundaryArcPaths (M.point a) (M.point (M.successor a)))
    (hother : ∀ a c : ι, c ≠ a → c ≠ M.successor a →
      M.point c ∈ range (T a).second)
    {a b : ι} (hab : a ≠ b) :
    range (T a).first ∩ range (T b).first ⊆
      ({M.point a, M.point (M.successor a)} : Set Plane) := by
  have hpoint (q c : ι) :
      M.point c ∈ range (T q).first ↔
        c = q ∨ c = M.successor q := by
    constructor
    · intro hc
      by_cases hcq : c = q
      · exact Or.inl hcq
      by_cases hcsucc : c = M.successor q
      · exact Or.inr hcsucc
      have hcEnds : M.point c ∈
          ({M.point q, M.point (M.successor q)} : Set Plane) := by
        rw [← (T q).overlap]
        exact ⟨hc, hother q c hcq hcsucc⟩
      rcases hcEnds with h | h
      · exact False.elim (hcq (M.point_injective h))
      · exact False.elim
          (hcsucc (M.point_injective (Set.mem_singleton_iff.mp h)))
    · intro h
      rcases h with h | h
      · rw [h]
        exact Path.source_mem_range (T q).first
      · rw [h]
        exact Path.target_mem_range (T q).first
  let Sa := T a
  let Sb := T b
  have hSbCarrier : range Sb.first ⊆ J.carrier :=
    Sb.first_range_subset_carrier
  have hAvoid : Disjoint
      (Sb.first '' Set.Ioo (0 : unitInterval) 1)
      ({M.point a, M.point (M.successor a)} : Set Plane) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ (hza | hza)
    · rcases (hpoint b a).mp ⟨t, hza⟩ with hab' | hab'
      · have ht0 : t = 0 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.source, hab'] using hza)
        exact (ne_of_gt ht.1) ht0
      · have ht1 : t = 1 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.target, hab'] using hza)
        exact (ne_of_lt ht.2) ht1
    · rw [Set.mem_singleton_iff] at hza
      rcases (hpoint b (M.successor a)).mp ⟨t, hza⟩ with hlabel | hlabel
      · have ht0 : t = 0 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.source, hlabel] using hza)
        exact (ne_of_gt ht.1) ht0
      · have ht1 : t = 1 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.target, hlabel] using hza)
        exact (ne_of_lt ht.2) ht1
  have hside := Sa.range_subset_first_or_second_of_interior_disjoint
    Sb.first hSbCarrier hAvoid
  have hnotFirst : ¬ range Sb.first ⊆ range Sa.first := by
    intro hsub
    by_cases hbnext : b = M.successor a
    · have hnextNotA : M.successor b ≠ a := by
        rw [hbnext]
        exact M.successor_successor_ne hcard a
      have hnextNotNext : M.successor b ≠ M.successor a := by
        intro h
        exact hab (M.successor_injective h).symm
      have hnotMem : M.point (M.successor b) ∉ range Sa.first :=
        fun h => (not_or_intro hnextNotA hnextNotNext)
          ((hpoint a (M.successor b)).mp h)
      exact hnotMem <| hsub <| Path.target_mem_range Sb.first
    · have hbNotA : b ≠ a := hab.symm
      have hnotMem : M.point b ∉ range Sa.first :=
        fun h => (not_or_intro hbNotA hbnext) ((hpoint a b).mp h)
      exact hnotMem <| hsub <| Path.source_mem_range Sb.first
  have hSbSecond : range Sb.first ⊆ range Sa.second :=
    hside.resolve_left hnotFirst
  intro z hz
  change z ∈ range Sa.first ∩ range Sb.first at hz
  rw [← Sa.overlap]
  exact ⟨hz.1, hSbSecond hz.2⟩

/-- Distinct canonical positive successor arcs meet only at endpoints of
the first arc. -/
theorem successorBoundarySplit_first_inter_subset_endpoints
    (hcard : 3 ≤ Fintype.card ι) {a b : ι} (hab : a ≠ b) :
    range (M.successorBoundarySplit a).first ∩
        range (M.successorBoundarySplit b).first ⊆
      ({M.point a, M.point (M.successor a)} : Set Plane) := by
  exact M.successorSplitFamily_first_inter_subset_endpoints hcard
    M.successorBoundarySplit
    M.other_point_mem_successorBoundarySplit_second hab

/-- With at least three marks, the condition that every third mark lies on
the complementary path determines which of the two point-set arcs is the
successor arc. -/
theorem ranges_eq_successorBoundarySplit
    (hcard : 3 ≤ Fintype.card ι) (a : ι)
    (T : J.TwoBoundaryArcPaths (M.point a) (M.point (M.successor a)))
    (hother : ∀ c : ι, c ≠ a → c ≠ M.successor a →
      M.point c ∈ range T.second) :
    range T.first = range (M.successorBoundarySplit a).first ∧
      range T.second = range (M.successorBoundarySplit a).second := by
  classical
  rcases (M.successorBoundarySplit a).range_pair_eq_or_swap T with h | h
  · exact h
  · have hpairCard :
      ({a, M.successor a} : Finset ι).card <
        (Finset.univ : Finset ι).card := by
      rw [Finset.card_univ]
      calc
        ({a, M.successor a} : Finset ι).card ≤
            ({M.successor a} : Finset ι).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
        _ < Fintype.card ι := by omega
    obtain ⟨c, _hcuniv, hc⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hpairCard
    have hc' : c ≠ a ∧ c ≠ M.successor a := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hc
    have hcBoth : M.point c ∈
        range (M.successorBoundarySplit a).first ∩
          range (M.successorBoundarySplit a).second := by
      constructor
      · rw [← h.2]
        exact hother c hc'.1 hc'.2
      · exact M.other_point_mem_successorBoundarySplit_second a c
          hc'.1 hc'.2
    rw [(M.successorBoundarySplit a).overlap] at hcBoth
    rcases hcBoth with hca | hcsucc
    · exact False.elim (hc'.1 (M.point_injective hca))
    · exact False.elim (hc'.2
        (M.point_injective (Set.mem_singleton_iff.mp hcsucc)))

end FiniteMarking

end JordanCircle

end

end Schoenflies
