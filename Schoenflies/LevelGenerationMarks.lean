import Schoenflies.AngularSubdivisions

/-!
# Generation marks on elementary subdivision arcs

At binary depth `n`, a depth-`n` descendant contains no retained generation
mark except its two endpoints.  This is the finite combinatorial fact needed
to keep a collar crosscut away from every nonincident retained access hair.
-/

namespace Schoenflies

open Set Function Real

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- A descendant boundary arc is contained in its ancestor, in the ambient
plane formulation. -/
theorem descendant_curveArcPlane_subset (A : J.AccessibleAngularArc)
    (bs : List Bool) :
    (A.descendant bs).curveArcPlane ⊆ A.curveArcPlane := by
  exact image_mono (A.descendant_curveArc_subset J bs)

/-- Every retained generation mark of an arc lies on that arc. -/
theorem generationMarks_subset_curveArcPlane (A : J.AccessibleAngularArc) :
    ∀ n : ℕ, ↑(A.generationMarks n) ⊆ A.curveArcPlane := by
  intro n
  induction n generalizing A with
  | zero =>
      intro x hx
      simp only [generationMarks, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact A.left_mem_curveArcPlane
      · exact A.right_mem_curveArcPlane
  | succ n ih =>
      intro x hx
      simp only [generationMarks, Finset.mem_coe, Finset.mem_union] at hx
      rw [← A.leftChild_union_rightChild_curveArcPlane]
      rcases hx with hx | hx
      · exact Or.inl (ih A.leftChild hx)
      · exact Or.inr (ih A.rightChild hx)

/-- If the right endpoint of an ancestor belongs to a descendant arc, it is
the right endpoint of that descendant. -/
theorem descendant_right_eq_of_parentRight_mem
    (A : J.AccessibleAngularArc) (bs : List Bool)
    (hmem : (J.curvePoint A.right : Plane) ∈
      (A.descendant bs).curveArcPlane) :
    (A.descendant bs).right = A.right := by
  rcases hmem with ⟨y, ⟨t, ht, rfl⟩, hplane⟩
  have hcurve : J.curvePoint t = J.curvePoint A.right :=
    Subtype.ext hplane
  have hparam : JordanCurve.Arcs.param t =
      JordanCurve.Arcs.param A.right :=
    J.carrierHomeomorph.injective hcurve
  have htroot : t ∈ Icc A.left A.right :=
    A.descendant_interval_subset bs ht
  have htEq : t = A.right :=
    JordanCurve.Arcs.param_injOn A.width_lt_turn htroot
      (right_mem_Icc.mpr A.left_lt_right.le) hparam
  have hrightLe : (A.descendant bs).right ≤ A.right :=
    (A.descendant_interval_subset bs
      (right_mem_Icc.mpr (A.descendant bs).left_lt_right.le)).2
  exact le_antisymm hrightLe (htEq ▸ ht.2)

/-- If the left endpoint of an ancestor belongs to a descendant arc, it is
the left endpoint of that descendant. -/
theorem descendant_left_eq_of_parentLeft_mem
    (A : J.AccessibleAngularArc) (bs : List Bool)
    (hmem : (J.curvePoint A.left : Plane) ∈
      (A.descendant bs).curveArcPlane) :
    (A.descendant bs).left = A.left := by
  rcases hmem with ⟨y, ⟨t, ht, rfl⟩, hplane⟩
  have hcurve : J.curvePoint t = J.curvePoint A.left :=
    Subtype.ext hplane
  have hparam : JordanCurve.Arcs.param t =
      JordanCurve.Arcs.param A.left :=
    J.carrierHomeomorph.injective hcurve
  have htroot : t ∈ Icc A.left A.right :=
    A.descendant_interval_subset bs ht
  have htEq : t = A.left :=
    JordanCurve.Arcs.param_injOn A.width_lt_turn htroot
      (left_mem_Icc.mpr A.left_lt_right.le) hparam
  have hleftLe : A.left ≤ (A.descendant bs).left :=
    (A.descendant_interval_subset bs
      (left_mem_Icc.mpr (A.descendant bs).left_lt_right.le)).1
  exact le_antisymm (htEq ▸ ht.1) hleftLe

/-- A depth-`n` descendant contains exactly the two generation marks that
bound it (the stated direction is the one used for hair avoidance). -/
theorem generationMark_mem_descendant_eq_endpoint
    (A : J.AccessibleAngularArc) :
    ∀ (bs : List Bool) {x : Plane},
      x ∈ A.generationMarks bs.length →
      x ∈ (A.descendant bs).curveArcPlane →
      x = (J.curvePoint (A.descendant bs).left : Plane) ∨
        x = (J.curvePoint (A.descendant bs).right : Plane) := by
  intro bs
  induction bs generalizing A with
  | nil =>
      intro x hxGen _hxArc
      simp only [List.length_nil, generationMarks, Finset.mem_insert,
        Finset.mem_singleton] at hxGen
      simpa [descendant] using hxGen
  | cons b bs ih =>
      intro x hxGen hxArc
      simp only [List.length_cons, generationMarks, Finset.mem_union] at hxGen
      cases b with
      | false =>
          change x ∈ (A.leftChild.descendant bs).curveArcPlane at hxArc
          change x = (J.curvePoint (A.leftChild.descendant bs).left : Plane) ∨
            x = (J.curvePoint (A.leftChild.descendant bs).right : Plane)
          rcases hxGen with hxLeft | hxRight
          · exact ih A.leftChild hxLeft hxArc
          · have hxRightArc : x ∈ A.rightChild.curveArcPlane :=
              A.rightChild.generationMarks_subset_curveArcPlane bs.length hxRight
            have hxLeftArc : x ∈ A.leftChild.curveArcPlane :=
              (A.leftChild.descendant_curveArcPlane_subset bs) hxArc
            have hxSplit : x = (J.curvePoint A.splitAngle : Plane) := by
              have hxInter : x ∈ A.leftChild.curveArcPlane ∩
                  A.rightChild.curveArcPlane := ⟨hxLeftArc, hxRightArc⟩
              rw [A.leftChild_inter_rightChild_curveArcPlane] at hxInter
              exact mem_singleton_iff.mp hxInter
            have hparentMem :
                (J.curvePoint A.leftChild.right : Plane) ∈
                  (A.leftChild.descendant bs).curveArcPlane := by
              simpa using hxSplit ▸ hxArc
            have hright := A.leftChild.descendant_right_eq_of_parentRight_mem
              bs hparentMem
            right
            rw [hxSplit, hright]
            rfl
      | true =>
          change x ∈ (A.rightChild.descendant bs).curveArcPlane at hxArc
          change x = (J.curvePoint (A.rightChild.descendant bs).left : Plane) ∨
            x = (J.curvePoint (A.rightChild.descendant bs).right : Plane)
          rcases hxGen with hxLeft | hxRight
          · have hxLeftArc : x ∈ A.leftChild.curveArcPlane :=
              A.leftChild.generationMarks_subset_curveArcPlane bs.length hxLeft
            have hxRightArc : x ∈ A.rightChild.curveArcPlane :=
              (A.rightChild.descendant_curveArcPlane_subset bs) hxArc
            have hxSplit : x = (J.curvePoint A.splitAngle : Plane) := by
              have hxInter : x ∈ A.leftChild.curveArcPlane ∩
                  A.rightChild.curveArcPlane := ⟨hxLeftArc, hxRightArc⟩
              rw [A.leftChild_inter_rightChild_curveArcPlane] at hxInter
              exact mem_singleton_iff.mp hxInter
            have hparentMem :
                (J.curvePoint A.rightChild.left : Plane) ∈
                  (A.rightChild.descendant bs).curveArcPlane := by
              simpa using hxSplit ▸ hxArc
            have hleft := A.rightChild.descendant_left_eq_of_parentLeft_mem
              bs hparentMem
            left
            rw [hxSplit, hleft]
            rfl
          · exact ih A.rightChild hxRight hxArc

end AccessibleAngularArc

namespace InitialAngularArcs

variable {J : JordanCircle}

/-- The two initial angular arcs meet precisely at their common and closing
endpoints. -/
theorem first_inter_second_curveArcPlane (I : J.InitialAngularArcs) :
    I.first.curveArcPlane ∩ I.second.curveArcPlane =
      {(J.curvePoint I.first.left : Plane),
        (J.curvePoint I.first.right : Plane)} := by
  ext x
  constructor
  · rintro ⟨⟨ys, ⟨s, hs, rfl⟩, hxs⟩,
      ⟨yt, ⟨t, ht, rfl⟩, hxt⟩⟩
    have hcurve : J.curvePoint s = J.curvePoint t := by
      apply Subtype.ext
      exact hxs.trans hxt.symm
    have hparam : JordanCurve.Arcs.param s = JordanCurve.Arcs.param t :=
      J.carrierHomeomorph.injective hcurve
    obtain ⟨m, hm⟩ := JordanCurve.Arcs.param_eq_iff.mp hparam
    have hp : (0 : ℝ) < 2 * π := by positivity
    have heq : s - t = (m : ℝ) * (2 * π) := by
      linarith
    have hmUpper : (m : ℝ) ≤ 0 := by
      have hmul : (m : ℝ) * (2 * π) ≤ 0 * (2 * π) := by
        rw [zero_mul, ← heq]
        linarith [hs.2, ht.1, I.adjacent]
      exact le_of_mul_le_mul_right hmul hp
    have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by
      have hmul : (-1 : ℝ) * (2 * π) ≤ (m : ℝ) * (2 * π) := by
        rw [neg_one_mul, ← heq]
        linarith [hs.1, ht.2, I.closes]
      exact le_of_mul_le_mul_right hmul hp
    have hmCases : m = 0 ∨ m = -1 := by
      have hmUpper' : m ≤ (0 : ℤ) := by exact_mod_cast hmUpper
      have hmLower' : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
      omega
    rcases hmCases with hmZero | hmNeg
    · right
      have hst : s = t := by
        rw [hmZero] at hm
        push_cast at hm
        linarith
      have hsRight : s = I.first.right := by
        apply le_antisymm hs.2
        rw [hst, I.adjacent]
        exact ht.1
      exact mem_singleton_iff.mpr (hxs.symm.trans
        (congrArg Subtype.val <| congrArg J.curvePoint hsRight))
    · left
      have hst : s = t - 2 * π := by
        rw [hmNeg] at hm
        push_cast at hm
        linarith
      have hsLeft : s = I.first.left := by
        apply le_antisymm
        · have htUpper : t ≤ I.first.left + 2 * π := by
            rw [← I.closes]
            exact ht.2
          rw [hst]
          linarith
        · exact hs.1
      exact hxs.symm.trans (congrArg Subtype.val <|
        congrArg J.curvePoint hsLeft)
  · intro hx
    rw [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨I.first.left_mem_curveArcPlane, ?_⟩
      have hperiodic : J.curvePoint I.second.right =
          J.curvePoint I.first.left := by
        change J.carrierHomeomorph
            (JordanCurve.Arcs.param I.second.right) =
          J.carrierHomeomorph (JordanCurve.Arcs.param I.first.left)
        rw [I.closes, JordanCurve.Arcs.param_periodic]
      exact hperiodic ▸ I.second.right_mem_curveArcPlane
    · refine ⟨I.first.right_mem_curveArcPlane, ?_⟩
      simpa [I.adjacent] using I.second.left_mem_curveArcPlane

/-- At a complete level, an arc contains no retained mark except its two
endpoints. -/
theorem generationMark_mem_levelArc_eq_endpoint
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    {x : Plane} (hxGen : x ∈ I.generationMarks n)
    (hxArc : x ∈ (I.levelArc a).curveArcPlane) :
    x = (J.curvePoint (I.levelArc a).left : Plane) ∨
      x = (J.curvePoint (I.levelArc a).right : Plane) := by
  rw [generationMarks, Finset.mem_union] at hxGen
  cases hroot : a.1 with
  | false =>
      simp only [levelArc, rootArc, hroot] at hxArc ⊢
      rcases hxGen with hxFirst | hxSecond
      · have hxFirst' : x ∈
            I.first.generationMarks (List.ofFn a.2).length := by
          simpa using hxFirst
        exact I.first.generationMark_mem_descendant_eq_endpoint
          (List.ofFn a.2) hxFirst' hxArc
      · have hxFirstArc : x ∈ I.first.curveArcPlane :=
          (I.first.descendant_curveArcPlane_subset (List.ofFn a.2)) hxArc
        have hxSecondArc : x ∈ I.second.curveArcPlane :=
          I.second.generationMarks_subset_curveArcPlane n hxSecond
        have hxEnds : x = (J.curvePoint I.first.left : Plane) ∨
            x = (J.curvePoint I.first.right : Plane) := by
          have hxInter : x ∈ I.first.curveArcPlane ∩ I.second.curveArcPlane :=
            ⟨hxFirstArc, hxSecondArc⟩
          rw [I.first_inter_second_curveArcPlane] at hxInter
          simpa only [mem_insert_iff, mem_singleton_iff] using hxInter
        rcases hxEnds with hxLeft | hxRight
        · left
          have hmem : (J.curvePoint I.first.left : Plane) ∈
              (I.first.descendant (List.ofFn a.2)).curveArcPlane := by
            simpa [hxLeft] using hxArc
          have hleft := I.first.descendant_left_eq_of_parentLeft_mem
            (List.ofFn a.2) hmem
          rw [hxLeft, hleft]
        · right
          have hmem : (J.curvePoint I.first.right : Plane) ∈
              (I.first.descendant (List.ofFn a.2)).curveArcPlane := by
            simpa [hxRight] using hxArc
          have hright := I.first.descendant_right_eq_of_parentRight_mem
            (List.ofFn a.2) hmem
          rw [hxRight, hright]
  | true =>
      simp only [levelArc, rootArc, hroot] at hxArc ⊢
      rcases hxGen with hxFirst | hxSecond
      · have hxFirstArc : x ∈ I.first.curveArcPlane :=
          I.first.generationMarks_subset_curveArcPlane n hxFirst
        have hxSecondArc : x ∈ I.second.curveArcPlane :=
          (I.second.descendant_curveArcPlane_subset (List.ofFn a.2)) hxArc
        have hxEnds : x = (J.curvePoint I.first.left : Plane) ∨
            x = (J.curvePoint I.first.right : Plane) := by
          have hxInter : x ∈ I.first.curveArcPlane ∩ I.second.curveArcPlane :=
            ⟨hxFirstArc, hxSecondArc⟩
          rw [I.first_inter_second_curveArcPlane] at hxInter
          simpa only [mem_insert_iff, mem_singleton_iff] using hxInter
        rcases hxEnds with hxClose | hxShared
        · right
          have hperiodic :
              (J.curvePoint I.first.left : Plane) =
                (J.curvePoint I.second.right : Plane) := by
            apply congrArg Subtype.val
            change J.carrierHomeomorph
                (JordanCurve.Arcs.param I.first.left) =
              J.carrierHomeomorph (JordanCurve.Arcs.param I.second.right)
            rw [I.closes, JordanCurve.Arcs.param_periodic]
          have hmem : (J.curvePoint I.second.right : Plane) ∈
              (I.second.descendant (List.ofFn a.2)).curveArcPlane := by
            rw [← hperiodic, ← hxClose]
            exact hxArc
          have hright := I.second.descendant_right_eq_of_parentRight_mem
            (List.ofFn a.2) hmem
          rw [hxClose, hperiodic, hright]
        · left
          have hshared :
              (J.curvePoint I.first.right : Plane) =
                (J.curvePoint I.second.left : Plane) := by
            rw [← I.adjacent]
          have hmem : (J.curvePoint I.second.left : Plane) ∈
              (I.second.descendant (List.ofFn a.2)).curveArcPlane := by
            rw [← hshared, ← hxShared]
            exact hxArc
          have hleft := I.second.descendant_left_eq_of_parentLeft_mem
            (List.ofFn a.2) hmem
          rw [hxShared, hshared, hleft]
      · exact I.second.generationMark_mem_descendant_eq_endpoint
          (List.ofFn a.2) (by simpa using hxSecond) hxArc

/-- The finite union of retained access hairs whose bases are not endpoints
of the selected elementary level arc. -/
noncomputable def nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) : Set Plane :=
  ⋃ m : I.GenerationMark n,
    if (m.1 : Plane) = (J.curvePoint (I.levelArc a).left : Plane) ∨
        (m.1 : Plane) = (J.curvePoint (I.levelArc a).right : Plane) then
      ∅
    else
      ((I.generationInsideHairFamily n).hair m).carrier

theorem isClosed_nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    IsClosed (I.nonEndpointHairCarrier a) := by
  apply isClosed_iUnion_of_finite
  intro m
  split
  · exact isClosed_empty
  · exact ((I.generationInsideHairFamily n).hair m).isClosed_carrier

/-- A level boundary arc is disjoint from every retained hair not based at
one of its two endpoints. -/
theorem nonEndpointHairCarrier_disjoint_curveArcPlane
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    Disjoint (I.nonEndpointHairCarrier a)
      (I.levelArc a).curveArcPlane := by
  rw [Set.disjoint_left]
  intro x hxHairs hxArc
  rw [nonEndpointHairCarrier, mem_iUnion] at hxHairs
  obtain ⟨m, hm⟩ := hxHairs
  by_cases hmEnd :
      (m.1 : Plane) = (J.curvePoint (I.levelArc a).left : Plane) ∨
        (m.1 : Plane) = (J.curvePoint (I.levelArc a).right : Plane)
  · simp [hmEnd] at hm
  · simp only [if_neg hmEnd] at hm
    rcases ((I.generationInsideHairFamily n).hair m).carrier_subset hm with
      hxInside | hxBase
    · exact (J.inside_subset_compl hxInside)
        ((I.levelArc a).curveArcPlane_subset_carrier J hxArc)
    · have hxm : x = (m.1 : Plane) := mem_singleton_iff.mp hxBase
      have hmArc : (m.1 : Plane) ∈ (I.levelArc a).curveArcPlane := by
        rw [← hxm]
        exact hxArc
      exact hmEnd (I.generationMark_mem_levelArc_eq_endpoint a m.2 hmArc)

theorem curveArcPlane_subset_compl_nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n) :
    (I.levelArc a).curveArcPlane ⊆ (I.nonEndpointHairCarrier a)ᶜ := by
  intro x hxArc hxHair
  exact Set.disjoint_left.mp
    (I.nonEndpointHairCarrier_disjoint_curveArcPlane a) hxHair hxArc

/-- Any retained generation hair whose base is not an endpoint of `a` is one
of the summands of `a`'s nonendpoint-hair carrier. -/
theorem generationHair_carrier_subset_nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a : LevelAddress n)
    (m : I.GenerationMark n)
    (hmLeft : (m.1 : Plane) ≠
      (J.curvePoint (I.levelArc a).left : Plane))
    (hmRight : (m.1 : Plane) ≠
      (J.curvePoint (I.levelArc a).right : Plane)) :
    ((I.generationInsideHairFamily n).hair m).carrier ⊆
      I.nonEndpointHairCarrier a := by
  intro x hx
  rw [nonEndpointHairCarrier, mem_iUnion]
  refine ⟨m, ?_⟩
  simp only [if_neg (not_or_intro hmLeft hmRight)]
  exact hx

theorem levelRightHair_carrier_subset_nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (hLeft :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).left : Plane))
    (hRight :
      (J.curvePoint (I.levelArc a).right : Plane) ≠
        (J.curvePoint (I.levelArc c).right : Plane)) :
    (I.levelRightHair a).carrier ⊆ I.nonEndpointHairCarrier c := by
  exact I.generationHair_carrier_subset_nonEndpointHairCarrier c
    ⟨(J.curvePoint (I.levelArc a).right : Plane),
      I.levelArc_right_mem_generationMarks a⟩ hLeft hRight

theorem levelLeftHair_carrier_subset_nonEndpointHairCarrier
    (I : J.InitialAngularArcs) {n : ℕ} (a c : LevelAddress n)
    (hLeft :
      (J.curvePoint (I.levelArc a).left : Plane) ≠
        (J.curvePoint (I.levelArc c).left : Plane))
    (hRight :
      (J.curvePoint (I.levelArc a).left : Plane) ≠
        (J.curvePoint (I.levelArc c).right : Plane)) :
    (I.levelLeftHair a).carrier ⊆ I.nonEndpointHairCarrier c := by
  exact I.generationHair_carrier_subset_nonEndpointHairCarrier c
    ⟨(J.curvePoint (I.levelArc a).left : Plane),
      I.levelArc_left_mem_generationMarks a⟩ hLeft hRight

end InitialAngularArcs
end JordanCircle

end Schoenflies
