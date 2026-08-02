import Schoenflies.BoundaryPathTransport

/-!
# Rigidity of complementary arcs on a Jordan circle

A Jordan circle has exactly two point-set arcs between two distinct points.
Consequently, two `TwoBoundaryArcPaths` presentations with the same endpoints
agree on their two ranges, up to swapping the complementary arcs.  This is
the point-set fact needed to compare independently chosen finite collar
cells.
-/

namespace Schoenflies

open Set Function

noncomputable section

namespace Path

/-- An injective path contained in the range of another injective path, with
the same ordered endpoints, has the same range. -/
theorem range_eq_of_subset_range {x y : Plane}
    (p q : Path x y) (_hp : Injective p) (hq : Injective q)
    (hsub : range p ⊆ range q) :
    range p = range q := by
  let toRange : unitInterval → range q := fun t => ⟨q t, ⟨t, rfl⟩⟩
  have htoRangeContinuous : Continuous toRange :=
    q.continuous.subtype_mk _
  have htoRangeBijective : Function.Bijective toRange := by
    constructor
    · intro s t hst
      apply hq
      exact congrArg Subtype.val hst
    · rintro ⟨z, t, rfl⟩
      exact ⟨t, rfl⟩
  let e₀ : unitInterval ≃ range q :=
    Equiv.ofBijective toRange htoRangeBijective
  let e : unitInterval ≃ₜ range q :=
    Continuous.homeoOfEquivCompactToT2 (f := e₀) htoRangeContinuous
  let f : unitInterval → unitInterval := fun t =>
    e.symm ⟨p t, hsub ⟨t, rfl⟩⟩
  have he (t : unitInterval) : (e t : Plane) = q t := rfl
  have hef (t : unitInterval) : (e (f t) : Plane) = p t := by
    exact congrArg Subtype.val <|
      e.apply_symm_apply ⟨p t, hsub ⟨t, rfl⟩⟩
  have hf : Continuous f := by
    exact e.symm.continuous.comp <| p.continuous.subtype_mk _
  have hf_zero : f 0 = 0 := by
    apply e.injective
    apply Subtype.ext
    rw [hef, he, p.source, q.source]
  have hf_one : f 1 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [hef, he, p.target, q.target]
  apply Set.Subset.antisymm hsub
  rintro z ⟨t, rfl⟩
  have hpreconnected : IsPreconnected (range f) :=
    by simpa only [Set.image_univ] using
      isPreconnected_univ.image f hf.continuousOn
  have ht : t ∈ range f := by
    apply hpreconnected.Icc_subset
        (show (0 : unitInterval) ∈ range f by
          exact ⟨0, hf_zero⟩)
        (show (1 : unitInterval) ∈ range f by
          exact ⟨1, hf_one⟩)
    exact t.2
  obtain ⟨s, hs⟩ := ht
  refine ⟨s, ?_⟩
  have hes : e (f s) = e t := congrArg e hs
  exact (hef s).symm.trans <| (congrArg Subtype.val hes).trans (he t)

end Path

namespace JordanCircle.TwoBoundaryArcPaths

variable {J : JordanCircle} {x y : Plane}

private theorem interiorImage_disjoint_endpoints
    (p : Path x y) (hp : Injective p) :
    Disjoint (p '' Set.Ioo (0 : unitInterval) 1) ({x, y} : Set Plane) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t, ht, rfl⟩ (hzx | hzy)
  · have ht0 : t = 0 := hp (by simpa only [p.source] using hzx)
    exact (ne_of_gt ht.1) ht0
  · rw [Set.mem_singleton_iff] at hzy
    have ht1 : t = 1 := hp (by simpa only [p.target] using hzy)
    exact (ne_of_lt ht.2) ht1

private theorem range_subset_of_interiorImage_subset
    (p : Path x y) {A : Set Plane}
    (hx : x ∈ A) (hy : y ∈ A)
    (hinter : p '' Set.Ioo (0 : unitInterval) 1 ⊆ A) :
    range p ⊆ A := by
  rintro z ⟨t, rfl⟩
  by_cases ht0 : t = 0
  · subst t
    simpa only [p.source] using hx
  by_cases ht1 : t = 1
  · subst t
    simpa only [p.target] using hy
  exact hinter ⟨t, ⟨bot_lt_iff_ne_bot.mpr ht0,
    lt_top_iff_ne_top.mpr ht1⟩, rfl⟩

private theorem first_sdiff_second_nonempty
    (S : J.TwoBoundaryArcPaths x y) :
    (range S.first \ range S.second).Nonempty := by
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  refine ⟨S.first t, ⟨t, rfl⟩, ?_⟩
  intro htSecond
  have htEnds : S.first t ∈ ({x, y} : Set Plane) := by
    rw [← S.overlap]
    exact ⟨⟨t, rfl⟩, htSecond⟩
  rcases htEnds with htx | hty
  · have ht0 : t = 0 := S.first_injective
      (by simpa only [S.first.source] using htx)
    have hval := congrArg Subtype.val ht0
    norm_num [t] at hval
  · rw [Set.mem_singleton_iff] at hty
    have ht1 : t = 1 := S.first_injective
      (by simpa only [S.first.target] using hty)
    have hval := congrArg Subtype.val ht1
    norm_num [t] at hval

private theorem second_sdiff_first_nonempty
    (S : J.TwoBoundaryArcPaths x y) :
    (range S.second \ range S.first).Nonempty := by
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  refine ⟨S.second t, ⟨t, rfl⟩, ?_⟩
  intro htFirst
  have htEnds : S.second t ∈ ({x, y} : Set Plane) := by
    rw [← S.overlap]
    exact ⟨htFirst, ⟨t, rfl⟩⟩
  rcases htEnds with htx | hty
  · have ht1 : t = 1 := S.second_injective
      (by simpa only [S.second.target] using htx)
    have hval := congrArg Subtype.val ht1
    norm_num [t] at hval
  · rw [Set.mem_singleton_iff] at hty
    have ht0 : t = 0 := S.second_injective
      (by simpa only [S.second.source] using hty)
    have hval := congrArg Subtype.val ht0
    norm_num [t] at hval

/-- An arc in the Jordan carrier whose open parameter interval avoids the
two splitting endpoints must lie wholly on one side of the split. -/
theorem range_subset_first_or_second_of_interior_disjoint
    (S : J.TwoBoundaryArcPaths x y) {u v : Plane} (p : Path u v)
    (hcarrier : range p ⊆ J.carrier)
    (havoid : Disjoint (p '' Set.Ioo (0 : unitInterval) 1)
      ({x, y} : Set Plane)) :
    range p ⊆ range S.first ∨ range p ⊆ range S.second := by
  have hpreconnected :
      IsPreconnected (p '' Set.Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image p p.continuous.continuousOn
  have hcover : p '' Set.Ioo (0 : unitInterval) 1 ⊆
      range S.first ∪ range S.second := by
    rw [S.cover]
    rintro z ⟨t, ht, rfl⟩
    exact hcarrier ⟨t, rfl⟩
  have hclosedFirst : IsClosed (range S.first) :=
    (isCompact_range S.first.continuous).isClosed
  have hclosedSecond : IsClosed (range S.second) :=
    (isCompact_range S.second.continuous).isClosed
  have hinterCases := isPreconnected_iff_subset_of_disjoint_closed.mp
    hpreconnected (range S.first) (range S.second)
      hclosedFirst hclosedSecond hcover (by
        rw [S.overlap]
        exact Set.disjoint_iff_inter_eq_empty.mp havoid)
  have hdense : Dense (Set.Ioo (0 : unitInterval) 1) := by
    rw [dense_iff_closure_eq, closure_Ioo (by norm_num :
      (0 : unitInterval) ≠ 1)]
    exact Set.Icc_bot_top
  rcases hinterCases with hfirst | hsecond
  · exact Or.inl <| (p.continuous.range_subset_closure_image_dense hdense).trans
      (closure_minimal hfirst hclosedFirst)
  · exact Or.inr <| (p.continuous.range_subset_closure_image_dense hdense).trans
      (closure_minimal hsecond hclosedSecond)

/-- An injective path in a Jordan carrier between the splitting endpoints
is exactly one of the two complementary boundary arcs. -/
theorem range_eq_first_or_second_of_path
    (S : J.TwoBoundaryArcPaths x y) (p : Path x y)
    (hp : Injective p) (hcarrier : range p ⊆ J.carrier) :
    range p = range S.first ∨ range p = range S.second := by
  have havoid : Disjoint
      (p '' Set.Ioo (0 : unitInterval) 1) ({x, y} : Set Plane) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ (hzx | hzy)
    · have ht0 : t = 0 := hp (by simpa only [p.source] using hzx)
      exact (ne_of_gt ht.1) ht0
    · rw [Set.mem_singleton_iff] at hzy
      have ht1 : t = 1 := hp (by simpa only [p.target] using hzy)
      exact (ne_of_lt ht.2) ht1
  rcases S.range_subset_first_or_second_of_interior_disjoint
      p hcarrier havoid with hfirst | hsecond
  · exact Or.inl (Path.range_eq_of_subset_range
      p S.first hp S.first_injective hfirst)
  · exact Or.inr (Path.range_eq_of_subset_range
      p S.second.symm hp
        (S.second_injective.comp unitInterval.symm_bijective.injective)
        (by simpa only [Path.symm_range] using hsecond) |>.trans
          (Path.symm_range S.second))

/-- Endpoint-free arcs indexed by one cyclic successor relation overlap only
at their labelled endpoints.  No relationship between that successor and a
separately chosen parametrization of the Jordan circle is required. -/
theorem successorSplitFamily_first_inter_subset_endpoints
    {iota : Type*} (point : iota → Plane) (hpoint : Injective point)
    (next : iota → iota) (hnextInjective : Injective next)
    (hnextNext : ∀ a, next (next a) ≠ a)
    (T : ∀ a : iota, J.TwoBoundaryArcPaths (point a) (point (next a)))
    (hother : ∀ a c : iota, c ≠ a → c ≠ next a →
      point c ∈ range (T a).second)
    {a b : iota} (hab : a ≠ b) :
    range (T a).first ∩ range (T b).first ⊆
      ({point a, point (next a)} : Set Plane) := by
  have hpointMem (q c : iota) :
      point c ∈ range (T q).first ↔ c = q ∨ c = next q := by
    constructor
    · intro hc
      by_cases hcq : c = q
      · exact Or.inl hcq
      by_cases hcnext : c = next q
      · exact Or.inr hcnext
      have hcEnds : point c ∈ ({point q, point (next q)} : Set Plane) := by
        rw [← (T q).overlap]
        exact ⟨hc, hother q c hcq hcnext⟩
      rcases hcEnds with h | h
      · exact False.elim (hcq (hpoint h))
      · exact False.elim
          (hcnext (hpoint (Set.mem_singleton_iff.mp h)))
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
      ({point a, point (next a)} : Set Plane) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ (hza | hza)
    · rcases (hpointMem b a).mp ⟨t, hza⟩ with hab' | hab'
      · have ht0 : t = 0 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.source, hab'] using hza)
        exact (ne_of_gt ht.1) ht0
      · have ht1 : t = 1 := Sb.first_injective (by
          simpa only [Sa, Sb, Sb.first.target, hab'] using hza)
        exact (ne_of_lt ht.2) ht1
    · rw [Set.mem_singleton_iff] at hza
      rcases (hpointMem b (next a)).mp ⟨t, hza⟩ with hlabel | hlabel
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
    by_cases hbnext : b = next a
    · have hnextNotA : next b ≠ a := by
        rw [hbnext]
        exact hnextNext a
      have hnextNotNext : next b ≠ next a := by
        intro h
        exact hab (hnextInjective h).symm
      have hnotMem : point (next b) ∉ range Sa.first :=
        fun h => (not_or_intro hnextNotA hnextNotNext)
          ((hpointMem a (next b)).mp h)
      exact hnotMem <| hsub <| Path.target_mem_range Sb.first
    · have hbNotA : b ≠ a := hab.symm
      have hnotMem : point b ∉ range Sa.first :=
        fun h => (not_or_intro hbNotA hbnext) ((hpointMem a b).mp h)
      exact hnotMem <| hsub <| Path.source_mem_range Sb.first
  have hSbSecond : range Sb.first ⊆ range Sa.second :=
    hside.resolve_left hnotFirst
  intro z hz
  change z ∈ range Sa.first ∩ range Sb.first at hz
  rw [← Sa.overlap]
  exact ⟨hz.1, hSbSecond hz.2⟩

/-- Two complementary-arc presentations with the same distinct endpoints
have the same two point-set arcs, possibly in the opposite order. -/
theorem range_pair_eq_or_swap
    (S T : J.TwoBoundaryArcPaths x y) :
    (range T.first = range S.first ∧
        range T.second = range S.second) ∨
      (range T.first = range S.second ∧
        range T.second = range S.first) := by
  let A := range S.first
  let B := range S.second
  have hAclosed : IsClosed A :=
    (isCompact_range S.first.continuous).isClosed
  have hBclosed : IsClosed B :=
    (isCompact_range S.second.continuous).isClosed
  have hcover : A ∪ B = J.carrier := S.cover
  have hoverlap : A ∩ B = ({x, y} : Set Plane) := S.overlap
  have hTfirstCarrier : range T.first ⊆ J.carrier :=
    T.first_range_subset_carrier
  have hTsecondCarrier : range T.second ⊆ J.carrier :=
    T.second_range_subset_carrier
  have hfirstPreconnected :
      IsPreconnected (T.first '' Set.Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image T.first T.first.continuous.continuousOn
  have hfirstCover :
      T.first '' Set.Ioo (0 : unitInterval) 1 ⊆ A ∪ B := by
    rw [hcover]
    rintro z ⟨t, ht, rfl⟩
    exact hTfirstCarrier ⟨t, rfl⟩
  have hfirstDisjoint : Disjoint
      (T.first '' Set.Ioo (0 : unitInterval) 1) (A ∩ B) := by
    rw [hoverlap]
    exact interiorImage_disjoint_endpoints T.first T.first_injective
  have hfirstCases :
      T.first '' Set.Ioo (0 : unitInterval) 1 ⊆ A ∨
        T.first '' Set.Ioo (0 : unitInterval) 1 ⊆ B :=
    isPreconnected_iff_subset_of_disjoint_closed.mp
      hfirstPreconnected A B hAclosed hBclosed hfirstCover
        (Set.disjoint_iff_inter_eq_empty.mp hfirstDisjoint)
  have hsecondPreconnected :
      IsPreconnected (T.second '' Set.Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image T.second T.second.continuous.continuousOn
  have hsecondCover :
      T.second '' Set.Ioo (0 : unitInterval) 1 ⊆ A ∪ B := by
    rw [hcover]
    rintro z ⟨t, ht, rfl⟩
    exact hTsecondCarrier ⟨t, rfl⟩
  have hsecondDisjoint : Disjoint
      (T.second '' Set.Ioo (0 : unitInterval) 1) (A ∩ B) := by
    rw [hoverlap, Set.pair_comm]
    exact interiorImage_disjoint_endpoints T.second T.second_injective
  have hsecondCases :
      T.second '' Set.Ioo (0 : unitInterval) 1 ⊆ A ∨
        T.second '' Set.Ioo (0 : unitInterval) 1 ⊆ B :=
    isPreconnected_iff_subset_of_disjoint_closed.mp
      hsecondPreconnected A B hAclosed hBclosed hsecondCover
        (Set.disjoint_iff_inter_eq_empty.mp hsecondDisjoint)
  have hxA : x ∈ A := Path.source_mem_range S.first
  have hyA : y ∈ A := Path.target_mem_range S.first
  have hxB : x ∈ B := Path.target_mem_range S.second
  have hyB : y ∈ B := Path.source_mem_range S.second
  have hsplit {z : Plane} (hz : z ∈ J.carrier) :
      z ∈ range T.first ∨ z ∈ range T.second := by
    rw [← T.cover] at hz
    exact hz
  rcases hfirstCases with hfirstA | hfirstB
  · have hTfirstA : range T.first ⊆ A :=
      range_subset_of_interiorImage_subset T.first hxA hyA hfirstA
    rcases hsecondCases with hsecondA | hsecondB
    · exfalso
      have hTsecondA : range T.second ⊆ A :=
        range_subset_of_interiorImage_subset T.second hyA hxA hsecondA
      obtain ⟨z, hzB, hzNotA⟩ := second_sdiff_first_nonempty S
      rcases hsplit (by rw [← hcover]; exact Or.inr hzB) with hzT | hzT
      · exact hzNotA (hTfirstA hzT)
      · exact hzNotA (hTsecondA hzT)
    · have hTsecondB : range T.second ⊆ B :=
        range_subset_of_interiorImage_subset T.second hyB hxB hsecondB
      left
      constructor
      · apply Set.Subset.antisymm hTfirstA
        intro z hzA
        rcases hsplit (by rw [← hcover]; exact Or.inl hzA) with hzT | hzT
        · exact hzT
        · have hzEnds : z ∈ ({x, y} : Set Plane) := by
            rw [← hoverlap]
            exact ⟨hzA, hTsecondB hzT⟩
          rcases hzEnds with rfl | rfl
          · exact Path.source_mem_range T.first
          · exact Path.target_mem_range T.first
      · apply Set.Subset.antisymm hTsecondB
        intro z hzB
        rcases hsplit (by rw [← hcover]; exact Or.inr hzB) with hzT | hzT
        · have hzEnds : z ∈ ({x, y} : Set Plane) := by
            rw [← hoverlap]
            exact ⟨hTfirstA hzT, hzB⟩
          rcases hzEnds with rfl | rfl
          · exact Path.target_mem_range T.second
          · exact Path.source_mem_range T.second
        · exact hzT
  · have hTfirstB : range T.first ⊆ B :=
      range_subset_of_interiorImage_subset T.first hxB hyB hfirstB
    rcases hsecondCases with hsecondA | hsecondB
    · have hTsecondA : range T.second ⊆ A :=
        range_subset_of_interiorImage_subset T.second hyA hxA hsecondA
      right
      constructor
      · apply Set.Subset.antisymm hTfirstB
        intro z hzB
        rcases hsplit (by rw [← hcover]; exact Or.inr hzB) with hzT | hzT
        · exact hzT
        · have hzEnds : z ∈ ({x, y} : Set Plane) := by
            rw [← hoverlap]
            exact ⟨hTsecondA hzT, hzB⟩
          rcases hzEnds with rfl | rfl
          · exact Path.source_mem_range T.first
          · exact Path.target_mem_range T.first
      · apply Set.Subset.antisymm hTsecondA
        intro z hzA
        rcases hsplit (by rw [← hcover]; exact Or.inl hzA) with hzT | hzT
        · have hzEnds : z ∈ ({x, y} : Set Plane) := by
            rw [← hoverlap]
            exact ⟨hzA, hTfirstB hzT⟩
          rcases hzEnds with rfl | rfl
          · exact Path.target_mem_range T.second
          · exact Path.source_mem_range T.second
        · exact hzT
    · exfalso
      have hTsecondB : range T.second ⊆ B :=
        range_subset_of_interiorImage_subset T.second hyB hxB hsecondB
      obtain ⟨z, hzA, hzNotB⟩ := first_sdiff_second_nonempty S
      rcases hsplit (by rw [← hcover]; exact Or.inl hzA) with hzT | hzT
      · exact hzNotB (hTfirstB hzT)
      · exact hzNotB (hTsecondB hzT)

end JordanCircle.TwoBoundaryArcPaths

end

end Schoenflies
