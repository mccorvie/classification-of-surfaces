import Schoenflies.AnnularSeparatorSides
import Schoenflies.JordanRegionRecognition
import Schoenflies.LocalStraightCrossing
import Schoenflies.PlaneTopology

/-!
# Regions of a locally polygonal Jordan theta graph

Suppose two Jordan circles share an arc `B`, close it by the two
complementary arcs `A₀` and `A₁` of an outer Jordan circle, and lie in the
outer closed disk.  If the common arc is locally straight away from finitely
many vertices, the two closed bounded regions exactly fill the outer closed
disk.  This is the crosscut theorem needed by the annular cyclic-order
argument.
-/

namespace Schoenflies

open Metric Set Function Bornology

noncomputable section

namespace JordanThetaRegions

variable {Q K₀ K₁ : JordanCircle} {B A₀ A₁ F : Set Plane}

private theorem inside_disjoint_otherCarrier
    (hK₀ : K₀.carrier ⊆ Q.inside ∪ Q.carrier)
    (hQ : Q.carrier = A₀ ∪ A₁)
    (hcarrier₀ : K₀.carrier = B ∪ A₀)
    (hcarrier₁ : K₁.carrier = B ∪ A₁) :
    Disjoint K₀.inside K₁.carrier := by
  have hboundaryOutside :=
    Q.carrier_sdiff_subset_outside_of_carrier_subset K₀ hK₀
  rw [Set.disjoint_left]
  intro x hxInside hxK₁
  rw [hcarrier₁] at hxK₁
  rcases hxK₁ with hxB | hxA₁
  · apply K₀.inside_subset_compl hxInside
    rw [hcarrier₀]
    exact Or.inl hxB
  · have hxQ : x ∈ Q.carrier := by
      rw [hQ]
      exact Or.inr hxA₁
    by_cases hxK₀ : x ∈ K₀.carrier
    · exact K₀.inside_subset_compl hxInside hxK₀
    · exact Set.disjoint_left.mp K₀.inside_disjoint_outside
        hxInside (hboundaryOutside ⟨hxQ, hxK₀⟩)

private theorem inside_subset_otherOutside
    (hK₀ : K₀.carrier ⊆ Q.inside ∪ Q.carrier)
    (hK₁ : K₁.carrier ⊆ Q.inside ∪ Q.carrier)
    (hQ : Q.carrier = A₀ ∪ A₁)
    (hcarrier₀ : K₀.carrier = B ∪ A₀)
    (hcarrier₁ : K₁.carrier = B ∪ A₁)
    (hA₀ : (A₀ \ K₁.carrier).Nonempty) :
    K₀.inside ⊆ K₁.outside := by
  have hdisjoint : Disjoint K₀.inside K₁.carrier :=
    inside_disjoint_otherCarrier hK₀ hQ hcarrier₀ hcarrier₁
  have hregions : K₀.inside ⊆ K₁.inside ∪ K₁.outside := by
    rw [K₁.inside_union_outside]
    intro x hxInside hxCarrier
    exact Set.disjoint_left.mp hdisjoint hxInside hxCarrier
  rcases K₀.inside_isConnected.isPreconnected.subset_or_subset
      K₁.inside_isOpen K₁.outside_isOpen K₁.inside_disjoint_outside
      hregions with hInside | hOutside
  · obtain ⟨x, hxA₀, hxNotK₁⟩ := hA₀
    have hxQ : x ∈ Q.carrier := by
      rw [hQ]
      exact Or.inl hxA₀
    have hxK₁Outside : x ∈ K₁.outside :=
      Q.carrier_sdiff_subset_outside_of_carrier_subset K₁ hK₁
        ⟨hxQ, hxNotK₁⟩
    have hxClosure : x ∈ closure K₀.inside := by
      rw [K₀.closure_inside, hcarrier₀]
      exact Or.inr (Or.inr hxA₀)
    have hxInterClosure :
        x ∈ closure (K₁.outside ∩ K₀.inside) :=
      K₁.outside_isOpen.inter_closure ⟨hxK₁Outside, hxClosure⟩
    obtain ⟨y, hyK₁Outside, hyK₀Inside⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact False.elim <| Set.disjoint_left.mp K₁.inside_disjoint_outside
      (hInside hyK₀Inside) hyK₁Outside
  · exact hOutside

private theorem closure_inside_regular (K : JordanCircle) :
    closure (interior (closure K.inside)) = closure K.inside := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact interior_maximal subset_closure K.inside_isOpen

private theorem local_shared_arc_mem_interior_union
    (hdisjoint : Disjoint K₀.inside K₁.inside)
    (hcarrier₀ : K₀.carrier = B ∪ A₀)
    {p d : Plane} {r : ℝ} (hr : 0 < r) (hpB : p ∈ B)
    (hlocal₀ : ball p r ∩ K₀.carrier =
      ball p r ∩ determinantLine p d)
    (hlocal₁ : ball p r ∩ K₁.carrier =
      ball p r ∩ determinantLine p d) :
    p ∈ interior (closure K₀.inside ∪ closure K₁.inside) := by
  have hpK₀ : p ∈ K₀.carrier := by
    rw [hcarrier₀]
    exact Or.inl hpB
  have hinsideWitness : (ball p r ∩ K₀.inside).Nonempty := by
    have hpClosure : p ∈ closure K₀.inside := by
      rw [K₀.closure_inside]
      exact Or.inr hpK₀
    obtain ⟨x, hxBall, hxInside⟩ :=
      (_root_.mem_closure_iff.mp hpClosure) (ball p r)
        isOpen_ball (mem_ball_self hr)
    exact ⟨x, hxBall, hxInside⟩
  have sameOrientationImpossible
      (hpos₀ : ball p r ∩ positiveLineSide p d ⊆ K₀.inside)
      (hneg₀ : ball p r ∩ negativeLineSide p d ⊆ K₀.outside)
      (hpos₁ : ball p r ∩ positiveLineSide p d ⊆ K₁.inside)
      (hneg₁ : ball p r ∩ negativeLineSide p d ⊆ K₁.outside) : False := by
    obtain ⟨x, hxBall, hxInside⟩ := hinsideWitness
    have hxNotLine : x ∉ determinantLine p d := by
      intro hxLine
      apply K₀.inside_subset_compl hxInside
      have hx : x ∈ ball p r ∩ determinantLine p d := ⟨hxBall, hxLine⟩
      rw [← hlocal₀] at hx
      exact hx.2
    have hxSides :
        x ∈ positiveLineSide p d ∪ negativeLineSide p d := by
      rw [positiveLineSide_union_negativeLineSide]
      exact hxNotLine
    rcases hxSides with hxPos | hxNeg
    · exact Set.disjoint_left.mp hdisjoint hxInside
        (hpos₁ ⟨hxBall, hxPos⟩)
    · have hxOutside := hneg₀ ⟨hxBall, hxNeg⟩
      exact Set.disjoint_left.mp K₀.inside_disjoint_outside
        hxInside hxOutside
  have sameReverseImpossible
      (hpos₀ : ball p r ∩ positiveLineSide p d ⊆ K₀.outside)
      (hneg₀ : ball p r ∩ negativeLineSide p d ⊆ K₀.inside)
      (hpos₁ : ball p r ∩ positiveLineSide p d ⊆ K₁.outside)
      (hneg₁ : ball p r ∩ negativeLineSide p d ⊆ K₁.inside) : False := by
    obtain ⟨x, hxBall, hxInside⟩ := hinsideWitness
    have hxNotLine : x ∉ determinantLine p d := by
      intro hxLine
      apply K₀.inside_subset_compl hxInside
      have hx : x ∈ ball p r ∩ determinantLine p d := ⟨hxBall, hxLine⟩
      rw [← hlocal₀] at hx
      exact hx.2
    have hxSides :
        x ∈ positiveLineSide p d ∪ negativeLineSide p d := by
      rw [positiveLineSide_union_negativeLineSide]
      exact hxNotLine
    rcases hxSides with hxPos | hxNeg
    · have hxOutside := hpos₀ ⟨hxBall, hxPos⟩
      exact Set.disjoint_left.mp K₀.inside_disjoint_outside
        hxInside hxOutside
    · exact Set.disjoint_left.mp hdisjoint hxInside
        (hneg₁ ⟨hxBall, hxNeg⟩)
  have hball_of_opposite
      (hpos : ball p r ∩ positiveLineSide p d ⊆ K₀.inside)
      (hneg : ball p r ∩ negativeLineSide p d ⊆ K₁.inside) :
      ball p r ⊆ closure K₀.inside ∪ closure K₁.inside := by
    intro x hxBall
    by_cases hxLine : x ∈ determinantLine p d
    · left
      rw [K₀.closure_inside]
      right
      have hx : x ∈ ball p r ∩ determinantLine p d := ⟨hxBall, hxLine⟩
      rw [← hlocal₀] at hx
      exact hx.2
    · have hxSides :
          x ∈ positiveLineSide p d ∪ negativeLineSide p d := by
        rw [positiveLineSide_union_negativeLineSide]
        exact hxLine
      rcases hxSides with hxPos | hxNeg
      · exact Or.inl (subset_closure (hpos ⟨hxBall, hxPos⟩))
      · exact Or.inr (subset_closure (hneg ⟨hxBall, hxNeg⟩))
  have hball_of_opposite'
      (hneg : ball p r ∩ negativeLineSide p d ⊆ K₀.inside)
      (hpos : ball p r ∩ positiveLineSide p d ⊆ K₁.inside) :
      ball p r ⊆ closure K₀.inside ∪ closure K₁.inside := by
    intro x hxBall
    by_cases hxLine : x ∈ determinantLine p d
    · left
      rw [K₀.closure_inside]
      right
      have hx : x ∈ ball p r ∩ determinantLine p d := ⟨hxBall, hxLine⟩
      rw [← hlocal₀] at hx
      exact hx.2
    · have hxSides :
          x ∈ positiveLineSide p d ∪ negativeLineSide p d := by
        rw [positiveLineSide_union_negativeLineSide]
        exact hxLine
      rcases hxSides with hxPos | hxNeg
      · exact Or.inr (subset_closure (hpos ⟨hxBall, hxPos⟩))
      · exact Or.inl (subset_closure (hneg ⟨hxBall, hxNeg⟩))
  rcases K₀.local_lineSide_dichotomy hr hpK₀ hlocal₀ with h₀ | h₀ <;>
    rcases K₁.local_lineSide_dichotomy hr
      (by
        have : p ∈ ball p r ∩ determinantLine p d :=
          ⟨mem_ball_self hr, by simp [determinantLine, planeDet]⟩
        rw [← hlocal₁] at this
        exact this.2)
      hlocal₁ with h₁ | h₁
  · exact (sameOrientationImpossible h₀.1 h₀.2 h₁.1 h₁.2).elim
  · exact mem_interior.mpr
      ⟨ball p r, hball_of_opposite h₀.1 h₁.2,
        isOpen_ball, mem_ball_self hr⟩
  · exact mem_interior.mpr
      ⟨ball p r, hball_of_opposite' h₀.2 h₁.1,
        isOpen_ball, mem_ball_self hr⟩
  · exact (sameReverseImpossible h₀.1 h₀.2 h₁.1 h₁.2).elim

/-- The two closed bounded regions of a locally polygonal theta graph fill
the closed bounded region of its outer Jordan circle. -/
theorem closure_inside_eq_union
    (hK₀ : K₀.carrier ⊆ Q.inside ∪ Q.carrier)
    (hK₁ : K₁.carrier ⊆ Q.inside ∪ Q.carrier)
    (hQ : Q.carrier = A₀ ∪ A₁)
    (hcarrier₀ : K₀.carrier = B ∪ A₀)
    (hcarrier₁ : K₁.carrier = B ∪ A₁)
    (hA₀ : (A₀ \ K₁.carrier).Nonempty)
    (hA₁ : (A₁ \ K₀.carrier).Nonempty)
    (hF : F.Finite)
    (hlocal : ∀ p ∈ B \ F, ∃ d : Plane, ∃ r : ℝ, 0 < r ∧
      ball p r ∩ K₀.carrier = ball p r ∩ determinantLine p d ∧
      ball p r ∩ K₁.carrier = ball p r ∩ determinantLine p d) :
    closure Q.inside = closure K₀.inside ∪ closure K₁.inside := by
  have hK₀Other : K₀.inside ⊆ K₁.outside :=
    inside_subset_otherOutside hK₀ hK₁ hQ hcarrier₀ hcarrier₁ hA₀
  have hK₁Other : K₁.inside ⊆ K₀.outside :=
    inside_subset_otherOutside (K₀ := K₁) (K₁ := K₀)
      (A₀ := A₁) (A₁ := A₀) hK₁ hK₀
      (by rw [hQ, Set.union_comm]) hcarrier₁ hcarrier₀ hA₁
  have hdisjoint : Disjoint K₀.inside K₁.inside := by
    rw [Set.disjoint_left]
    intro x hx₀ hx₁
    exact Set.disjoint_left.mp K₁.inside_disjoint_outside
      hx₁ (hK₀Other hx₀)
  let S : Set Plane := closure K₀.inside ∪ closure K₁.inside
  have hSclosed : IsClosed S := isClosed_closure.union isClosed_closure
  have hScompact : IsCompact S :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      K₀.inside_bounded.closure).union
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure
        K₁.inside_bounded.closure)
  have hSregular : closure (interior S) = S := by
    apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hSclosed
    · rintro x (hx₀ | hx₁)
      · rw [← closure_inside_regular K₀] at hx₀
        exact closure_mono (interior_mono Set.subset_union_left) hx₀
      · rw [← closure_inside_regular K₁] at hx₁
        exact closure_mono (interior_mono Set.subset_union_right) hx₁
  have hSsubset : S ⊆ closure Q.inside := by
    apply Set.union_subset <;> apply closure_mono
    · exact Q.inside_subset_inside_of_carrier_subset K₀ hK₀
    · exact Q.inside_subset_inside_of_carrier_subset K₁ hK₁
  have hfrontierBasic : frontier S ⊆ K₀.carrier ∪ K₁.carrier :=
    (frontier_union_subset _ _).trans <|
      Set.union_subset
        (Set.inter_subset_left.trans <|
          (frontier_closure_subset.trans <| by rw [K₀.frontier_inside]).trans
            Set.subset_union_left)
        (Set.inter_subset_right.trans <|
          (frontier_closure_subset.trans <| by rw [K₁.frontier_inside]).trans
            Set.subset_union_right)
  have hfrontierCarrierOrFinite : frontier S ⊆ Q.carrier ∪ F := by
    intro x hxFrontier
    have hxBasic := hfrontierBasic hxFrontier
    rcases hxBasic with hxK₀ | hxK₁
    · rw [hcarrier₀] at hxK₀
      rcases hxK₀ with hxB | hxA₀
      · by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · obtain ⟨d, r, hr, hlocal₀, hlocal₁⟩ := hlocal x ⟨hxB, hxF⟩
          have hxInterior := local_shared_arc_mem_interior_union
              hdisjoint hcarrier₀ hr hxB hlocal₀ hlocal₁
          exact False.elim <| Set.disjoint_left.mp
            disjoint_interior_frontier hxInterior hxFrontier
      · left
        rw [hQ]
        exact Or.inl hxA₀
    · rw [hcarrier₁] at hxK₁
      rcases hxK₁ with hxB | hxA₁
      · by_cases hxF : x ∈ F
        · exact Or.inr hxF
        · obtain ⟨d, r, hr, hlocal₀, hlocal₁⟩ := hlocal x ⟨hxB, hxF⟩
          have hxInterior := local_shared_arc_mem_interior_union
            hdisjoint hcarrier₀ hr hxB hlocal₀ hlocal₁
          exact False.elim <| Set.disjoint_left.mp
            disjoint_interior_frontier hxInterior hxFrontier
      · left
        rw [hQ]
        exact Or.inr hxA₁
  have hfrontierSubset : frontier S ⊆ Q.carrier := by
    have hQclosed : IsClosed Q.carrier :=
      (isCompact_range Q.continuous).isClosed
    intro x hxFrontier
    apply closure_minimal _ hQclosed <|
      frontier_subset_closure_sdiff_finite_of_regularClosed
        hSclosed hSregular hF hxFrontier
    rintro y ⟨hyFrontier, hyNotF⟩
    rcases hfrontierCarrierOrFinite hyFrontier with hyQ | hyF
    · exact hyQ
    · exact False.elim (hyNotF hyF)
  have hcarrierSubset : Q.carrier ⊆ frontier S := by
    intro x hxQ
    have hxS : x ∈ S := by
      rw [hQ] at hxQ
      rcases hxQ with hxA₀ | hxA₁
      · left
        rw [K₀.closure_inside, hcarrier₀]
        exact Or.inr (Or.inr hxA₀)
      · right
        rw [K₁.closure_inside, hcarrier₁]
        exact Or.inr (Or.inr hxA₁)
    have hOutsideCompl : Q.outside ⊆ Sᶜ := by
      intro y hyOutside hyS
      have hyClosure := hSsubset hyS
      rw [Q.closure_inside] at hyClosure
      rcases hyClosure with hyInside | hyCarrier
      · exact Set.disjoint_left.mp Q.inside_disjoint_outside
          hyInside hyOutside
      · exact Q.outside_subset_compl hyOutside hyCarrier
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hxS, ?_⟩
    apply closure_mono hOutsideCompl
    apply frontier_subset_closure
    rw [Q.frontier_outside]
    exact hxQ
  have hfrontier : frontier S = Q.carrier :=
    Set.Subset.antisymm hfrontierSubset hcarrierSubset
  have hinterior : (interior S).Nonempty := by
    refine ⟨K₀.insidePoint, ?_⟩
    apply interior_maximal _ K₀.inside_isOpen K₀.insidePoint_mem_inside
    exact subset_closure.trans Set.subset_union_left
  have hrecognized : S = closure Q.inside :=
    Q.eq_closure_inside_of_isCompact_frontier_eq
      hScompact hfrontier hinterior
  exact hrecognized.symm

end JordanThetaRegions

end

end Schoenflies
