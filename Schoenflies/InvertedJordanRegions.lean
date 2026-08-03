import Schoenflies.InsideBoundaryExtension
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Inverting the unbounded Jordan region

Inversion about a point of the bounded component sends the unbounded
component, with the point at infinity filled in, to the bounded component of
the inverted Jordan circle.  The center itself represents infinity.
-/

namespace Schoenflies

open Metric Set Function Bornology

noncomputable section

namespace EuclideanInversion

/-- The punctured plane at an inversion center. -/
def puncturedPlane (c : Plane) : Set Plane := {c}ᶜ

/-- Euclidean inversion of radius one as a self-homeomorphism of the
punctured plane. -/
noncomputable def puncturedHomeomorph (c : Plane) :
    puncturedPlane c ≃ₜ puncturedPlane c where
  toFun x := ⟨EuclideanGeometry.inversion c 1 x, by
    change EuclideanGeometry.inversion c 1 (x : Plane) ≠ c
    have hx : (x : Plane) ≠ c := by
      simpa only [puncturedPlane, mem_compl_iff, mem_singleton_iff] using x.2
    exact fun h => hx ((EuclideanGeometry.inversion_eq_center one_ne_zero).mp h)⟩
  invFun x := ⟨EuclideanGeometry.inversion c 1 x, by
    change EuclideanGeometry.inversion c 1 (x : Plane) ≠ c
    have hx : (x : Plane) ≠ c := by
      simpa only [puncturedPlane, mem_compl_iff, mem_singleton_iff] using x.2
    exact fun h => hx ((EuclideanGeometry.inversion_eq_center one_ne_zero).mp h)⟩
  left_inv x := by
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion c one_ne_zero x
  right_inv x := by
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion c one_ne_zero x
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const continuous_subtype_val
      (fun x => x.2)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const continuous_subtype_val
      (fun x => x.2)

@[simp] theorem puncturedHomeomorph_apply (c : Plane)
    (x : puncturedPlane c) :
    (puncturedHomeomorph c x : Plane) =
      EuclideanGeometry.inversion c 1 x := rfl

/-- Inversion maps an open set avoiding its center to an open set. -/
theorem isOpen_image_inversion {c : Plane} {U : Set Plane}
    (hU : IsOpen U) (hc : c ∉ U) :
    IsOpen (EuclideanGeometry.inversion c 1 '' U) := by
  let U' : Set (puncturedPlane c) :=
    ((↑) : puncturedPlane c → Plane) ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have himage' : IsOpen (puncturedHomeomorph c '' U') :=
    (puncturedHomeomorph c).isOpenMap U' hU'
  have hambient : IsOpen
      (((↑) : puncturedPlane c → Plane) ''
        (puncturedHomeomorph c '' U')) :=
    isOpen_compl_singleton.isOpenMap_subtype_val _ himage'
  convert hambient using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    have hxc : x ∈ puncturedPlane c := by
      change x ≠ c
      exact fun h => hc (h ▸ hxU)
    exact ⟨puncturedHomeomorph c ⟨x, hxc⟩,
      ⟨⟨x, hxc⟩, hxU, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hxU, hxy⟩, rfl⟩
    exact ⟨x, hxU, congrArg Subtype.val hxy⟩

end EuclideanInversion

namespace JordanCircle

variable (J : JordanCircle)

/-- The Jordan circle obtained by inversion about its chosen inside point. -/
noncomputable def inverted : JordanCircle where
  parametrization := fun u =>
    EuclideanGeometry.inversion J.insidePoint 1 (J.parametrization u)
  continuous := continuous_const.inversion continuous_const J.continuous
    (fun u h => J.insidePoint_mem
      ⟨u, (show J.parametrization u = J.insidePoint from h)⟩)
  injective :=
    (EuclideanGeometry.inversion_injective J.insidePoint one_ne_zero).comp
      J.injective

theorem inverted_carrier :
    J.inverted.carrier =
      EuclideanGeometry.inversion J.insidePoint 1 '' J.carrier := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨J.parametrization u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

@[simp] theorem inverted_carrierHomeomorph_apply
    (q : sphere (0 : Plane) 1) :
    (J.inverted.carrierHomeomorph q : Plane) =
      EuclideanGeometry.inversion J.insidePoint 1
        (J.carrierHomeomorph q : Plane) := by
  rfl

/-- The inversion image of the outside with the inversion center added. -/
def invertedOutsideFill : Set Plane :=
  EuclideanGeometry.inversion J.insidePoint 1 '' J.outside ∪
    {J.insidePoint}

/-- The inversion image of the punctured original inside. -/
def invertedInsidePunctured : Set Plane :=
  EuclideanGeometry.inversion J.insidePoint 1 ''
    (J.inside \ {J.insidePoint})

theorem insidePoint_mem_invertedOutsideFill :
    J.insidePoint ∈ J.invertedOutsideFill :=
  Or.inr (mem_singleton _)

theorem insidePoint_not_mem_inverted_carrier :
    J.insidePoint ∉ J.inverted.carrier := by
  rw [J.inverted_carrier]
  rintro ⟨x, hx, hinv⟩
  have hxcenter : x = J.insidePoint := by
    rw [EuclideanGeometry.inversion_eq_center one_ne_zero] at hinv
    exact hinv
  exact J.insidePoint_mem (hxcenter ▸ hx)

theorem inverted_compl_carrier_eq_union :
    J.inverted.carrierᶜ =
      J.invertedOutsideFill ∪ J.invertedInsidePunctured := by
  apply Set.Subset.antisymm
  · intro y hy
    by_cases hyc : y = J.insidePoint
    · exact Or.inl (Or.inr (hyc ▸ mem_singleton _))
    · let x := EuclideanGeometry.inversion J.insidePoint 1 y
      have hxc : x ≠ J.insidePoint := by
        intro h
        exact hyc ((EuclideanGeometry.inversion_eq_center one_ne_zero).mp h)
      have hxNotCarrier : x ∈ J.carrierᶜ := by
        intro hxCarrier
        apply hy
        rw [J.inverted_carrier]
        refine ⟨x, hxCarrier, ?_⟩
        exact EuclideanGeometry.inversion_inversion
          J.insidePoint one_ne_zero y
      rcases J.mem_inside_or_outside hxNotCarrier with hxInside | hxOutside
      · apply Or.inr
        refine ⟨x, ⟨hxInside, ?_⟩, ?_⟩
        · simpa only [mem_singleton_iff] using hxc
        · exact EuclideanGeometry.inversion_inversion
            J.insidePoint one_ne_zero y
      · apply Or.inl
        exact Or.inl ⟨x, hxOutside,
          EuclideanGeometry.inversion_inversion
            J.insidePoint one_ne_zero y⟩
  · rintro y (hyOutside | hyInside)
    · rcases hyOutside with ⟨x, hxOutside, rfl⟩ | rfl
      · rw [J.inverted_carrier]
        rintro ⟨z, hzCarrier, hzx⟩
        have hzx' : z = x :=
          (EuclideanGeometry.inversion_injective
            J.insidePoint one_ne_zero) hzx
        exact J.outside_subset_compl hxOutside (hzx' ▸ hzCarrier)
      · exact J.insidePoint_not_mem_inverted_carrier
    · rcases hyInside with ⟨x, ⟨hxInside, _⟩, rfl⟩
      rw [J.inverted_carrier]
      rintro ⟨z, hzCarrier, hzx⟩
      have hzx' : z = x :=
        (EuclideanGeometry.inversion_injective
          J.insidePoint one_ne_zero) hzx
      exact J.inside_subset_compl hxInside (hzx' ▸ hzCarrier)

theorem disjoint_invertedOutsideFill_invertedInsidePunctured :
    Disjoint J.invertedOutsideFill J.invertedInsidePunctured := by
  rw [Set.disjoint_left]
  intro y hyOutside hyInside
  rcases hyInside with ⟨z, ⟨hzInside, hzNe⟩, hzy⟩
  rcases hyOutside with ⟨x, hxOutside, hxy⟩ | hyc
  · have hxz : x = z :=
      (EuclideanGeometry.inversion_injective J.insidePoint one_ne_zero)
        (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp J.inside_disjoint_outside hzInside
      (hxz ▸ hxOutside)
  · have hyEq : y = J.insidePoint := mem_singleton_iff.mp hyc
    have hzEq : z = J.insidePoint := by
      rw [← EuclideanGeometry.inversion_eq_center one_ne_zero]
      exact hzy.trans hyEq
    exact hzNe (mem_singleton_iff.mpr hzEq)

theorem isOpen_invertedInsidePunctured :
    IsOpen J.invertedInsidePunctured := by
  apply EuclideanInversion.isOpen_image_inversion
  · exact J.inside_isOpen.sdiff isClosed_singleton
  · intro h
    exact h.2 (mem_singleton _)

theorem isOpen_invertedOutside_image :
    IsOpen (EuclideanGeometry.inversion J.insidePoint 1 '' J.outside) := by
  apply EuclideanInversion.isOpen_image_inversion J.outside_isOpen
  intro h
  exact Set.disjoint_left.mp J.inside_disjoint_outside
    J.insidePoint_mem_inside h

theorem insidePoint_mem_closure_invertedOutside_image :
    J.insidePoint ∈ closure
      (EuclideanGeometry.inversion J.insidePoint 1 '' J.outside) := by
  rw [Metric.mem_closure_iff]
  intro epsilon hepsilon
  have hballBounded : IsBounded (closedBall J.insidePoint (1 / epsilon)) :=
    isBounded_closedBall
  have hnotSubset : ¬ J.outside ⊆ closedBall J.insidePoint (1 / epsilon) := by
    intro hsub
    exact J.outside_unbounded (hballBounded.subset hsub)
  obtain ⟨x, hxOutside, hxFar⟩ := Set.not_subset.mp hnotSubset
  refine ⟨EuclideanGeometry.inversion J.insidePoint 1 x,
    ⟨x, hxOutside, rfl⟩, ?_⟩
  rw [dist_comm, EuclideanGeometry.dist_inversion_center]
  have hdistPos : 0 < dist x J.insidePoint := by
    exact dist_pos.mpr fun h => Set.disjoint_left.mp J.inside_disjoint_outside
      J.insidePoint_mem_inside (h ▸ hxOutside)
  have hfar : 1 / epsilon < dist x J.insidePoint := by
    simpa only [mem_closedBall, not_le] using hxFar
  have : 1 / dist x J.insidePoint < epsilon := by
    rw [div_lt_iff₀ hdistPos]
    have := (div_lt_iff₀ hepsilon).mp hfar
    nlinarith
  simpa only [one_pow] using this

theorem isPreconnected_invertedOutsideFill :
    IsPreconnected J.invertedOutsideFill := by
  have himage : IsPreconnected
      (EuclideanGeometry.inversion J.insidePoint 1 '' J.outside) := by
    exact J.outside_isConnected.isPreconnected.image _ <|
      continuousOn_const.inversion continuousOn_const continuousOn_id
        (fun x hx h => Set.disjoint_left.mp J.inside_disjoint_outside
          J.insidePoint_mem_inside (h ▸ hx))
  apply himage.subset_closure Set.subset_union_left
  intro y hy
  rcases hy with hy | hy
  · exact subset_closure hy
  · have hyEq : y = J.insidePoint := mem_singleton_iff.mp hy
    exact hyEq ▸ J.insidePoint_mem_closure_invertedOutside_image

theorem isBounded_invertedOutsideFill :
    IsBounded J.invertedOutsideFill := by
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.isOpen_iff.mp J.inside_isOpen J.insidePoint
      J.insidePoint_mem_inside
  let R : ℝ := 1 / delta
  apply (isBounded_closedBall :
    IsBounded (closedBall (J.insidePoint : Plane) R)).subset
  rintro y (⟨x, hxOutside, rfl⟩ | hy)
  · rw [mem_closedBall, EuclideanGeometry.dist_inversion_center]
    have hxNotBall : x ∉ ball J.insidePoint delta := by
      intro hx
      exact Set.disjoint_left.mp J.inside_disjoint_outside (hball hx) hxOutside
    have hdist : delta ≤ dist x J.insidePoint := by
      simpa only [mem_ball, not_lt] using hxNotBall
    have hdistPos : 0 < dist x J.insidePoint :=
      hdelta.trans_le hdist
    dsimp only [R]
    simp only [one_pow]
    exact one_div_le_one_div_of_le hdelta hdist
  · rw [mem_singleton_iff.mp hy, mem_closedBall, dist_self]
    exact div_nonneg zero_le_one hdelta.le

theorem isOpen_invertedOutsideFill :
    IsOpen J.invertedOutsideFill := by
  have hopenAway := J.isOpen_invertedOutside_image
  rw [Metric.isOpen_iff]
  intro y hy
  by_cases hyc : y = J.insidePoint
  · subst y
    obtain ⟨R, hR⟩ := J.inside_bounded.closure.subset_closedBall J.insidePoint
    let A : ℝ := |R| + 1
    have hA : 0 < A := by positivity
    refine ⟨1 / A, one_div_pos.mpr hA, ?_⟩
    intro z hz
    by_cases hzc : z = J.insidePoint
    · exact Or.inr (hzc ▸ mem_singleton _)
    · let x := EuclideanGeometry.inversion J.insidePoint 1 z
      have hdistz : dist z J.insidePoint < 1 / A := by
        simpa only [mem_ball] using hz
      have hdistx : R < dist x J.insidePoint := by
        rw [EuclideanGeometry.dist_inversion_center]
        have hzpos : 0 < dist z J.insidePoint := dist_pos.mpr hzc
        have hlarge : A < 1 / dist z J.insidePoint := by
          rw [lt_div_iff₀ hzpos]
          have := (lt_div_iff₀ hA).mp hdistz
          nlinarith
        have habs : |R| < 1 / dist z J.insidePoint :=
          (lt_add_one |R|).trans hlarge
        simpa only [one_pow] using (lt_of_le_of_lt (le_abs_self R) habs)
      have hxNotClosure : x ∉ closure J.inside := by
        intro hx
        have := hR hx
        rw [mem_closedBall] at this
        exact (not_lt_of_ge this) hdistx
      have hxOutside := J.compl_closure_inside_subset_outside hxNotClosure
      exact Or.inl ⟨x, hxOutside,
        EuclideanGeometry.inversion_inversion
          J.insidePoint one_ne_zero z⟩
  · have hyImage : y ∈
        EuclideanGeometry.inversion J.insidePoint 1 '' J.outside :=
      hy.resolve_right fun h => hyc (mem_singleton_iff.mp h)
    obtain ⟨epsilon, hepsilon, hball⟩ :=
      Metric.isOpen_iff.mp hopenAway y hyImage
    exact ⟨epsilon, hepsilon, hball.trans Set.subset_union_left⟩

/-- Inversion identifies the filled outside with the bounded component of
the inverted Jordan circle. -/
theorem inverted_inside :
    J.inverted.inside = J.invertedOutsideFill := by
  have hcCompl : J.insidePoint ∈ J.inverted.carrierᶜ :=
    J.insidePoint_not_mem_inverted_carrier
  have hcover : J.invertedOutsideFill ∪ J.invertedInsidePunctured =
      J.inverted.carrierᶜ := J.inverted_compl_carrier_eq_union.symm
  have hcRegion := J.inverted.mem_inside_or_outside hcCompl
  rcases hcRegion with hcInside | hcOutside
  · apply Set.Subset.antisymm
    · exact J.inverted.inside_isConnected.isPreconnected
        |>.subset_left_of_subset_union
          J.isOpen_invertedOutsideFill J.isOpen_invertedInsidePunctured
          J.disjoint_invertedOutsideFill_invertedInsidePunctured
          (by rw [hcover]; exact J.inverted.inside_subset_compl)
          ⟨J.insidePoint, hcInside, J.insidePoint_mem_invertedOutsideFill⟩
    · have hcomponent : connectedComponentIn J.inverted.carrierᶜ
          J.insidePoint = J.inverted.inside := by
        exact (connectedComponentIn_eq hcInside).symm
      rw [← hcomponent]
      exact J.isPreconnected_invertedOutsideFill.subset_connectedComponentIn
        J.insidePoint_mem_invertedOutsideFill
        (hcover ▸ Set.subset_union_left)
  · exfalso
    apply J.inverted.outside_unbounded
    apply J.isBounded_invertedOutsideFill.subset
    exact J.inverted.outside_isConnected.isPreconnected
      |>.subset_left_of_subset_union
        J.isOpen_invertedOutsideFill J.isOpen_invertedInsidePunctured
        J.disjoint_invertedOutsideFill_invertedInsidePunctured
        (by rw [hcover]; exact J.inverted.outside_subset_compl)
        ⟨J.insidePoint, hcOutside, J.insidePoint_mem_invertedOutsideFill⟩

/-- Inversion on the original carrier, with its image tightened to the
carrier of the inverted Jordan circle. -/
noncomputable def carrierInversionHomeomorph :
    J.carrier ≃ₜ J.inverted.carrier where
  toFun x := ⟨EuclideanGeometry.inversion J.insidePoint 1 x, by
    rw [J.inverted_carrier]
    exact ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨EuclideanGeometry.inversion J.insidePoint 1 y, by
    have hyImage : (y : Plane) ∈
        EuclideanGeometry.inversion J.insidePoint 1 '' J.carrier :=
      (Set.ext_iff.mp J.inverted_carrier (y : Plane)).mp y.property
    obtain ⟨x, hx, hxy⟩ := hyImage
    have hval : EuclideanGeometry.inversion J.insidePoint 1 (y : Plane) = x := by
      rw [← hxy]
      exact EuclideanGeometry.inversion_inversion
        J.insidePoint one_ne_zero x
    rwa [hval]⟩
  left_inv x := by
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion
      J.insidePoint one_ne_zero x
  right_inv y := by
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion
      J.insidePoint one_ne_zero y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const continuous_subtype_val
      (fun x h => J.insidePoint_mem (h ▸ x.2))
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const continuous_subtype_val
      (fun y h => J.insidePoint_not_mem_inverted_carrier (h ▸ y.2))

@[simp] theorem carrierInversionHomeomorph_apply (x : J.carrier) :
    (J.carrierInversionHomeomorph x : Plane) =
      EuclideanGeometry.inversion J.insidePoint 1 x := rfl

@[simp] theorem inverted_carrierHomeomorph_symm_carrierInversion
    (x : J.carrier) :
    J.inverted.carrierHomeomorph.symm (J.carrierInversionHomeomorph x) =
      J.carrierHomeomorph.symm x := by
  apply J.inverted.carrierHomeomorph.injective
  apply Subtype.ext
  rw [J.inverted.carrierHomeomorph.apply_symm_apply,
    J.inverted_carrierHomeomorph_apply,
    J.carrierHomeomorph.apply_symm_apply]
  rfl

/-- Inversion identifies the original closed outside with the punctured
closed inside of the inverted Jordan circle; the deleted center is the point
at infinity. -/
noncomputable def outsideToPuncturedInvertedInside :
    closure J.outside ≃ₜ
      {y : closure J.inverted.inside // (y : Plane) ≠ J.insidePoint} where
  toFun x := by
    have hxLayers : (x : Plane) ∈ J.outside ∪ J.carrier := by
      rw [← J.closure_outside]
      exact x.2
    have hyClosure : EuclideanGeometry.inversion J.insidePoint 1 x ∈
        closure J.inverted.inside := by
      rw [J.inverted.closure_inside]
      rcases hxLayers with hxOutside | hxCarrier
      · apply Or.inl
        rw [J.inverted_inside]
        exact Or.inl ⟨x, hxOutside, rfl⟩
      · apply Or.inr
        rw [J.inverted_carrier]
        exact ⟨x, hxCarrier, rfl⟩
    refine ⟨⟨EuclideanGeometry.inversion J.insidePoint 1 x, hyClosure⟩, ?_⟩
    intro h
    have hxCenter : (x : Plane) = J.insidePoint :=
      (EuclideanGeometry.inversion_eq_center one_ne_zero).mp h
    rcases hxLayers with hxOutside | hxCarrier
    · exact Set.disjoint_left.mp J.inside_disjoint_outside
        J.insidePoint_mem_inside (hxCenter ▸ hxOutside)
    · exact J.insidePoint_mem (hxCenter ▸ hxCarrier)
  invFun y := by
    have hyLayers : (y : Plane) ∈
        J.inverted.inside ∪ J.inverted.carrier := by
      rw [← J.inverted.closure_inside]
      exact y.1.2
    have hxClosure : EuclideanGeometry.inversion J.insidePoint 1 y ∈
        closure J.outside := by
      rw [J.closure_outside]
      rcases hyLayers with hyInside | hyCarrier
      · have hyFill : (y : Plane) ∈ J.invertedOutsideFill := by
          rw [← J.inverted_inside]
          exact hyInside
        rcases hyFill with ⟨x, hxOutside, hxy⟩ | hyCenter
        · apply Or.inl
          have hval : EuclideanGeometry.inversion J.insidePoint 1 (y : Plane) = x := by
            rw [← hxy]
            exact EuclideanGeometry.inversion_inversion
              J.insidePoint one_ne_zero x
          rwa [hval]
        · exact False.elim <| y.2 (mem_singleton_iff.mp hyCenter)
      · have hyImage : (y : Plane) ∈
            EuclideanGeometry.inversion J.insidePoint 1 '' J.carrier := by
          exact (Set.ext_iff.mp J.inverted_carrier (y : Plane)).mp hyCarrier
        obtain ⟨x, hxCarrier, hxy⟩ := hyImage
        apply Or.inr
        have hval : EuclideanGeometry.inversion J.insidePoint 1 (y : Plane) = x := by
          rw [← hxy]
          exact EuclideanGeometry.inversion_inversion
            J.insidePoint one_ne_zero x
        rwa [hval]
    exact ⟨EuclideanGeometry.inversion J.insidePoint 1 y, hxClosure⟩
  left_inv x := by
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion
      J.insidePoint one_ne_zero x
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact EuclideanGeometry.inversion_inversion
      J.insidePoint one_ne_zero y
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const continuous_subtype_val
      (fun x h => by
        have hxLayers : (x : Plane) ∈ J.outside ∪ J.carrier := by
          rw [← J.closure_outside]
          exact x.2
        rcases hxLayers with hxOutside | hxCarrier
        · exact Set.disjoint_left.mp J.inside_disjoint_outside
            J.insidePoint_mem_inside (h ▸ hxOutside)
        · exact J.insidePoint_mem (h ▸ hxCarrier))
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_const.inversion continuous_const
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

@[simp] theorem outsideToPuncturedInvertedInside_apply
    (x : closure J.outside) :
    ((J.outsideToPuncturedInvertedInside x :
        closure J.inverted.inside) : Plane) =
      EuclideanGeometry.inversion J.insidePoint 1 x := rfl

end JordanCircle

end

end Schoenflies
