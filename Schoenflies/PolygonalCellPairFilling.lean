import Schoenflies.ClosedCoverHomeomorph
import Schoenflies.PolygonalDiskBoundaryExtension

/-!
# Filling and gluing a pair of polygonal cells

The polygonal disk-extension theorem fills one cell.  The theorem below is
the finite two-cell interface needed by the annular theta construction: a
single PL boundary map is filled on both cells and the fillings are pasted
across their common boundary locus.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle

/-- Two polygonal disk fillings glue whenever the closed-cell overlaps are
contained in the corresponding boundary overlaps. -/
theorem exists_unionClosedRegionHomeomorph_extending
    (R₀ R₁ T₀ T₁ : PolygonalCircle)
    {f : Plane → Plane}
    (hpl₀ : IsPLOnSet R₀.carrier f)
    (hpl₁ : IsPLOnSet R₁.carrier f)
    (hinj : Set.InjOn f (R₀.carrier ∪ R₁.carrier))
    (himage₀ : f '' R₀.carrier = T₀.carrier)
    (himage₁ : f '' R₁.carrier = T₁.carrier)
    (hsourceInter : R₀.closedRegion ∩ R₁.closedRegion ⊆
      R₀.carrier ∩ R₁.carrier)
    (htargetInter : T₀.closedRegion ∩ T₁.closedRegion ⊆
      T₀.carrier ∩ T₁.carrier) :
    ∃ e : (R₀.closedRegion ∪ R₁.closedRegion : Set Plane) ≃ₜ
        (T₀.closedRegion ∪ T₁.closedRegion : Set Plane),
      ∀ x : (R₀.carrier ∪ R₁.carrier : Set Plane),
        (e ⟨x, by
          rcases x.2 with hx₀ | hx₁
          · left
            rw [R₀.closedRegion_eq_union]
            exact Or.inr hx₀
          · right
            rw [R₁.closedRegion_eq_union]
            exact Or.inr hx₁⟩ : Plane) = f x := by
  obtain ⟨e₀, he₀⟩ :=
    exists_closedRegionHomeomorph_extending R₀ T₀ hpl₀
      (hinj.mono Set.subset_union_left) himage₀
  obtain ⟨e₁, he₁⟩ :=
    exists_closedRegionHomeomorph_extending R₁ T₁ hpl₁
      (hinj.mono Set.subset_union_right) himage₁
  have hforward : ∀ x
      (hx₀ : x ∈ R₀.closedRegion) (hx₁ : x ∈ R₁.closedRegion),
      (e₀ ⟨x, hx₀⟩ : Plane) = e₁ ⟨x, hx₁⟩ := by
    intro x hx₀ hx₁
    have hxCarrier := hsourceInter ⟨hx₀, hx₁⟩
    have hleft := he₀ ⟨x, hxCarrier.1⟩
    have hright := he₁ ⟨x, hxCarrier.2⟩
    exact hleft.trans hright.symm
  have hbackward : ∀ y
      (hy₀ : y ∈ T₀.closedRegion) (hy₁ : y ∈ T₁.closedRegion),
      (e₀.symm ⟨y, hy₀⟩ : Plane) = e₁.symm ⟨y, hy₁⟩ := by
    intro y hy₀ hy₁
    have hyCarrier := htargetInter ⟨hy₀, hy₁⟩
    obtain ⟨x₀, hx₀, hfx₀⟩ : y ∈ f '' R₀.carrier := by
      rw [himage₀]
      exact hyCarrier.1
    obtain ⟨x₁, hx₁, hfx₁⟩ : y ∈ f '' R₁.carrier := by
      rw [himage₁]
      exact hyCarrier.2
    have hx₀Closed : x₀ ∈ R₀.closedRegion := by
      rw [R₀.closedRegion_eq_union]
      exact Or.inr hx₀
    have hx₁Closed : x₁ ∈ R₁.closedRegion := by
      rw [R₁.closedRegion_eq_union]
      exact Or.inr hx₁
    have he₀x : (e₀ ⟨x₀, hx₀Closed⟩ : Plane) = y :=
      (he₀ ⟨x₀, hx₀⟩).trans hfx₀
    have he₁x : (e₁ ⟨x₁, hx₁Closed⟩ : Plane) = y :=
      (he₁ ⟨x₁, hx₁⟩).trans hfx₁
    have hpre₀ : e₀.symm ⟨y, hy₀⟩ = ⟨x₀, hx₀Closed⟩ := by
      apply e₀.injective
      rw [e₀.apply_symm_apply]
      exact Subtype.ext he₀x.symm
    have hpre₁ : e₁.symm ⟨y, hy₁⟩ = ⟨x₁, hx₁Closed⟩ := by
      apply e₁.injective
      rw [e₁.apply_symm_apply]
      exact Subtype.ext he₁x.symm
    have hxEq : x₀ = x₁ :=
      hinj (Or.inl hx₀) (Or.inr hx₁) (hfx₀.trans hfx₁.symm)
    exact (congrArg Subtype.val hpre₀).trans <|
      hxEq.trans (congrArg Subtype.val hpre₁).symm
  let e := ClosedCoverHomeomorph.glue
    R₀.isCompact_closedRegion.isClosed R₁.isCompact_closedRegion.isClosed
    T₀.isCompact_closedRegion.isClosed T₁.isCompact_closedRegion.isClosed
    e₀ e₁ hforward hbackward
  refine ⟨e, ?_⟩
  intro x
  rcases x.2 with hx₀ | hx₁
  · have hx₀Closed : (x : Plane) ∈ R₀.closedRegion := by
      rw [R₀.closedRegion_eq_union]
      exact Or.inr hx₀
    rw [ClosedCoverHomeomorph.coe_glue_apply_of_mem_left
      R₀.isCompact_closedRegion.isClosed R₁.isCompact_closedRegion.isClosed
      T₀.isCompact_closedRegion.isClosed T₁.isCompact_closedRegion.isClosed
      e₀ e₁ hforward hbackward _ hx₀Closed]
    exact he₀ ⟨x, hx₀⟩
  · have hx₁Closed : (x : Plane) ∈ R₁.closedRegion := by
      rw [R₁.closedRegion_eq_union]
      exact Or.inr hx₁
    rw [ClosedCoverHomeomorph.coe_glue_apply_of_mem_right
      R₀.isCompact_closedRegion.isClosed R₁.isCompact_closedRegion.isClosed
      T₀.isCompact_closedRegion.isClosed T₁.isCompact_closedRegion.isClosed
      e₀ e₁ hforward hbackward _ hx₁Closed]
    exact he₁ ⟨x, hx₁⟩

end PolygonalCircle

end

end Schoenflies
