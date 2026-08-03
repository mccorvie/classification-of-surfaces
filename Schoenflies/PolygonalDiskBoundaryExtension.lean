import ClassificationOfSurfaces.Moise.PLApproximation

/-!
# Extending parametrized polygonal boundaries

The Moise library extends a PL embedding of a triangular boundary across the
closed triangle.  Collar cells, however, naturally have arbitrary polygonal
source boundaries.  We reduce that case to the triangular theorem by a
relative polygonal Schoenflies straightening of the source disk.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle

/-- A PL embedding of one polygonal boundary onto another extends to a
continuous bijection of their closed regions.  The extension agrees with the
prescribed boundary map pointwise.

Continuity of the inverse follows automatically when this result is packaged
as a homeomorphism, since the source region is compact and the target is
Hausdorff. -/
theorem exists_closedRegion_extension (P Q : PolygonalCircle)
    {f : Plane → Plane} (hpl : IsPLOnSet P.carrier f)
    (hinj : Set.InjOn f P.carrier)
    (himage : f '' P.carrier = Q.carrier) :
    ∃ F : Plane → Plane,
      Set.EqOn F f P.carrier ∧
        ContinuousOn F P.closedRegion ∧
        Set.InjOn F P.closedRegion ∧
        F '' P.closedRegion = Q.closedRegion := by
  obtain ⟨h, hPL, ⟨C, hC, hboundary, hregion⟩, _hfix⟩ :=
    P.polygonal_schoenflies_rel Set.univ isOpen_univ
      (Set.subset_univ P.closedRegion)
  obtain ⟨T, hTcarrier⟩ := hC.exists_polygonalCircle
  have hTregion : C = T.closedRegion := by
    apply T.eq_closedRegion_of_isCompact_frontier_eq hC.isCompact
    · exact hTcarrier.symm
    · exact hC.infinite_interior.nonempty
  let hPLRegion : FinitePLHomeomorphOn h P.closedRegion :=
    hPL.congrSet P.closedRegionMesh_support
  let hInvPL : FinitePLHomeomorphOn h.symm T.closedRegion :=
    hPLRegion.symm.congrSet (hregion.trans hTregion)
  have hInvBoundaryPL : IsPLOnSet T.carrier h.symm :=
    hInvPL.isPLOnSet_polygonal_frontier T rfl
  have hInvImage : h.symm '' T.carrier = P.carrier := by
    rw [hTcarrier, ← hboundary, Set.image_image]
    simp
  let b : Plane → Plane := f ∘ h.symm
  have hbPL : IsPLOnSet (frontier C) b := by
    have hcomp : IsPLOnSet T.carrier (f ∘ h.symm) :=
      IsPLOnSet.comp_polygonal_embedding T P hInvBoundaryPL
        h.symm.injective.injOn hInvImage hpl
    simpa only [hTcarrier] using hcomp
  have hbInj : Set.InjOn b (frontier C) := by
    intro x hx y hy hxy
    apply h.symm.injective
    apply hinj
    · rw [← hInvImage]
      exact ⟨x, hTcarrier.symm ▸ hx, rfl⟩
    · rw [← hInvImage]
      exact ⟨y, hTcarrier.symm ▸ hy, rfl⟩
    · exact hxy
  have hbImage : b '' frontier C = Q.carrier := by
    calc
      b '' frontier C = f '' (h.symm '' frontier C) :=
        Set.image_comp f h.symm (frontier C)
      _ = f '' P.carrier := by
        rw [← hTcarrier, hInvImage]
      _ = Q.carrier := himage
  obtain ⟨G, hGeq, hGcont, hGinj, hGimage, _hGPL, _hGcert⟩ :=
    pl_extension_of_triangle_to_polygon_boundary hC Q hbPL hbInj hbImage
  let F : Plane → Plane := G ∘ h
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change G (h x) = f x
    have hhx : h x ∈ frontier C := by
      rw [← hboundary]
      exact ⟨x, hx, rfl⟩
    rw [hGeq hhx]
    exact congrArg f (h.symm_apply_apply x)
  · apply hGcont.comp h.continuous.continuousOn
    intro x hx
    rw [← hregion]
    exact ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    apply h.injective
    apply hGinj
    · rw [← hregion]
      exact ⟨x, hx, rfl⟩
    · rw [← hregion]
      exact ⟨y, hy, rfl⟩
    · exact hxy
  · change (G ∘ h) '' P.closedRegion = Q.closedRegion
    rw [Set.image_comp, hregion, hGimage]

/-- Subtype-homeomorphism form of `exists_closedRegion_extension`.  This is
the cell-filling interface used by the Chapter 9 gluing construction. -/
theorem exists_closedRegionHomeomorph_extending (P Q : PolygonalCircle)
    {f : Plane → Plane} (hpl : IsPLOnSet P.carrier f)
    (hinj : Set.InjOn f P.carrier)
    (himage : f '' P.carrier = Q.carrier) :
    ∃ e : P.closedRegion ≃ₜ Q.closedRegion,
      ∀ x : P.carrier,
        (e ⟨x, by
          rw [P.closedRegion_eq_union]
          exact Or.inr x.2⟩ : Plane) = f x := by
  obtain ⟨F, hFeq, hFcont, hFinj, hFimage⟩ :=
    exists_closedRegion_extension P Q hpl hinj himage
  let g : P.closedRegion → Q.closedRegion := fun x =>
    ⟨F x, by
      rw [← hFimage]
      exact ⟨x, x.2, rfl⟩⟩
  have hgcont : Continuous g := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_restrict.mp hFcont
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hFinj x.2 y.2
    exact congrArg Subtype.val hxy
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : Plane) ∈ F '' P.closedRegion := by
      rw [hFimage]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact hxy
  letI : CompactSpace P.closedRegion :=
    isCompact_iff_compactSpace.mp P.isCompact_closedRegion
  let e : P.closedRegion ≃ₜ Q.closedRegion :=
    (hgcont.isClosedEmbedding hginj).isEmbedding.toHomeomorphOfSurjective
      hgsurj
  refine ⟨e, ?_⟩
  intro x
  change F x = f x
  exact hFeq x.2

end PolygonalCircle

end

end Schoenflies
