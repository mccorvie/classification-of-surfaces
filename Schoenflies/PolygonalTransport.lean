import Schoenflies.JordanRegions
import ClassificationOfSurfaces.Moise.PLApproximation

/-!
# Transport of polygonal Jordan regions

An ambient homeomorphism carrying one polygonal carrier to another carries
the bounded complementary region to the bounded complementary region.  The
proof is phrased through connected components, so it does not depend on an
orientation or winding-number calculation.
-/

namespace Schoenflies

open Set Function Bornology
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace PolygonalTransport

/-- The polygon interior is the connected component of any one of its
points in the carrier complement. -/
theorem connectedComponentIn_eq_interiorRegion
    (P : PolygonalCircle) {x : Plane} (hx : x ∈ P.interiorRegion) :
    connectedComponentIn P.carrierᶜ x = P.interiorRegion := by
  have hxCompl : x ∈ P.carrierᶜ := by
    rw [← P.interior_union_exterior]
    exact Or.inl hx
  apply Set.Subset.antisymm
  · have hregions : connectedComponentIn P.carrierᶜ x ⊆
        P.interiorRegion ∪ P.exteriorRegion := by
      rw [P.interior_union_exterior]
      exact connectedComponentIn_subset _ _
    rcases isPreconnected_connectedComponentIn.subset_or_subset
        P.isOpen_interiorRegion P.isOpen_exteriorRegion
        P.disjoint_interior_exterior hregions with hInside | hOutside
    · exact hInside
    · have hxOutside : x ∈ P.exteriorRegion :=
        hOutside (mem_connectedComponentIn hxCompl)
      exact False.elim
        (Set.disjoint_left.mp P.disjoint_interior_exterior hx hxOutside)
  · intro y hy
    exact P.isConnected_interiorRegion.isPreconnected.subset_connectedComponentIn
      hx (by
        rw [← P.interior_union_exterior]
        exact subset_union_left) hy

/-- The polygon exterior is the connected component of any one of its
points in the carrier complement. -/
theorem connectedComponentIn_eq_exteriorRegion
    (P : PolygonalCircle) {x : Plane} (hx : x ∈ P.exteriorRegion) :
    connectedComponentIn P.carrierᶜ x = P.exteriorRegion := by
  have hxCompl : x ∈ P.carrierᶜ := by
    rw [← P.interior_union_exterior]
    exact Or.inr hx
  apply Set.Subset.antisymm
  · have hregions : connectedComponentIn P.carrierᶜ x ⊆
        P.interiorRegion ∪ P.exteriorRegion := by
      rw [P.interior_union_exterior]
      exact connectedComponentIn_subset _ _
    rcases isPreconnected_connectedComponentIn.subset_or_subset
        P.isOpen_interiorRegion P.isOpen_exteriorRegion
        P.disjoint_interior_exterior hregions with hInside | hOutside
    · have hxInside : x ∈ P.interiorRegion :=
        hInside (mem_connectedComponentIn hxCompl)
      exact False.elim
        (Set.disjoint_left.mp P.disjoint_interior_exterior hxInside hx)
    · exact hOutside
  · intro y hy
    exact P.isConnected_exteriorRegion.isPreconnected.subset_connectedComponentIn
      hx (by
        rw [← P.interior_union_exterior]
        exact subset_union_right) hy

/-- Ambient homeomorphisms preserve the bounded side of polygonal circles. -/
theorem image_interiorRegion
    (P Q : PolygonalCircle) (h : Plane ≃ₜ Plane)
    (hcarrier : h '' P.carrier = Q.carrier) :
    h '' P.interiorRegion = Q.interiorRegion := by
  obtain ⟨x, hxInside⟩ := P.isConnected_interiorRegion.nonempty
  have hxCompl : x ∈ P.carrierᶜ := by
    rw [← P.interior_union_exterior]
    exact Or.inl hxInside
  have hhxCompl : h x ∈ Q.carrierᶜ := by
    rw [← hcarrier, ← h.image_compl]
    exact ⟨x, hxCompl, rfl⟩
  have hcomponent :
      h '' P.interiorRegion =
        connectedComponentIn Q.carrierᶜ (h x) := by
    rw [← connectedComponentIn_eq_interiorRegion P hxInside,
      h.image_connectedComponentIn hxCompl, h.image_compl, hcarrier]
  rcases Q.interior_union_exterior ▸ hhxCompl with hhxInside | hhxOutside
  · exact hcomponent.trans
      (connectedComponentIn_eq_interiorRegion Q hhxInside)
  · have himageExterior : h '' P.interiorRegion = Q.exteriorRegion :=
      hcomponent.trans
        (connectedComponentIn_eq_exteriorRegion Q hhxOutside)
    have himageBounded : IsBounded (h '' P.interiorRegion) := by
      apply (P.isCompact_closedRegion.image h.continuous).isBounded.subset
      exact image_mono (by
        rw [P.closedRegion_eq_union]
        exact subset_union_left)
    exact False.elim
      (Q.not_isBounded_exteriorRegion (himageExterior ▸ himageBounded))

/-- The unbounded sides are transported as well. -/
theorem image_exteriorRegion
    (P Q : PolygonalCircle) (h : Plane ≃ₜ Plane)
    (hcarrier : h '' P.carrier = Q.carrier) :
    h '' P.exteriorRegion = Q.exteriorRegion := by
  have hcompl : h '' P.carrierᶜ = Q.carrierᶜ := by
    rw [h.image_compl, hcarrier]
  have hunion : Q.interiorRegion ∪ h '' P.exteriorRegion =
      Q.interiorRegion ∪ Q.exteriorRegion := by
    calc
      Q.interiorRegion ∪ h '' P.exteriorRegion =
          h '' P.interiorRegion ∪ h '' P.exteriorRegion := by
            rw [image_interiorRegion P Q h hcarrier]
      _ = h '' (P.interiorRegion ∪ P.exteriorRegion) := by
        rw [image_union]
      _ = h '' P.carrierᶜ := by rw [P.interior_union_exterior]
      _ = Q.carrierᶜ := hcompl
      _ = Q.interiorRegion ∪ Q.exteriorRegion :=
        Q.interior_union_exterior.symm
  have hdisjoint : Disjoint Q.interiorRegion (h '' P.exteriorRegion) := by
    rw [← image_interiorRegion P Q h hcarrier, Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' : a = b := h.injective hab.symm
    subst b
    exact Set.disjoint_left.mp P.disjoint_interior_exterior ha hb
  apply Set.Subset.antisymm
  · intro x hxImage
    have hxUnion : x ∈ Q.interiorRegion ∪ Q.exteriorRegion := by
      rw [← hunion]
      exact Or.inr hxImage
    rcases hxUnion with hxInside | hxOutside
    · exact False.elim
        (Set.disjoint_left.mp hdisjoint hxInside hxImage)
    · exact hxOutside
  · intro x hxOutside
    have hxUnion : x ∈ Q.interiorRegion ∪ h '' P.exteriorRegion := by
      rw [hunion]
      exact Or.inr hxOutside
    rcases hxUnion with hxInside | hxImage
    · exact False.elim
        (Set.disjoint_left.mp Q.disjoint_interior_exterior
          hxInside hxOutside)
    · exact hxImage

/-- Translating a polygonal circle produces another polygonal circle with
the expected carrier and complementary regions. -/
theorem exists_translation (P : PolygonalCircle) (v : Plane) :
    ∃ Q : PolygonalCircle,
      Q.carrier = (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.carrier ∧
      (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.interiorRegion =
        Q.interiorRegion ∧
      (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.exteriorRegion =
        Q.exteriorRegion := by
  let h : Plane ≃ₜ Plane := Homeomorph.addLeft v
  have hpl : IsPLOnSet P.carrier h := by
    refine ⟨P.edgeComplex, P.edgeComplex_support, ?_⟩
    apply IsPLOn.of_affineOn_support
    refine ⟨(AffineEquiv.vaddConst ℝ v).toAffineMap, ?_⟩
    intro x _hx
    simp [h, add_comm]
  obtain ⟨Q, hQcarrier⟩ :=
    P.exists_image_of_isPLOnSet_embedding hpl h.injective.injOn
  have hcarrier : h '' P.carrier = Q.carrier := hQcarrier.symm
  exact ⟨Q, hQcarrier,
    image_interiorRegion P Q h hcarrier,
    image_exteriorRegion P Q h hcarrier⟩

end PolygonalTransport

end Schoenflies
