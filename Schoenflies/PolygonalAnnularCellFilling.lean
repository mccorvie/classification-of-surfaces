import Schoenflies.PolygonalAnnularCellDecomposition
import Schoenflies.PolygonalCellPairFilling

/-!
# Filling a polygonal annulus cut into two cells

The two separator disks of an annular cell decomposition cover the outer
disk.  Thus compatible polygonal boundary data on the separator graph can
be filled cellwise and pasted to a homeomorphism of the entire outer disk.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.AnnularCellDecomposition

variable {P Q P' Q' : PolygonalCircle}

/-- Fill corresponding two-cell decompositions and transport the resulting
homeomorphism from the cell unions to the two closed outer disks. -/
theorem exists_outerClosedRegionHomeomorph_extending
    (D : AnnularCellDecomposition P Q)
    (E : AnnularCellDecomposition P' Q')
    {f : Plane → Plane}
    (hpl₀ : IsPLOnSet D.cell₀.carrier f)
    (hpl₁ : IsPLOnSet D.cell₁.carrier f)
    (hinj : Set.InjOn f (D.cell₀.carrier ∪ D.cell₁.carrier))
    (himage₀ : f '' D.cell₀.carrier = E.cell₀.carrier)
    (himage₁ : f '' D.cell₁.carrier = E.cell₁.carrier) :
    ∃ e : Q.closedRegion ≃ₜ Q'.closedRegion,
      ∀ (x : Plane) (hx : x ∈ D.cell₀.carrier ∪ D.cell₁.carrier),
        (e ⟨x, D.cellCarriers_union_subset_closedRegion hx⟩ : Plane) = f x := by
  obtain ⟨eCells, heCells⟩ :=
    exists_unionClosedRegionHomeomorph_extending
      D.cell₀ D.cell₁ E.cell₀ E.cell₁
      hpl₀ hpl₁ hinj himage₀ himage₁
      D.cellClosedRegions_inter_subset_carriers
      E.cellClosedRegions_inter_subset_carriers
  let e : Q.closedRegion ≃ₜ Q'.closedRegion :=
    (Homeomorph.setCongr D.cellClosedRegions_union.symm).trans <|
      eCells.trans (Homeomorph.setCongr E.cellClosedRegions_union)
  refine ⟨e, ?_⟩
  intro x hx
  let xCarrier : (D.cell₀.carrier ∪ D.cell₁.carrier : Set Plane) := ⟨x, hx⟩
  have hfill := heCells xCarrier
  change
    (((Homeomorph.setCongr E.cellClosedRegions_union)
      (eCells ((Homeomorph.setCongr D.cellClosedRegions_union.symm)
        ⟨x, D.cellCarriers_union_subset_closedRegion hx⟩))) : Plane) = f x
  rw [coe_setCongr_apply]
  convert hfill using 1
  apply congrArg Subtype.val
  apply congrArg eCells
  apply Subtype.ext
  rfl

end PolygonalCircle.AnnularCellDecomposition

end

end Schoenflies
