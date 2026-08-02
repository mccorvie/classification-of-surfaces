import Schoenflies.ClosedCoverHomeomorph
import Schoenflies.TwoArcCarrierHomeomorph

/-!
# Attaching one polygonal disk relative to an existing homeomorphism

This is the relative finite-stage primitive used by the collar argument.
An existing closed region is enlarged by a polygonal disk whose intersection
with that region is one parametrized boundary arc.  A corresponding target
disk is attached along the pointwise corresponding arc.  The complementary
boundary arcs are matched canonically, Alexander extension fills the new
disk, and closed-cover gluing leaves the old map unchanged.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalDiskAttachment

/-- A polygonal disk attached to a closed base exactly along the first arc
of a two-arc presentation of its boundary. -/
structure Presentation (A : Set Plane) where
  disk : PolygonalCircle
  startPoint : Plane
  endPoint : Plane
  shared : Path startPoint endPoint
  exposed : Path endPoint startPoint
  shared_injective : Injective shared
  exposed_injective : Injective exposed
  boundary_overlap : range shared ∩ range exposed =
    {startPoint, endPoint}
  carrier_eq : disk.carrier = range shared ∪ range exposed
  base_closed : IsClosed A
  base_inter_disk : A ∩ disk.closedRegion = range shared

variable {A B : Set Plane}

namespace Presentation

theorem shared_mem_base (D : Presentation A) (t : unitInterval) :
    D.shared t ∈ A := by
  have h : D.shared t ∈ A ∩ D.disk.closedRegion := by
    rw [D.base_inter_disk]
    exact ⟨t, rfl⟩
  exact h.1

theorem shared_mem_closedRegion (D : Presentation A)
    (t : unitInterval) : D.shared t ∈ D.disk.closedRegion := by
  have h : D.shared t ∈ A ∩ D.disk.closedRegion := by
    rw [D.base_inter_disk]
    exact ⟨t, rfl⟩
  exact h.2

theorem shared_mem_carrier (D : Presentation A) (t : unitInterval) :
    D.shared t ∈ D.disk.carrier := by
  rw [D.carrier_eq]
  exact Or.inl ⟨t, rfl⟩

end Presentation

variable (D : Presentation A) (E : Presentation B)

private def rawBoundaryHomeomorph :
    (range D.shared ∪ range D.exposed : Set Plane) ≃ₜ
      (range E.shared ∪ range E.exposed : Set Plane) :=
  TwoArcJordan.carrierCorrespondence
    D.shared D.exposed D.shared_injective D.exposed_injective
      D.boundary_overlap
    E.shared E.exposed E.shared_injective E.exposed_injective
      E.boundary_overlap

/-- The canonical boundary correspondence for the newly attached disks. -/
def boundaryHomeomorph : D.disk.carrier ≃ₜ E.disk.carrier :=
  (Homeomorph.setCongr D.carrier_eq).trans
    ((rawBoundaryHomeomorph D E).trans
      (Homeomorph.setCongr E.carrier_eq.symm))

theorem boundaryHomeomorph_apply_shared (t : unitInterval) :
    boundaryHomeomorph D E ⟨D.shared t, D.shared_mem_carrier t⟩ =
      ⟨E.shared t, E.shared_mem_carrier t⟩ := by
  apply Subtype.ext
  change
    ((rawBoundaryHomeomorph D E)
      ⟨D.shared t, Or.inl ⟨t, rfl⟩⟩ : Plane) = E.shared t
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_first
      D.shared D.exposed D.shared_injective D.exposed_injective
        D.boundary_overlap
      E.shared E.exposed E.shared_injective E.exposed_injective
      E.boundary_overlap t

theorem boundaryHomeomorph_apply_exposed (t : unitInterval) :
    boundaryHomeomorph D E ⟨D.exposed t, by
      rw [D.carrier_eq]
      exact Or.inr ⟨t, rfl⟩⟩ =
      ⟨E.exposed t, by
        rw [E.carrier_eq]
        exact Or.inr ⟨t, rfl⟩⟩ := by
  apply Subtype.ext
  change
    ((rawBoundaryHomeomorph D E)
      ⟨D.exposed t, Or.inr ⟨t, rfl⟩⟩ : Plane) = E.exposed t
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_second
      D.shared D.exposed D.shared_injective D.exposed_injective
        D.boundary_overlap
      E.shared E.exposed E.shared_injective E.exposed_injective
        E.boundary_overlap t

/-- Fill the new polygonal disk by Alexander extension. -/
def newDiskHomeomorph : D.disk.closedRegion ≃ₜ E.disk.closedRegion :=
  PolygonalCircle.extendBoundaryHomeomorph D.disk E.disk
    (boundaryHomeomorph D E)

theorem newDiskHomeomorph_apply_shared (t : unitInterval) :
    (newDiskHomeomorph D E
        ⟨D.shared t, D.shared_mem_closedRegion t⟩ : Plane) =
      E.shared t := by
  calc
    (newDiskHomeomorph D E
        ⟨D.shared t, D.shared_mem_closedRegion t⟩ : Plane) =
        (boundaryHomeomorph D E
          ⟨D.shared t, D.shared_mem_carrier t⟩ : Plane) :=
      PolygonalCircle.extendBoundaryHomeomorph_apply
        D.disk E.disk (boundaryHomeomorph D E)
          ⟨D.shared t, D.shared_mem_carrier t⟩
    _ = E.shared t :=
      congrArg Subtype.val (boundaryHomeomorph_apply_shared D E t)

theorem newDiskHomeomorph_apply_exposed (t : unitInterval) :
    (newDiskHomeomorph D E
        ⟨D.exposed t, by
          rw [D.disk.closedRegion_eq_union]
          right
          rw [D.carrier_eq]
          exact Or.inr ⟨t, rfl⟩⟩ : Plane) =
      E.exposed t := by
  calc
    (newDiskHomeomorph D E
        ⟨D.exposed t, by
          rw [D.disk.closedRegion_eq_union]
          right
          rw [D.carrier_eq]
          exact Or.inr ⟨t, rfl⟩⟩ : Plane) =
        (boundaryHomeomorph D E
          ⟨D.exposed t, by
            rw [D.carrier_eq]
            exact Or.inr ⟨t, rfl⟩⟩ : Plane) :=
      PolygonalCircle.extendBoundaryHomeomorph_apply
        D.disk E.disk (boundaryHomeomorph D E)
          ⟨D.exposed t, by
            rw [D.carrier_eq]
            exact Or.inr ⟨t, rfl⟩⟩
    _ = E.exposed t :=
      congrArg Subtype.val (boundaryHomeomorph_apply_exposed D E t)

variable (old : A ≃ₜ B)
  (hshared : ∀ t : unitInterval,
    (old ⟨D.shared t, D.shared_mem_base t⟩ : Plane) = E.shared t)

include hshared

private theorem forward_agree :
    ∀ x (hxA : x ∈ A) (hxD : x ∈ D.disk.closedRegion),
      (old ⟨x, hxA⟩ : Plane) =
        newDiskHomeomorph D E ⟨x, hxD⟩ := by
  intro x hxA hxD
  have hxShared : x ∈ range D.shared := by
    rw [← D.base_inter_disk]
    exact ⟨hxA, hxD⟩
  obtain ⟨t, rfl⟩ := hxShared
  exact (hshared t).trans (newDiskHomeomorph_apply_shared D E t).symm

private theorem backward_agree :
    ∀ y (hyB : y ∈ B) (hyE : y ∈ E.disk.closedRegion),
      (old.symm ⟨y, hyB⟩ : Plane) =
        (newDiskHomeomorph D E).symm ⟨y, hyE⟩ := by
  intro y hyB hyE
  have hyShared : y ∈ range E.shared := by
    rw [← E.base_inter_disk]
    exact ⟨hyB, hyE⟩
  obtain ⟨t, rfl⟩ := hyShared
  let xBase : A := ⟨D.shared t, D.shared_mem_base t⟩
  let xDisk : D.disk.closedRegion :=
    ⟨D.shared t, D.shared_mem_closedRegion t⟩
  have hOld : old xBase =
      ⟨E.shared t, E.shared_mem_base t⟩ := by
    apply Subtype.ext
    exact hshared t
  have hNew : newDiskHomeomorph D E xDisk =
      ⟨E.shared t, E.shared_mem_closedRegion t⟩ := by
    apply Subtype.ext
    exact newDiskHomeomorph_apply_shared D E t
  rw [← hOld, ← hNew, old.symm_apply_apply,
    (newDiskHomeomorph D E).symm_apply_apply]

/-- Attach the new disks while retaining the old homeomorphism pointwise on
the entire old base. -/
def homeomorph :
    (A ∪ D.disk.closedRegion : Set Plane) ≃ₜ
      (B ∪ E.disk.closedRegion : Set Plane) :=
  ClosedCoverHomeomorph.glue
    D.base_closed D.disk.isCompact_closedRegion.isClosed
    E.base_closed E.disk.isCompact_closedRegion.isClosed
    old (newDiskHomeomorph D E)
    (forward_agree D E old hshared)
    (backward_agree D E old hshared)

theorem homeomorph_apply_base
    (x : Plane) (hx : x ∈ A) :
    (homeomorph D E old hshared ⟨x, Or.inl hx⟩ : Plane) =
      old ⟨x, hx⟩ := by
  exact ClosedCoverHomeomorph.coe_glue_apply_of_mem_left
    D.base_closed D.disk.isCompact_closedRegion.isClosed
    E.base_closed E.disk.isCompact_closedRegion.isClosed
    old (newDiskHomeomorph D E)
    (forward_agree D E old hshared)
    (backward_agree D E old hshared) _ hx

theorem homeomorph_apply_newDisk
    (x : Plane) (hx : x ∈ D.disk.closedRegion) :
    (homeomorph D E old hshared ⟨x, Or.inr hx⟩ : Plane) =
      newDiskHomeomorph D E ⟨x, hx⟩ := by
  exact ClosedCoverHomeomorph.coe_glue_apply_of_mem_right
    D.base_closed D.disk.isCompact_closedRegion.isClosed
    E.base_closed E.disk.isCompact_closedRegion.isClosed
    old (newDiskHomeomorph D E)
    (forward_agree D E old hshared)
    (backward_agree D E old hshared) _ hx

end PolygonalDiskAttachment

end

end Schoenflies
