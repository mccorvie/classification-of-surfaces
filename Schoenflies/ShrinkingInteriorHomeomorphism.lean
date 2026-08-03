import Schoenflies.ShrinkingSourceExhaustion

/-!
# The open direct limit of the shrinking compatible disk stages

The compatible finite closed-disk stages of the shrinking Moise sequence
define mutually inverse maps between the open Jordan inside and the open
standard triangle.  Both exhaustions have open interiors covering their
domains, so the direct-limit maps are continuous locally on a finite stage.

Unlike the older localized construction, these stages carry the quantitative
marked-cell estimates, so this homeomorphism is the one that extends across
the Jordan boundary.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- A chosen shrinking source stage whose interior contains the point. -/
def shrinkingSourceStageIndex (x : J.inside) : ℕ := by
  classical
  exact Nat.find
    (I.exists_mem_shrinkingCompatibleStageSourceDisk_interiorRegion x.2)

theorem shrinkingSourceStageIndex_mem_interior (x : J.inside) :
    (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk
        (I.shrinkingSourceStageIndex x)).interiorRegion := by
  classical
  exact Nat.find_spec
    (I.exists_mem_shrinkingCompatibleStageSourceDisk_interiorRegion x.2)

/-- A chosen standard target stage whose interior contains the point. -/
def shrinkingTargetStageIndex
    (y : interior StandardPolygonalCollars.triangleBody) : ℕ := by
  classical
  exact Nat.find (StandardPolygonalCollars.exists_mem_disk_interiorRegion y.2)

theorem shrinkingTargetStageIndex_mem_interior
    (y : interior StandardPolygonalCollars.triangleBody) :
    (y : Plane) ∈
      (StandardPolygonalCollars.disk
        (shrinkingTargetStageIndex y)).interiorRegion := by
  classical
  exact Nat.find_spec
    (StandardPolygonalCollars.exists_mem_disk_interiorRegion y.2)

/-- The direct-limit forward map on the open Jordan inside. -/
def shrinkingInsideMap (x : J.inside) :
    interior StandardPolygonalCollars.triangleBody := by
  let n := I.shrinkingSourceStageIndex x
  have hxClosed : (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := by
    rw [(I.shrinkingCompatibleStageSourceDisk n).closedRegion_eq_union]
    exact Or.inl (I.shrinkingSourceStageIndex_mem_interior x)
  let y := (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
    ⟨x, hxClosed⟩
  exact ⟨y,
    StandardPolygonalCollars.disk_closedRegion_subset_interior_triangleBody
      n y.2⟩

/-- The direct-limit inverse map on the open standard triangle. -/
def shrinkingInsideInv
    (y : interior StandardPolygonalCollars.triangleBody) : J.inside := by
  let n := shrinkingTargetStageIndex y
  have hyClosed : (y : Plane) ∈
      (StandardPolygonalCollars.disk n).closedRegion := by
    rw [(StandardPolygonalCollars.disk n).closedRegion_eq_union]
    exact Or.inl (shrinkingTargetStageIndex_mem_interior y)
  let x := (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm
    ⟨y, hyClosed⟩
  exact ⟨x,
    I.shrinkingCompatibleStageSourceDisk_closedRegion_subset_inside n x.2⟩

/-- On any source stage containing the point, the direct-limit map is exactly
that finite-stage homeomorphism. -/
theorem shrinkingInsideMap_eq_stage
    (m : ℕ) (x : J.inside)
    (hx : (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk m).closedRegion) :
    (I.shrinkingInsideMap x : Plane) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph
        ⟨x, hx⟩ := by
  let n := I.shrinkingSourceStageIndex x
  have hxN : (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := by
    rw [(I.shrinkingCompatibleStageSourceDisk n).closedRegion_eq_union]
    exact Or.inl (I.shrinkingSourceStageIndex_mem_interior x)
  have hn := I.shrinkingCompatibleClosedDiskHomeomorphStage_apply_of_le
    (le_max_right m n) ⟨x, hxN⟩
  have hm := I.shrinkingCompatibleClosedDiskHomeomorphStage_apply_of_le
    (le_max_left m n) ⟨x, hx⟩
  rw [shrinkingInsideMap]
  exact hn.symm.trans hm

/-- On any target stage containing the point, the direct-limit inverse is
exactly that finite-stage inverse. -/
theorem shrinkingInsideInv_eq_stage
    (m : ℕ) (y : interior StandardPolygonalCollars.triangleBody)
    (hy : (y : Plane) ∈
      (StandardPolygonalCollars.disk m).closedRegion) :
    (I.shrinkingInsideInv y : Plane) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage m).homeomorph.symm
        ⟨y, hy⟩ := by
  let n := shrinkingTargetStageIndex y
  have hyN : (y : Plane) ∈
      (StandardPolygonalCollars.disk n).closedRegion := by
    rw [(StandardPolygonalCollars.disk n).closedRegion_eq_union]
    exact Or.inl (shrinkingTargetStageIndex_mem_interior y)
  have hn := I.shrinkingCompatibleClosedDiskHomeomorphStage_symm_apply_of_le
    (le_max_right m n) ⟨y, hyN⟩
  have hm := I.shrinkingCompatibleClosedDiskHomeomorphStage_symm_apply_of_le
    (le_max_left m n) ⟨y, hy⟩
  rw [shrinkingInsideInv]
  exact hn.symm.trans hm

theorem shrinkingInsideInv_leftInverse :
    Function.LeftInverse I.shrinkingInsideInv I.shrinkingInsideMap := by
  intro x
  let n := I.shrinkingSourceStageIndex x
  have hxClosed : (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := by
    rw [(I.shrinkingCompatibleStageSourceDisk n).closedRegion_eq_union]
    exact Or.inl (I.shrinkingSourceStageIndex_mem_interior x)
  have hyClosed : (I.shrinkingInsideMap x : Plane) ∈
      (StandardPolygonalCollars.disk n).closedRegion := by
    rw [I.shrinkingInsideMap_eq_stage n x hxClosed]
    exact ((I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
      ⟨x, hxClosed⟩).2
  apply Subtype.ext
  rw [I.shrinkingInsideInv_eq_stage n (I.shrinkingInsideMap x) hyClosed]
  have harg :
      (⟨(I.shrinkingInsideMap x : Plane), hyClosed⟩ :
        (StandardPolygonalCollars.disk n).closedRegion) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
        ⟨x, hxClosed⟩ := by
    apply Subtype.ext
    exact I.shrinkingInsideMap_eq_stage n x hxClosed
  rw [harg,
    (I.shrinkingCompatibleClosedDiskHomeomorphStage
      n).homeomorph.symm_apply_apply]

theorem shrinkingInsideInv_rightInverse :
    Function.RightInverse I.shrinkingInsideInv I.shrinkingInsideMap := by
  intro y
  let n := shrinkingTargetStageIndex y
  have hyClosed : (y : Plane) ∈
      (StandardPolygonalCollars.disk n).closedRegion := by
    rw [(StandardPolygonalCollars.disk n).closedRegion_eq_union]
    exact Or.inl (shrinkingTargetStageIndex_mem_interior y)
  have hxClosed : (I.shrinkingInsideInv y : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := by
    rw [I.shrinkingInsideInv_eq_stage n y hyClosed]
    exact ((I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm
      ⟨y, hyClosed⟩).2
  apply Subtype.ext
  rw [I.shrinkingInsideMap_eq_stage n (I.shrinkingInsideInv y) hxClosed]
  have harg :
      (⟨(I.shrinkingInsideInv y : Plane), hxClosed⟩ :
        (I.shrinkingCompatibleStageSourceDisk n).closedRegion) =
      (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm
        ⟨y, hyClosed⟩ := by
    apply Subtype.ext
    exact I.shrinkingInsideInv_eq_stage n y hyClosed
  rw [harg,
    (I.shrinkingCompatibleClosedDiskHomeomorphStage
      n).homeomorph.apply_symm_apply]

/-- The source-stage interiors as open subsets of the Jordan inside. -/
def shrinkingSourceInteriorSet (n : ℕ) : Set J.inside :=
  ((↑) : J.inside → Plane) ⁻¹'
    (I.shrinkingCompatibleStageSourceDisk n).interiorRegion

theorem isOpen_shrinkingSourceInteriorSet (n : ℕ) :
    IsOpen (I.shrinkingSourceInteriorSet n) :=
  (I.shrinkingCompatibleStageSourceDisk n).isOpen_interiorRegion.preimage
    continuous_subtype_val

theorem iUnion_shrinkingSourceInteriorSet :
    ⋃ n : ℕ, I.shrinkingSourceInteriorSet n = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact I.exists_mem_shrinkingCompatibleStageSourceDisk_interiorRegion x.2

theorem continuousOn_shrinkingInsideMap_sourceInterior (n : ℕ) :
    ContinuousOn I.shrinkingInsideMap
      (I.shrinkingSourceInteriorSet n) := by
  rw [continuousOn_iff_continuous_restrict]
  let inclusion : (I.shrinkingSourceInteriorSet n) →
      (I.shrinkingCompatibleStageSourceDisk n).closedRegion := fun x =>
    ⟨x, by
      rw [(I.shrinkingCompatibleStageSourceDisk n).closedRegion_eq_union]
      exact Or.inl x.2⟩
  have hinclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let g : (I.shrinkingSourceInteriorSet n) →
      interior StandardPolygonalCollars.triangleBody := fun x =>
    let y := (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph
      (inclusion x)
    ⟨y,
      StandardPolygonalCollars.disk_closedRegion_subset_interior_triangleBody
        n y.2⟩
  have hg : Continuous g := by
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val : Continuous
      ((↑) : (StandardPolygonalCollars.disk n).closedRegion →
        Plane)).comp <|
      (I.shrinkingCompatibleClosedDiskHomeomorphStage
        n).homeomorph.continuous.comp hinclusion
  apply hg.congr
  intro x
  apply Subtype.ext
  exact (I.shrinkingInsideMap_eq_stage n x.1 <| by
    rw [(I.shrinkingCompatibleStageSourceDisk n).closedRegion_eq_union]
    exact Or.inl x.2).symm

theorem continuous_shrinkingInsideMap :
    Continuous I.shrinkingInsideMap := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := I.shrinkingSourceInteriorSet)
  · exact I.continuousOn_shrinkingInsideMap_sourceInterior
  · exact I.isOpen_shrinkingSourceInteriorSet
  · exact I.iUnion_shrinkingSourceInteriorSet

/-- The target-stage interiors as open subsets of the standard triangle. -/
def shrinkingTargetInteriorSet (n : ℕ) :
    Set (interior StandardPolygonalCollars.triangleBody) :=
  ((↑) : interior StandardPolygonalCollars.triangleBody → Plane) ⁻¹'
    (StandardPolygonalCollars.disk n).interiorRegion

theorem isOpen_shrinkingTargetInteriorSet (n : ℕ) :
    IsOpen (shrinkingTargetInteriorSet n) :=
  (StandardPolygonalCollars.disk n).isOpen_interiorRegion.preimage
    continuous_subtype_val

theorem iUnion_shrinkingTargetInteriorSet :
    ⋃ n : ℕ, shrinkingTargetInteriorSet n = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact StandardPolygonalCollars.exists_mem_disk_interiorRegion y.2

theorem continuousOn_shrinkingInsideInv_targetInterior (n : ℕ) :
    ContinuousOn I.shrinkingInsideInv (shrinkingTargetInteriorSet n) := by
  rw [continuousOn_iff_continuous_restrict]
  let inclusion : (shrinkingTargetInteriorSet n) →
      (StandardPolygonalCollars.disk n).closedRegion := fun y =>
    ⟨y, by
      rw [(StandardPolygonalCollars.disk n).closedRegion_eq_union]
      exact Or.inl y.2⟩
  have hinclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let g : (shrinkingTargetInteriorSet n) → J.inside := fun y =>
    let x := (I.shrinkingCompatibleClosedDiskHomeomorphStage n).homeomorph.symm
      (inclusion y)
    ⟨x, I.shrinkingCompatibleStageSourceDisk_closedRegion_subset_inside
      n x.2⟩
  have hg : Continuous g := by
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val : Continuous
      ((↑) : (I.shrinkingCompatibleStageSourceDisk n).closedRegion →
        Plane)).comp <|
      (I.shrinkingCompatibleClosedDiskHomeomorphStage
        n).homeomorph.symm.continuous.comp hinclusion
  apply hg.congr
  intro y
  apply Subtype.ext
  exact (I.shrinkingInsideInv_eq_stage n y.1 <| by
    rw [(StandardPolygonalCollars.disk n).closedRegion_eq_union]
    exact Or.inl y.2).symm

theorem continuous_shrinkingInsideInv :
    Continuous I.shrinkingInsideInv := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := shrinkingTargetInteriorSet)
  · exact I.continuousOn_shrinkingInsideInv_targetInterior
  · exact isOpen_shrinkingTargetInteriorSet
  · exact iUnion_shrinkingTargetInteriorSet

/-- The shrinking compatible stages assemble to a homeomorphism from the
open Jordan inside onto the open standard triangle.  This is the direct
limit that the boundary extension of Moise Chapter 9 completes. -/
def shrinkingInsideHomeomorph :
    J.inside ≃ₜ interior StandardPolygonalCollars.triangleBody where
  toFun := I.shrinkingInsideMap
  invFun := I.shrinkingInsideInv
  left_inv := I.shrinkingInsideInv_leftInverse
  right_inv := I.shrinkingInsideInv_rightInverse
  continuous_toFun := I.continuous_shrinkingInsideMap
  continuous_invFun := I.continuous_shrinkingInsideInv

end JordanCircle.InitialAngularArcs

end

end Schoenflies
