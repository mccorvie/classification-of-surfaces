import Schoenflies.CompatibleDiskStages

/-!
# The direct-limit homeomorphism of open Jordan disks

The compatible finite closed-disk stages define mutually inverse maps on the
unions of the source and target exhaustions.  Since the exhaustion interiors
form open covers, the resulting maps are continuous locally on a finite
stage.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Every point of the Jordan inside belongs to the interior of a compatible
source stage. -/
theorem exists_mem_compatibleSourceStage_interior (x : J.inside) :
    ∃ n : ℕ,
      (x : Plane) ∈
        (I.localizedMarkedPolygonalDisk (n + 2)).interiorRegion := by
  obtain ⟨N, hN⟩ :=
    I.eventually_mem_localizedMarkedPolygonalDisk_interior x.2
  refine ⟨N, ?_⟩
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    hN (N + 1) (Nat.le_succ N)

/-- A chosen finite stage containing an inside point in its interior. -/
def compatibleSourceStageIndex
    (I : J.InitialAngularArcs) (x : J.inside) : ℕ := by
  classical
  exact Nat.find (I.exists_mem_compatibleSourceStage_interior x)

theorem compatibleSourceStageIndex_mem_interior (x : J.inside) :
    (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk
        (I.compatibleSourceStageIndex x + 2)).interiorRegion := by
  classical
  exact Nat.find_spec (I.exists_mem_compatibleSourceStage_interior x)

/-- Every point of the open standard triangle belongs to the interior of a
compatible target stage. -/
theorem exists_mem_compatibleTargetStage_interior
    (y : interior StandardPolygonalCollars.triangleBody) :
    ∃ n : ℕ,
      (y : Plane) ∈
        (StandardPolygonalCollars.disk (n + 2)).interiorRegion := by
  obtain ⟨N, hN⟩ :=
    StandardPolygonalCollars.exists_mem_disk_interiorRegion y.2
  have hNClosed : (y : Plane) ∈
      (StandardPolygonalCollars.disk N).closedRegion := by
    rw [(StandardPolygonalCollars.disk N).closedRegion_eq_union]
    exact Or.inl hN
  have hN1Interior : (y : Plane) ∈
      (StandardPolygonalCollars.disk (N + 1)).interiorRegion :=
    StandardPolygonalCollars.disk_strictlyNested N hNClosed
  have hN1Closed : (y : Plane) ∈
      (StandardPolygonalCollars.disk (N + 1)).closedRegion := by
    rw [(StandardPolygonalCollars.disk (N + 1)).closedRegion_eq_union]
    exact Or.inl hN1Interior
  exact ⟨N, StandardPolygonalCollars.disk_strictlyNested (N + 1) hN1Closed⟩

/-- A chosen standard target stage containing a triangle-interior point. -/
def compatibleTargetStageIndex
    (y : interior StandardPolygonalCollars.triangleBody) : ℕ :=
  by
    classical
    exact Nat.find (exists_mem_compatibleTargetStage_interior y)

theorem compatibleTargetStageIndex_mem_interior
    (y : interior StandardPolygonalCollars.triangleBody) :
    (y : Plane) ∈
      (StandardPolygonalCollars.disk
        (compatibleTargetStageIndex y + 2)).interiorRegion := by
  classical
  exact Nat.find_spec (exists_mem_compatibleTargetStage_interior y)

/-- The direct-limit forward map on the open Jordan inside. -/
def compatibleInsideMap
    (I : J.InitialAngularArcs) (x : J.inside) :
    interior StandardPolygonalCollars.triangleBody := by
  let n := I.compatibleSourceStageIndex x
  have hxClosed : (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion := by
    rw [(I.localizedMarkedPolygonalDisk (n + 2)).closedRegion_eq_union]
    exact Or.inl (I.compatibleSourceStageIndex_mem_interior x)
  let y := (I.compatibleClosedDiskHomeomorphStage n).homeomorph
    ⟨x, hxClosed⟩
  exact ⟨y,
    StandardPolygonalCollars.disk_closedRegion_subset_interior_triangleBody
      (n + 2) y.2⟩

/-- The direct-limit inverse map on the open standard triangle. -/
def compatibleInsideInv (I : J.InitialAngularArcs)
    (y : interior StandardPolygonalCollars.triangleBody) : J.inside := by
  let n := compatibleTargetStageIndex y
  have hyClosed : (y : Plane) ∈
      (StandardPolygonalCollars.disk (n + 2)).closedRegion := by
    rw [(StandardPolygonalCollars.disk (n + 2)).closedRegion_eq_union]
    exact Or.inl (compatibleTargetStageIndex_mem_interior y)
  let x := (I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm
    ⟨y, hyClosed⟩
  exact ⟨x,
    I.localizedMarkedPolygonalDisk_closedRegion_subset_inside
      (n + 2) x.2⟩

/-- On any source stage containing the point, the direct-limit map is exactly
that finite-stage homeomorphism. -/
theorem compatibleInsideMap_eq_stage
    (m : ℕ) (x : J.inside)
    (hx : (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk (m + 2)).closedRegion) :
    (I.compatibleInsideMap x : Plane) =
      (I.compatibleClosedDiskHomeomorphStage m).homeomorph ⟨x, hx⟩ := by
  let n := I.compatibleSourceStageIndex x
  have hxN : (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion := by
    rw [(I.localizedMarkedPolygonalDisk (n + 2)).closedRegion_eq_union]
    exact Or.inl (I.compatibleSourceStageIndex_mem_interior x)
  let k := max m n
  have hmk : m ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  have hn := I.compatibleClosedDiskHomeomorphStage_apply_of_le
    hnk ⟨x, hxN⟩
  have hm := I.compatibleClosedDiskHomeomorphStage_apply_of_le
    hmk ⟨x, hx⟩
  rw [compatibleInsideMap]
  exact hn.symm.trans hm

/-- On any target stage containing the point, the direct-limit inverse is
exactly that finite-stage inverse. -/
theorem compatibleInsideInv_eq_stage
    (m : ℕ) (y : interior StandardPolygonalCollars.triangleBody)
    (hy : (y : Plane) ∈
      (StandardPolygonalCollars.disk (m + 2)).closedRegion) :
    (I.compatibleInsideInv y : Plane) =
      (I.compatibleClosedDiskHomeomorphStage m).homeomorph.symm
        ⟨y, hy⟩ := by
  let n := compatibleTargetStageIndex y
  have hyN : (y : Plane) ∈
      (StandardPolygonalCollars.disk (n + 2)).closedRegion := by
    rw [(StandardPolygonalCollars.disk (n + 2)).closedRegion_eq_union]
    exact Or.inl (compatibleTargetStageIndex_mem_interior y)
  let k := max m n
  have hmk : m ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  have hn := I.compatibleClosedDiskHomeomorphStage_symm_apply_of_le
    hnk ⟨y, hyN⟩
  have hm := I.compatibleClosedDiskHomeomorphStage_symm_apply_of_le
    hmk ⟨y, hy⟩
  rw [compatibleInsideInv]
  exact hn.symm.trans hm

theorem compatibleInsideInv_leftInverse :
    Function.LeftInverse I.compatibleInsideInv I.compatibleInsideMap := by
  intro x
  let n := I.compatibleSourceStageIndex x
  have hxClosed : (x : Plane) ∈
      (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion := by
    rw [(I.localizedMarkedPolygonalDisk (n + 2)).closedRegion_eq_union]
    exact Or.inl (I.compatibleSourceStageIndex_mem_interior x)
  have hyClosed : (I.compatibleInsideMap x : Plane) ∈
      (StandardPolygonalCollars.disk (n + 2)).closedRegion := by
    rw [I.compatibleInsideMap_eq_stage n x hxClosed]
    exact ((I.compatibleClosedDiskHomeomorphStage n).homeomorph
      ⟨x, hxClosed⟩).2
  apply Subtype.ext
  rw [I.compatibleInsideInv_eq_stage n (I.compatibleInsideMap x) hyClosed]
  have harg :
      (⟨(I.compatibleInsideMap x : Plane), hyClosed⟩ :
        (StandardPolygonalCollars.disk (n + 2)).closedRegion) =
      (I.compatibleClosedDiskHomeomorphStage n).homeomorph
        ⟨x, hxClosed⟩ := by
    apply Subtype.ext
    exact I.compatibleInsideMap_eq_stage n x hxClosed
  rw [harg,
    (I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm_apply_apply]

theorem compatibleInsideInv_rightInverse :
    Function.RightInverse I.compatibleInsideInv I.compatibleInsideMap := by
  intro y
  let n := compatibleTargetStageIndex y
  have hyClosed : (y : Plane) ∈
      (StandardPolygonalCollars.disk (n + 2)).closedRegion := by
    rw [(StandardPolygonalCollars.disk (n + 2)).closedRegion_eq_union]
    exact Or.inl (compatibleTargetStageIndex_mem_interior y)
  have hxClosed : (I.compatibleInsideInv y : Plane) ∈
      (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion := by
    rw [I.compatibleInsideInv_eq_stage n y hyClosed]
    exact ((I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm
      ⟨y, hyClosed⟩).2
  apply Subtype.ext
  rw [I.compatibleInsideMap_eq_stage n (I.compatibleInsideInv y) hxClosed]
  have harg :
      (⟨(I.compatibleInsideInv y : Plane), hxClosed⟩ :
        (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion) =
      (I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm
        ⟨y, hyClosed⟩ := by
    apply Subtype.ext
    exact I.compatibleInsideInv_eq_stage n y hyClosed
  rw [harg,
    (I.compatibleClosedDiskHomeomorphStage n).homeomorph.apply_symm_apply]

/-- The source-stage interiors as open subsets of the Jordan inside. -/
def compatibleSourceInteriorSet (n : ℕ) : Set J.inside :=
  ((↑) : J.inside → Plane) ⁻¹'
    (I.localizedMarkedPolygonalDisk (n + 2)).interiorRegion

theorem isOpen_compatibleSourceInteriorSet (n : ℕ) :
    IsOpen (I.compatibleSourceInteriorSet n) :=
  (I.localizedMarkedPolygonalDisk (n + 2)).isOpen_interiorRegion.preimage
    continuous_subtype_val

theorem iUnion_compatibleSourceInteriorSet :
    ⋃ n : ℕ, I.compatibleSourceInteriorSet n = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact I.exists_mem_compatibleSourceStage_interior x

/-- On each source exhaustion interior, the direct-limit map is the
restriction of one finite-stage homeomorphism. -/
theorem continuousOn_compatibleInsideMap_sourceInterior (n : ℕ) :
    ContinuousOn I.compatibleInsideMap
      (I.compatibleSourceInteriorSet n) := by
  rw [continuousOn_iff_continuous_restrict]
  let inclusion : (I.compatibleSourceInteriorSet n) →
      (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion := fun x =>
    ⟨x, by
      rw [(I.localizedMarkedPolygonalDisk (n + 2)).closedRegion_eq_union]
      exact Or.inl x.2⟩
  have hinclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let g : (I.compatibleSourceInteriorSet n) →
      interior StandardPolygonalCollars.triangleBody := fun x =>
    let y := (I.compatibleClosedDiskHomeomorphStage n).homeomorph
      (inclusion x)
    ⟨y,
      StandardPolygonalCollars.disk_closedRegion_subset_interior_triangleBody
        (n + 2) y.2⟩
  have hg : Continuous g := by
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val : Continuous
      ((↑) : (StandardPolygonalCollars.disk (n + 2)).closedRegion →
        Plane)).comp <|
      (I.compatibleClosedDiskHomeomorphStage n).homeomorph.continuous.comp
        hinclusion
  apply hg.congr
  intro x
  apply Subtype.ext
  exact (I.compatibleInsideMap_eq_stage n x.1 <| by
    rw [(I.localizedMarkedPolygonalDisk (n + 2)).closedRegion_eq_union]
    exact Or.inl x.2).symm

theorem continuous_compatibleInsideMap :
    Continuous I.compatibleInsideMap := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := I.compatibleSourceInteriorSet)
  · exact I.continuousOn_compatibleInsideMap_sourceInterior
  · exact I.isOpen_compatibleSourceInteriorSet
  · exact I.iUnion_compatibleSourceInteriorSet

/-- The target-stage interiors as open subsets of the standard triangle. -/
def compatibleTargetInteriorSet (n : ℕ) :
    Set (interior StandardPolygonalCollars.triangleBody) :=
  ((↑) : interior StandardPolygonalCollars.triangleBody → Plane) ⁻¹'
    (StandardPolygonalCollars.disk (n + 2)).interiorRegion

theorem isOpen_compatibleTargetInteriorSet (n : ℕ) :
    IsOpen (compatibleTargetInteriorSet n) :=
  (StandardPolygonalCollars.disk (n + 2)).isOpen_interiorRegion.preimage
    continuous_subtype_val

theorem iUnion_compatibleTargetInteriorSet :
    ⋃ n : ℕ, compatibleTargetInteriorSet n = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_compatibleTargetStage_interior y

/-- On each target exhaustion interior, the direct-limit inverse is one
finite-stage inverse. -/
theorem continuousOn_compatibleInsideInv_targetInterior (n : ℕ) :
    ContinuousOn I.compatibleInsideInv (compatibleTargetInteriorSet n) := by
  rw [continuousOn_iff_continuous_restrict]
  let inclusion : (compatibleTargetInteriorSet n) →
      (StandardPolygonalCollars.disk (n + 2)).closedRegion := fun y =>
    ⟨y, by
      rw [(StandardPolygonalCollars.disk (n + 2)).closedRegion_eq_union]
      exact Or.inl y.2⟩
  have hinclusion : Continuous inclusion :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let g : (compatibleTargetInteriorSet n) → J.inside := fun y =>
    let x := (I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm
      (inclusion y)
    ⟨x, I.localizedMarkedPolygonalDisk_closedRegion_subset_inside
      (n + 2) x.2⟩
  have hg : Continuous g := by
    apply continuous_induced_rng.mpr
    exact (continuous_subtype_val : Continuous
      ((↑) : (I.localizedMarkedPolygonalDisk (n + 2)).closedRegion →
        Plane)).comp <|
      (I.compatibleClosedDiskHomeomorphStage n).homeomorph.symm.continuous.comp
        hinclusion
  apply hg.congr
  intro y
  apply Subtype.ext
  exact (I.compatibleInsideInv_eq_stage n y.1 <| by
    rw [(StandardPolygonalCollars.disk (n + 2)).closedRegion_eq_union]
    exact Or.inl y.2).symm

theorem continuous_compatibleInsideInv :
    Continuous I.compatibleInsideInv := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := compatibleTargetInteriorSet)
  · exact I.continuousOn_compatibleInsideInv_targetInterior
  · exact isOpen_compatibleTargetInteriorSet
  · exact iUnion_compatibleTargetInteriorSet

/-- The compatible finite collar stages assemble to a homeomorphism from the
open Jordan inside onto the open standard triangle. -/
def compatibleInsideHomeomorph :
    J.inside ≃ₜ interior StandardPolygonalCollars.triangleBody where
  toFun := I.compatibleInsideMap
  invFun := I.compatibleInsideInv
  left_inv := I.compatibleInsideInv_leftInverse
  right_inv := I.compatibleInsideInv_rightInverse
  continuous_toFun := I.continuous_compatibleInsideMap
  continuous_invFun := I.continuous_compatibleInsideInv

end JordanCircle.InitialAngularArcs

end


end Schoenflies
