import Schoenflies.MoiseBandCellSeams
import Schoenflies.SharedArcDiskSeparation

/-!
# Filled intersections of adjacent recursive Moise cells

The carrier calculation gives the exact common seam.  Once the two cells
have the outward orientation relative to the preceding polygonal disk, an
interior point of either old parent crosscut witnesses that the rest of its
cell boundary lies outside the neighboring cell.  The shared-arc separation
lemma then upgrades boundary control to disjoint open interiors and an exact
closed-disk intersection.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

noncomputable def crosscutMidpoint
    (_L : RecursiveInsideCollarStep.Later F hn)
    (a : LevelAddress n) : Plane :=
  F.synchronizedCrosscutPath a ⟨1 / 2, by norm_num⟩

theorem crosscutMidpoint_mem_parentClosedRegion (a : LevelAddress n) :
    L.crosscutMidpoint a ∈
      (F.synchronizedPolygonalCircle hn).closedRegion := by
  rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
  apply Or.inr
  rw [F.carrier_synchronizedPolygonalCircle hn]
  exact Set.mem_iUnion.mpr ⟨a, ⟨⟨1 / 2, by norm_num⟩, rfl⟩⟩

theorem crosscutMidpoint_mem_cellCarrier (a : LevelAddress n) :
    L.crosscutMidpoint a ∈ (L.moiseBandPolygonalCircle a).carrier := by
  rw [L.moiseBandPolygonalCircle_carrier a]
  apply L.parentCrosscutRange_subset_moiseBandCarrier a
  exact ⟨⟨1 / 2, by norm_num⟩, rfl⟩

theorem crosscutMidpoint_not_mem_nextCrosscutRange
    (a : LevelAddress n) :
    L.crosscutMidpoint a ∉
      range (F.synchronizedCrosscutPath (nextLevelAddress n a)) := by
  intro hzNext
  have hzCommon : L.crosscutMidpoint a ∈
      range (F.synchronizedCrosscutPath a) ∩
        range (F.synchronizedCrosscutPath (nextLevelAddress n a)) :=
    ⟨⟨⟨1 / 2, by norm_num⟩, rfl⟩, hzNext⟩
  rw [F.range_synchronizedCrosscutPath_inter_next hn a] at hzCommon
  have hzEq : L.crosscutMidpoint a = F.rightSynchronizedPoint a :=
    mem_singleton_iff.mp hzCommon
  have ht : (⟨1 / 2, by norm_num⟩ : unitInterval) = 1 :=
    F.synchronizedCrosscutPath_injective a (by
      simpa only [crosscutMidpoint, Path.target] using hzEq)
  have hval := congrArg Subtype.val ht
  norm_num at hval

theorem nextCrosscutMidpoint_not_mem_crosscutRange
    (a : LevelAddress n) :
    L.crosscutMidpoint (nextLevelAddress n a) ∉
      range (F.synchronizedCrosscutPath a) := by
  intro hzCurrent
  have hzCommon : L.crosscutMidpoint (nextLevelAddress n a) ∈
      range (F.synchronizedCrosscutPath a) ∩
        range (F.synchronizedCrosscutPath (nextLevelAddress n a)) :=
    ⟨hzCurrent, ⟨⟨1 / 2, by norm_num⟩, rfl⟩⟩
  rw [F.range_synchronizedCrosscutPath_inter_next hn a] at hzCommon
  have hzEq : L.crosscutMidpoint (nextLevelAddress n a) =
      F.rightSynchronizedPoint a := mem_singleton_iff.mp hzCommon
  have hzSource : L.crosscutMidpoint (nextLevelAddress n a) =
      F.leftSynchronizedPoint (nextLevelAddress n a) := by
    rwa [← F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a]
  have ht : (⟨1 / 2, by norm_num⟩ : unitInterval) = 0 :=
    F.synchronizedCrosscutPath_injective (nextLevelAddress n a) (by
      simpa only [crosscutMidpoint, Path.source] using hzSource)
  have hval := congrArg Subtype.val ht
  norm_num at hval

/-- The old crosscut portion of the current cell supplies an exterior
witness for the following cell. -/
theorem exists_cellCarrier_mem_nextExterior
    (a : LevelAddress n)
    (hnext : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle (nextLevelAddress n a)).closedRegion =
      range (F.synchronizedCrosscutPath (nextLevelAddress n a))) :
    ∃ z ∈ (L.moiseBandPolygonalCircle a).carrier,
      z ∈ (L.moiseBandPolygonalCircle
        (nextLevelAddress n a)).exteriorRegion := by
  let z := L.crosscutMidpoint a
  let Q := L.moiseBandPolygonalCircle (nextLevelAddress n a)
  have hzParent := L.crosscutMidpoint_mem_parentClosedRegion a
  have hzNotClosed : z ∉ Q.closedRegion := by
    intro hzQ
    apply L.crosscutMidpoint_not_mem_nextCrosscutRange a
    rw [← hnext]
    exact ⟨hzParent, hzQ⟩
  have hzNotCarrier : z ∉ Q.carrier := by
    intro hzQ
    apply hzNotClosed
    rw [Q.closedRegion_eq_union]
    exact Or.inr hzQ
  have hzNotInterior : z ∉ Q.interiorRegion := by
    intro hzQ
    apply hzNotClosed
    rw [Q.closedRegion_eq_union]
    exact Or.inl hzQ
  refine ⟨z, L.crosscutMidpoint_mem_cellCarrier a, ?_⟩
  have hzComplement : z ∈ Q.carrierᶜ := hzNotCarrier
  rw [← Q.interior_union_exterior] at hzComplement
  exact hzComplement.resolve_left hzNotInterior

/-- The following old crosscut symmetrically supplies an exterior witness
for the current cell. -/
theorem exists_nextCellCarrier_mem_exterior
    (a : LevelAddress n)
    (hcurrent : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a)) :
    ∃ z ∈ (L.moiseBandPolygonalCircle
        (nextLevelAddress n a)).carrier,
      z ∈ (L.moiseBandPolygonalCircle a).exteriorRegion := by
  let z := L.crosscutMidpoint (nextLevelAddress n a)
  let P := L.moiseBandPolygonalCircle a
  have hzParent := L.crosscutMidpoint_mem_parentClosedRegion
    (nextLevelAddress n a)
  have hzNotClosed : z ∉ P.closedRegion := by
    intro hzP
    apply L.nextCrosscutMidpoint_not_mem_crosscutRange a
    rw [← hcurrent]
    exact ⟨hzParent, hzP⟩
  have hzNotCarrier : z ∉ P.carrier := by
    intro hzP
    apply hzNotClosed
    rw [P.closedRegion_eq_union]
    exact Or.inr hzP
  have hzNotInterior : z ∉ P.interiorRegion := by
    intro hzP
    apply hzNotClosed
    rw [P.closedRegion_eq_union]
    exact Or.inl hzP
  refine ⟨z, L.crosscutMidpoint_mem_cellCarrier
    (nextLevelAddress n a), ?_⟩
  have hzComplement : z ∈ P.carrierᶜ := hzNotCarrier
  rw [← P.interior_union_exterior] at hzComplement
  exact hzComplement.resolve_left hzNotInterior

theorem cellCarrier_disjoint_nextInterior
    (a : LevelAddress n)
    (hnext : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle (nextLevelAddress n a)).closedRegion =
      range (F.synchronizedCrosscutPath (nextLevelAddress n a))) :
    Disjoint (L.moiseBandPolygonalCircle a).carrier
      (L.moiseBandPolygonalCircle
        (nextLevelAddress n a)).interiorRegion := by
  apply PolygonalCircle.carrier_disjoint_interiorRegion_of_inter_eq_arc
    (L.moiseBandPolygonalCircle a)
    (L.moiseBandPolygonalCircle (nextLevelAddress n a))
    (L.adjacentMoiseBandSideSeamPath a)
    (L.adjacentMoiseBandSideSeamPath_injective a)
  · rw [L.moiseBandPolygonalCircle_carrier a,
      L.moiseBandPolygonalCircle_carrier (nextLevelAddress n a),
      L.moiseBandCarrier_inter_next a,
      ← L.range_adjacentMoiseBandSideSeamPath a]
  · exact L.exists_cellCarrier_mem_nextExterior a hnext

theorem nextCellCarrier_disjoint_interior
    (a : LevelAddress n)
    (hcurrent : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a)) :
    Disjoint (L.moiseBandPolygonalCircle (nextLevelAddress n a)).carrier
      (L.moiseBandPolygonalCircle a).interiorRegion := by
  apply PolygonalCircle.carrier_disjoint_interiorRegion_of_inter_eq_arc
    (L.moiseBandPolygonalCircle (nextLevelAddress n a))
    (L.moiseBandPolygonalCircle a)
    (L.adjacentMoiseBandSideSeamPath a)
    (L.adjacentMoiseBandSideSeamPath_injective a)
  · rw [L.moiseBandPolygonalCircle_carrier a,
      L.moiseBandPolygonalCircle_carrier (nextLevelAddress n a),
      Set.inter_comm, L.moiseBandCarrier_inter_next a,
      ← L.range_adjacentMoiseBandSideSeamPath a]
  · exact L.exists_nextCellCarrier_mem_exterior a hcurrent

/-- Outward-oriented adjacent Moise cells have disjoint open disks. -/
theorem disjoint_cellInterior_next
    (a : LevelAddress n)
    (hcurrent : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a))
    (hnext : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle (nextLevelAddress n a)).closedRegion =
      range (F.synchronizedCrosscutPath (nextLevelAddress n a))) :
    Disjoint (L.moiseBandPolygonalCircle a).interiorRegion
      (L.moiseBandPolygonalCircle
        (nextLevelAddress n a)).interiorRegion := by
  apply (L.moiseBandPolygonalCircle a)
    |>.disjoint_interiorRegion_of_boundary_avoidance
      (L.moiseBandPolygonalCircle (nextLevelAddress n a))
  · exact L.cellCarrier_disjoint_nextInterior a hnext
  · exact L.nextCellCarrier_disjoint_interior a hcurrent
  · obtain ⟨z, hzNext, hzExterior⟩ :=
      L.exists_nextCellCarrier_mem_exterior a hcurrent
    exact ⟨z, hzNext, fun hzCurrent =>
      Set.disjoint_left.mp
        (L.moiseBandPolygonalCircle a).disjoint_closedRegion_exteriorRegion
        (by
          rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr hzCurrent)
        hzExterior⟩

/-- Exact filled overlap: adjacent closed Moise cells meet only along their
common side seam. -/
theorem cellClosedRegion_inter_next
    (a : LevelAddress n)
    (hcurrent : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle a).closedRegion =
      range (F.synchronizedCrosscutPath a))
    (hnext : (F.synchronizedPolygonalCircle hn).closedRegion ∩
        (L.moiseBandPolygonalCircle (nextLevelAddress n a)).closedRegion =
      range (F.synchronizedCrosscutPath (nextLevelAddress n a))) :
    (L.moiseBandPolygonalCircle a).closedRegion ∩
        (L.moiseBandPolygonalCircle
          (nextLevelAddress n a)).closedRegion =
      L.adjacentMoiseBandSideSeam a := by
  let P := L.moiseBandPolygonalCircle a
  let Q := L.moiseBandPolygonalCircle (nextLevelAddress n a)
  have hII := L.disjoint_cellInterior_next a hcurrent hnext
  have hPQ := L.cellCarrier_disjoint_nextInterior a hnext
  have hQP := L.nextCellCarrier_disjoint_interior a hcurrent
  apply Set.Subset.antisymm
  · rintro x ⟨hxP, hxQ⟩
    rw [P.closedRegion_eq_union] at hxP
    rw [Q.closedRegion_eq_union] at hxQ
    rcases hxP with hxPI | hxPC <;> rcases hxQ with hxQI | hxQC
    · exact False.elim <| Set.disjoint_left.mp hII hxPI hxQI
    · exact False.elim <| Set.disjoint_left.mp hQP hxQC hxPI
    · exact False.elim <| Set.disjoint_left.mp hPQ hxPC hxQI
    · rw [← L.moiseBandCarrier_inter_next a,
        ← L.moiseBandPolygonalCircle_carrier a,
        ← L.moiseBandPolygonalCircle_carrier (nextLevelAddress n a)]
      exact ⟨hxPC, hxQC⟩
  · exact L.adjacentMoiseBandSideSeam_subset_closedRegion_inter a

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
