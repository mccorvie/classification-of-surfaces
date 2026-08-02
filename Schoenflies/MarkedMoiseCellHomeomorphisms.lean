import Schoenflies.MoiseCellBoundaryRoutes
import Schoenflies.TopologicalDiskBoundaryExtension
import Schoenflies.TwoArcCarrierHomeomorph

/-!
# Seam-compatible homeomorphisms of recursive Moise cells

An embedded marked route in each source and target cell is completed to the
other boundary arc.  Matching the two routes with their literal nested path
parameters and extending the resulting boundary homeomorphism across the
polygonal disks gives a cell map controlled simultaneously on the incoming
seam, the old synchronized crosscut, and the outgoing seam.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle

/-- Complete a prescribed embedded boundary path to a two-arc presentation,
while retaining that path literally as the first field. -/
noncomputable def boundarySplitOfInjectivePath
    (J : JordanCircle) {x y : Plane} (p : Path x y)
    (hp : Injective p) (hxy : x ≠ y)
    (hcarrier : range p ⊆ J.carrier) : J.TwoBoundaryArcPaths x y := by
  let S := Classical.choice <| J.exists_twoBoundaryArcPaths
    (hcarrier (Path.source_mem_range p))
    (hcarrier (Path.target_mem_range p)) hxy
  have hranges := S.range_eq_first_or_second_of_path p hp hcarrier
  by_cases hfirst : range p = range S.first
  · exact {
      first := p
      second := S.second
      first_injective := hp
      second_injective := S.second_injective
      cover := by rw [hfirst, S.cover]
      overlap := by rw [hfirst, S.overlap] }
  · have hsecond : range p = range S.second :=
      hranges.resolve_left hfirst
    exact {
      first := p
      second := S.first.symm
      first_injective := hp
      second_injective :=
        S.first_injective.comp unitInterval.symm_bijective.injective
      cover := by
        rw [hsecond, Path.symm_range, Set.union_comm, S.cover]
      overlap := by
        rw [hsecond, Path.symm_range, Set.inter_comm, S.overlap] }

@[simp] theorem boundarySplitOfInjectivePath_first
    (J : JordanCircle) {x y : Plane} (p : Path x y)
    (hp : Injective p) (hxy : x ≠ y)
    (hcarrier : range p ⊆ J.carrier) :
    (J.boundarySplitOfInjectivePath p hp hxy hcarrier).first = p := by
  simp only [boundarySplitOfInjectivePath]
  split <;> rfl

end JordanCircle

namespace MarkedPolygonalDisk

variable {P Q : PolygonalCircle} {x y u v : Plane}

/-- Boundary homeomorphism obtained by matching two marked complementary-arc
presentations with the same unit-interval parameters. -/
def boundaryHomeomorph
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y)
    (T : Q.toJordanCircle.TwoBoundaryArcPaths u v) :
    P.carrier ≃ₜ Q.carrier := by
  let raw :
      (range S.first ∪ range S.second : Set Plane) ≃ₜ
        (range T.first ∪ range T.second : Set Plane) :=
    TwoArcJordan.carrierCorrespondence
      S.first S.second S.first_injective S.second_injective S.overlap
      T.first T.second T.first_injective T.second_injective T.overlap
  have hP : P.carrier = range S.first ∪ range S.second := by
    rw [← P.carrier_toJordanCircle, ← S.cover]
  have hQ : range T.first ∪ range T.second = Q.carrier := by
    rw [T.cover, Q.carrier_toJordanCircle]
  exact (Homeomorph.setCongr hP).trans
    (raw.trans (Homeomorph.setCongr hQ))

theorem boundaryHomeomorph_apply_first
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y)
    (T : Q.toJordanCircle.TwoBoundaryArcPaths u v)
    (t : unitInterval) :
    ((boundaryHomeomorph S T)
        ⟨S.first t, by
          rw [← P.carrier_toJordanCircle, ← S.cover]
          exact Or.inl ⟨t, rfl⟩⟩ : Plane) = T.first t := by
  change
    ((TwoArcJordan.carrierCorrespondence
      S.first S.second S.first_injective S.second_injective S.overlap
      T.first T.second T.first_injective T.second_injective T.overlap)
        ⟨S.first t, Or.inl ⟨t, rfl⟩⟩ : Plane) = T.first t
  exact congrArg Subtype.val <|
    TwoArcJordan.carrierCorrespondence_apply_first
      S.first S.second S.first_injective S.second_injective S.overlap
      T.first T.second T.first_injective T.second_injective T.overlap t

/-- Extend the marked boundary correspondence over both polygonal disks. -/
def closedRegionHomeomorph
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y)
    (T : Q.toJordanCircle.TwoBoundaryArcPaths u v) :
    P.closedRegion ≃ₜ Q.closedRegion :=
  PolygonalCircle.extendBoundaryHomeomorph P Q (boundaryHomeomorph S T)

theorem closedRegionHomeomorph_apply_first
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y)
    (T : Q.toJordanCircle.TwoBoundaryArcPaths u v)
    (t : unitInterval) :
    ((closedRegionHomeomorph S T)
        ⟨S.first t, by
          rw [P.closedRegion_eq_union]
          exact Or.inr <| by
            rw [← P.carrier_toJordanCircle, ← S.cover]
            exact Or.inl ⟨t, rfl⟩⟩ : Plane) = T.first t := by
  let z : P.carrier := ⟨S.first t, by
    rw [← P.carrier_toJordanCircle, ← S.cover]
    exact Or.inl ⟨t, rfl⟩⟩
  have hExtend := PolygonalCircle.extendBoundaryHomeomorph_apply
    P Q (boundaryHomeomorph S T) z
  calc
    ((closedRegionHomeomorph S T) ⟨S.first t, _⟩ : Plane) =
        ((boundaryHomeomorph S T) z : Plane) := hExtend
    _ = T.first t := by
      change ((boundaryHomeomorph S T)
        ⟨S.first t, by
          rw [← P.carrier_toJordanCircle, ← S.cover]
          exact Or.inl ⟨t, rfl⟩⟩ : Plane) = T.first t
      exact boundaryHomeomorph_apply_first S T t

end MarkedPolygonalDisk

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private theorem moiseCellInnerBoundaryPath_endpoints_ne
    (a : LevelAddress n) :
    (L.adjacentMoiseBandInnerSeamPoint (prevLevelAddress n a) : Plane) ≠
      (L.adjacentMoiseBandInnerSeamPoint a : Plane) := by
  intro h
  have hpath : L.moiseCellInnerBoundaryPath a 0 =
      L.moiseCellInnerBoundaryPath a 1 := by
    rw [(L.moiseCellInnerBoundaryPath a).source,
      (L.moiseCellInnerBoundaryPath a).target]
    exact h
  have hparameters := L.moiseCellInnerBoundaryPath_injective a hpath
  exact zero_ne_one hparameters

/-- The source cell boundary split whose first arc is the marked three-piece
route. -/
noncomputable def moiseCellBoundarySplit (a : LevelAddress n) :
    (L.moiseBandPolygonalCircle a).toJordanCircle.TwoBoundaryArcPaths
      (L.adjacentMoiseBandInnerSeamPoint (prevLevelAddress n a) : Plane)
      (L.adjacentMoiseBandInnerSeamPoint a : Plane) :=
  (L.moiseBandPolygonalCircle a).toJordanCircle.boundarySplitOfInjectivePath
    (L.moiseCellInnerBoundaryPath a)
    (L.moiseCellInnerBoundaryPath_injective a)
    (L.moiseCellInnerBoundaryPath_endpoints_ne a)
    (by
      rw [(L.moiseBandPolygonalCircle a).carrier_toJordanCircle]
      exact L.range_moiseCellInnerBoundaryPath_subset_carrier a)

@[simp] theorem moiseCellBoundarySplit_first (a : LevelAddress n) :
    (L.moiseCellBoundarySplit a).first =
      L.moiseCellInnerBoundaryPath a := by
  exact JordanCircle.boundarySplitOfInjectivePath_first _ _ _ _ _

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private theorem indexedTargetCellInnerBoundaryPath_endpoints_ne
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    I.indexedTargetMark (m + 1) a ≠
      I.indexedTargetMark (m + 1) (nextLevelAddress n a) :=
  (I.indexedTargetMark_injective (m + 1) n).ne
    (nextLevelAddress_ne n a).symm

/-- The target cell split with the matching marked radial-inner-radial
route as its first arc. -/
noncomputable def indexedTargetCellBoundarySplit
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    ((I.cyclicTargetAttachmentPresentation m a).disk.toJordanCircle).TwoBoundaryArcPaths
        (I.indexedTargetMark (m + 1) a)
        (I.indexedTargetMark (m + 1) (nextLevelAddress n a)) :=
  ((I.cyclicTargetAttachmentPresentation m a).disk.toJordanCircle).boundarySplitOfInjectivePath
      (I.indexedTargetCellInnerBoundaryPath m a)
      (I.indexedTargetCellInnerBoundaryPath_injective m a)
      (I.indexedTargetCellInnerBoundaryPath_endpoints_ne m a)
      (by
        rw [(I.cyclicTargetAttachmentPresentation m a).disk.carrier_toJordanCircle]
        exact I.range_indexedTargetCellInnerBoundaryPath_subset_carrier m a)

@[simp] theorem indexedTargetCellBoundarySplit_first
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    (I.indexedTargetCellBoundarySplit m a).first =
      I.indexedTargetCellInnerBoundaryPath m a := by
  exact JordanCircle.boundarySplitOfInjectivePath_first _ _ _ _ _

end JordanCircle.InitialAngularArcs

namespace JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

/-- A recursive Moise cell mapped to its canonically labelled standard
radial target cell, with all three marked boundary pieces controlled. -/
noncomputable def markedMoiseCellHomeomorph
    (m : ℕ) (a : LevelAddress n) :
    (L.moiseBandPolygonalCircle a).closedRegion ≃ₜ
      (I.cyclicTargetAttachmentPresentation m a).disk.closedRegion :=
  MarkedPolygonalDisk.closedRegionHomeomorph
    (L.moiseCellBoundarySplit a)
    (I.indexedTargetCellBoundarySplit m a)

theorem markedMoiseCellHomeomorph_apply_innerBoundaryPath
    (m : ℕ) (a : LevelAddress n) (t : unitInterval) :
    (L.markedMoiseCellHomeomorph m a
        ⟨L.moiseCellInnerBoundaryPath a t, by
          rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
            a ⟨t, rfl⟩⟩ : Plane) =
      I.indexedTargetCellInnerBoundaryPath m a t := by
  simpa only [markedMoiseCellHomeomorph,
    L.moiseCellBoundarySplit_first,
    I.indexedTargetCellBoundarySplit_first] using
      MarkedPolygonalDisk.closedRegionHomeomorph_apply_first
        (L.moiseCellBoundarySplit a)
        (I.indexedTargetCellBoundarySplit m a) t

theorem markedMoiseCellHomeomorph_apply_incomingSeam
    (m : ℕ) (a : LevelAddress n) (t : unitInterval) :
    (L.markedMoiseCellHomeomorph m a
        ⟨L.incomingMoiseBandSideSeamPath a t, by
          rw [← L.moiseCellInnerBoundaryPath_firstCoordinate a t,
            (L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
            a ⟨ThreePiecePath.firstCoordinate t, rfl⟩⟩ : Plane) =
      (I.indexedTargetAnnularCrosscut m a).path t := by
  let s := ThreePiecePath.firstCoordinate t
  calc
    (L.markedMoiseCellHomeomorph m a
        ⟨L.incomingMoiseBandSideSeamPath a t, _⟩ : Plane) =
        (L.markedMoiseCellHomeomorph m a
          ⟨L.moiseCellInnerBoundaryPath a s, by
            rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
            exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
              a ⟨s, rfl⟩⟩ : Plane) := by
      apply congrArg (fun z => (L.markedMoiseCellHomeomorph m a z : Plane))
      exact Subtype.ext (L.moiseCellInnerBoundaryPath_firstCoordinate a t).symm
    _ = I.indexedTargetCellInnerBoundaryPath m a s :=
      L.markedMoiseCellHomeomorph_apply_innerBoundaryPath m a s
    _ = (I.indexedTargetAnnularCrosscut m a).path t :=
      I.indexedTargetCellInnerBoundaryPath_firstCoordinate m a t

theorem markedMoiseCellHomeomorph_apply_parentCrosscut
    (m : ℕ) (a : LevelAddress n) (t : unitInterval) :
    (L.markedMoiseCellHomeomorph m a
        ⟨F.synchronizedCrosscutPath a t, by
          rw [← L.moiseCellInnerBoundaryPath_middleCoordinate a t,
            (L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
            a ⟨ThreePiecePath.middleCoordinate t, rfl⟩⟩ : Plane) =
      (I.indexedTargetBoundarySplit m a).first t := by
  let s := ThreePiecePath.middleCoordinate t
  calc
    (L.markedMoiseCellHomeomorph m a
        ⟨F.synchronizedCrosscutPath a t, _⟩ : Plane) =
        (L.markedMoiseCellHomeomorph m a
          ⟨L.moiseCellInnerBoundaryPath a s, by
            rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
            exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
              a ⟨s, rfl⟩⟩ : Plane) := by
      apply congrArg (fun z => (L.markedMoiseCellHomeomorph m a z : Plane))
      exact Subtype.ext (L.moiseCellInnerBoundaryPath_middleCoordinate a t).symm
    _ = I.indexedTargetCellInnerBoundaryPath m a s :=
      L.markedMoiseCellHomeomorph_apply_innerBoundaryPath m a s
    _ = (I.indexedTargetBoundarySplit m a).first t :=
      I.indexedTargetCellInnerBoundaryPath_middleCoordinate m a t

theorem markedMoiseCellHomeomorph_apply_outgoingSeam_symm
    (m : ℕ) (a : LevelAddress n) (t : unitInterval) :
    (L.markedMoiseCellHomeomorph m a
        ⟨(L.adjacentMoiseBandSideSeamPath a).symm t, by
          rw [← L.moiseCellInnerBoundaryPath_thirdCoordinate a t,
            (L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
            a ⟨ThreePiecePath.thirdCoordinate t, rfl⟩⟩ : Plane) =
      (I.indexedTargetAnnularCrosscut m
        (nextLevelAddress n a)).path.symm t := by
  let s := ThreePiecePath.thirdCoordinate t
  calc
    (L.markedMoiseCellHomeomorph m a
        ⟨(L.adjacentMoiseBandSideSeamPath a).symm t, _⟩ : Plane) =
        (L.markedMoiseCellHomeomorph m a
          ⟨L.moiseCellInnerBoundaryPath a s, by
            rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
            exact Or.inr <| L.range_moiseCellInnerBoundaryPath_subset_carrier
              a ⟨s, rfl⟩⟩ : Plane) := by
      apply congrArg (fun z => (L.markedMoiseCellHomeomorph m a z : Plane))
      exact Subtype.ext (L.moiseCellInnerBoundaryPath_thirdCoordinate a t).symm
    _ = I.indexedTargetCellInnerBoundaryPath m a s :=
      L.markedMoiseCellHomeomorph_apply_innerBoundaryPath m a s
    _ = (I.indexedTargetAnnularCrosscut m
        (nextLevelAddress n a)).path.symm t :=
      I.indexedTargetCellInnerBoundaryPath_thirdCoordinate m a t

theorem markedMoiseCellHomeomorph_apply_outgoingSeam
    (m : ℕ) (a : LevelAddress n) (t : unitInterval) :
    (L.markedMoiseCellHomeomorph m a
        ⟨L.adjacentMoiseBandSideSeamPath a t, by
          have h := L.range_moiseCellInnerBoundaryPath_subset_carrier a
            ⟨ThreePiecePath.thirdCoordinate (unitInterval.symm t), rfl⟩
          rw [(L.moiseBandPolygonalCircle a).closedRegion_eq_union]
          exact Or.inr <| by
            simpa only [L.moiseCellInnerBoundaryPath_thirdCoordinate,
              Path.symm_apply, Function.comp_apply,
              unitInterval.symm_symm] using h⟩ : Plane) =
      (I.indexedTargetAnnularCrosscut m
        (nextLevelAddress n a)).path t := by
  simpa only [Path.symm_apply, Function.comp_apply,
    unitInterval.symm_symm] using
      L.markedMoiseCellHomeomorph_apply_outgoingSeam_symm
        m a (unitInterval.symm t)

end JordanCircle.InitialAngularArcs.RecursiveInsideCollarStep.Later

end

end Schoenflies
