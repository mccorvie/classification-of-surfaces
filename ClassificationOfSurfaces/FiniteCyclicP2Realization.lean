/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.DiskSquare
import ClassificationOfSurfaces.FiniteCyclicMoves

/-!
# Polygonal realization of Gallier--Xu P2

This file packages the local two-disk cut model from `DiskSquare` for finite cyclic
presentations.  The first layer normalizes the cyclic position of a nondegenerate positively
oriented cut and supplies an exact selected-face homeomorphism.  It is deliberately stated in
terms of the existing `P2Cut` data, so the presentation-level quotient comparison can use the
same side indices and no second formulation of P2 is introduced.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

/-- The selected source face has as many stored sides as the two linear cut pieces together. -/
theorem sourceBoundaryLength_eq_cutLength
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    (P.boundary cut.face.face).length =
      cut.left.length + cut.right.length := by
  obtain ⟨k, hk⟩ := cut.boundary_rotated
  have hlength := congrArg List.length hk
  rw [List.length_rotate, List.length_append] at hlength
  exact (P.orientedBoundary_length cut.face).symm.trans hlength

/-- Rotation of the linear cut word that recovers the stored source boundary.  This version is
used after reducing to the positive traversal orientation. -/
noncomputable def positiveCutRotation
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) : ℕ :=
  Classical.choose (show
    (cut.left ++ cut.right).IsRotated
      (P.boundary cut.face.face) by
    have h := cut.boundary_rotated.symm
    simpa [orientedBoundary, horientation] using h)

theorem rotate_cutBoundary_eq_sourceBoundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (cut.left ++ cut.right).rotate
        (positiveCutRotation P cut horientation) =
      P.boundary cut.face.face :=
  Classical.choose_spec (show
    (cut.left ++ cut.right).IsRotated
      (P.boundary cut.face.face) by
    have h := cut.boundary_rotated.symm
    simpa [orientedBoundary, horientation] using h)

/-- The linear cut-word index carrying a stored source side. -/
noncomputable def positiveCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    Fin (cut.left.length + cut.right.length) :=
  ⟨(i.val + positiveCutRotation P cut horientation) %
      (cut.left.length + cut.right.length),
    Nat.mod_lt _ (Nat.add_pos_left hl _)⟩

@[simp]
theorem positiveCutSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (positiveCutSideIndex P cut horientation hl hr i).val =
      (i.val + positiveCutRotation P cut horientation) %
        (cut.left.length + cut.right.length) :=
  rfl

/-- The selected source face, with its cyclic starting point aligned to the cut, is exactly the
local one-polygon-to-two-child quotient model. -/
noncomputable def positiveSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
      (sourceBoundaryLength_eq_cutLength P cut)
      (positiveCutRotation P cut horientation)).trans
    (DiskSquare.sourceChildGluingHomeomorph
      cut.left.length cut.right.length hl hr)

/-- Exact side computation for the cyclically aligned selected-face homeomorphism. -/
theorem positiveSelectedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      DiskSquare.sourceChildGluingHomeomorph
        cut.left.length cut.right.length hl hr
        (PolygonCell.side
          (positiveCutSideIndex P cut horientation hl hr i) t) := by
  rw [positiveSelectedCellHomeomorph, Homeomorph.trans_apply]
  congr 1
  exact PolygonCell.rotateHomeomorph_side_of_eq
    (sourceBoundaryLength_eq_cutLength P cut)
    (Nat.add_pos_left hl _) (positiveCutRotation P cut horientation) i t

/-- A rotated source side lying in the left cut piece, viewed with its local left index. -/
noncomputable def positiveLeftSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    Fin cut.left.length :=
  ⟨(positiveCutSideIndex P cut horientation hl hr i).val, hleft⟩

@[simp]
theorem positiveLeftSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    (positiveLeftSideIndex P cut horientation hl hr i hleft).val =
      (positiveCutSideIndex P cut horientation hl hr i).val :=
  rfl

/-- A rotated source side lying in the right cut piece, viewed with its local right index. -/
noncomputable def positiveRightSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    Fin cut.right.length :=
  ⟨(positiveCutSideIndex P cut horientation hl hr i).val -
      cut.left.length,
    by
      have hbound :=
        (positiveCutSideIndex P cut horientation hl hr i).isLt
      omega⟩

@[simp]
theorem positiveRightSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    (positiveRightSideIndex P cut horientation hl hr i hright).val =
      (positiveCutSideIndex P cut horientation hl hr i).val -
        cut.left.length :=
  rfl

/-- Exact selected-face computation for a side belonging to the left cut piece. -/
theorem positiveSelectedCellHomeomorph_side_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid cut.left.length cut.right.length)
        (.inl
          (PolygonCell.side
            (Fin.castAdd 1
              (positiveLeftSideIndex P cut horientation hl hr i hleft)) t)) := by
  rw [positiveSelectedCellHomeomorph_side]
  have hindex :
      positiveCutSideIndex P cut horientation hl hr i =
        Fin.castAdd cut.right.length
          (positiveLeftSideIndex P cut horientation hl hr i hleft) := by
    apply Fin.ext
    rfl
  rw [hindex, DiskSquare.sourceChildGluingHomeomorph_left_side]

/-- Exact selected-face computation for a side belonging to the right cut piece. -/
theorem positiveSelectedCellHomeomorph_side_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    positiveSelectedCellHomeomorph P cut horientation hl hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid cut.left.length cut.right.length)
        (.inr
          (PolygonCell.side
            ((positiveRightSideIndex P cut horientation hl hr i hright).addNat 1) t)) := by
  rw [positiveSelectedCellHomeomorph_side]
  have hindex :
      positiveCutSideIndex P cut horientation hl hr i =
        Fin.natAdd cut.left.length
          (positiveRightSideIndex P cut horientation hl hr i hright) := by
    apply Fin.ext
    simp only [Fin.val_natAdd, positiveRightSideIndex_val]
    omega
  rw [hindex, DiskSquare.sourceChildGluingHomeomorph_right_side]

/-! ### The fresh seam inside the actual split presentation -/

@[simp]
theorem positive_split_boundary_selected_length
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    ((split P cut).boundary (oldFace P cut cut.face.face)).length =
      cut.left.length + 1 := by
  calc
    ((split P cut).boundary
        (oldFace P cut cut.face.face)).length =
        (selectedBoundary P cut).length :=
      congrArg List.length (split_boundary_selected P cut)
    _ = cut.left.length + 1 := by
      rw [selectedBoundary_of_orientation_false P cut horientation]
      simp [retainWord]

@[simp]
theorem positive_split_boundary_right_length
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    ((split P cut).boundary (rightFace P cut)).length =
      cut.right.length + 1 := by
  calc
    ((split P cut).boundary (rightFace P cut)).length =
        (rightBoundary P cut).length :=
      congrArg List.length (split_boundary_right P cut)
    _ = cut.right.length + 1 := by
      rw [rightBoundary_of_orientation_false P cut horientation]
      simp [retainWord, Nat.add_comm]

/-- Stored target index of the positive fresh dart in the selected child. -/
def positiveSelectedFreshIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Fin ((split P cut).boundary
      (oldFace P cut cut.face.face)).length :=
  ⟨cut.left.length, by
    rw [positive_split_boundary_selected_length P cut horientation]
    omega⟩

@[simp]
theorem positiveSelectedFreshIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshIndex P cut horientation).val =
      cut.left.length :=
  rfl

/-- Stored target index of the negative fresh dart in the right child. -/
def positiveRightFreshIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Fin ((split P cut).boundary (rightFace P cut)).length :=
  ⟨0, by
    rw [positive_split_boundary_right_length P cut horientation]
    omega⟩

@[simp]
theorem positiveRightFreshIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshIndex P cut horientation).val = 0 :=
  rfl

/-- The selected child's fresh-edge boundary occurrence. -/
def positiveSelectedFreshOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryOccurrence :=
  ⟨oldFace P cut cut.face.face,
    positiveSelectedFreshIndex P cut horientation⟩

/-- The right child's fresh-edge boundary occurrence. -/
def positiveRightFreshOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryOccurrence :=
  ⟨rightFace P cut, positiveRightFreshIndex P cut horientation⟩

theorem positiveSelectedBoundary_get_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (selectedBoundary P cut).get
        ⟨cut.left.length, by
          rw [selectedBoundary_of_orientation_false P cut horientation]
          unfold retainWord
          simp⟩ =
      .pos (freshEdge P) := by
  rw [List.get_of_eq
    (selectedBoundary_of_orientation_false P cut horientation)]
  simp [retainWord]

theorem positiveRightBoundary_get_fresh
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (rightBoundary P cut).get
        ⟨0, by
          rw [rightBoundary_of_orientation_false P cut horientation]
          simp⟩ =
      .neg (freshEdge P) := by
  rw [List.get_of_eq
    (rightBoundary_of_orientation_false P cut horientation)]
  rfl

@[simp]
theorem positiveSelectedFreshOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshOccurrence P cut horientation).dart =
      .pos (freshEdge P) := by
  rw [positiveSelectedFreshOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (split_boundary_selected P cut)]
  change
    (selectedBoundary P cut).get
        ⟨cut.left.length, by
          rw [selectedBoundary_of_orientation_false P cut horientation]
          unfold retainWord
          simp⟩ =
      (SignedDart.pos (freshEdge P) :
        SignedDart (Fin (P.edgeCount + 1)))
  simpa only [positiveSelectedFreshIndex_val] using
    positiveSelectedBoundary_get_fresh P cut horientation

@[simp]
theorem positiveRightFreshOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshOccurrence P cut horientation).dart =
      .neg (freshEdge P) := by
  rw [positiveRightFreshOccurrence, BoundaryOccurrence.dart_mk]
  rw [List.get_of_eq (split_boundary_right P cut)]
  change
    (rightBoundary P cut).get
        ⟨0, by
          rw [rightBoundary_of_orientation_false P cut horientation]
          simp⟩ =
      (SignedDart.neg (freshEdge P) :
        SignedDart (Fin (P.edgeCount + 1)))
  simpa only [positiveRightFreshIndex_val] using
    positiveRightBoundary_get_fresh P cut horientation

@[simp]
theorem positiveSelectedFreshOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveSelectedFreshOccurrence P cut horientation).edge =
      freshEdge P := by
  rw [BoundaryOccurrence.edge,
    positiveSelectedFreshOccurrence_dart]
  rfl

@[simp]
theorem positiveRightFreshOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveRightFreshOccurrence P cut horientation).edge =
      freshEdge P := by
  rw [BoundaryOccurrence.edge,
    positiveRightFreshOccurrence_dart]
  rfl

theorem positiveSelectedFreshOccurrence_ne_right
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    positiveSelectedFreshOccurrence P cut horientation ≠
      positiveRightFreshOccurrence P cut horientation := by
  intro h
  have hface := congrArg Sigma.fst h
  have hval := congrArg Fin.val hface
  change cut.face.face.val = P.faces.length at hval
  exact (Nat.ne_of_lt cut.face.face.isLt) hval

theorem positiveFresh_not_boundary
    (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    ¬(split P cut).IsBoundaryEdge (freshEdge P) := by
  rw [IsBoundaryEdge, edgeMultiplicity_split_freshEdge]
  norm_num

/-- The exact reversed-parameter pairing carried by the fresh P2 seam. -/
def positiveFreshPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (split P cut).BoundaryPairing where
  source := positiveSelectedFreshOccurrence P cut horientation
  target := positiveRightFreshOccurrence P cut horientation
  source_ne_target :=
    positiveSelectedFreshOccurrence_ne_right P cut horientation
  source_not_boundary := by
    rw [positiveSelectedFreshOccurrence_edge]
    exact positiveFresh_not_boundary P cut
  target_not_boundary := by
    rw [positiveRightFreshOccurrence_edge]
    exact positiveFresh_not_boundary P cut
  direction := .opposite
  compatible := by
    rw [positiveRightFreshOccurrence_dart,
      positiveSelectedFreshOccurrence_dart]
    rfl

@[simp]
theorem positiveFreshPairing_source
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).source =
      positiveSelectedFreshOccurrence P cut horientation :=
  rfl

@[simp]
theorem positiveFreshPairing_target
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).target =
      positiveRightFreshOccurrence P cut horientation :=
  rfl

@[simp]
theorem positiveFreshPairing_direction
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    (positiveFreshPairing P cut horientation).direction = .opposite :=
  rfl

/-! ### Embedding the local child quotient in the target realization -/

/-- Phantom side-count transport from the local selected child to the actual target face. -/
noncomputable def positiveSelectedChildCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell (cut.left.length + 1) ≃ₜ
      PolygonCell
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length :=
  PolygonCell.rotateHomeomorph
    (positive_split_boundary_selected_length P cut horientation).symm 0

/-- Phantom side-count transport from the local right child to the actual target face. -/
noncomputable def positiveRightChildCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    PolygonCell (cut.right.length + 1) ≃ₜ
      PolygonCell ((split P cut).boundary (rightFace P cut)).length :=
  PolygonCell.rotateHomeomorph
    (positive_split_boundary_right_length P cut horientation).symm 0

/-- The target selected-child index corresponding to a local child side. -/
def positiveSelectedChildSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.left.length + 1)) :
    Fin ((split P cut).boundary
      (oldFace P cut cut.face.face)).length :=
  ⟨i.val, by
    rw [positive_split_boundary_selected_length P cut horientation]
    exact i.isLt⟩

/-- The target right-child index corresponding to a local child side. -/
def positiveRightChildSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.right.length + 1)) :
    Fin ((split P cut).boundary (rightFace P cut)).length :=
  ⟨i.val, by
    rw [positive_split_boundary_right_length P cut horientation]
    exact i.isLt⟩

@[simp]
theorem positiveSelectedChildCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.left.length + 1)) (t : unitInterval) :
    positiveSelectedChildCellHomeomorph P cut horientation
        (PolygonCell.side i t) =
      PolygonCell.side
        (positiveSelectedChildSideIndex P cut horientation i) t := by
  rw [positiveSelectedChildCellHomeomorph]
  have hpos :
      0 <
        ((split P cut).boundary
          (oldFace P cut cut.face.face)).length := by
    rw [positive_split_boundary_selected_length P cut horientation]
    omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (positive_split_boundary_selected_length P cut horientation).symm
    hpos 0 i t]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk,
    positiveSelectedChildSideIndex]
  apply Nat.mod_eq_of_lt
  rw [positive_split_boundary_selected_length P cut horientation]
  simpa using i.isLt

@[simp]
theorem positiveRightChildCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (i : Fin (cut.right.length + 1)) (t : unitInterval) :
    positiveRightChildCellHomeomorph P cut horientation
        (PolygonCell.side i t) =
      PolygonCell.side
        (positiveRightChildSideIndex P cut horientation i) t := by
  rw [positiveRightChildCellHomeomorph]
  have hpos :
      0 < ((split P cut).boundary (rightFace P cut)).length := by
    rw [positive_split_boundary_right_length P cut horientation]
    omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (positive_split_boundary_right_length P cut horientation).symm
    hpos 0 i t]
  congr 2
  apply Fin.ext
  simp only [Fin.val_mk,
    positiveRightChildSideIndex]
  apply Nat.mod_eq_of_lt
  rw [positive_split_boundary_right_length P cut horientation]
  simpa using i.isLt

/-- Include the two local child cells into the corresponding two faces of the split
pre-realization. -/
noncomputable def positiveChildPairPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    DiskSquare.ChildPair cut.left.length cut.right.length →
      (split P cut).PolygonalPreRealization :=
  Sum.elim
    (fun z =>
      ⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩)
    (fun z =>
      ⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩)

theorem continuous_positiveChildPairPreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false) :
    Continuous (positiveChildPairPreMap P cut horientation) := by
  apply Continuous.sumElim
  · show Continuous (fun z =>
      (⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩ :
          (split P cut).PolygonalPreRealization))
    exact continuous_sigmaMk.comp
      (positiveSelectedChildCellHomeomorph P cut horientation).continuous
  · show Continuous (fun z =>
      (⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩ :
          (split P cut).PolygonalPreRealization))
    exact continuous_sigmaMk.comp
      (positiveRightChildCellHomeomorph P cut horientation).continuous

@[simp]
theorem positiveChildPairPreMap_inl
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.left.length + 1)) :
    positiveChildPairPreMap P cut horientation (.inl z) =
      ⟨oldFace P cut cut.face.face,
        positiveSelectedChildCellHomeomorph P cut horientation z⟩ :=
  rfl

@[simp]
theorem positiveChildPairPreMap_inr
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (z : PolygonCell (cut.right.length + 1)) :
    positiveChildPairPreMap P cut horientation (.inr z) =
      ⟨rightFace P cut,
        positiveRightChildCellHomeomorph P cut horientation z⟩ :=
  rfl

/-- Send a local child point to its class in the complete split realization. -/
noncomputable def positiveChildPairMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ChildPair cut.left.length cut.right.length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  (split P cut).polygonalMk (split_isSurfaceValid P cut validP) ∘
    positiveChildPairPreMap P cut horientation

theorem continuous_positiveChildPairMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveChildPairMap P cut horientation validP) :=
  ((split P cut).continuous_polygonalMk
      (split_isSurfaceValid P cut validP)).comp
    (continuous_positiveChildPairPreMap P cut horientation)

theorem positiveChildPairPreMap_fresh_inl
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (t : unitInterval) :
    positiveChildPairPreMap P cut horientation
        (.inl (PolygonCell.side (Fin.last cut.left.length) t)) =
      ((split P cut).occurrenceSide
        (positiveSelectedFreshOccurrence P cut horientation)).point t := by
  rw [positiveChildPairPreMap_inl,
    positiveSelectedChildCellHomeomorph_side]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    congr 2

theorem positiveChildPairPreMap_fresh_inr
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (t : unitInterval) :
    positiveChildPairPreMap P cut horientation
        (.inr
          (PolygonCell.side (0 : Fin (cut.right.length + 1)) t)) =
      ((split P cut).occurrenceSide
        (positiveRightFreshOccurrence P cut horientation)).point t := by
  rw [positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    congr 2

/-- The local seam generator is exactly the fresh-edge gluing already present in the target
polygonal quotient. -/
theorem positiveChildPairMap_fresh_seam
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) (t : unitInterval) :
    positiveChildPairMap P cut horientation validP
        (.inl (PolygonCell.side (Fin.last cut.left.length) t)) =
      positiveChildPairMap P cut horientation validP
        (.inr
          (PolygonCell.side (0 : Fin (cut.right.length + 1))
            (unitInterval.symm t))) := by
  simp only [positiveChildPairMap, Function.comp_apply]
  rw [positiveChildPairPreMap_fresh_inl,
    positiveChildPairPreMap_fresh_inr]
  simpa [positiveFreshPairing,
      PolygonGluing.Identification.parameter] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (positiveFreshPairing P cut horientation) t

/-- The target quotient map is constant on the complete local child-seam relation. -/
theorem positiveChildPairMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    {x y : DiskSquare.ChildPair cut.left.length cut.right.length}
    (hxy :
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator
          cut.left.length cut.right.length) x y) :
    positiveChildPairMap P cut horientation validP x =
      positiveChildPairMap P cut horientation validP y := by
  induction hxy with
  | rel _ _ h =>
      cases h with
      | glue t =>
          exact positiveChildPairMap_fresh_seam
            P cut horientation validP t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Include the locally glued pair of P2 children into the complete target realization. -/
noncomputable def positiveChildGluingMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    DiskSquare.ParamChildGluing cut.left.length cut.right.length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  Quotient.lift
    (positiveChildPairMap P cut horientation validP)
    (fun _ _ hxy =>
      positiveChildPairMap_respects P cut horientation validP hxy)

theorem continuous_positiveChildGluingMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid) :
    Continuous (positiveChildGluingMap P cut horientation validP) :=
  (continuous_positiveChildPairMap P cut horientation validP).quotient_lift
    (fun _ _ hxy =>
      positiveChildPairMap_respects P cut horientation validP hxy)

@[simp]
theorem positiveChildGluingMap_mk
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (validP : P.IsSurfaceValid)
    (x : DiskSquare.ChildPair cut.left.length cut.right.length) :
    positiveChildGluingMap P cut horientation validP
        (@Quotient.mk''
          (DiskSquare.ChildPair cut.left.length cut.right.length)
          (DiskSquare.paramChildSeamSetoid
            cut.left.length cut.right.length) x) =
      positiveChildPairMap P cut horientation validP x :=
  rfl

/-! ### The selected source face as a map into the split realization -/

/-- The positive, nondegenerate selected source face, cut into the two target children and then
included in the complete split quotient. -/
noncomputable def positiveSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary cut.face.face).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  positiveChildGluingMap P cut horientation validP ∘
    positiveSelectedCellHomeomorph P cut horientation hl hr

theorem continuous_positiveSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous
      (positiveSelectedFaceMap
        P cut horientation hl hr validP) :=
  (continuous_positiveChildGluingMap P cut horientation validP).comp
    (positiveSelectedCellHomeomorph
      P cut horientation hl hr).continuous

/-- A selected source side in the left cut piece lands on the exact old side of the selected
target child. -/
theorem positiveSelectedFaceMap_side_of_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hleft :
      (positiveCutSideIndex P cut horientation hl hr i).val <
        cut.left.length) :
    positiveSelectedFaceMap P cut horientation hl hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut cut.face.face,
          PolygonCell.side
            (positiveSelectedChildSideIndex P cut horientation
              (Fin.castAdd 1
                (positiveLeftSideIndex
                  P cut horientation hl hr i hleft))) t⟩ := by
  rw [positiveSelectedFaceMap, Function.comp_apply,
    positiveSelectedCellHomeomorph_side_of_lt
      P cut horientation hl hr i t hleft]
  rw [positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inl,
    positiveSelectedChildCellHomeomorph_side]

/-- A selected source side in the right cut piece lands on the exact old side of the right target
child. -/
theorem positiveSelectedFaceMap_side_of_not_lt
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length) (t : unitInterval)
    (hright :
      cut.left.length ≤
        (positiveCutSideIndex P cut horientation hl hr i).val) :
    positiveSelectedFaceMap P cut horientation hl hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((positiveRightSideIndex
                P cut horientation hl hr i hright).addNat 1)) t⟩ := by
  rw [positiveSelectedFaceMap, Function.comp_apply,
    positiveSelectedCellHomeomorph_side_of_not_lt
      P cut horientation hl hr i t hright]
  rw [positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]

end P2

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
