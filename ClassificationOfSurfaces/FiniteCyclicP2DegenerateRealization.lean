/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicP2Realization
import ClassificationOfSurfaces.P2DegenerateDisk

/-!
# Polygonal realization of one-sided-degenerate Gallier--Xu P2

This file lifts the local monogon--polygon disk theorem to finite cyclic presentations.  The
positive base case has an empty left cut word and a nonempty right cut word.  Reversal and child
swap transport that case to every ordinary-valid one-sided-degenerate cut.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

theorem leftLength_eq_zero
    {P : FiniteCyclicPresentation} {cut : P2Cut P}
    (hleft : cut.left = []) :
    cut.left.length = 0 := by
  simp [hleft]

/-- The rotated source side index, specialized to an empty-left cut. -/
noncomputable def rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (_hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    Fin cut.right.length :=
  ⟨(i.val + positiveCutRotation P cut horientation) %
      cut.right.length,
    Nat.mod_lt _ hr⟩

@[simp]
theorem rightDegenerateCutSideIndex_val
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr i).val =
      (i.val + positiveCutRotation P cut horientation) %
        cut.right.length :=
  rfl

theorem sourceBoundaryLength_eq_rightLength
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hleft : cut.left = []) :
    (P.boundary cut.face.face).length =
      cut.right.length := by
  rw [sourceBoundaryLength_eq_cutLength P cut,
    hleft]
  simp

theorem rightDegenerateCutSideIndex_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  intro i j hij
  have hmod :
      i.val + positiveCutRotation P cut horientation ≡
        j.val + positiveCutRotation P cut horientation
          [MOD cut.right.length] :=
    congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD cut.right.length] :=
    Nat.ModEq.add_right_cancel'
      (positiveCutRotation P cut horientation) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← sourceBoundaryLength_eq_rightLength P cut hleft,
    Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

theorem rightDegenerateCutSideIndex_surjective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Surjective
      (rightDegenerateCutSideIndex
        P cut horientation hleft hr) := by
  exact ((Fintype.bijective_iff_injective_and_card
    (rightDegenerateCutSideIndex
      P cut horientation hleft hr)).2
      ⟨rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr,
        by
          simp only [Fintype.card_fin]
          exact sourceBoundaryLength_eq_rightLength
            P cut hleft⟩).2

theorem right_get_rightDegenerateCutSideIndex
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    cut.right[
        (rightDegenerateCutSideIndex
          P cut horientation hleft hr i).val] =
      (P.boundary cut.face.face)[i.val] := by
  -- Use the rotation lookup directly, with the empty append simplified.
  have hiCut :
      i.val < (cut.left ++ cut.right).length := by
    rw [hleft, List.nil_append,
      ← sourceBoundaryLength_eq_rightLength P cut hleft]
    exact i.isLt
  have hpoint :=
    congrArg (fun word => word[i.val]?)
      (rotate_cutBoundary_eq_sourceBoundary
        P cut horientation)
  rw [List.getElem?_rotate hiCut] at hpoint
  rw [hleft, List.nil_append] at hpoint
  rw [List.getElem?_eq_getElem
      (Nat.mod_lt _ hr),
    List.getElem?_eq_getElem i.isLt] at hpoint
  exact Option.some.inj (by
    simpa [rightDegenerateCutSideIndex] using hpoint)

/-- Phantom transport from the literal monogon to a selected child whose old-side count is
propositionally zero. -/
noncomputable def zeroLeftCellHomeomorph
    {l : ℕ} (hl : l = 0) :
    PolygonCell 1 ≃ₜ PolygonCell (l + 1) :=
  PolygonCell.rotateHomeomorph (by omega) 0

theorem zeroLeftCellHomeomorph_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    zeroLeftCellHomeomorph hl
        (PolygonCell.side (0 : Fin 1) t) =
      PolygonCell.side (Fin.last l) t := by
  rw [zeroLeftCellHomeomorph]
  have hpos : 0 < l + 1 := by omega
  rw [PolygonCell.rotateHomeomorph_side_of_eq
    (by omega) hpos 0 (0 : Fin 1) t]
  congr 2
  apply Fin.ext
  simp [hl]

noncomputable def zeroLeftChildPairHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ChildPair 0 r ≃ₜ
      DiskSquare.ChildPair l r :=
  Homeomorph.sumCongr
    (zeroLeftCellHomeomorph hl)
    (Homeomorph.refl (PolygonCell (r + 1)))

theorem zeroLeftChildPair_generator_map
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator l r
      (zeroLeftChildPairHomeomorph hl x)
      (zeroLeftChildPairHomeomorph hl y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator l r
          (.inl
            (zeroLeftCellHomeomorph hl
              (PolygonCell.side (0 : Fin 1) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftCellHomeomorph_symm_side
    {l : ℕ} (hl : l = 0) (t : unitInterval) :
    (zeroLeftCellHomeomorph hl).symm
        (PolygonCell.side (Fin.last l) t) =
      PolygonCell.side (0 : Fin 1) t := by
  apply (zeroLeftCellHomeomorph hl).injective
  rw [Homeomorph.apply_symm_apply,
    zeroLeftCellHomeomorph_side]

theorem zeroLeftChildPair_generator_comap
    {l r : ℕ} (hl : l = 0)
    {x y : DiskSquare.ChildPair l r}
    (hxy : DiskSquare.ParamChildSeamGenerator l r x y) :
    DiskSquare.ParamChildSeamGenerator 0 r
      ((zeroLeftChildPairHomeomorph hl).symm x)
      ((zeroLeftChildPairHomeomorph hl).symm y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 r
          (.inl
            ((zeroLeftCellHomeomorph hl).symm
              (PolygonCell.side (Fin.last l) t)))
          (.inr
            (PolygonCell.side (0 : Fin (r + 1))
              (unitInterval.symm t)))
      rw [zeroLeftCellHomeomorph_symm_side]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem zeroLeftChildPair_eqvGen_iff
    {l r : ℕ} (hl : l = 0)
    (x y : DiskSquare.ChildPair 0 r) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 r) x y ↔
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator l r)
        (zeroLeftChildPairHomeomorph hl x)
        (zeroLeftChildPairHomeomorph hl y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (zeroLeftChildPair_generator_map hl h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e :
        DiskSquare.ChildPair 0 r ≃ₜ
          DiskSquare.ChildPair l r :=
      zeroLeftChildPairHomeomorph hl
    have hcomap :
        ∀ {u v : DiskSquare.ChildPair l r},
          Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator l r) u v →
            Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 r)
              (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          exact Relation.EqvGen.rel _ _
            (zeroLeftChildPair_generator_comap hl h)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using
      hcomap hxy

noncomputable def zeroLeftChildGluingHomeomorph
    {l r : ℕ} (hl : l = 0) :
    DiskSquare.ParamChildGluing 0 r ≃ₜ
      DiskSquare.ParamChildGluing l r :=
  Homeomorph.Quotient.congr
    (zeroLeftChildPairHomeomorph hl)
    (zeroLeftChildPair_eqvGen_iff hl)

@[simp]
theorem zeroLeftChildGluingHomeomorph_mk_inr
    {l r : ℕ} (hl : l = 0)
    (z : PolygonCell (r + 1)) :
    zeroLeftChildGluingHomeomorph hl
        (@Quotient.mk''
          (DiskSquare.ChildPair 0 r)
          (DiskSquare.paramChildSeamSetoid 0 r)
          (.inr z)) =
      @Quotient.mk''
        (DiskSquare.ChildPair l r)
        (DiskSquare.paramChildSeamSetoid l r)
        (.inr z) :=
  rfl

/-- The selected source cell, cyclically aligned and then cut by the local degenerate disk
homeomorphism. -/
noncomputable def rightDegenerateSelectedCellHomeomorph
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    PolygonCell (P.boundary cut.face.face).length ≃ₜ
      DiskSquare.ParamChildGluing
        cut.left.length cut.right.length :=
  (PolygonCell.rotateHomeomorph
    (sourceBoundaryLength_eq_rightLength P cut hleft)
    (positiveCutRotation P cut horientation)).trans
    ((P2DegenerateDisk.sourceChildGluingHomeomorph
      cut.right.length hr).trans
      (zeroLeftChildGluingHomeomorph
        (leftLength_eq_zero hleft)))

theorem rightDegenerateSelectedCellHomeomorph_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedCellHomeomorph
        P cut horientation hleft hr
        (PolygonCell.side i t) =
      @Quotient.mk''
        (DiskSquare.ChildPair
          cut.left.length cut.right.length)
        (DiskSquare.paramChildSeamSetoid
          cut.left.length cut.right.length)
        (.inr
          (PolygonCell.side
            ((rightDegenerateCutSideIndex
              P cut horientation hleft hr i).addNat 1) t)) := by
  have hrotate :=
    PolygonCell.rotateHomeomorph_side_of_eq
      (sourceBoundaryLength_eq_rightLength P cut hleft)
      hr
      (positiveCutRotation P cut horientation) i t
  rw [rightDegenerateSelectedCellHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    hrotate,
    P2DegenerateDisk.sourceChildGluingHomeomorph_side,
    zeroLeftChildGluingHomeomorph_mk_inr]
  congr 3

/-- Cut the selected source face and include its local child quotient in the complete split
realization. -/
noncomputable def rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    PolygonCell (P.boundary cut.face.face).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  positiveChildGluingMap P cut horientation validP ∘
    rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr

theorem continuous_rightDegenerateSelectedFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP) :=
  (continuous_positiveChildGluingMap
      P cut horientation validP).comp
    (rightDegenerateSelectedCellHomeomorph
      P cut horientation hleft hr).continuous

theorem rightDegenerateSelectedFaceMap_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
        (PolygonCell.side i t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegenerateSelectedFaceMap,
    Function.comp_apply,
    rightDegenerateSelectedCellHomeomorph_side,
    positiveChildGluingMap_mk]
  simp only [positiveChildPairMap, Function.comp_apply,
    positiveChildPairPreMap_inr,
    positiveRightChildCellHomeomorph_side]

/-- Facewise forward map for an empty-left positive cut. -/
noncomputable def rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    PolygonCell (P.boundary f).length →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    exact rightDegenerateSelectedFaceMap
      P cut horientation hleft hr validP
  · exact retainedFaceMap P cut hface validP

theorem continuous_rightDegenerateFaceMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) (f : P.Face) :
    Continuous (rightDegenerateFaceMap
      P cut horientation hleft hr validP f) := by
  classical
  by_cases hface : f = cut.face.face
  · subst f
    simpa [rightDegenerateFaceMap] using
      continuous_rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP
  · simpa [rightDegenerateFaceMap, hface] using
      continuous_retainedFaceMap P cut hface validP

noncomputable def rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    P.PolygonalPreRealization →
      (split P cut).PolygonalRealization
        (split_isSurfaceValid P cut validP) :=
  fun x => rightDegenerateFaceMap
    P cut horientation hleft hr validP x.1 x.2

theorem continuous_rightDegeneratePreMap
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    Continuous (rightDegeneratePreMap
      P cut horientation hleft hr validP) := by
  apply continuous_sigma
  exact continuous_rightDegenerateFaceMap
    P cut horientation hleft hr validP

@[simp]
theorem rightDegeneratePreMap_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (z : PolygonCell (P.boundary cut.face.face).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, z⟩ =
      rightDegenerateSelectedFaceMap
        P cut horientation hleft hr validP z := by
  simp [rightDegeneratePreMap, rightDegenerateFaceMap]

@[simp]
theorem rightDegeneratePreMap_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (z : PolygonCell (P.boundary f).length) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP ⟨f, z⟩ =
      retainedFaceMap P cut hface validP z := by
  simp [rightDegeneratePreMap,
    rightDegenerateFaceMap, hface]

theorem rightDegeneratePreMap_selected_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (i : Fin (P.boundary cut.face.face).length)
    (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨cut.face.face, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨rightFace P cut,
          PolygonCell.side
            (positiveRightChildSideIndex P cut horientation
              ((rightDegenerateCutSideIndex
                P cut horientation hleft hr i).addNat 1)) t⟩ := by
  rw [rightDegeneratePreMap_selected,
    rightDegenerateSelectedFaceMap_side]

theorem rightDegeneratePreMap_retained_side
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ⟨f, PolygonCell.side i t⟩ =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        ⟨oldFace P cut f,
          PolygonCell.side
            (retainedSideIndex P cut hface i) t⟩ := by
  rw [rightDegeneratePreMap_retained
      P cut horientation hleft hr validP hface,
    retainedFaceMap, retainedCellHomeomorph_side]

/-- Route every old source occurrence to the target occurrence carrying it after the split. -/
noncomputable def rightDegenerateMapOccurrence
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (split P cut).BoundaryOccurrence := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    exact
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩
  · exact
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩

@[simp]
theorem rightDegenerateMapOccurrence_selected
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (i : Fin (P.boundary cut.face.face).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr
        ⟨cut.face.face, i⟩ =
      ⟨rightFace P cut,
        positiveRightChildSideIndex P cut horientation
          ((rightDegenerateCutSideIndex
            P cut horientation hleft hr i).addNat 1)⟩ := by
  simp [rightDegenerateMapOccurrence]

@[simp]
theorem rightDegenerateMapOccurrence_retained
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    {f : P.Face} (hface : f ≠ cut.face.face)
    (i : Fin (P.boundary f).length) :
    rightDegenerateMapOccurrence
        P cut horientation hleft hr ⟨f, i⟩ =
      ⟨oldFace P cut f,
        retainedSideIndex P cut hface i⟩ := by
  simp [rightDegenerateMapOccurrence, hface]

theorem rightDegeneratePreMap_occurrenceSide
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        ((P.occurrenceSide o).point t) =
      (split P cut).polygonalMk
        (split_isSurfaceValid P cut validP)
        (((split P cut).occurrenceSide
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr o)).point t) := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_selected_side
      P cut horientation hleft hr validP i t using 1 <;> rfl
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i]
    simp only [occurrenceSide,
      PolygonGluing.Side.point]
    convert rightDegeneratePreMap_retained_side
      P cut horientation hleft hr validP hface i t using 1 <;> rfl

theorem rightDegenerateMapOccurrence_dart
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).dart =
      P1.castSuccDart o.dart := by
  classical
  rcases o with ⟨f, i⟩
  by_cases hface : f = cut.face.face
  · subst f
    rw [rightDegenerateMapOccurrence_selected,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq (split_boundary_right P cut)]
    change
      (rightBoundary P cut).get
          ⟨(rightDegenerateCutSideIndex
              P cut horientation hleft hr i).val + 1,
            by
              rw [rightBoundary_of_orientation_false
                P cut horientation]
              simp [retainWord]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt⟩ =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.get_of_eq
      (rightBoundary_of_orientation_false
        P cut horientation)]
    change
      (.neg (freshEdge P) :: retainWord cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val + 1]'(by
              simp [retainWord]
              exact
                (rightDegenerateCutSideIndex
                  P cut horientation hleft hr i).isLt) =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_cons_succ]
    change
      (List.map P1.castSuccDart cut.right)[
          (rightDegenerateCutSideIndex
            P cut horientation hleft hr i).val] =
        P1.castSuccDart
          ((P.boundary cut.face.face)[i.val])
    rw [List.getElem_map]
    exact congrArg P1.castSuccDart
      (right_get_rightDegenerateCutSideIndex
        P cut horientation hleft hr i)
  · rw [rightDegenerateMapOccurrence_retained
      P cut horientation hleft hr hface i,
      BoundaryOccurrence.dart_mk]
    rw [List.get_of_eq
      (split_boundary_old_of_ne P cut hface)]
    change
      (List.map P1.castSuccDart
        (P.boundary f))[i.val] =
          P1.castSuccDart
            ((P.boundary f)[i.val])
    rw [List.getElem_map]

@[simp]
theorem rightDegenerateMapOccurrence_edge
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (o : P.BoundaryOccurrence) :
    (rightDegenerateMapOccurrence
      P cut horientation hleft hr o).edge =
      o.edge.castSucc := by
  rw [BoundaryOccurrence.edge,
    rightDegenerateMapOccurrence_dart]
  exact P1.edgeOfDart_castSuccDart o.dart

theorem rightDegenerateMapOccurrence_injective
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length) :
    Function.Injective
      (rightDegenerateMapOccurrence
        P cut horientation hleft hr) := by
  classical
  rintro ⟨f, i⟩ ⟨g, j⟩ hmap
  by_cases hf : f = cut.face.face
  · subst f
    by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_selected] at hmap
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hindex :
          rightDegenerateCutSideIndex
              P cut horientation hleft hr i =
            rightDegenerateCutSideIndex
              P cut horientation hleft hr j := by
        apply Fin.ext
        simpa [positiveRightChildSideIndex] using hval
      have hij :=
        rightDegenerateCutSideIndex_injective
          P cut horientation hleft hr hindex
      subst j
      rfl
    · rw [rightDegenerateMapOccurrence_selected,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      exact (oldFace_ne_rightFace P cut g
        (congrArg Sigma.fst hmap).symm).elim
  · by_cases hg : g = cut.face.face
    · subst g
      rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_selected] at hmap
      exact (oldFace_ne_rightFace P cut f
        (congrArg Sigma.fst hmap)).elim
    · rw [rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hf i,
        rightDegenerateMapOccurrence_retained
          P cut horientation hleft hr hg j] at hmap
      have hface : f = g :=
        oldFace_injective P cut
          (congrArg Sigma.fst hmap)
      subst g
      have hval := congrArg
        (fun o : (split P cut).BoundaryOccurrence =>
          o.2.val) hmap
      have hij : i = j := by
        apply Fin.ext
        simpa [retainedSideIndex] using hval
      subst j
      rfl

noncomputable def rightDegenerateMapPairing
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (pairing : P.BoundaryPairing) :
    (split P cut).BoundaryPairing where
  source :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.source
  target :=
    rightDegenerateMapOccurrence
      P cut horientation hleft hr pairing.target
  source_ne_target := by
    intro h
    exact pairing.source_ne_target
      (rightDegenerateMapOccurrence_injective
        P cut horientation hleft hr h)
  source_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.source_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  target_not_boundary := by
    rw [rightDegenerateMapOccurrence_edge]
    intro hboundary
    apply pairing.target_not_boundary
    unfold IsBoundaryEdge at hboundary ⊢
    rw [edgeMultiplicity_split_castSucc P cut]
    exact hboundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction with
    | same =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        exact congrArg P1.castSuccDart hcompatible
    | opposite =>
        have hcompatible := pairing.compatible
        rw [hdirection] at hcompatible
        change
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.target).dart =
          (rightDegenerateMapOccurrence
            P cut horientation hleft hr pairing.source).dart.flip
        rw [rightDegenerateMapOccurrence_dart,
          rightDegenerateMapOccurrence_dart]
        change
          P1.castSuccDart pairing.target.dart =
            (P1.castSuccDart pairing.source.dart).flip
        rw [← P2.castSuccDart_flip]
        exact congrArg P1.castSuccDart hcompatible

theorem rightDegeneratePreMap_pairing_eq
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.source.point t) =
      rightDegeneratePreMap
        P cut horientation hleft hr validP
        (pairing.identification.target.point
          (pairing.identification.parameter t)) := by
  rw [BoundaryPairing.identification_source,
    BoundaryPairing.identification_target,
    rightDegeneratePreMap_occurrenceSide,
    rightDegeneratePreMap_occurrenceSide]
  simpa [rightDegenerateMapPairing,
      PolygonGluing.Identification.parameter] using
    (split P cut).polygonalMk_pairing_eq
      (split_isSurfaceValid P cut validP)
      (rightDegenerateMapPairing
        P cut horientation hleft hr pairing) t

theorem rightDegeneratePreMap_respects
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid)
    {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    rightDegeneratePreMap
        P cut horientation hleft hr validP x =
      rightDegeneratePreMap
        P cut horientation hleft hr validP y := by
  change Relation.EqvGen
    (PolygonGluing.Generator
      (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel _ _ hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact rightDegeneratePreMap_pairing_eq
            P cut horientation hleft hr validP pairing t
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

end P2

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
