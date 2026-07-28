/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicDerivedRewrites

/-!
# Cancellation chains for finite cyclic presentations

This file implements Gallier--Xu Step 1.  The exact base spelling has a fresh-last edge followed
immediately by its inverse.  Splitting between that pair and the remaining word produces exactly
the P1 expansion of the one-sided split of the word with the pair removed.  Thus one P2 split,
one P1 contraction, and one one-sided P2 merge cancel the pair.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Cancellation

/-- The word after deleting the displayed inverse pair. -/
@[reducible]
def target {n : ℕ} (X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace X

/-- The base cancellation spelling, with the cancellable edge named last. -/
@[reducible]
def source {n : ℕ} (X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace
    ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
      P2.retainWord X)

/-- Split the inverse pair from the remaining word. -/
def sourceCut {n : ℕ} (X : List (SignedDart (Fin n))) :
    P2Cut (source X) where
  face := ⟨0, false⟩
  left := [.pos (P1.freshEdge n)]
  right := [.neg (P1.freshEdge n)] ++ P2.retainWord X
  boundary_rotated := by
    exact List.IsRotated.refl _

/-- Split the target at position zero, producing a monogon and the target word. -/
def targetCut {n : ℕ} (X : List (SignedDart (Fin n))) :
    P2Cut (target X) :=
  P2Cut.canonical ⟨0, false⟩ 0

@[simp]
theorem sourceCut_left {n : ℕ} (X : List (SignedDart (Fin n))) :
    (sourceCut X).left = [.pos (P1.freshEdge n)] :=
  rfl

@[simp]
theorem sourceCut_right {n : ℕ} (X : List (SignedDart (Fin n))) :
    (sourceCut X).right =
      [.neg (P1.freshEdge n)] ++ P2.retainWord X :=
  rfl

theorem sourceCut_isNondegenerate {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    (sourceCut X).IsNondegenerate := by
  constructor <;> simp

@[simp]
theorem targetCut_left {n : ℕ} (X : List (SignedDart (Fin n))) :
    (targetCut X).left = [] :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ} (X : List (SignedDart (Fin n))) :
    (targetCut X).right = X :=
  rfl

/-- Expanding at the fresh-last edge only retains every twice-embedded old dart. -/
theorem expandWord_retainWord_fresh {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    P1.expandWord (P1.freshEdge n) (P2.retainWord X) =
      P2.retainWord (P2.retainWord X) := by
  change
    P1.expandWord (Fin.last n) (X.map P1.castSuccDart) =
      (X.map P1.castSuccDart).map P1.castSuccDart
  induction X with
  | nil => rfl
  | cons d X ih =>
      simp only [List.map_cons, P1.expandWord_cons]
      cases d with
      | pos e =>
          simp only [P1.castSuccDart_pos]
          rw [P1.expandDart_pos_of_ne (Fin.castSucc_ne_last e)]
          simp only [ih, List.singleton_append]
      | neg e =>
          simp only [P1.castSuccDart_neg]
          rw [P1.expandDart_neg_of_ne (Fin.castSucc_ne_last e)]
          simp only [ih, List.singleton_append]

/-- The source split is exactly the P1 expansion of the target's one-sided split. -/
theorem split_source_eq_expand_split_target {n : ℕ}
    (X : List (SignedDart (Fin n))) :
    P2.split (source X) (sourceCut X) =
      P1.expand (P2.split (target X) (targetCut X))
        (P2.freshEdge (target X)) := by
  simp [P2.split, P2.faceWord, P1.expand, P1.expandWord,
    P2.selectedBoundary, P2.rightBoundary,
    P2.selectedOrientedBoundary, P2.rightOrientedBoundary,
    P2.storedWord, source, target, sourceCut, targetCut,
    P2Cut.canonical, Dyck.oneFace, P2.retainWord,
    P1.freshEdge, P2.freshEdge]
  constructor
  · change
      [SignedDart.pos (Fin.last n).castSucc,
        SignedDart.pos (Fin.last (n + 1))] =
        P1.expandWord (Fin.last n) [.pos (Fin.last n)]
    simp [P1.firstSubedge, P1.freshEdge]
  · change
      SignedDart.neg (Fin.last (n + 1)) ::
          SignedDart.neg (Fin.last n).castSucc ::
            X.map (P1.castSuccDart ∘ P1.castSuccDart) =
        P1.expandWord (Fin.last n)
          (SignedDart.neg (Fin.last n) ::
            X.map P1.castSuccDart)
    rw [P1.expandWord_cons, P1.expandDart_neg_self,
      show
        P1.expandWord (Fin.last n) (X.map P1.castSuccDart) =
          (X.map P1.castSuccDart).map P1.castSuccDart by
            simpa [P1.freshEdge, P2.retainWord] using
              expandWord_retainWord_fresh X]
    simp [P1.firstSubedge, P1.freshEdge, Function.comp_def]

/-- Deleting an inverse pair preserves the unoriented edge-occurrence multiplicities of all
remaining edges. -/
theorem target_isSurfaceValid {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (hX : X ≠ [])
    (validSource : (source X).IsSurfaceValid) :
    (target X).IsSurfaceValid := by
  classical
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    have hsourceNonempty :
        ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
          P2.retainWord X) ≠ [] := by
      simp
    simpa [target, Dyck.oneFace_boundary] using hX
  · intro f g _h
    exact Dyck.oneFace_face_eq_zero X f |>.trans
      (Dyck.oneFace_face_eq_zero X g).symm
  · intro e
    have hmultiplicity := validSource.2.2.2 e.castSucc
    rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity ⊢
    simp only [List.map_append, List.map_cons,
      List.map_nil, edgeOfDart, List.count_append,
      List.count_cons, List.count_nil] at hmultiplicity
    rw [P2.count_retainWord_castSucc] at hmultiplicity
    have hne : e.castSucc ≠ P1.freshEdge n :=
      P1.firstSubedge_ne_freshEdge e
    simp [hne.symm] at hmultiplicity
    exact hmultiplicity

/-- Gallier--Xu Step 1 for the base spelling: split the inverse pair, contract the resulting
two-edge paths, then merge the monogon produced by the one-sided target split. -/
theorem normalizationEquivalent {n : ℕ}
    (X : List (SignedDart (Fin n)))
    (hX : X ≠ [])
    (validSource : (source X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source X, validSource⟩
      ⟨target X, target_isSurfaceValid X hX validSource⟩ := by
  let validTarget : (target X).IsSurfaceValid :=
    target_isSurfaceValid X hX validSource
  let sourceSplit := P2.split (source X) (sourceCut X)
  let targetSplit := P2.split (target X) (targetCut X)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source X) (sourceCut X) validSource
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (target X) (targetCut X) validTarget
  have hsource :
      NormalizationEquivalent
        ⟨source X, validSource⟩
        ⟨sourceSplit, validSourceSplit⟩ :=
    NormalizationEquivalent.ofP2
      (P2Subdivision.canonical
        (source X) (sourceCut X) (sourceCut_isNondegenerate X))
  have hmiddle :
      NormalizationEquivalent
        ⟨sourceSplit, validSourceSplit⟩
        ⟨targetSplit, validTargetSplit⟩ := by
    have hcontract :=
      P1.contractionNormalizationEquivalent
        targetSplit (P2.freshEdge (target X)) validTargetSplit
    have hnode :
        (⟨sourceSplit, validSourceSplit⟩ : ValidPresentation) =
          ⟨P1.expand targetSplit (P2.freshEdge (target X)),
            P1.expand_isSurfaceValid targetSplit
              (P2.freshEdge (target X)) validTargetSplit⟩ := by
      apply ValidPresentation.ext
      exact split_source_eq_expand_split_target X
    rw [hnode]
    exact hcontract
  have htarget :
      NormalizationEquivalent
        ⟨targetSplit, validTargetSplit⟩
        ⟨target X, validTarget⟩ := by
    apply P2.oneSidedMergeNormalizationEquivalent
    exact Or.inl
      ⟨targetCut_left X,
        List.length_pos_iff_ne_nil.mpr hX⟩
  exact hsource.trans (hmiddle.trans htarget)

end Cancellation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
