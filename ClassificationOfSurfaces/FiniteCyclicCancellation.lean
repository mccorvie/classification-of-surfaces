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

/-- Retaining after contraction recovers a word which does not use the fresh-last edge. -/
theorem retainWord_contractWord_of_fresh_not_mem {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (hfresh : P1.freshEdge n ∉ word.map edgeOfDart) :
    P2.retainWord (P1.contractWord word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      have htail : P1.freshEdge n ∉ word.map edgeOfDart := by
        intro h
        exact hfresh (by simp [h])
      have hd : edgeOfDart d ≠ P1.freshEdge n := by
        intro h
        exact hfresh (by simp [h])
      cases d with
      | pos e =>
          induction e using Fin.lastCases with
          | last =>
              exact (hd rfl).elim
          | cast e =>
              rw [show P1.contractWord
                    (SignedDart.pos e.castSucc :: word) =
                  SignedDart.pos e :: P1.contractWord word by
                simp [P1.contractWord]]
              change
                P2.retainWord
                    (SignedDart.pos e :: P1.contractWord word) =
                  SignedDart.pos e.castSucc :: word
              have ih' := ih htail
              change
                (P1.contractWord word).map P1.castSuccDart = word at ih'
              rw [P2.retainWord, List.map_cons,
                P1.castSuccDart_pos, ih']
      | neg e =>
          induction e using Fin.lastCases with
          | last =>
              exact (hd rfl).elim
          | cast e =>
              rw [show P1.contractWord
                    (SignedDart.neg e.castSucc :: word) =
                  SignedDart.neg e :: P1.contractWord word by
                simp [P1.contractWord]]
              change
                P2.retainWord
                    (SignedDart.neg e :: P1.contractWord word) =
                  SignedDart.neg e.castSucc :: word
              have ih' := ih htail
              change
                (P1.contractWord word).map P1.castSuccDart = word at ih'
              rw [P2.retainWord, List.map_cons,
                P1.castSuccDart_neg, ih']

/-- Move a chosen edge name to the fresh-last position. -/
def moveToLast {n : ℕ} (a : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.swap a (Fin.last n)

/-- Rename a tail so that the displayed cancellable edge becomes last. -/
def renamedTail {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin (n + 1))) :=
  X.map (SignedDart.mapEquiv (moveToLast a))

/-- Delete the now-unused last edge name from a renamed tail. -/
def lowerTail {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  P1.contractWord (renamedTail a X)

theorem freshEdge_not_mem_renamedTail {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    P1.freshEdge n ∉ (renamedTail a X).map edgeOfDart := by
  intro hfresh
  rcases List.mem_map.mp hfresh with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  rw [edgeOfDart_mapEquiv] at hedge
  have holdEdge : edgeOfDart old = a := by
    apply (moveToLast a).injective
    rw [hedge]
    simp [moveToLast, P1.freshEdge]
  exact ha (List.mem_map.mpr ⟨old, hold, holdEdge⟩)

/-- Lowering and re-embedding a tail which avoids the cancellable edge recovers its exact
renamed spelling. -/
theorem retainWord_lowerTail {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    P2.retainWord (lowerTail a X) = renamedTail a X :=
  retainWord_contractWord_of_fresh_not_mem
    (renamedTail a X) (freshEdge_not_mem_renamedTail a X ha)

/-- A one-face word with a displayed positive inverse pair. -/
@[reducible]
def namedSource {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.pos a, .neg a] ++ X)

/-- Rename a displayed cancellable edge to last and contract the unused name from its tail. -/
def namedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (namedSource a X) (source (lowerTail a X)) where
  edgeRelabeling := EdgeRelabeling.ofEquiv (moveToLast a)
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    rw [retainWord_lowerTail a X ha]
    change
      ([SignedDart.mapEquiv (moveToLast a) (.pos a),
          SignedDart.mapEquiv (moveToLast a) (.neg a)] ++
        renamedTail a X).IsRotated
        ([.pos (P1.freshEdge n), .neg (P1.freshEdge n)] ++
          renamedTail a X)
    have hmove : moveToLast a a = P1.freshEdge n := by
      simp [moveToLast, P1.freshEdge]
    rw [show SignedDart.mapEquiv (moveToLast a) (.pos a) =
          .pos (P1.freshEdge n) by simp [hmove],
      show SignedDart.mapEquiv (moveToLast a) (.neg a) =
          .neg (P1.freshEdge n) by simp [hmove]]

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

/-- The zero-tail cancellation branch lands at the ordinary two-monogon sphere. -/
theorem sphereNormalizationEquivalent
    (validSource : (source ([] : List (SignedDart (Fin 0)))).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source ([] : List (SignedDart (Fin 0))), validSource⟩
      ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ := by
  let X : List (SignedDart (Fin 0)) := []
  let sourceSplit := P2.split (source X) (sourceCut X)
  let targetSplit := P2.split (target X) (targetCut X)
  let validSourceSplit : sourceSplit.IsSurfaceValid :=
    P2.split_isSurfaceValid (source X) (sourceCut X) validSource
  have htargetSplit : targetSplit = twoMonogonSphere := by
    rfl
  let validTargetSplit : targetSplit.IsSurfaceValid :=
    htargetSplit.symm ▸ twoMonogonSphere_isSurfaceValid
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
  have htargetNode :
      (⟨targetSplit, validTargetSplit⟩ : ValidPresentation) =
        ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ := by
    apply ValidPresentation.ext
    exact htargetSplit
  rw [← htargetNode]
  exact hsource.trans hmiddle

/-- Transport base cancellation across arbitrary signed presentation isomorphisms. This is the
stable constructor used after rotating a face and renaming its cancellable edge to the last
index. -/
theorem normalizationEquivalentOfSignedIsos
    {P Q : FiniteCyclicPresentation} {n : ℕ}
    (X : List (SignedDart (Fin n))) (hX : X ≠ [])
    (sourceIso : SignedPresentationIso P (source X))
    (targetIso : SignedPresentationIso (target X) Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent ⟨P, validP⟩ ⟨Q, validQ⟩ := by
  let validSource : (source X).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validTarget : (target X).IsSurfaceValid :=
    target_isSurfaceValid X hX validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent X hX validSource).trans
        (NormalizationEquivalent.ofSignedIso targetIso))

/-- Cancellation preserves faithful polygonal realization, in the transported public form. -/
theorem polygonallyEquivalentOfSignedIsos
    {P Q : FiniteCyclicPresentation} {n : ℕ}
    (X : List (SignedDart (Fin n))) (hX : X ≠ [])
    (sourceIso : SignedPresentationIso P (source X))
    (targetIso : SignedPresentationIso (target X) Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  (normalizationEquivalentOfSignedIsos
    X hX sourceIso targetIso validP validQ).polygonallyEquivalent

/-- Cancel a positively displayed adjacent inverse pair with an arbitrary edge name. -/
theorem namedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (namedSource a X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨namedSource a X, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid validSource)⟩ := by
  let sourceIso := namedSourceSignedIso a X ha
  let validBase : (source (lowerTail a X)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      (normalizationEquivalent (lowerTail a X) hlower validBase)

/-- A one-face word with a negatively displayed inverse pair. -/
@[reducible]
def negativeNamedSource {n : ℕ} (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace ([.neg a, .pos a] ++ X)

/-- Reverse only the displayed edge to turn negative cancellation into positive cancellation. -/
def negativeNamedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeNamedSource a X) (namedSource a X) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [List.map_append, List.map_cons, List.map_nil,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos]
    rw [Dyck.reverseEdgeRelabeling_word a X ha]

/-- Cancel a negatively displayed adjacent inverse pair. -/
theorem negativeNamedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (negativeNamedSource a X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeNamedSource a X, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((negativeNamedSourceSignedIso a X ha).isSurfaceValid
              validSource))⟩ := by
  let signIso := negativeNamedSourceSignedIso a X ha
  let validPositive : (namedSource a X).IsSurfaceValid :=
    signIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso signIso).trans
      (namedNormalizationEquivalent a X ha hlower validPositive)

/-- Cancel a positive adjacent inverse pair exposed by a cyclic rotation. -/
theorem normalizationEquivalentOfIsRotated {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (hrotated : word.IsRotated ([.pos a, .neg a] ++ X))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (Dyck.oneFace word).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((Dyck.oneFaceSignedIsoOfIsRotated hrotated).isSurfaceValid
              validSource))⟩ := by
  let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
  let validNamed : (namedSource a X).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso rotation).trans
      (namedNormalizationEquivalent a X ha hlower validNamed)

/-- Cancel a negative adjacent inverse pair exposed by a cyclic rotation. -/
theorem negativeNormalizationEquivalentOfIsRotated {n : ℕ}
    (word : List (SignedDart (Fin (n + 1))))
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (hrotated : word.IsRotated ([.neg a, .pos a] ++ X))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : lowerTail a X ≠ [])
    (validSource : (Dyck.oneFace word).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, validSource⟩
      ⟨target (lowerTail a X),
        target_isSurfaceValid (lowerTail a X) hlower
          ((namedSourceSignedIso a X ha).isSurfaceValid
            ((negativeNamedSourceSignedIso a X ha).isSurfaceValid
              ((Dyck.oneFaceSignedIsoOfIsRotated hrotated).isSurfaceValid
                validSource)))⟩ := by
  let rotation := Dyck.oneFaceSignedIsoOfIsRotated hrotated
  let validNamed : (negativeNamedSource a X).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso rotation).trans
      (negativeNamedNormalizationEquivalent
        a X ha hlower validNamed)

end Cancellation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
