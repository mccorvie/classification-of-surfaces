/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicCancellation

/-!
# Exact two-face merging for finite cyclic presentations

Two displayed faces separated by a last-index edge are the canonical P2 split of the
concatenation of their old boundary words, up to rotating the first child.  This supplies the
local merge used to reduce a connected presentation to one face.  It covers both ordinary
nondegenerate cuts and the one-sided monogon case.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace FaceMerge

/-- The one-face presentation obtained after merging the displayed pair. -/
@[reducible]
def target {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (U ++ V)

/-- Two displayed faces sharing only the last-index separator in the shown positions. -/
@[reducible]
def source {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces :=
    [[.pos (P1.freshEdge n)] ++ P2.retainWord U,
      [.neg (P1.freshEdge n)] ++ P2.retainWord V]

/-- The canonical cut of the concatenated target word between `U` and `V`. -/
def targetCut {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    P2Cut (target U V) where
  face := ⟨0, false⟩
  left := U
  right := V
  boundary_rotated := List.IsRotated.refl _

@[simp]
theorem targetCut_left {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).left = U :=
  rfl

@[simp]
theorem targetCut_right {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    (targetCut U V).right = V :=
  rfl

/-- The displayed two-face source differs from the canonical target split only by rotating its
first child boundary. -/
def sourceSignedIsoSplitTarget {n : ℕ}
    (U V : List (SignedDart (Fin n))) :
    SignedPresentationIso
      (source U V) (P2.split (target U V) (targetCut U V)) where
  edgeRelabeling := by
    change EdgeRelabeling (Fin (n + 1)) (Fin (n + 1))
    exact EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    change
      (((source U V).boundary f).map
        (EdgeRelabeling.refl (Fin (n + 1))).mapDart).IsRotated
        ((P2.split (target U V) (targetCut U V)).boundary f)
    rw [EdgeRelabeling.map_mapDart_refl]
    fin_cases f
    · change
        ([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).IsRotated
          (P2.retainWord U ++
            [SignedDart.pos (P1.freshEdge n)])
      exact List.isRotated_append
    · change
        ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).IsRotated
          ([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V)
      exact List.IsRotated.refl _

/-- Merging preserves ordinary validity whenever the resulting face is nonempty. -/
theorem target_isSurfaceValid {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (target U V).IsSurfaceValid := by
  classical
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa [target, Dyck.oneFace_boundary] using hUV
  · intro f g _h
    exact (Dyck.oneFace_face_eq_zero (U ++ V) f).trans
      (Dyck.oneFace_face_eq_zero (U ++ V) g).symm
  · intro e
    have hmultiplicity := validSource.2.2.2 e.castSucc
    change
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 1 ∨
      (∑ f : Fin 2,
        (source U V).faceEdgeMultiplicity f e.castSucc) = 2
        at hmultiplicity
    rw [Fin.sum_univ_two] at hmultiplicity
    change
      ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 1) ∨
        ((([SignedDart.pos (P1.freshEdge n)] ++
            P2.retainWord U).map edgeOfDart).count e.castSucc +
          (([SignedDart.neg (P1.freshEdge n)] ++
            P2.retainWord V).map edgeOfDart).count e.castSucc = 2)
        at hmultiplicity
    have hne : P1.freshEdge n ≠ e.castSucc :=
      (P1.firstSubedge_ne_freshEdge e).symm
    simp only [List.map_append, List.map_cons, List.map_nil,
      edgeOfDart, List.count_append, List.count_cons,
      List.count_nil] at hmultiplicity
    simp [hne] at hmultiplicity
    rw [P2.count_retainWord_castSucc,
      P2.count_retainWord_castSucc] at hmultiplicity
    rw [Dyck.oneFace_edgeMultiplicity]
    change
      ((U ++ V).map edgeOfDart).count e = 1 ∨
        ((U ++ V).map edgeOfDart).count e = 2
    simpa [List.map_append, List.count_append] using hmultiplicity

/-- The canonical cut is ordinary whenever the concatenated target is nonempty: it is either
nondegenerate or exactly one-sided-degenerate. -/
theorem targetCut_isOrdinary {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ []) :
    (targetCut U V).IsNondegenerate ∨
      ((targetCut U V).left = [] ∧
          0 < (targetCut U V).right.length) ∨
        (0 < (targetCut U V).left.length ∧
          (targetCut U V).right = []) := by
  by_cases hU : U = []
  · right
    left
    subst U
    exact ⟨rfl, List.length_pos_iff_ne_nil.mpr (by simpa using hUV)⟩
  · by_cases hV : V = []
    · right
      right
      exact ⟨List.length_pos_iff_ne_nil.mpr hU, hV⟩
    · left
      exact ⟨hU, hV⟩

/-- Merge the displayed two faces into their concatenated one-face presentation. -/
theorem normalizationEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source U V, validSource⟩
      ⟨target U V,
        target_isSurfaceValid U V hUV validSource⟩ := by
  let splitTarget := P2.split (target U V) (targetCut U V)
  let sourceIso := sourceSignedIsoSplitTarget U V
  let validSplit : splitTarget.IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validTarget : (target U V).IsSurfaceValid :=
    target_isSurfaceValid U V hUV validSource
  have hsplit :
      NormalizationEquivalent
        ⟨source U V, validSource⟩
        ⟨splitTarget, validSplit⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  have hmerge :
      NormalizationEquivalent
        ⟨splitTarget, validSplit⟩
        ⟨target U V, validTarget⟩ := by
    have hcanonical :=
      P2.ordinaryMergeNormalizationEquivalent
        (target U V) (targetCut U V)
        (targetCut_isOrdinary U V hUV) validTarget
    exact hcanonical
  exact hsplit.trans hmerge

/-- Public realization-invariance form of exact two-face merging. -/
theorem polygonallyEquivalent {n : ℕ}
    (U V : List (SignedDart (Fin n)))
    (hUV : U ++ V ≠ [])
    (validSource : (source U V).IsSurfaceValid) :
    (source U V).PolygonallyEquivalent
      (target U V) validSource
      (target_isSurfaceValid U V hUV validSource) :=
  (normalizationEquivalent U V hUV validSource).polygonallyEquivalent

/-! ### Merging through an arbitrary signed-isomorphic split -/

/-- Any presentation signed-isomorphic to an ordinary canonical P2 split can be merged.
This is the stable interface used when the two child faces occur among additional untouched
faces: all face ordering and edge naming is confined to `sourceIso`. -/
theorem normalizationEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    NormalizationEquivalent
      ⟨P, validP⟩
      ⟨Q, validQ⟩ := by
  let validSplitFromIso : (P2.split Q cut).IsSurfaceValid :=
    sourceIso.isSurfaceValid validP
  let validCanonicalSplit : (P2.split Q cut).IsSurfaceValid :=
    P2.split_isSurfaceValid Q cut validQ
  have hsplitNode :
      (⟨P2.split Q cut, validSplitFromIso⟩ : ValidPresentation) =
        ⟨P2.split Q cut, validCanonicalSplit⟩ := by
    apply ValidPresentation.ext
    rfl
  have hsource :
      NormalizationEquivalent
        ⟨P, validP⟩
        ⟨P2.split Q cut, validSplitFromIso⟩ :=
    NormalizationEquivalent.ofSignedIso sourceIso
  rw [hsplitNode] at hsource
  exact hsource.trans
    (P2.ordinaryMergeNormalizationEquivalent Q cut hcut validQ)

/-- Public realization-invariance form of merging through a signed-isomorphic split. -/
theorem polygonallyEquivalentOfSignedIso
    {P Q : FiniteCyclicPresentation}
    (cut : P2Cut Q)
    (hcut :
      cut.IsNondegenerate ∨
        (cut.left = [] ∧ 0 < cut.right.length) ∨
          (0 < cut.left.length ∧ cut.right = []))
    (sourceIso : SignedPresentationIso P (P2.split Q cut))
    (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  (normalizationEquivalentOfSignedIso
    cut hcut sourceIso validP validQ).polygonallyEquivalent

/-! ### Arbitrary separator names -/

/-- Two displayed faces with an arbitrarily named, oppositely oriented separator. -/
@[reducible]
def namedSource {n : ℕ} (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1)))) :
    FiniteCyclicPresentation where
  edgeCount := n + 1
  faces := [[.pos a] ++ U, [.neg a] ++ V]

/-- Rename the separator to last and delete that name from both remaining face words. -/
def namedSourceSignedIso {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart) :
    SignedPresentationIso
      (namedSource a U V)
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv (Cancellation.moveToLast a)
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    fin_cases f
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.pos a)] ++
          Cancellation.renamedTail a U).IsRotated
          ([.pos (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a U))
      rw [Cancellation.retainWord_lowerTail a U haU]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.pos a) =
            .pos (P1.freshEdge n) by simp [hmove]]
    · change
        ([SignedDart.mapEquiv
            (Cancellation.moveToLast a) (.neg a)] ++
          Cancellation.renamedTail a V).IsRotated
          ([.neg (P1.freshEdge n)] ++
            P2.retainWord (Cancellation.lowerTail a V))
      rw [Cancellation.retainWord_lowerTail a V haV]
      have hmove :
          Cancellation.moveToLast a a = P1.freshEdge n := by
        simp [Cancellation.moveToLast, P1.freshEdge]
      rw [show SignedDart.mapEquiv
          (Cancellation.moveToLast a) (.neg a) =
            .neg (P1.freshEdge n) by simp [hmove]]

/-- Merge two displayed faces with an arbitrary separator name. -/
theorem namedNormalizationEquivalent {n : ℕ}
    (a : Fin (n + 1))
    (U V : List (SignedDart (Fin (n + 1))))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (hUV :
      Cancellation.lowerTail a U ++
        Cancellation.lowerTail a V ≠ [])
    (validSource : (namedSource a U V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨namedSource a U V, validSource⟩
      ⟨target
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V),
        target_isSurfaceValid
          (Cancellation.lowerTail a U)
          (Cancellation.lowerTail a V) hUV
          ((namedSourceSignedIso a U V haU haV).isSurfaceValid
            validSource)⟩ := by
  let sourceIso := namedSourceSignedIso a U V haU haV
  let validBase :
      (source
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V)).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      (normalizationEquivalent
        (Cancellation.lowerTail a U)
        (Cancellation.lowerTail a V) hUV validBase)

end FaceMerge

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
