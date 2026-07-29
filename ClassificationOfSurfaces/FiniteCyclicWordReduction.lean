/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicCancellation
import ClassificationOfSurfaces.FiniteCyclicReduction
import ClassificationOfSurfaces.FiniteCyclicNormalizationResult

/-!
# Recursive reduction of finite cyclic one-face words

The face-merging recursion deliberately retains each deleted separator as a cyclically adjacent
inverse pair.  This file supplies the next normalization phase: repeatedly cancel every such pair
while preserving a validity-bundled normalization chain.  If the final pair is the whole word,
the result is the agreed ordinary-valid two-monogon sphere presentation.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

/-- The unique face of a presentation whose stored face list has length one. -/
def onlyFace (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    P.Face :=
  ⟨0, by omega⟩

/-- Rewrite an arbitrary one-face presentation using its unique stored boundary word. -/
@[reducible]
def explicitOneFace
    (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (P.boundary (onlyFace P hfaces))

/-- Every presentation with one stored face is signed-isomorphic to its explicit one-word
spelling. -/
def explicitOneFaceSignedIso
    (P : FiniteCyclicPresentation) (hfaces : P.faces.length = 1) :
    SignedPresentationIso P (explicitOneFace P hfaces) where
  edgeRelabeling := EdgeRelabeling.refl _
  faceEquiv := by
    change Fin P.faces.length ≃ Fin 1
    exact finCongr hfaces
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl, Dyck.oneFace_boundary]
    have hf : f = onlyFace P hfaces := by
      apply Fin.ext
      have hflt := f.isLt
      change f.val < P.faces.length at hflt
      change f.val = 0
      omega
    rw [hf]

/-- The two possible signed spellings of an adjacent inverse pair. -/
def inversePair {Edge : Type} (a : Edge) : Bool → List (SignedDart Edge)
  | false => [.pos a, .neg a]
  | true => [.neg a, .pos a]

/-- Data exposing a cyclically adjacent inverse pair in a one-face word. -/
structure CancellablePair {n : ℕ}
    (word : List (SignedDart (Fin n))) where
  edge : Fin n
  tail : List (SignedDart (Fin n))
  negativeFirst : Bool
  rotated : word.IsRotated (inversePair edge negativeFirst ++ tail)

/-- A one-face word has no cyclically adjacent inverse pair. -/
def IsPairReduced {n : ℕ}
    (word : List (SignedDart (Fin n))) : Prop :=
  IsEmpty (CancellablePair word)

/-- Validity forces the displayed inverse pair's edge to be absent from its remaining tail. -/
theorem CancellablePair.edge_not_mem_tail {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    pair.edge ∉ pair.tail.map edgeOfDart := by
  intro htail
  have hpositive :
      0 < (pair.tail.map edgeOfDart).count pair.edge :=
    List.count_pos_iff.mpr htail
  have hcount :=
    (pair.rotated.map edgeOfDart).perm.count_eq pair.edge
  have hmultiplicity := valid.2.2.2 pair.edge
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  have hcount' :
      (word.map edgeOfDart).count pair.edge =
        2 + (pair.tail.map edgeOfDart).count pair.edge := by
    rw [hcount]
    cases pair.negativeFirst <;>
      simp [inversePair, edgeOfDart] <;>
      omega
  omega

/-- If deleting a displayed pair leaves the empty word, there were no other edge names. -/
theorem predecessor_eq_zero_of_lowerTail_eq_nil {n : ℕ}
    (a : Fin (n + 1))
    (X : List (SignedDart (Fin (n + 1))))
    (ha : a ∉ X.map edgeOfDart)
    (hlower : Cancellation.lowerTail a X = [])
    (valid : (Cancellation.namedSource a X).IsSurfaceValid) :
    n = 0 := by
  have hrenamed :
      Cancellation.renamedTail a X = [] := by
    rw [← Cancellation.retainWord_lowerTail a X ha, hlower]
    rfl
  have hX : X = [] := by
    simpa [Cancellation.renamedTail] using hrenamed
  by_contra hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let e : Fin n := ⟨0, hnpos⟩
  let b : Fin (n + 1) :=
    (Cancellation.moveToLast a).symm e.castSucc
  have hba : b ≠ a := by
    intro h
    have hmapped := congrArg (Cancellation.moveToLast a) h
    have hbmap :
        Cancellation.moveToLast a b = e.castSucc := by
      exact (Cancellation.moveToLast a).apply_symm_apply e.castSucc
    rw [hbmap] at hmapped
    rw [show Cancellation.moveToLast a a = Fin.last n by
      simp [Cancellation.moveToLast]]
      at hmapped
    exact Fin.castSucc_ne_last e hmapped
  have hmultiplicity := valid.2.2.2 b
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  simp [hX, edgeOfDart, hba.symm] at hmultiplicity

/-- A reduced non-spherical endpoint reached after inverse-pair cancellation. -/
structure ReducedWordResult (P : ValidPresentation) where
  edgeCount : ℕ
  word : List (SignedDart (Fin edgeCount))
  valid : (Dyck.oneFace word).IsSurfaceValid
  reduced : IsPairReduced word
  equivalent :
    NormalizationEquivalent P ⟨Dyck.oneFace word, valid⟩

/-- Cancellation either reaches the canonical sphere presentation or a pair-reduced one-face
word. -/
inductive CancellationResult (P : ValidPresentation)
  | sphere
      (equivalent :
        NormalizationEquivalent P
          ⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩)
  | reduced (result : ReducedWordResult P)

namespace CancellationResult

/-- Transport a cancellation result backward through a normalization equivalence. -/
noncomputable def ofEquivalent {P Q : ValidPresentation}
    (hPQ : NormalizationEquivalent P Q) :
    CancellationResult Q → CancellationResult P
  | .sphere hQS => .sphere (hPQ.trans hQS)
  | .reduced result =>
      .reduced
        { edgeCount := result.edgeCount
          word := result.word
          valid := result.valid
          reduced := result.reduced
          equivalent := hPQ.trans result.equivalent }

end CancellationResult

/-- Fuel-bounded implementation of repeated inverse-pair cancellation. -/
noncomputable def cancelInversePairsFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    word.length ≤ fuel →
      CancellationResult ⟨Dyck.oneFace word, valid⟩ := by
  classical
  intro hbound
  by_cases hpairs : Nonempty (CancellablePair word)
  · let pair := Classical.choice hpairs
    cases n with
    | zero =>
        exact Fin.elim0 pair.edge
    | succ n =>
        let a : Fin (n + 1) := pair.edge
        let X : List (SignedDart (Fin (n + 1))) := pair.tail
        have ha : a ∉ X.map edgeOfDart :=
          pair.edge_not_mem_tail valid
        let lower := Cancellation.lowerTail a X
        have hlowerLength : lower.length = X.length := by
          have hlength :=
            congrArg List.length
              (Cancellation.retainWord_lowerTail a X ha)
          simpa [lower, P2.retainWord,
            Cancellation.renamedTail] using hlength
        have hwordLength :
            word.length = 2 + X.length := by
          have hlength := pair.rotated.perm.length_eq
          cases horientation : pair.negativeFirst
          · have hlength' :
                word.length = X.length + 1 + 1 := by
              simpa [a, X, inversePair, horientation] using hlength
            omega
          · have hlength' :
                word.length = X.length + 1 + 1 := by
              simpa [a, X, inversePair, horientation] using hlength
            omega
        have hlowerShorter : lower.length < word.length := by
          omega
        have hfuelPositive : 0 < fuel := by
          omega
        have hlowerBound : lower.length ≤ fuel - 1 := by
          omega
        by_cases hlower : lower = []
        · cases horientation : pair.negativeFirst
          · have hrotated :
                word.IsRotated
                  ([.pos a, .neg a] ++ X) := by
              simpa [a, X, inversePair, horientation] using pair.rotated
            let rotation :=
              Dyck.oneFaceSignedIsoOfIsRotated hrotated
            let validNamed :
                (Cancellation.namedSource a X).IsSurfaceValid :=
              rotation.isSurfaceValid valid
            have hnzero :=
              predecessor_eq_zero_of_lowerTail_eq_nil
                a X ha hlower validNamed
            subst n
            let renameIso :=
              Cancellation.namedSourceSignedIso a X ha
            let validBase :
                (Cancellation.source
                  (Cancellation.lowerTail a X)).IsSurfaceValid :=
              renameIso.isSurfaceValid validNamed
            have hRotate :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.namedSource a X, validNamed⟩ :=
              NormalizationEquivalent.ofSignedIso rotation
            have hRename :
                NormalizationEquivalent
                  ⟨Cancellation.namedSource a X, validNamed⟩
                  ⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :=
              NormalizationEquivalent.ofSignedIso renameIso
            have hToBase :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :=
              hRotate.trans hRename
            have hbase :
                Cancellation.source (Cancellation.lowerTail a X) =
                  Cancellation.source
                    ([] : List (SignedDart (Fin 0))) :=
              congrArg Cancellation.source hlower
            let validEmpty :
                (Cancellation.source
                  ([] : List (SignedDart (Fin 0)))).IsSurfaceValid :=
              hbase ▸ validBase
            have hnode :
                (⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :
                    ValidPresentation) =
                  ⟨Cancellation.source
                    ([] : List (SignedDart (Fin 0))), validEmpty⟩ :=
              ValidPresentation.ext hbase
            rw [hnode] at hToBase
            exact .sphere
              (hToBase.trans
                (Cancellation.sphereNormalizationEquivalent validEmpty))
          · have hrotated :
                word.IsRotated
                  ([.neg a, .pos a] ++ X) := by
              simpa [a, X, inversePair, horientation] using pair.rotated
            let rotation :=
              Dyck.oneFaceSignedIsoOfIsRotated hrotated
            let validNegative :
                (Cancellation.negativeNamedSource a X).IsSurfaceValid :=
              rotation.isSurfaceValid valid
            let signIso :=
              Cancellation.negativeNamedSourceSignedIso a X ha
            let validNamed :
                (Cancellation.namedSource a X).IsSurfaceValid :=
              signIso.isSurfaceValid validNegative
            have hnzero :=
              predecessor_eq_zero_of_lowerTail_eq_nil
                a X ha hlower validNamed
            subst n
            let renameIso :=
              Cancellation.namedSourceSignedIso a X ha
            let validBase :
                (Cancellation.source
                  (Cancellation.lowerTail a X)).IsSurfaceValid :=
              renameIso.isSurfaceValid validNamed
            have hRotate :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.negativeNamedSource a X,
                    validNegative⟩ :=
              NormalizationEquivalent.ofSignedIso rotation
            have hSign :
                NormalizationEquivalent
                  ⟨Cancellation.negativeNamedSource a X,
                    validNegative⟩
                  ⟨Cancellation.namedSource a X, validNamed⟩ :=
              NormalizationEquivalent.ofSignedIso signIso
            have hRename :
                NormalizationEquivalent
                  ⟨Cancellation.namedSource a X, validNamed⟩
                  ⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :=
              NormalizationEquivalent.ofSignedIso renameIso
            have hToBase :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :=
              hRotate.trans (hSign.trans hRename)
            have hbase :
                Cancellation.source (Cancellation.lowerTail a X) =
                  Cancellation.source
                    ([] : List (SignedDart (Fin 0))) :=
              congrArg Cancellation.source hlower
            let validEmpty :
                (Cancellation.source
                  ([] : List (SignedDart (Fin 0)))).IsSurfaceValid :=
              hbase ▸ validBase
            have hnode :
                (⟨Cancellation.source
                    (Cancellation.lowerTail a X), validBase⟩ :
                    ValidPresentation) =
                  ⟨Cancellation.source
                    ([] : List (SignedDart (Fin 0))), validEmpty⟩ :=
              ValidPresentation.ext hbase
            rw [hnode] at hToBase
            exact .sphere
              (hToBase.trans
                (Cancellation.sphereNormalizationEquivalent validEmpty))
        · cases horientation : pair.negativeFirst
          · have hrotated :
                word.IsRotated
                  ([.pos a, .neg a] ++ X) := by
              simpa [a, X, inversePair, horientation] using pair.rotated
            let rotation :=
              Dyck.oneFaceSignedIsoOfIsRotated hrotated
            let validNamed :
                (Cancellation.namedSource a X).IsSurfaceValid :=
              rotation.isSurfaceValid valid
            let renameIso :=
              Cancellation.namedSourceSignedIso a X ha
            let validBase :
                (Cancellation.source lower).IsSurfaceValid :=
              renameIso.isSurfaceValid validNamed
            let validLower :
                (Cancellation.target lower).IsSurfaceValid :=
              Cancellation.target_isSurfaceValid lower hlower validBase
            have hRotate :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.namedSource a X, validNamed⟩ :=
              NormalizationEquivalent.ofSignedIso rotation
            have hRename :
                NormalizationEquivalent
                  ⟨Cancellation.namedSource a X, validNamed⟩
                  ⟨Cancellation.source lower, validBase⟩ :=
              NormalizationEquivalent.ofSignedIso renameIso
            have hstep :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.target lower, validLower⟩ :=
              hRotate.trans
                (hRename.trans
                  (Cancellation.normalizationEquivalent
                    lower hlower validBase))
            exact
              (cancelInversePairsFuel (fuel - 1)
                lower validLower hlowerBound).ofEquivalent hstep
          · have hrotated :
                word.IsRotated
                  ([.neg a, .pos a] ++ X) := by
              simpa [a, X, inversePair, horientation] using pair.rotated
            let rotation :=
              Dyck.oneFaceSignedIsoOfIsRotated hrotated
            let validNegative :
                (Cancellation.negativeNamedSource a X).IsSurfaceValid :=
              rotation.isSurfaceValid valid
            let signIso :=
              Cancellation.negativeNamedSourceSignedIso a X ha
            let validNamed :
                (Cancellation.namedSource a X).IsSurfaceValid :=
              signIso.isSurfaceValid validNegative
            let renameIso :=
              Cancellation.namedSourceSignedIso a X ha
            let validBase :
                (Cancellation.source lower).IsSurfaceValid :=
              renameIso.isSurfaceValid validNamed
            let validLower :
                (Cancellation.target lower).IsSurfaceValid :=
              Cancellation.target_isSurfaceValid lower hlower validBase
            have hRotate :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.negativeNamedSource a X,
                    validNegative⟩ :=
              NormalizationEquivalent.ofSignedIso rotation
            have hSign :
                NormalizationEquivalent
                  ⟨Cancellation.negativeNamedSource a X,
                    validNegative⟩
                  ⟨Cancellation.namedSource a X, validNamed⟩ :=
              NormalizationEquivalent.ofSignedIso signIso
            have hRename :
                NormalizationEquivalent
                  ⟨Cancellation.namedSource a X, validNamed⟩
                  ⟨Cancellation.source lower, validBase⟩ :=
              NormalizationEquivalent.ofSignedIso renameIso
            have hstep :
                NormalizationEquivalent
                  ⟨Dyck.oneFace word, valid⟩
                  ⟨Cancellation.target lower, validLower⟩ :=
              hRotate.trans
                (hSign.trans
                  (hRename.trans
                    (Cancellation.normalizationEquivalent
                      lower hlower validBase)))
            exact
              (cancelInversePairsFuel (fuel - 1)
                lower validLower hlowerBound).ofEquivalent hstep
  · exact .reduced
      { edgeCount := n
        word := word
        valid := valid
        reduced := ⟨fun pair ↦ hpairs ⟨pair⟩⟩
        equivalent := NormalizationEquivalent.refl _ }
termination_by fuel
decreasing_by
  all_goals
    apply Nat.sub_lt
    · exact hfuelPositive
    · omega

/-- Repeatedly cancel cyclically adjacent inverse pairs in an ordinary-valid one-face word. -/
noncomputable def cancelInversePairs {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    CancellationResult ⟨Dyck.oneFace word, valid⟩ :=
  cancelInversePairsFuel word.length word valid (le_refl _)

/-- Merge a connected valid presentation to one face, rewrite that face explicitly as a cyclic
word, and cancel every adjacent inverse pair. -/
noncomputable def reduceAndCancel
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    CancellationResult P := by
  let oneFace := Reduction.reduceToOneFace P connectedP
  let word :=
    oneFace.target.presentation.boundary
      (onlyFace oneFace.target.presentation oneFace.faces_length)
  let iso :=
    explicitOneFaceSignedIso
      oneFace.target.presentation oneFace.faces_length
  let validWord : (Dyck.oneFace word).IsSurfaceValid :=
    iso.isSurfaceValid oneFace.target.valid
  have hToWord :
      NormalizationEquivalent P
        ⟨Dyck.oneFace word, validWord⟩ :=
    oneFace.equivalent.trans
      (NormalizationEquivalent.ofSignedIso iso)
  exact (cancelInversePairs word validWord).ofEquivalent hToWord

end WordReduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
