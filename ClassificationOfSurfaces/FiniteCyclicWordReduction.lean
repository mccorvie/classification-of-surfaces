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

/-- Relabel a finished `Fin`-indexed one-face word directly to the existing typed one-face
adapter.  This is the final bridge used by canonical normalization; it does not introduce a
second spelling of any Lean-Eval representative. -/
noncomputable def oneFaceSignedIsoToOfOneFaceWord {n : ℕ}
    {Edge : Type} [Fintype Edge]
    (sourceWord : List (SignedDart (Fin n)))
    (typedWord : List (SignedDart Edge))
    (edgeEquiv : Fin n ≃ Edge)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        typedWord) :
    SignedPresentationIso
      (Dyck.oneFace sourceWord)
      (ofOneFaceWord typedWord) where
  edgeRelabeling :=
    EdgeRelabeling.ofEquiv
      (edgeEquiv.trans (Fintype.equivFin Edge))
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, ofOneFaceWord_boundary,
      EdgeRelabeling.map_mapDart_ofEquiv,
      map_mapEquiv_trans]
    exact rotated.map
      (SignedDart.mapEquiv (Fintype.equivFin Edge))

/-- A finished orientable word, up to its explicit edge relabeling and cyclic rotation, gives a
normalization result at the exact existing orientable canonical presentation. -/
noncomputable def orientableNormalizationResultOfRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeEquiv : Fin k ≃ NormalForm.OrientableEdge p n)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        (NormalForm.orientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible : (NormalForm.orientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.orientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWord
      sourceWord (NormalForm.orientableBoundaryWord p n)
      edgeEquiv rotated)

/-- A finished nonorientable word, up to its explicit edge relabeling and cyclic rotation, gives
a normalization result at the exact existing nonorientable canonical presentation. -/
noncomputable def nonOrientableNormalizationResultOfRotated
    {k p n : ℕ}
    (sourceWord : List (SignedDart (Fin k)))
    (edgeEquiv : Fin k ≃ NormalForm.NonOrientableEdge p n)
    (rotated :
      (sourceWord.map (SignedDart.mapEquiv edgeEquiv)).IsRotated
        (NormalForm.nonOrientableBoundaryWord p n))
    (valid : (Dyck.oneFace sourceWord).IsSurfaceValid)
    (admissible :
      (NormalForm.nonOrientable p n).IsEvalAdmissible) :
    NormalizationResult ⟨Dyck.oneFace sourceWord, valid⟩ :=
  (NormalizationResult.canonical
      (NormalForm.nonOrientable p n) admissible).ofSignedIso
    (oneFaceSignedIsoToOfOneFaceWord
      sourceWord (NormalForm.nonOrientableBoundaryWord p n)
      edgeEquiv rotated)

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

/-- Finish a cancellation result once pair-reduced one-face words have a canonical normalizer. -/
noncomputable def finish {P : ValidPresentation}
    (normalizeReduced :
      (result : ReducedWordResult P) →
        NormalizationResult
          ⟨Dyck.oneFace result.word, result.valid⟩) :
    CancellationResult P → NormalizationResult P
  | .sphere hSphere => by
      have hnode :
          (⟨twoMonogonSphere, twoMonogonSphere_isSurfaceValid⟩ :
            ValidPresentation) =
            canonicalValidPresentation NormalForm.sphere trivial := by
        apply ValidPresentation.ext
        rfl
      rw [hnode] at hSphere
      exact
        { normalForm := .sphere
          admissible := trivial
          equivalent := hSphere }
  | .reduced result =>
      (normalizeReduced result).ofEquivalent result.equivalent

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

/-- The remaining proof obligation after face merging and inverse-pair cancellation: normalize
an arbitrary pair-reduced valid one-face word. -/
structure PairReducedNormalizer where
  normalize :
    {n : ℕ} →
      (word : List (SignedDart (Fin n))) →
      (valid : (Dyck.oneFace word).IsSurfaceValid) →
      IsPairReduced word →
      NormalizationResult ⟨Dyck.oneFace word, valid⟩

/-- A normalizer for pair-reduced words completes the faithful finite-cyclic Gallier--Xu
normalization theorem for every connected valid presentation. -/
noncomputable def normalizeConnected
    (normalizer : PairReducedNormalizer)
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    NormalizationResult P :=
  (reduceAndCancel P connectedP).finish fun result ↦
    normalizer.normalize
      result.word result.valid result.reduced

/-! ### Certified occurrence decompositions for the remaining pairing reduction -/

namespace Pairing

/-- A signed dart with its orientation represented by a Boolean. -/
def dart {α : Type*} (a : α) : Bool → SignedDart α
  | false => .pos a
  | true => .neg a

/-- Boolean orientation of a signed dart. -/
def dartNegative {α : Type*} : SignedDart α → Bool
  | .pos _ => false
  | .neg _ => true

@[simp]
theorem edgeOfDart_dart {α : Type*} (a : α) (negative : Bool) :
    edgeOfDart (dart a negative) = a := by
  cases negative <;> rfl

@[simp]
theorem edgeOfDart_pos {α : Type*} (a : α) :
    edgeOfDart (.pos a) = a := rfl

@[simp]
theorem edgeOfDart_neg {α : Type*} (a : α) :
    edgeOfDart (.neg a) = a := rfl

@[simp]
theorem dart_edgeOfDart_dartNegative {α : Type*}
    (d : SignedDart α) :
    dart (edgeOfDart d) (dartNegative d) = d := by
  cases d <;> rfl

/-- Unoriented edge count is the sum of its positive and negative dart counts. -/
theorem count_edgeOfDart_eq_pos_add_neg {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) :
    (word.map edgeOfDart).count a =
      word.count (.pos a) + word.count (.neg a) := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos e =>
          by_cases hea : e = a
          · subst e
            simp [edgeOfDart, ih]
            omega
          · simp [edgeOfDart, ih, hea]
      | neg e =>
          by_cases hea : e = a
          · subst e
            simp [edgeOfDart, ih]
            omega
          · simp [edgeOfDart, ih, hea]

/-- The four occurrence patterns allowed for one edge of a valid one-face word. -/
inductive EdgePattern {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
  | boundary
      (total : (word.map edgeOfDart).count a = 1)
  | positiveCrosscap
      (positive : word.count (.pos a) = 2)
      (negative : word.count (.neg a) = 0)
  | negativeCrosscap
      (positive : word.count (.pos a) = 0)
      (negative : word.count (.neg a) = 2)
  | opposite
      (positive : word.count (.pos a) = 1)
      (negative : word.count (.neg a) = 1)

/-- Every edge name actually used by a residual word still has a surface multiplicity.  Unlike
`IsSurfaceValid`, this predicate permits the ambient `Fin` type to contain already-grouped edge
names which no longer occur in the residual word. -/
def HasValidUsedMultiplicities {n : ℕ}
    (word : List (SignedDart (Fin n))) : Prop :=
  ∀ a, a ∈ word.map edgeOfDart →
    (word.map edgeOfDart).count a = 1 ∨
      (word.map edgeOfDart).count a = 2

/-- Ordinary one-face validity implies valid multiplicity for every used edge. -/
theorem hasValidUsedMultiplicities_of_isSurfaceValid {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    HasValidUsedMultiplicities word := by
  intro a _ha
  simpa only [Dyck.oneFace_edgeMultiplicity] using valid.2.2.2 a

/-- Residual surface multiplicities force the edge of a displayed inverse pair to occur nowhere
else in its tail. -/
theorem cancellablePair_edge_not_mem_tail_of_usedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word) :
    pair.edge ∉ pair.tail.map edgeOfDart := by
  have hcount :
      (word.map edgeOfDart).count pair.edge =
        2 + (pair.tail.map edgeOfDart).count pair.edge := by
    have hrotatedCount :=
      (pair.rotated.map edgeOfDart).perm.count_eq pair.edge
    rw [hrotatedCount]
    cases pair.negativeFirst <;>
      simp [inversePair, edgeOfDart] <;>
      omega
  have hedge : pair.edge ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by rw [hcount]; omega)
  have hmultiplicity := multiplicities pair.edge hedge
  intro htail
  have hpositive :
      0 < (pair.tail.map edgeOfDart).count pair.edge :=
    List.count_pos_iff.mpr htail
  omega

/-- Deleting a displayed inverse pair preserves the count of every edge which remains in the
tail. -/
theorem cancellablePair_count_tail_of_mem {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word)
    (e : Fin n)
    (he : e ∈ pair.tail.map edgeOfDart) :
    (word.map edgeOfDart).count e =
      (pair.tail.map edgeOfDart).count e := by
  have hpairAbsent :=
    cancellablePair_edge_not_mem_tail_of_usedMultiplicities
      pair multiplicities
  have hne : pair.edge ≠ e := by
    intro h
    subst e
    exact hpairAbsent he
  have hcount :=
    (pair.rotated.map edgeOfDart).perm.count_eq e
  cases hnegative : pair.negativeFirst <;>
    simp [inversePair, hnegative, hne] at hcount <;>
    exact hcount

/-- Residual surface multiplicities survive deletion of a displayed inverse pair. -/
theorem cancellablePair_hasValidUsedMultiplicities_tail {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (pair : CancellablePair word)
    (multiplicities : HasValidUsedMultiplicities word) :
    HasValidUsedMultiplicities pair.tail := by
  intro e he
  rw [← cancellablePair_count_tail_of_mem
    pair multiplicities e he]
  apply multiplicities e
  exact List.count_pos_iff.mp
    (by
      rw [cancellablePair_count_tail_of_mem
        pair multiplicities e he]
      exact List.count_pos_iff.mpr he)

/-- Certified result of repeatedly deleting adjacent inverse pairs from a residual word.  The
ambient edge type is intentionally retained: names belonging to already-extracted blocks may be
absent from both the input and output residual words. -/
structure ResidualPairReduction {n : ℕ}
    (sourceWord : List (SignedDart (Fin n))) where
  reducedWord : List (SignedDart (Fin n))
  multiplicities : HasValidUsedMultiplicities reducedWord
  reduced : IsPairReduced reducedWord
  count_eq_of_mem :
    ∀ e, e ∈ reducedWord.map edgeOfDart →
      (sourceWord.map edgeOfDart).count e =
        (reducedWord.map edgeOfDart).count e
  length_le : reducedWord.length ≤ sourceWord.length

/-- Fuel-bounded residual inverse-pair cancellation. -/
noncomputable def reduceResidualPairsFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word) :
    word.length ≤ fuel → ResidualPairReduction word := by
  classical
  intro hbound
  by_cases hpairs : Nonempty (CancellablePair word)
  · let pair := Classical.choice hpairs
    have hlength :
        word.length = 2 + pair.tail.length := by
      have hrotatedLength := pair.rotated.perm.length_eq
      cases hnegative : pair.negativeFirst
      · have hrotatedLength' :
            word.length = pair.tail.length + 1 + 1 := by
          simpa [inversePair, hnegative] using hrotatedLength
        omega
      · have hrotatedLength' :
            word.length = pair.tail.length + 1 + 1 := by
          simpa [inversePair, hnegative] using hrotatedLength
        omega
    have hfuelPositive : 0 < fuel := by
      omega
    have htailBound : pair.tail.length ≤ fuel - 1 := by
      omega
    let tailMultiplicities :=
      cancellablePair_hasValidUsedMultiplicities_tail
        pair multiplicities
    let result :=
      reduceResidualPairsFuel (fuel - 1)
        pair.tail tailMultiplicities htailBound
    exact
      { reducedWord := result.reducedWord
        multiplicities := result.multiplicities
        reduced := result.reduced
        count_eq_of_mem := by
          intro e he
          have htail :
              e ∈ pair.tail.map edgeOfDart := by
            apply List.count_pos_iff.mp
            rw [result.count_eq_of_mem e he]
            exact List.count_pos_iff.mpr he
          exact
            (cancellablePair_count_tail_of_mem
              pair multiplicities e htail).trans
              (result.count_eq_of_mem e he)
        length_le := by
          exact result.length_le.trans (by omega) }
  · exact
      { reducedWord := word
        multiplicities := multiplicities
        reduced := ⟨fun pair ↦ hpairs ⟨pair⟩⟩
        count_eq_of_mem := by
          intro _ _
          rfl
        length_le := le_refl _ }
termination_by fuel
decreasing_by
  apply Nat.sub_lt
  · exact hfuelPositive
  · omega

/-- Repeatedly delete every adjacent inverse pair from a residual word while retaining its ambient
edge namespace and the surface multiplicities of all surviving names. -/
noncomputable def reduceResidualPairs {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word) :
    ResidualPairReduction word :=
  reduceResidualPairsFuel word.length word multiplicities (le_refl _)

namespace ResidualPairReduction

/-- Every name surviving residual cancellation occurred in the input residual word. -/
theorem mem_source_of_mem {n : ℕ}
    {sourceWord : List (SignedDart (Fin n))}
    (result : ResidualPairReduction sourceWord)
    (e : Fin n)
    (he : e ∈ result.reducedWord.map edgeOfDart) :
    e ∈ sourceWord.map edgeOfDart := by
  apply List.count_pos_iff.mp
  rw [result.count_eq_of_mem e he]
  exact List.count_pos_iff.mpr he

end ResidualPairReduction

/-- A known surface multiplicity classifies the two signed counts of an edge. -/
theorem exists_edgePattern_of_multiplicity {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hmultiplicity :
      (word.map edgeOfDart).count a = 1 ∨
        (word.map edgeOfDart).count a = 2) :
    Nonempty (EdgePattern word a) := by
  rcases hmultiplicity with hone | htwo
  · exact ⟨.boundary hone⟩
  · have hsum :
        word.count (.pos a) + word.count (.neg a) = 2 := by
      rw [← count_edgeOfDart_eq_pos_add_neg]
      exact htwo
    by_cases hpositive : word.count (.pos a) = 2
    · exact ⟨.positiveCrosscap hpositive (by omega)⟩
    · by_cases hnegative : word.count (.neg a) = 2
      · exact ⟨.negativeCrosscap (by omega) hnegative⟩
      · exact ⟨.opposite (by omega) (by omega)⟩

/-- Surface validity classifies every edge as boundary, equally oriented, or oppositely
oriented. -/
theorem exists_edgePattern {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (a : Fin n) :
    Nonempty (EdgePattern word a) :=
  exists_edgePattern_of_multiplicity word a (by
    simpa only [Dyck.oneFace_edgeMultiplicity] using valid.2.2.2 a)

/-- A list in which `a` occurs exactly once can be split at that occurrence, with certified
absence on both sides. -/
theorem exists_decomposition_of_count_eq_one {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 1) :
    ∃ (negative : Bool) (left right : List (SignedDart (Fin n))),
      word = left ++ dart a negative :: right ∧
        a ∉ left.map edgeOfDart ∧
        a ∉ right.map edgeOfDart := by
  have hmem : a ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by omega)
  rcases Reduction.exists_dart_of_mem_map_edgeOfDart hmem with
    ⟨d, hdword, hdedge⟩
  rw [List.mem_iff_append] at hdword
  rcases hdword with ⟨left, right, hword⟩
  have hleftCount : (left.map edgeOfDart).count a = 0 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hdedge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    omega
  have hrightCount : (right.map edgeOfDart).count a = 0 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hdedge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    omega
  have hleft : a ∉ left.map edgeOfDart :=
    List.count_eq_zero.mp hleftCount
  have hright : a ∉ right.map edgeOfDart :=
    List.count_eq_zero.mp hrightCount
  cases d with
  | pos e =>
      change e = a at hdedge
      subst e
      exact ⟨false, left, right, hword, hleft, hright⟩
  | neg e =>
      change e = a at hdedge
      subst e
      exact ⟨true, left, right, hword, hleft, hright⟩

/-- Cyclic data exposing the two occurrences of a twice-used edge. -/
structure DoubleOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  firstNegative : Bool
  secondNegative : Bool
  between : List (SignedDart (Fin n))
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a firstNegative :: between ++
        dart a secondNegative :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- Every edge of multiplicity two in a one-face word has a certified cyclic two-occurrence
decomposition. -/
theorem exists_doubleOccurrenceForm_of_count_eq_two {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 2) :
    Nonempty (DoubleOccurrenceForm word a) := by
  have hmem : a ∈ word.map edgeOfDart :=
    List.count_pos_iff.mp (by omega)
  rcases Reduction.exists_dart_of_mem_map_edgeOfDart hmem with
    ⟨first, hfirstWord, hfirstEdge⟩
  rw [List.mem_iff_append] at hfirstWord
  rcases hfirstWord with ⟨left, right, hword⟩
  let cyclicRemainder := right ++ left
  have hcyclicCount :
      (cyclicRemainder.map edgeOfDart).count a = 1 := by
    rw [hword] at hcount
    simp only [List.map_append, List.map_cons, List.count_append,
      List.count_cons] at hcount
    rw [hfirstEdge] at hcount
    simp only [beq_self_eq_true, if_true] at hcount
    simp only [cyclicRemainder, List.map_append, List.count_append]
    omega
  rcases exists_decomposition_of_count_eq_one
      cyclicRemainder a hcyclicCount with
    ⟨secondNegative, between, remainder,
      hcyclic, hbetween, hremainder⟩
  have hrotation :
      word.IsRotated (first :: cyclicRemainder) := by
    rw [hword]
    simpa only [List.cons_append, List.append_assoc,
      cyclicRemainder] using
      (List.isRotated_append
        (l := left) (l' := first :: right))
  rw [hcyclic] at hrotation
  cases first with
  | pos e =>
      change e = a at hfirstEdge
      subst e
      exact ⟨
        { firstNegative := false
          secondNegative := secondNegative
          between := between
          remainder := remainder
          rotated := by
            simpa [dart, List.cons_append,
              List.append_assoc] using hrotation
          edge_not_mem_between := hbetween
          edge_not_mem_remainder := hremainder }⟩
  | neg e =>
      change e = a at hfirstEdge
      subst e
      exact ⟨
        { firstNegative := true
          secondNegative := secondNegative
          between := between
          remainder := remainder
          rotated := by
            simpa [dart, List.cons_append,
              List.append_assoc] using hrotation
          edge_not_mem_between := hbetween
          edge_not_mem_remainder := hremainder }⟩

/-- Surface validity supplies a double-occurrence form for every twice-used edge. -/
noncomputable def doubleOccurrenceFormOfMultiplicityTwo {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (_valid : (Dyck.oneFace word).IsSurfaceValid)
    (a : Fin n)
    (htwo : (Dyck.oneFace word).edgeMultiplicity a = 2) :
    DoubleOccurrenceForm word a :=
  Classical.choice
    (exists_doubleOccurrenceForm_of_count_eq_two word a
      (by simpa only [Dyck.oneFace_edgeMultiplicity] using htwo))

/-- In a pair-reduced word, oppositely oriented occurrences cannot be cyclically adjacent. -/
theorem DoubleOccurrenceForm.between_ne_nil_of_opposite {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : DoubleOccurrenceForm word a)
    (reduced : IsPairReduced word)
    (hopposite : form.firstNegative ≠ form.secondNegative) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  apply hreduced
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · exact (hopposite (hfirst.trans hsecond.symm)).elim
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := false
        rotated := by
          simpa [inversePair, dart, hfirst, hsecond,
            hbetween] using form.rotated }
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := true
        rotated := by
          simpa [inversePair, dart, hfirst, hsecond,
            hbetween] using form.rotated }
  · exact (hopposite (hfirst.trans hsecond.symm)).elim

/-- A twice-used edge displayed with equal orientations. -/
structure CrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  negative : Bool
  between : List (SignedDart (Fin n))
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a negative :: between ++
        dart a negative :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- An oppositely used edge displayed positive first and negative second. -/
structure OppositeOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  between : List (SignedDart (Fin n))
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (.pos a :: between ++ .neg a :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- An orientation-symmetric directed arc between the two opposite occurrences of an edge.
Unlike `OppositeOccurrenceForm`, this form permits either sign at the beginning, which is the
right induction invariant when descending to a shorter nested pair. -/
structure OppositeArcForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  firstNegative : Bool
  between : List (SignedDart (Fin n))
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (dart a firstNegative :: between ++
        dart a (!firstNegative) :: remainder)
  edge_not_mem_between : a ∉ between.map edgeOfDart
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- Forget the positive-first convention of an opposite occurrence form. -/
def OppositeOccurrenceForm.toArc {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeOccurrenceForm word a) :
    OppositeArcForm word a where
  firstNegative := false
  between := form.between
  remainder := form.remainder
  rotated := by
    simpa [dart] using form.rotated
  edge_not_mem_between := form.edge_not_mem_between
  edge_not_mem_remainder := form.edge_not_mem_remainder

/-- Pair reduction makes the directed interval of every opposite arc nonempty. -/
theorem OppositeArcForm.between_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (reduced : IsPairReduced word) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  apply hreduced
  cases horientation : form.firstNegative
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := false
        rotated := by
          simpa [inversePair, dart, horientation,
            hbetween] using form.rotated }
  · exact
      { edge := a
        tail := form.remainder
        negativeFirst := true
        rotated := by
          simpa [inversePair, dart, horientation,
            hbetween] using form.rotated }

/-- Two oppositely oriented edge pairs whose endpoints interleave cyclically.  The first
distinguished pair is displayed positive then negative.  The Boolean records whether the
occurrence of `b` inside that pair is negative; a signed relabeling will reverse `b` when
necessary before applying handle extraction. -/
structure InterleavedOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a b : Fin n) where
  bNegativeInside : Bool
  beforeB : List (SignedDart (Fin n))
  beforeNegA : List (SignedDart (Fin n))
  beforeOutsideB : List (SignedDart (Fin n))
  remainder : List (SignedDart (Fin n))
  rotated :
    word.IsRotated
      (.pos a :: beforeB ++
        dart b bNegativeInside :: beforeNegA ++
        .neg a :: beforeOutsideB ++
        dart b (!bNegativeInside) :: remainder)
  edge_ne : a ≠ b
  a_not_mem_beforeB : a ∉ beforeB.map edgeOfDart
  a_not_mem_beforeNegA : a ∉ beforeNegA.map edgeOfDart
  a_not_mem_beforeOutsideB : a ∉ beforeOutsideB.map edgeOfDart
  a_not_mem_remainder : a ∉ remainder.map edgeOfDart
  b_not_mem_beforeB : b ∉ beforeB.map edgeOfDart
  b_not_mem_beforeNegA : b ∉ beforeNegA.map edgeOfDart
  b_not_mem_beforeOutsideB : b ∉ beforeOutsideB.map edgeOfDart
  b_not_mem_remainder : b ∉ remainder.map edgeOfDart

/-- A positive crosscap edge has an equally oriented occurrence form. -/
theorem exists_positiveCrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 2)
    (hnegative : word.count (.neg a) = 0) :
    Nonempty (CrosscapOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hcount :=
    form.rotated.perm.count_eq (.neg a)
  rw [hnegative] at hcount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · exact ⟨
      { negative := false
        between := form.between
        remainder := form.remainder
        rotated := by
          simpa [dart, hfirst, hsecond] using form.rotated
        edge_not_mem_between := form.edge_not_mem_between
        edge_not_mem_remainder := form.edge_not_mem_remainder }⟩
  all_goals
    simp [dart, hfirst, hsecond] at hcount

/-- A negative crosscap edge has an equally oriented occurrence form. -/
theorem exists_negativeCrosscapOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 0)
    (hnegative : word.count (.neg a) = 2) :
    Nonempty (CrosscapOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hcount :=
    form.rotated.perm.count_eq (.pos a)
  rw [hpositive] at hcount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  all_goals try
    simp [dart, hfirst, hsecond] at hcount
  exact ⟨
    { negative := true
      between := form.between
      remainder := form.remainder
      rotated := by
        simpa [dart, hfirst, hsecond] using form.rotated
      edge_not_mem_between := form.edge_not_mem_between
      edge_not_mem_remainder := form.edge_not_mem_remainder }⟩

/-- An opposite edge has a cyclic spelling with its positive occurrence first. -/
theorem exists_oppositeOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hpositive : word.count (.pos a) = 1)
    (hnegative : word.count (.neg a) = 1) :
    Nonempty (OppositeOccurrenceForm word a) := by
  have htotal : (word.map edgeOfDart).count a = 2 := by
    rw [count_edgeOfDart_eq_pos_add_neg, hpositive, hnegative]
  rcases exists_doubleOccurrenceForm_of_count_eq_two
      word a htotal with ⟨form⟩
  have hposCount :=
    form.rotated.perm.count_eq (.pos a)
  have hnegCount :=
    form.rotated.perm.count_eq (.neg a)
  rw [hpositive] at hposCount
  rw [hnegative] at hnegCount
  cases hfirst : form.firstNegative <;>
    cases hsecond : form.secondNegative
  · simp [dart, hfirst, hsecond] at hposCount
  · exact ⟨
      { between := form.between
        remainder := form.remainder
        rotated := by
          simpa [dart, hfirst, hsecond] using form.rotated
        edge_not_mem_between := form.edge_not_mem_between
        edge_not_mem_remainder := form.edge_not_mem_remainder }⟩
  · refine ⟨
      { between := form.remainder
        remainder := form.between
        rotated := ?_
        edge_not_mem_between := form.edge_not_mem_remainder
        edge_not_mem_remainder := form.edge_not_mem_between }⟩
    have hrotateAgain :
        (dart a form.firstNegative :: form.between ++
          dart a form.secondNegative :: form.remainder).IsRotated
            (.pos a :: form.remainder ++
              .neg a :: form.between) := by
      convert
        (List.isRotated_append
          (l := .neg a :: form.between)
          (l' := .pos a :: form.remainder)) using 1
      all_goals
        simp [dart, hfirst, hsecond, List.cons_append]
    exact form.rotated.trans hrotateAgain
  · simp [dart, hfirst, hsecond] at hnegCount

/-- A once-used boundary edge displayed at the cyclic head. -/
structure BoundaryOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n) where
  negative : Bool
  remainder : List (SignedDart (Fin n))
  rotated : word.IsRotated (dart a negative :: remainder)
  edge_not_mem_remainder : a ∉ remainder.map edgeOfDart

/-- A pairing feature on which the normalization recursion can immediately act. -/
inductive ActionablePairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
  | handle (a b : Fin n) (form : InterleavedOccurrenceForm word a b)

namespace ActionablePairReductionFeature

/-- Delete the darts of the extracted block, retaining the exact residual order produced by the
proof-generating rewrite endpoint. -/
def residualWord {n : ℕ} {word : List (SignedDart (Fin n))} :
    ActionablePairReductionFeature word →
      List (SignedDart (Fin n))
  | .boundary _ form =>
      form.remainder
  | .crosscap _ form =>
      inverseWord form.remainder ++ form.between
  | .handle _ _ form =>
      form.remainder ++ form.beforeOutsideB ++
        form.beforeNegA ++ form.beforeB

/-- Every actionable extraction strictly shortens its residual word. -/
theorem residualWord_length_lt {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.residualWord.length < word.length := by
  cases feature with
  | boundary a form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_cons] at hlength ⊢
      omega
  | crosscap a form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_append,
        inverseWord_length, List.length_cons] at hlength ⊢
      omega
  | handle a b form =>
      have hlength := form.rotated.perm.length_eq
      simp only [residualWord, List.length_append,
        List.length_cons] at hlength ⊢
      omega

/-- Counts of every edge still used by the residual word agree with their counts in the source
word. -/
theorem count_residualWord_of_mem {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (e : Fin n)
    (he : e ∈ feature.residualWord.map edgeOfDart) :
    (word.map edgeOfDart).count e =
      (feature.residualWord.map edgeOfDart).count e := by
  cases feature with
  | boundary a form =>
      have hae : a ≠ e := by
        intro h
        subst e
        exact form.edge_not_mem_remainder he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons,
        edgeOfDart_dart, List.count_cons] at hcount ⊢
      simp [hae] at hcount
      exact hcount
  | crosscap a form =>
      have haResidual :
          a ∉ (inverseWord form.remainder ++
            form.between).map edgeOfDart := by
        simp [map_edgeOfDart_inverseWord,
          form.edge_not_mem_remainder,
          form.edge_not_mem_between]
      have hae : a ≠ e := by
        intro h
        subst e
        exact haResidual he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons, List.map_append,
        edgeOfDart_dart, List.count_cons,
        List.count_append] at hcount ⊢
      rw [map_edgeOfDart_inverseWord, List.count_reverse]
      simp [hae] at hcount
      omega
  | handle a b form =>
      have haResidual :
          a ∉ (form.remainder ++ form.beforeOutsideB ++
            form.beforeNegA ++ form.beforeB).map edgeOfDart := by
        simp [form.a_not_mem_remainder,
          form.a_not_mem_beforeOutsideB,
          form.a_not_mem_beforeNegA,
          form.a_not_mem_beforeB]
      have hbResidual :
          b ∉ (form.remainder ++ form.beforeOutsideB ++
            form.beforeNegA ++ form.beforeB).map edgeOfDart := by
        simp [form.b_not_mem_remainder,
          form.b_not_mem_beforeOutsideB,
          form.b_not_mem_beforeNegA,
          form.b_not_mem_beforeB]
      have hae : a ≠ e := by
        intro h
        subst e
        exact haResidual he
      have hbe : b ≠ e := by
        intro h
        subst e
        exact hbResidual he
      have hcount :=
        (form.rotated.map edgeOfDart).perm.count_eq e
      simp only [residualWord, List.map_cons, List.map_append,
        edgeOfDart_pos, edgeOfDart_neg, edgeOfDart_dart,
        List.count_cons,
        List.count_append] at hcount ⊢
      simp [hae, hbe] at hcount
      omega

/-- Used-edge surface multiplicities survive deletion of an extracted block. -/
theorem hasValidUsedMultiplicities_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (multiplicities : HasValidUsedMultiplicities word) :
    HasValidUsedMultiplicities feature.residualWord := by
  intro e he
  rw [← feature.count_residualWord_of_mem e he]
  apply multiplicities e
  exact List.count_pos_iff.mp
    (by
      rw [feature.count_residualWord_of_mem e he]
      exact List.count_pos_iff.mpr he)

end ActionablePairReductionFeature

/-- The combinatorial block contributed by one actionable extraction.  Orientations on boundary
and crosscap blocks are retained until the final signed relabeling; handle extraction has already
normalized both distinguished edge orientations. -/
inductive ExtractedBlock (n : ℕ)
  | boundary (a : Fin n) (negative : Bool)
  | crosscap (a : Fin n) (negative : Bool)
  | handle (a b : Fin n)

namespace ExtractedBlock

/-- Ambient edge names consumed by an extracted block. -/
def edges {n : ℕ} : ExtractedBlock n → List (Fin n)
  | .boundary a _ => [a]
  | .crosscap a _ => [a]
  | .handle a b => [a, b]

/-- Exact signed word contributed by an extracted block. -/
def word {n : ℕ} : ExtractedBlock n →
    List (SignedDart (Fin n))
  | .boundary a negative => [dart a negative]
  | .crosscap a negative =>
      [dart a negative, dart a negative]
  | .handle a b =>
      [.pos a, .pos b, .neg a, .neg b]

/-- Block obtained by reading an extracted block backwards with every dart reversed. -/
def inverse {n : ℕ} : ExtractedBlock n → ExtractedBlock n
  | .boundary a negative => .boundary a (!negative)
  | .crosscap a negative => .crosscap a (!negative)
  | .handle a b => .handle b a

/-- Relabel every ambient edge name in an extracted block. -/
def mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    ExtractedBlock n → ExtractedBlock m
  | .boundary a negative => .boundary (e a) negative
  | .crosscap a negative => .crosscap (e a) negative
  | .handle a b => .handle (e a) (e b)

@[simp]
theorem word_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.word = inverseWord block.word := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle a b =>
      rfl

@[simp]
theorem inverse_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.inverse = block := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle a b =>
      rfl

@[simp]
theorem edges_inverse {n : ℕ} (block : ExtractedBlock n) :
    block.inverse.edges = block.edges.reverse := by
  cases block <;> rfl

@[simp]
theorem word_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).word =
      block.word.map (SignedDart.mapEquiv e) := by
  cases block with
  | boundary a negative =>
      cases negative <;> rfl
  | crosscap a negative =>
      cases negative <;> rfl
  | handle =>
      rfl

@[simp]
theorem edges_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).edges = block.edges.map e := by
  cases block <;> rfl

@[simp]
theorem mem_map_edgeOfDart_word_iff {n : ℕ}
    (block : ExtractedBlock n) (a : Fin n) :
    a ∈ block.word.map edgeOfDart ↔ a ∈ block.edges := by
  cases block with
  | boundary edge negative =>
      cases negative <;> simp [word, edges]
  | crosscap edge negative =>
      cases negative <;> simp [word, edges]
  | handle first second =>
      simp [word, edges]
      tauto

@[simp]
theorem inverse_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (block : ExtractedBlock n) :
    (block.mapEquiv e).inverse =
      block.inverse.mapEquiv e := by
  cases block <;> rfl

/-- Concatenate a sequence of extracted blocks into its exact signed boundary word. -/
def sequenceWord {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (SignedDart (Fin n)) :=
  (blocks.map word).flatten

/-- Reverse a block sequence in the order induced by reversing its full signed word. -/
def inverseSequence {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (ExtractedBlock n) :=
  (blocks.map inverse).reverse

@[simp]
theorem sequenceWord_nil {n : ℕ} :
    sequenceWord ([] : List (ExtractedBlock n)) = [] :=
  rfl

@[simp]
theorem sequenceWord_cons {n : ℕ}
    (block : ExtractedBlock n)
    (blocks : List (ExtractedBlock n)) :
    sequenceWord (block :: blocks) =
      block.word ++ sequenceWord blocks := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_append {n : ℕ}
    (left right : List (ExtractedBlock n)) :
    sequenceWord (left ++ right) =
      sequenceWord left ++ sequenceWord right := by
  simp [sequenceWord]

@[simp]
theorem sequenceWord_inverseSequence {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    sequenceWord (inverseSequence blocks) =
      inverseWord (sequenceWord blocks) := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      have ih' :
          sequenceWord ((blocks.map inverse).reverse) =
            inverseWord (sequenceWord blocks) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

end ExtractedBlock

/-- A marked normalization word.  Residual darts are still available to subsequent pairing
reductions; extracted blocks are atomic tokens whose exact dart succession must be preserved. -/
inductive ReductionToken (n : ℕ)
  | residual (dart : SignedDart (Fin n))
  | extracted (block : ExtractedBlock n)

namespace ReductionToken

/-- Exact signed word represented by one marked token. -/
def word {n : ℕ} : ReductionToken n →
    List (SignedDart (Fin n))
  | .residual dart => [dart]
  | .extracted block => block.word

/-- Residual contribution of one marked token. -/
def residualWord {n : ℕ} : ReductionToken n →
    List (SignedDart (Fin n))
  | .residual dart => [dart]
  | .extracted _ => []

/-- Edge names protected inside one extracted-block token. -/
def extractedEdges {n : ℕ} : ReductionToken n → List (Fin n)
  | .residual _ => []
  | .extracted block => block.edges

@[simp]
theorem word_residual {n : ℕ} (dart : SignedDart (Fin n)) :
    word (.residual dart) = [dart] :=
  rfl

@[simp]
theorem word_extracted {n : ℕ} (block : ExtractedBlock n) :
    word (.extracted block) = block.word :=
  rfl

@[simp]
theorem residualWord_residual {n : ℕ}
    (dart : SignedDart (Fin n)) :
    residualWord (.residual dart) = [dart] :=
  rfl

@[simp]
theorem residualWord_extracted {n : ℕ}
    (block : ExtractedBlock n) :
    residualWord (.extracted block) = [] :=
  rfl

@[simp]
theorem extractedEdges_residual {n : ℕ}
    (dart : SignedDart (Fin n)) :
    extractedEdges (.residual dart) = [] :=
  rfl

@[simp]
theorem extractedEdges_extracted {n : ℕ}
    (block : ExtractedBlock n) :
    extractedEdges (.extracted block) = block.edges :=
  rfl

/-- Reverse a token while preserving an extracted block as one atomic token. -/
def inverse {n : ℕ} : ReductionToken n → ReductionToken n
  | .residual dart => .residual dart.flip
  | .extracted block => .extracted block.inverse

/-- Relabel every edge name represented by a marked token. -/
def mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    ReductionToken n → ReductionToken m
  | .residual dart => .residual (SignedDart.mapEquiv e dart)
  | .extracted block => .extracted (block.mapEquiv e)

@[simp]
theorem word_inverse {n : ℕ} (token : ReductionToken n) :
    token.inverse.word = inverseWord token.word := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      exact ExtractedBlock.word_inverse block

@[simp]
theorem residualWord_inverse {n : ℕ}
    (token : ReductionToken n) :
    token.inverse.residualWord =
      inverseWord token.residualWord := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted =>
      rfl

@[simp]
theorem inverse_inverse {n : ℕ} (token : ReductionToken n) :
    token.inverse.inverse = token := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      simp [inverse]

@[simp]
theorem word_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (token : ReductionToken n) :
    (token.mapEquiv e).word =
      token.word.map (SignedDart.mapEquiv e) := by
  cases token with
  | residual =>
      rfl
  | extracted block =>
      exact ExtractedBlock.word_mapEquiv e block

@[simp]
theorem residualWord_mapEquiv {n m : ℕ}
    (e : Fin n ≃ Fin m) (token : ReductionToken n) :
    (token.mapEquiv e).residualWord =
      token.residualWord.map (SignedDart.mapEquiv e) := by
  cases token <;> rfl

@[simp]
theorem inverse_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (token : ReductionToken n) :
    (token.mapEquiv e).inverse =
      token.inverse.mapEquiv e := by
  cases token with
  | residual dart =>
      cases dart <;> rfl
  | extracted block =>
      simp [inverse, mapEquiv]

/-- Expand a marked word to the exact signed word on which normalization moves act. -/
def expand {n : ℕ} (tokens : List (ReductionToken n)) :
    List (SignedDart (Fin n)) :=
  (tokens.map word).flatten

/-- Erase extracted blocks and retain only the darts still available to pairing reduction. -/
def residualDarts {n : ℕ} (tokens : List (ReductionToken n)) :
    List (SignedDart (Fin n)) :=
  (tokens.map residualWord).flatten

/-- All edge names protected inside extracted block tokens. -/
def protectedEdges {n : ℕ} (tokens : List (ReductionToken n)) :
    List (Fin n) :=
  (tokens.map extractedEdges).flatten

/-- Reverse a marked word at token granularity. -/
def inverseSequence {n : ℕ} (tokens : List (ReductionToken n)) :
    List (ReductionToken n) :=
  (tokens.map inverse).reverse

/-- Initially every dart is still residual. -/
def ofWord {n : ℕ} (word : List (SignedDart (Fin n))) :
    List (ReductionToken n) :=
  word.map .residual

/-- A finished marked word contains only extracted block tokens. -/
def ofBlocks {n : ℕ} (blocks : List (ExtractedBlock n)) :
    List (ReductionToken n) :=
  blocks.map .extracted

@[simp]
theorem expand_nil {n : ℕ} :
    expand ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem expand_cons {n : ℕ} (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    expand (token :: tokens) =
      token.word ++ expand tokens := by
  simp [expand]

@[simp]
theorem expand_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    expand (left ++ right) = expand left ++ expand right := by
  simp [expand]

@[simp]
theorem residualDarts_nil {n : ℕ} :
    residualDarts ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem residualDarts_cons {n : ℕ} (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    residualDarts (token :: tokens) =
      token.residualWord ++ residualDarts tokens := by
  simp [residualDarts]

@[simp]
theorem residualDarts_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    residualDarts (left ++ right) =
      residualDarts left ++ residualDarts right := by
  simp [residualDarts]

@[simp]
theorem protectedEdges_nil {n : ℕ} :
    protectedEdges ([] : List (ReductionToken n)) = [] :=
  rfl

@[simp]
theorem protectedEdges_cons {n : ℕ}
    (token : ReductionToken n)
    (tokens : List (ReductionToken n)) :
    protectedEdges (token :: tokens) =
      token.extractedEdges ++ protectedEdges tokens := by
  simp [protectedEdges]

@[simp]
theorem protectedEdges_append {n : ℕ}
    (left right : List (ReductionToken n)) :
    protectedEdges (left ++ right) =
      protectedEdges left ++ protectedEdges right := by
  simp [protectedEdges]

/-- An edge occurs in the expanded word exactly when it is residual or protected in an extracted
block token. -/
theorem mem_map_edgeOfDart_expand_iff {n : ℕ}
    (tokens : List (ReductionToken n)) (a : Fin n) :
    a ∈ (expand tokens).map edgeOfDart ↔
      a ∈ (residualDarts tokens).map edgeOfDart ∨
        a ∈ protectedEdges tokens := by
  induction tokens with
  | nil =>
      simp
  | cons token tokens ih =>
      cases token with
      | residual dart =>
          simp only [expand_cons, word_residual,
            residualDarts_cons, residualWord_residual,
            protectedEdges_cons, extractedEdges_residual,
            List.nil_append, List.map_append, List.map_cons,
            List.map_nil, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false]
          rw [ih]
          tauto
      | extracted block =>
          simp only [expand_cons, word_extracted,
            residualDarts_cons, residualWord_extracted,
            protectedEdges_cons, extractedEdges_extracted,
            List.nil_append, List.map_append,
            List.mem_append]
          rw [ExtractedBlock.mem_map_edgeOfDart_word_iff,
            ih]
          tauto

/-- Flattening preserves a cyclic rotation of a list of lists. -/
theorem isRotated_flatten {α : Type*}
    {lists target : List (List α)}
    (hrotated : lists.IsRotated target) :
    lists.flatten.IsRotated target.flatten := by
  rcases hrotated with ⟨steps, hsteps⟩
  let cut := steps % lists.length
  let left := lists.take cut
  let right := lists.drop cut
  have hlists : lists = left ++ right :=
    (List.take_append_drop cut lists).symm
  have htarget : target = right ++ left := by
    rw [← hsteps, List.rotate_eq_drop_append_take_mod]
  rw [hlists, htarget, List.flatten_append,
    List.flatten_append]
  exact List.isRotated_append

/-- Expanding atomic marked tokens preserves cyclic rotation. -/
theorem expand_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    (expand tokens).IsRotated (expand target) := by
  exact isRotated_flatten (hrotated.map word)

/-- Protected edge names rotate with their atomic marked tokens. -/
theorem protectedEdges_isRotated {n : ℕ}
    {tokens target : List (ReductionToken n)}
    (hrotated : tokens.IsRotated target) :
    (protectedEdges tokens).IsRotated
      (protectedEdges target) := by
  exact isRotated_flatten (hrotated.map extractedEdges)

@[simp]
theorem expand_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    expand (ofWord word) = word := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        expand (.residual dart :: ofWord word) =
          dart :: word
      rw [expand_cons, word_residual, ih]
      rfl

@[simp]
theorem residualDarts_ofWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    residualDarts (ofWord word) = word := by
  induction word with
  | nil =>
      rfl
  | cons dart word ih =>
      change
        residualDarts (.residual dart :: ofWord word) =
          dart :: word
      rw [residualDarts_cons, residualWord_residual, ih]
      rfl

@[simp]
theorem expand_ofBlocks {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    expand (ofBlocks blocks) =
      ExtractedBlock.sequenceWord blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      change
        expand (.extracted block :: ofBlocks blocks) =
          ExtractedBlock.sequenceWord (block :: blocks)
      rw [expand_cons, word_extracted, ih,
        ExtractedBlock.sequenceWord_cons]

@[simp]
theorem residualDarts_ofBlocks {n : ℕ}
    (blocks : List (ExtractedBlock n)) :
    residualDarts (ofBlocks blocks) = [] := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      change
        residualDarts (.extracted block :: ofBlocks blocks) = []
      rw [residualDarts_cons, residualWord_extracted, ih,
        List.nil_append]

/-- Lift a displayed residual dart occurrence to an exact split of the marked token list. -/
theorem exists_split_of_residualDarts_eq_append_cons {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n))
    (hresidual :
      residualDarts tokens = left ++ dart :: right) :
    ∃ tokenLeft tokenRight,
      tokens = tokenLeft ++ .residual dart :: tokenRight ∧
        residualDarts tokenLeft = left ∧
        residualDarts tokenRight = right := by
  induction tokens generalizing left with
  | nil =>
      simp at hresidual
  | cons token tokens ih =>
      cases token with
      | extracted block =>
          simp only [residualDarts_cons, residualWord,
            List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.extracted block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons, residualWord,
                  List.nil_append]
                exact hleft,
              hright⟩
      | residual first =>
          cases left with
          | nil =>
              simp only [residualDarts_cons, residualWord,
                List.singleton_append, List.nil_append,
                List.cons.injEq] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              exact ⟨[], tokens, rfl, rfl, htail⟩
          | cons head left =>
              simp only [residualDarts_cons, residualWord,
                List.cons_append, List.cons.injEq,
                List.nil_append] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              rcases ih left htail with
                ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
              exact
                ⟨.residual first :: tokenLeft, tokenRight,
                  by simp [htokens], by simp [hleft], hright⟩

/-- Lift an arbitrary residual-word cut to a cut of the marked token list. -/
theorem exists_split_of_residualDarts_eq_append {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (hresidual : residualDarts tokens = left ++ right) :
    ∃ tokenLeft tokenRight,
      tokens = tokenLeft ++ tokenRight ∧
        residualDarts tokenLeft = left ∧
        residualDarts tokenRight = right := by
  induction tokens generalizing left with
  | nil =>
      have happend : left ++ right = [] := hresidual.symm
      have hparts : left = [] ∧ right = [] := by
        simpa using happend
      rcases hparts with ⟨hleft, hright⟩
      subst left
      subst right
      exact ⟨[], [], rfl, rfl, rfl⟩
  | cons token tokens ih =>
      cases token with
      | extracted block =>
          simp only [residualDarts_cons,
            residualWord_extracted, List.nil_append] at hresidual
          rcases ih left hresidual with
            ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
          exact
            ⟨.extracted block :: tokenLeft, tokenRight,
              by simp [htokens],
              by
                simp only [residualDarts_cons,
                  residualWord_extracted, List.nil_append]
                exact hleft,
              hright⟩
      | residual first =>
          cases left with
          | nil =>
              exact
                ⟨[], .residual first :: tokens, rfl, rfl,
                  by simpa using hresidual⟩
          | cons head left =>
              simp only [residualDarts_cons,
                residualWord_residual,
                List.cons_append, List.cons.injEq] at hresidual
              rcases hresidual with ⟨rfl, htail⟩
              rcases ih left htail with
                ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
              exact
                ⟨.residual first :: tokenLeft, tokenRight,
                  by simp [htokens],
                  by simp [hleft],
                  hright⟩

/-- Every cyclic rotation of the residual darts is induced by a cyclic rotation of the marked
tokens. -/
theorem exists_isRotated_of_residualDarts_isRotated {n : ℕ}
    (tokens : List (ReductionToken n))
    {target : List (SignedDart (Fin n))}
    (hrotated : (residualDarts tokens).IsRotated target) :
    ∃ rotatedTokens,
      tokens.IsRotated rotatedTokens ∧
        residualDarts rotatedTokens = target := by
  rcases hrotated with ⟨steps, hsteps⟩
  let cut := steps % (residualDarts tokens).length
  let left := (residualDarts tokens).take cut
  let right := (residualDarts tokens).drop cut
  have hsource :
      residualDarts tokens = left ++ right := by
    exact (List.take_append_drop cut
      (residualDarts tokens)).symm
  have htarget :
      target = right ++ left := by
    rw [← hsteps, List.rotate_eq_drop_append_take_mod]
  rcases exists_split_of_residualDarts_eq_append
      tokens left right hsource with
    ⟨tokenLeft, tokenRight, htokens, hleft, hright⟩
  refine ⟨tokenRight ++ tokenLeft, ?_, ?_⟩
  · rw [htokens]
    exact List.isRotated_append
  · rw [residualDarts_append, hright, hleft, ← htarget]

/-- Lift a residual rotation which displays one dart at its head to a marked-token rotation with
that exact residual token at its head. -/
theorem exists_isRotated_residual_cons {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n)))
    (hrotated :
      (residualDarts tokens).IsRotated (dart :: remainder)) :
    ∃ tokenRemainder,
      tokens.IsRotated
        (.residual dart :: tokenRemainder) ∧
      residualDarts tokenRemainder = remainder := by
  rcases exists_isRotated_of_residualDarts_isRotated
      tokens hrotated with
    ⟨rotatedTokens, htokens, hresidual⟩
  have hdisplay :
      residualDarts rotatedTokens =
        [] ++ dart :: remainder := by
    simpa using hresidual
  rcases exists_split_of_residualDarts_eq_append_cons
      rotatedTokens [] remainder dart hdisplay with
    ⟨tokenLeft, tokenRight, hsplit, hleft, hright⟩
  refine ⟨tokenRight ++ tokenLeft, ?_, ?_⟩
  · apply htokens.trans
    rw [hsplit]
    simpa only [List.nil_append, List.cons_append] using
      (List.isRotated_append
        (l := tokenLeft)
        (l' := .residual dart :: tokenRight))
  · rw [residualDarts_append, hright, hleft]
    simp

/-- Type-valued packaging of a marked split, suitable for recursive normalization data. -/
structure ResidualSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n))) where
  tokenLeft : List (ReductionToken n)
  tokenRight : List (ReductionToken n)
  tokens_eq : tokens = tokenLeft ++ tokenRight
  residual_left : residualDarts tokenLeft = left
  residual_right : residualDarts tokenRight = right

/-- Type-valued packaging of a marked split at one displayed residual dart. -/
structure ResidualDartSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n)) where
  tokenLeft : List (ReductionToken n)
  tokenRight : List (ReductionToken n)
  tokens_eq :
    tokens = tokenLeft ++ .residual dart :: tokenRight
  residual_left : residualDarts tokenLeft = left
  residual_right : residualDarts tokenRight = right

/-- Choose a marked split above a displayed residual-word split. -/
noncomputable def residualSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (hresidual : residualDarts tokens = left ++ right) :
    ResidualSplit tokens left right := by
  let witness :=
    exists_split_of_residualDarts_eq_append
      tokens left right hresidual
  let tokenLeft := Classical.choose witness
  let rightWitness := Classical.choose_spec witness
  let tokenRight := Classical.choose rightWitness
  let properties := Classical.choose_spec rightWitness
  exact
    { tokenLeft := tokenLeft
      tokenRight := tokenRight
      tokens_eq := properties.1
      residual_left := properties.2.1
      residual_right := properties.2.2 }

/-- Choose a marked split at a displayed residual dart. -/
noncomputable def residualDartSplit {n : ℕ}
    (tokens : List (ReductionToken n))
    (left right : List (SignedDart (Fin n)))
    (dart : SignedDart (Fin n))
    (hresidual :
      residualDarts tokens = left ++ dart :: right) :
    ResidualDartSplit tokens left right dart := by
  let witness :=
    exists_split_of_residualDarts_eq_append_cons
      tokens left right dart hresidual
  let tokenLeft := Classical.choose witness
  let rightWitness := Classical.choose_spec witness
  let tokenRight := Classical.choose rightWitness
  let properties := Classical.choose_spec rightWitness
  exact
    { tokenLeft := tokenLeft
      tokenRight := tokenRight
      tokens_eq := properties.1
      residual_left := properties.2.1
      residual_right := properties.2.2 }

/-- Type-valued packaging of a marked rotation with one residual dart at its head. -/
structure ResidualConsRotation {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n))) where
  tokenRemainder : List (ReductionToken n)
  rotated :
    tokens.IsRotated (.residual dart :: tokenRemainder)
  residual_remainder :
    residualDarts tokenRemainder = remainder

/-- Choose the marked rotation above a residual rotation with one displayed head dart. -/
noncomputable def residualConsRotation {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n)))
    (hrotated :
      (residualDarts tokens).IsRotated (dart :: remainder)) :
    ResidualConsRotation tokens dart remainder := by
  let witness :=
    exists_isRotated_residual_cons
      tokens dart remainder hrotated
  let tokenRemainder := Classical.choose witness
  let properties := Classical.choose_spec witness
  exact
    { tokenRemainder := tokenRemainder
      rotated := properties.1
      residual_remainder := properties.2 }

@[simp]
theorem expand_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    expand (inverseSequence tokens) =
      inverseWord (expand tokens) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have ih' :
          expand ((tokens.map inverse).reverse) =
            inverseWord (expand tokens) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

@[simp]
theorem residualDarts_inverseSequence {n : ℕ}
    (tokens : List (ReductionToken n)) :
    residualDarts (inverseSequence tokens) =
      inverseWord (residualDarts tokens) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      have ih' :
          residualDarts ((tokens.map inverse).reverse) =
            inverseWord (residualDarts tokens) := by
        simpa only [inverseSequence] using ih
      simp [inverseSequence, inverseWord_append, ih']

@[simp]
theorem expand_mapEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (tokens : List (ReductionToken n)) :
    expand (tokens.map (mapEquiv e)) =
      (expand tokens).map (SignedDart.mapEquiv e) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      simp [ih]

@[simp]
theorem residualDarts_mapEquiv {n m : ℕ}
    (e : Fin n ≃ Fin m)
    (tokens : List (ReductionToken n)) :
    residualDarts (tokens.map (mapEquiv e)) =
      (residualDarts tokens).map (SignedDart.mapEquiv e) := by
  induction tokens with
  | nil =>
      rfl
  | cons token tokens ih =>
      simp [ih]

end ReductionToken

/-- Forget an actionable feature's occurrence decomposition while retaining its extracted block. -/
def ActionablePairReductionFeature.block {n : ℕ}
    {word : List (SignedDart (Fin n))} :
    ActionablePairReductionFeature word → ExtractedBlock n
  | .boundary a form => .boundary a form.negative
  | .crosscap a form => .crosscap a form.negative
  | .handle a b _ => .handle a b

namespace ActionablePairReductionFeature

/-- The edge names consumed by an actionable extraction. -/
def extractedEdges {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    List (Fin n) :=
  feature.block.edges

/-- The edge names inside one extracted block are distinct. -/
theorem extractedEdges_nodup {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.extractedEdges.Nodup := by
  cases feature with
  | boundary => simp [extractedEdges, block, ExtractedBlock.edges]
  | crosscap => simp [extractedEdges, block, ExtractedBlock.edges]
  | handle a b form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        form.edge_ne]

/-- No edge consumed by a feature remains in its residual word. -/
theorem extractedEdges_disjoint_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.extractedEdges.Disjoint
      (feature.residualWord.map edgeOfDart) := by
  cases feature with
  | boundary a form =>
      simpa [extractedEdges, block, ExtractedBlock.edges,
        residualWord] using form.edge_not_mem_remainder
  | crosscap a form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        residualWord, map_edgeOfDart_inverseWord,
        form.edge_not_mem_remainder,
        form.edge_not_mem_between]
  | handle a b form =>
      simp [extractedEdges, block, ExtractedBlock.edges,
        residualWord, form.a_not_mem_remainder,
        form.a_not_mem_beforeOutsideB,
        form.a_not_mem_beforeNegA,
        form.a_not_mem_beforeB,
        form.b_not_mem_remainder,
        form.b_not_mem_beforeOutsideB,
        form.b_not_mem_beforeNegA,
        form.b_not_mem_beforeB]

/-- Every name consumed by a feature occurs in its source word. -/
theorem extractedEdges_subset_source {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    ∀ e ∈ feature.extractedEdges, e ∈ word.map edgeOfDart := by
  intro e he
  cases feature with
  | boundary a form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp only [extractedEdges, block, ExtractedBlock.edges,
        List.mem_singleton] at he
      subst e
      simp
  | crosscap a form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp only [extractedEdges, block, ExtractedBlock.edges,
        List.mem_singleton] at he
      subst e
      simp
  | handle a b form =>
      have hperm := (form.rotated.map edgeOfDart).perm
      rw [hperm.mem_iff]
      simp [extractedEdges, block, ExtractedBlock.edges] at he
      rcases he with rfl | rfl <;> simp

end ActionablePairReductionFeature

/-- An actionable residual feature lifted to a marked word.  Extracted blocks occupy whole token
segments between the distinguished residual darts, so later rewrites can reorder or reverse those
segments without splitting a protected block. -/
inductive MarkedActionablePairReductionFeature {n : ℕ}
    (tokens : List (ReductionToken n))
  | boundary (a : Fin n)
      (form :
        BoundaryOccurrenceForm
          (ReductionToken.residualDarts tokens) a)
      (remainderTokens : List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (dart a form.negative) ::
            remainderTokens))
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)
  | crosscap (a : Fin n)
      (form :
        CrosscapOccurrenceForm
          (ReductionToken.residualDarts tokens) a)
      (betweenTokens remainderTokens :
        List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (dart a form.negative) ::
            betweenTokens ++
            .residual (dart a form.negative) ::
            remainderTokens))
      (residual_between :
        ReductionToken.residualDarts betweenTokens =
          form.between)
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)
  | handle (a b : Fin n)
      (form :
        InterleavedOccurrenceForm
          (ReductionToken.residualDarts tokens) a b)
      (beforeBTokens beforeNegATokens
        beforeOutsideBTokens remainderTokens :
        List (ReductionToken n))
      (rotated :
        tokens.IsRotated
          (.residual (.pos a) ::
            beforeBTokens ++
            .residual (dart b form.bNegativeInside) ::
            beforeNegATokens ++
            .residual (.neg a) ::
            beforeOutsideBTokens ++
            .residual (dart b (!form.bNegativeInside)) ::
            remainderTokens))
      (residual_beforeB :
        ReductionToken.residualDarts beforeBTokens =
          form.beforeB)
      (residual_beforeNegA :
        ReductionToken.residualDarts beforeNegATokens =
          form.beforeNegA)
      (residual_beforeOutsideB :
        ReductionToken.residualDarts beforeOutsideBTokens =
          form.beforeOutsideB)
      (residual_remainder :
        ReductionToken.residualDarts remainderTokens =
          form.remainder)

namespace MarkedActionablePairReductionFeature

/-- Residual feature underlying a marked feature. -/
def residualFeature {n : ℕ}
    {tokens : List (ReductionToken n)} :
    MarkedActionablePairReductionFeature tokens →
      ActionablePairReductionFeature
        (ReductionToken.residualDarts tokens)
  | .boundary a form _ _ _ => .boundary a form
  | .crosscap a form _ _ _ _ _ => .crosscap a form
  | .handle a b form _ _ _ _ _ _ _ _ _ =>
      .handle a b form

/-- Marked target: replace the distinguished residual darts by one atomic extracted block while
performing the same segment reversal/reordering as the local Gallier--Xu rewrite. -/
def targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)} :
    MarkedActionablePairReductionFeature tokens →
      List (ReductionToken n)
  | marked@(.boundary _ _ remainderTokens _ _) =>
      .extracted marked.residualFeature.block ::
        remainderTokens
  | marked@(.crosscap _ _ betweenTokens
      remainderTokens _ _ _) =>
      .extracted marked.residualFeature.block ::
        ReductionToken.inverseSequence remainderTokens ++
        betweenTokens
  | marked@(.handle _ _ _ beforeBTokens
      beforeNegATokens beforeOutsideBTokens
      remainderTokens _ _ _ _ _) =>
      .extracted marked.residualFeature.block ::
        remainderTokens ++ beforeOutsideBTokens ++
        beforeNegATokens ++ beforeBTokens

/-- Lift an actionable feature of the erased residual word to the marked token word. -/
noncomputable def lift {n : ℕ}
    {tokens : List (ReductionToken n)}
    (feature :
      ActionablePairReductionFeature
        (ReductionToken.residualDarts tokens)) :
    MarkedActionablePairReductionFeature tokens := by
  cases feature with
  | boundary a form =>
      let lifted :=
        ReductionToken.residualConsRotation
          tokens (dart a form.negative) form.remainder
          form.rotated
      exact .boundary a form lifted.tokenRemainder
        lifted.rotated lifted.residual_remainder
  | crosscap a form =>
      have hhead :
          (ReductionToken.residualDarts tokens).IsRotated
            (dart a form.negative ::
              (form.between ++
                dart a form.negative :: form.remainder)) := by
        simpa only [List.cons_append,
          List.append_assoc] using form.rotated
      let headLift :=
        ReductionToken.residualConsRotation
          tokens (dart a form.negative)
          (form.between ++
            dart a form.negative :: form.remainder)
          hhead
      let split :=
        ReductionToken.residualDartSplit
          headLift.tokenRemainder form.between
          form.remainder (dart a form.negative)
          headLift.residual_remainder
      have hrotated' :
          tokens.IsRotated
            (.residual (dart a form.negative) ::
              split.tokenLeft ++
              .residual (dart a form.negative) ::
              split.tokenRight) := by
        have hrotated := headLift.rotated
        rw [split.tokens_eq] at hrotated
        simpa only [List.cons_append,
          List.append_assoc] using hrotated
      exact .crosscap a form split.tokenLeft
        split.tokenRight hrotated'
        split.residual_left split.residual_right
  | handle a b form =>
      have hhead :
          (ReductionToken.residualDarts tokens).IsRotated
            (.pos a ::
              (form.beforeB ++
                dart b form.bNegativeInside ::
                form.beforeNegA ++
                .neg a ::
                form.beforeOutsideB ++
                dart b (!form.bNegativeInside) ::
                form.remainder)) := by
        simpa only [List.cons_append,
          List.append_assoc] using form.rotated
      let headLift :=
        ReductionToken.residualConsRotation
          tokens (.pos a)
          (form.beforeB ++
            dart b form.bNegativeInside ::
            form.beforeNegA ++
            .neg a ::
            form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          hhead
      let splitB :=
        ReductionToken.residualDartSplit
          headLift.tokenRemainder form.beforeB
          (form.beforeNegA ++
            .neg a ::
            form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          (dart b form.bNegativeInside)
          (by
            simpa only [List.cons_append,
              List.append_assoc] using
              headLift.residual_remainder)
      let splitNegA :=
        ReductionToken.residualDartSplit
          splitB.tokenRight form.beforeNegA
          (form.beforeOutsideB ++
            dart b (!form.bNegativeInside) ::
            form.remainder)
          (.neg a)
          (by
            simpa only [List.cons_append,
              List.append_assoc] using
              splitB.residual_right)
      let splitOutsideB :=
        ReductionToken.residualDartSplit
          splitNegA.tokenRight form.beforeOutsideB
          form.remainder
          (dart b (!form.bNegativeInside))
          splitNegA.residual_right
      have hrotated' :
          tokens.IsRotated
            (.residual (.pos a) ::
              splitB.tokenLeft ++
              .residual (dart b form.bNegativeInside) ::
              splitNegA.tokenLeft ++
              .residual (.neg a) ::
              splitOutsideB.tokenLeft ++
              .residual (dart b (!form.bNegativeInside)) ::
              splitOutsideB.tokenRight) := by
        have hrotated := headLift.rotated
        rw [splitB.tokens_eq, splitNegA.tokens_eq,
          splitOutsideB.tokens_eq] at hrotated
        simpa only [List.cons_append,
          List.append_assoc] using hrotated
      exact .handle a b form splitB.tokenLeft
        splitNegA.tokenLeft splitOutsideB.tokenLeft
        splitOutsideB.tokenRight hrotated'
        splitB.residual_left splitNegA.residual_left
        splitOutsideB.residual_left
        splitOutsideB.residual_right

/-- Erasing the marked target recovers exactly the residual word of the underlying feature. -/
theorem residualDarts_targetTokens {n : ℕ}
    {tokens : List (ReductionToken n)}
    (marked : MarkedActionablePairReductionFeature tokens) :
    ReductionToken.residualDarts marked.targetTokens =
      marked.residualFeature.residualWord := by
  cases marked with
  | boundary a form remainderTokens _ hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hremainder]
  | crosscap a form betweenTokens remainderTokens
      _ hbetween hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hbetween, hremainder]
  | handle a b form beforeBTokens beforeNegATokens
      beforeOutsideBTokens remainderTokens _
      hbeforeB hbeforeNegA hbeforeOutsideB hremainder =>
      simp [targetTokens, residualFeature,
        ActionablePairReductionFeature.residualWord,
        hbeforeB, hbeforeNegA, hbeforeOutsideB,
        hremainder, List.append_assoc]

end MarkedActionablePairReductionFeature

/-- A complete proof-relevant decomposition trace.  Each step extracts one certified block, then
pair-reduces the strictly shorter residual before continuing. -/
inductive ResidualDecomposition {n : ℕ} :
    List (SignedDart (Fin n)) → Type
  | done : ResidualDecomposition []
  | step {word : List (SignedDart (Fin n))}
      (feature : ActionablePairReductionFeature word)
      (reduction : ResidualPairReduction feature.residualWord)
      (tail : ResidualDecomposition reduction.reducedWord) :
      ResidualDecomposition word

namespace ResidualDecomposition

/-- Extracted blocks, in recursive extraction order. -/
def blocks {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → List (ExtractedBlock n)
  | .done => []
  | .step feature _ tail => feature.block :: tail.blocks

/-- Edge names consumed by all blocks in extraction order. -/
def extractedEdges {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → List (Fin n)
  | .done => []
  | .step feature _ tail =>
      feature.extractedEdges ++ tail.extractedEdges

/-- Number of boundary singleton blocks in a decomposition. -/
def boundaryCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .boundary _ _ => 1
        | _ => 0) + tail.boundaryCount

/-- Number of crosscap square blocks in a decomposition. -/
def crosscapCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .crosscap _ _ => 1
        | _ => 0) + tail.crosscapCount

/-- Number of handle blocks in a decomposition. -/
def handleCount {n : ℕ} {word : List (SignedDart (Fin n))} :
    ResidualDecomposition word → ℕ
  | .done => 0
  | .step feature _ tail =>
      (match feature.block with
        | .handle _ _ => 1
        | _ => 0) + tail.handleCount

/-- The normal-form parameters selected by a complete block decomposition.  In the presence of
any crosscap, each handle contributes two additional crosscaps via Gallier--Xu Step 5. -/
def normalForm {n : ℕ} {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) : NormalForm :=
  if decomposition.crosscapCount = 0 then
    .orientable decomposition.handleCount
      decomposition.boundaryCount
  else
    .nonOrientable
      (decomposition.crosscapCount +
        2 * decomposition.handleCount)
      decomposition.boundaryCount

/-- Every extracted block belongs to exactly one of the three block classes. -/
theorem count_sum_eq_blocks_length {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) :
    decomposition.boundaryCount +
        decomposition.crosscapCount +
        decomposition.handleCount =
      decomposition.blocks.length := by
  induction decomposition with
  | done =>
      rfl
  | step feature reduction tail ih =>
      cases feature <;>
        simp only [boundaryCount, crosscapCount, handleCount,
          blocks, ActionablePairReductionFeature.block,
          List.length_cons] at ih ⊢ <;>
        omega

/-- A decomposition of a nonempty word extracts at least one block. -/
theorem blocks_ne_nil_of_word_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (hne : word ≠ []) :
    decomposition.blocks ≠ [] := by
  cases decomposition with
  | done =>
      exact (hne rfl).elim
  | step =>
      simp [blocks]

/-- The normal form selected from a nonempty decomposition is Eval-admissible. -/
theorem normalForm_isEvalAdmissible_of_word_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (hne : word ≠ []) :
    decomposition.normalForm.IsEvalAdmissible := by
  have hblocks :
      0 < decomposition.blocks.length :=
    List.length_pos_iff_ne_nil.mpr
      (decomposition.blocks_ne_nil_of_word_ne_nil hne)
  have hsum := decomposition.count_sum_eq_blocks_length
  simp only [normalForm]
  split_ifs with hcrosscap
  · change 1 ≤ decomposition.handleCount ∨
      1 ≤ decomposition.boundaryCount
    rw [hcrosscap] at hsum
    omega
  · change
      1 ≤ decomposition.crosscapCount +
        2 * decomposition.handleCount
    omega

/-- Every edge recorded by a decomposition occurs in that decomposition's source word. -/
theorem mem_source_of_mem_extractedEdges {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (e : Fin n)
    (he : e ∈ decomposition.extractedEdges) :
    e ∈ word.map edgeOfDart := by
  induction decomposition with
  | done =>
      simp [extractedEdges] at he
  | step feature reduction tail ih =>
      simp only [extractedEdges, List.mem_append] at he
      rcases he with hfeature | htail
      · exact feature.extractedEdges_subset_source e hfeature
      · have hReduced :
            e ∈ reduction.reducedWord.map edgeOfDart :=
          ih htail
        have hResidual :=
          reduction.mem_source_of_mem e hReduced
        apply List.count_pos_iff.mp
        rw [feature.count_residualWord_of_mem e hResidual]
        exact List.count_pos_iff.mpr hResidual

/-- Distinct extraction steps consume disjoint edge names. -/
theorem extractedEdges_nodup {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word) :
    decomposition.extractedEdges.Nodup := by
  induction decomposition with
  | done =>
      simp [extractedEdges]
  | step feature reduction tail ih =>
      rw [extractedEdges, List.nodup_append]
      refine ⟨feature.extractedEdges_nodup, ih, ?_⟩
      intro e hfeature e' htail heq
      subst e'
      have hReduced :
          e ∈ reduction.reducedWord.map edgeOfDart :=
        tail.mem_source_of_mem_extractedEdges e htail
      have hResidual :=
        reduction.mem_source_of_mem e hReduced
      exact
        (List.disjoint_left.mp
          feature.extractedEdges_disjoint_residualWord)
          hfeature hResidual

end ResidualDecomposition

/-- One descent step from a directed opposite arc: either an immediately extractable feature,
or a strictly shorter opposite arc nested inside it. -/
inductive OppositeArcStep {n : ℕ}
    (word : List (SignedDart (Fin n))) {a : Fin n}
    (form : OppositeArcForm word a)
  | actionable (feature : ActionablePairReductionFeature word)
  | nested (b : Fin n) (inner : OppositeArcForm word b)
      (shorter : inner.between.length < form.between.length)

/-- Every once-used edge can be displayed at the cyclic head. -/
theorem exists_boundaryOccurrenceForm {n : ℕ}
    (word : List (SignedDart (Fin n))) (a : Fin n)
    (hcount : (word.map edgeOfDart).count a = 1) :
    Nonempty (BoundaryOccurrenceForm word a) := by
  rcases exists_decomposition_of_count_eq_one word a hcount with
    ⟨negative, left, right, hword, hleft, hright⟩
  let remainder := right ++ left
  have hrotation :
      word.IsRotated (dart a negative :: remainder) := by
    rw [hword]
    simpa only [remainder, List.cons_append,
      List.append_assoc] using
      (List.isRotated_append
        (l := left) (l' := dart a negative :: right))
  exact ⟨
    { negative := negative
      remainder := remainder
      rotated := hrotation
      edge_not_mem_remainder := by
        simp only [remainder, List.map_append,
          List.mem_append, not_or]
        exact ⟨hright, hleft⟩ }⟩

/-- Inspect the first dart of a nonempty opposite arc.  A boundary or equal-orientation edge is
immediately actionable.  An opposite edge either crosses the selected pair, yielding a handle,
or closes inside it, yielding a strictly shorter directed arc. -/
theorem OppositeArcForm.exists_step_of_usedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    Nonempty (OppositeArcStep word form) := by
  classical
  cases hbetween : form.between with
  | nil =>
      exact (form.between_ne_nil reduced hbetween).elim
  | cons d tail =>
      let b : Fin n := edgeOfDart d
      let bNegative : Bool := dartNegative d
      have hd : d = dart b bNegative := by
        exact (dart_edgeOfDart_dartNegative d).symm
      have hbmem : b ∈ form.between.map edgeOfDart := by
        rw [hbetween]
        simp [b]
      have hbword : b ∈ word.map edgeOfDart := by
        apply (form.rotated.map edgeOfDart).mem_iff.mpr
        simp [hbetween, b]
      have hba : b ≠ a := by
        intro h
        exact form.edge_not_mem_between (h ▸ hbmem)
      have hab : a ≠ b := hba.symm
      let pattern :=
        Classical.choice
          (exists_edgePattern_of_multiplicity
            word b (multiplicities b hbword))
      cases pattern with
      | boundary hcount =>
          let boundaryForm :=
            Classical.choice
              (exists_boundaryOccurrenceForm word b hcount)
          exact ⟨.actionable (.boundary b boundaryForm)⟩
      | positiveCrosscap hpositive hnegative =>
          let crosscapForm :=
            Classical.choice
              (exists_positiveCrosscapOccurrenceForm
                word b hpositive hnegative)
          exact ⟨.actionable (.crosscap b crosscapForm)⟩
      | negativeCrosscap hpositive hnegative =>
          let crosscapForm :=
            Classical.choice
              (exists_negativeCrosscapOccurrenceForm
                word b hpositive hnegative)
          exact ⟨.actionable (.crosscap b crosscapForm)⟩
      | opposite hpositive hnegative =>
          have htotal :
              (word.map edgeOfDart).count b = 2 := by
            rw [count_edgeOfDart_eq_pos_add_neg,
              hpositive, hnegative]
          have hrotatedCount :=
            (form.rotated.map edgeOfDart).perm.count_eq b
          have hsum :
              (tail.map edgeOfDart).count b +
                  (form.remainder.map edgeOfDart).count b = 1 := by
            rw [htotal] at hrotatedCount
            simp only [hbetween, List.map_cons, List.map_append,
              List.count_cons, List.count_append] at hrotatedCount
            rw [hd, edgeOfDart_dart, edgeOfDart_dart] at hrotatedCount
            simp [hab] at hrotatedCount
            omega
          by_cases hbTail : b ∈ tail.map edgeOfDart
          · have htailPositive :
                0 < (tail.map edgeOfDart).count b :=
              List.count_pos_iff.mpr hbTail
            have htailCount :
                (tail.map edgeOfDart).count b = 1 := by
              omega
            have hremainderCount :
                (form.remainder.map edgeOfDart).count b = 0 := by
              omega
            have hbRemainder :
                b ∉ form.remainder.map edgeOfDart :=
              List.count_eq_zero.mp hremainderCount
            rcases exists_decomposition_of_count_eq_one
                tail b htailCount with
              ⟨secondNegative, left, right, htail,
                hbLeft, hbRight⟩
            have hpositiveCount :=
              form.rotated.perm.count_eq (.pos b)
            have hnegativeCount :=
              form.rotated.perm.count_eq (.neg b)
            rw [hpositive] at hpositiveCount
            rw [hnegative] at hnegativeCount
            have hopposite :
                secondNegative = !bNegative := by
              cases hfirst : bNegative <;>
                cases hsecond : secondNegative
              · simp only [Bool.not_false]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, htail, dart, hfirst, hsecond,
                    haorientation, hab] at hpositiveCount
              · rfl
              · rfl
              · simp only [Bool.not_true]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, htail, dart, hfirst, hsecond,
                    haorientation, hab] at hnegativeCount
            let innerRemainder :=
              right ++
                dart a (!form.firstNegative) ::
                  form.remainder ++ [dart a form.firstNegative]
            have hrotateInner :
                word.IsRotated
                  (dart b bNegative :: left ++
                    dart b (!bNegative) :: innerRemainder) := by
              have hmoveA :=
                List.isRotated_append
                  (l := [dart a form.firstNegative])
                  (l' := dart b bNegative :: left ++
                    dart b (!bNegative) ::
                      (right ++
                        dart a (!form.firstNegative) ::
                          form.remainder))
              apply form.rotated.trans
              rw [hbetween, hd, htail, hopposite]
              simpa only [innerRemainder, List.nil_append,
                List.cons_append, List.append_assoc] using hmoveA
            let inner : OppositeArcForm word b :=
              { firstNegative := bNegative
                between := left
                remainder := innerRemainder
                rotated := hrotateInner
                edge_not_mem_between := hbLeft
                edge_not_mem_remainder := by
                  simp [innerRemainder, hba, hbRight, hbRemainder] }
            have hlength := congrArg List.length htail
            have hshorter :
                inner.between.length < form.between.length := by
              simp only [inner, hbetween, List.length_cons]
              simp only [List.length_append, List.length_cons] at hlength
              omega
            exact ⟨.nested b inner hshorter⟩
          · have htailCount :
                (tail.map edgeOfDart).count b = 0 :=
              List.count_eq_zero.mpr hbTail
            have hremainderCount :
                (form.remainder.map edgeOfDart).count b = 1 := by
              omega
            rcases exists_decomposition_of_count_eq_one
                form.remainder b hremainderCount with
              ⟨outsideNegative, left, right, hremainder,
                hbLeft, hbRight⟩
            have hpositiveCount :=
              form.rotated.perm.count_eq (.pos b)
            have hnegativeCount :=
              form.rotated.perm.count_eq (.neg b)
            rw [hpositive] at hpositiveCount
            rw [hnegative] at hnegativeCount
            have hopposite :
                outsideNegative = !bNegative := by
              cases hfirst : bNegative <;>
                cases hsecond : outsideNegative
              · simp only [Bool.not_false]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, hremainder, dart, hfirst, hsecond,
                    haorientation, hab] at hpositiveCount
              · rfl
              · rfl
              · simp only [Bool.not_true]
                exfalso
                cases haorientation : form.firstNegative <;>
                  simp [hbetween, hd, hremainder, dart, hfirst, hsecond,
                    haorientation, hab] at hnegativeCount
            cases horientation : form.firstNegative
            · let handleForm : InterleavedOccurrenceForm word a b :=
                { bNegativeInside := bNegative
                  beforeB := []
                  beforeNegA := tail
                  beforeOutsideB := left
                  remainder := right
                  rotated := by
                    have hrotated := form.rotated
                    rw [hbetween, hd, hremainder, hopposite,
                      horientation] at hrotated
                    simpa [dart, List.cons_append,
                      List.append_assoc] using hrotated
                  edge_ne := hba.symm
                  a_not_mem_beforeB := by simp
                  a_not_mem_beforeNegA := by
                    intro haTail
                    apply form.edge_not_mem_between
                    rw [hbetween]
                    simp [haTail]
                  a_not_mem_beforeOutsideB := by
                    intro haLeft
                    apply form.edge_not_mem_remainder
                    rw [hremainder]
                    simp [haLeft]
                  a_not_mem_remainder := by
                    intro haRight
                    apply form.edge_not_mem_remainder
                    rw [hremainder]
                    simp [haRight]
                  b_not_mem_beforeB := by simp
                  b_not_mem_beforeNegA := hbTail
                  b_not_mem_beforeOutsideB := hbLeft
                  b_not_mem_remainder := hbRight }
              exact ⟨.actionable (.handle a b handleForm)⟩
            · let handleForm : InterleavedOccurrenceForm word a b :=
                { bNegativeInside := outsideNegative
                  beforeB := left
                  beforeNegA := right
                  beforeOutsideB := []
                  remainder := tail
                  rotated := by
                    have hrotate :=
                      List.isRotated_append
                        (l := dart a form.firstNegative ::
                          dart b bNegative :: tail)
                        (l' := dart a (!form.firstNegative) ::
                          left ++ dart b outsideNegative :: right)
                    have hrotated := form.rotated
                    rw [hbetween, hd, hremainder] at hrotated
                    apply hrotated.trans
                    simpa [
                      dart, horientation, hopposite,
                      List.cons_append, List.append_assoc] using hrotate
                  edge_ne := hba.symm
                  a_not_mem_beforeB := by
                    intro haLeft
                    apply form.edge_not_mem_remainder
                    rw [hremainder]
                    simp [haLeft]
                  a_not_mem_beforeNegA := by
                    intro haRight
                    apply form.edge_not_mem_remainder
                    rw [hremainder]
                    simp [haRight]
                  a_not_mem_beforeOutsideB := by simp
                  a_not_mem_remainder := by
                    intro haTail
                    apply form.edge_not_mem_between
                    rw [hbetween]
                    simp [haTail]
                  b_not_mem_beforeB := hbLeft
                  b_not_mem_beforeNegA := hbRight
                  b_not_mem_beforeOutsideB := by simp
                  b_not_mem_remainder := hbTail }
              exact ⟨.actionable (.handle a b handleForm)⟩

/-- Surface-valid words supply the residual multiplicity hypothesis required by one opposite-arc
descent step. -/
theorem OppositeArcForm.exists_step {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    Nonempty (OppositeArcStep word form) :=
  form.exists_step_of_usedMultiplicities
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid) reduced

/-- Well-founded descent through nested opposite pairs terminates at a boundary, crosscap, or
interleaved handle feature. -/
noncomputable def OppositeArcForm.findActionableOfUsedMultiplicities {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    ActionablePairReductionFeature word := by
  let step :=
    Classical.choice
      (form.exists_step_of_usedMultiplicities
        multiplicities reduced)
  cases step with
  | actionable feature =>
      exact feature
  | nested b inner shorter =>
      exact inner.findActionableOfUsedMultiplicities
        multiplicities reduced
termination_by form.between.length
decreasing_by exact shorter

/-- Validity-specialized spelling of the residual opposite-arc descent. -/
noncomputable def OppositeArcForm.findActionable {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeArcForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    ActionablePairReductionFeature word :=
  form.findActionableOfUsedMultiplicities
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid) reduced

/-- In a pair-reduced word, the two darts of an opposite form have a nonempty intervening
word. -/
theorem OppositeOccurrenceForm.between_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : OppositeOccurrenceForm word a)
    (reduced : IsPairReduced word) :
    form.between ≠ [] := by
  intro hbetween
  rcases reduced with ⟨hreduced⟩
  exact hreduced
    { edge := a
      tail := form.remainder
      negativeFirst := false
      rotated := by
        simpa [inversePair, hbetween] using form.rotated }

/-! ### Proof-producing extraction of the easy pairing features -/

/-- The displayed cyclic word carried by an interleaved-pair certificate. -/
def InterleavedOccurrenceForm.displayedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b) :
    List (SignedDart (Fin n)) :=
  .pos a :: form.beforeB ++
    dart b form.bNegativeInside :: form.beforeNegA ++
    .neg a :: form.beforeOutsideB ++
    dart b (!form.bNegativeInside) :: form.remainder

/-- The adjacent handle block produced by the three-Dyck extraction chain. -/
def InterleavedOccurrenceForm.groupedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b) :
    List (SignedDart (Fin n)) :=
  [.pos a, .pos b, .neg a, .neg b] ++
    form.remainder ++ form.beforeOutsideB ++
    form.beforeNegA ++ form.beforeB

/-- When `b` is encountered negative inside the `a`-pair, reverse that edge to obtain the
positive-first source spelling required by handle extraction. -/
def InterleavedOccurrenceForm.negativeInsideSignedIso {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b)
    (hnegative : form.bNegativeInside = true) :
    SignedPresentationIso
      (Dyck.oneFace form.displayedWord)
      (Handle.source a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling b
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    have hposA :
        (Dyck.reverseEdgeRelabeling b).mapDart (.pos a) = .pos a :=
      Dyck.reverseEdgeRelabeling_of_ne b a form.edge_ne false
    have hnegA :
        (Dyck.reverseEdgeRelabeling b).mapDart (.neg a) = .neg a :=
      Dyck.reverseEdgeRelabeling_of_ne b a form.edge_ne true
    simp only [InterleavedOccurrenceForm.displayedWord,
      List.map_cons, List.map_append, hposA, hnegA,
      hnegative, Bool.not_true, dart,
      Dyck.reverseEdgeRelabeling_neg,
      Dyck.reverseEdgeRelabeling_pos]
    rw [Dyck.reverseEdgeRelabeling_word b form.beforeB
        form.b_not_mem_beforeB,
      Dyck.reverseEdgeRelabeling_word b form.beforeNegA
        form.b_not_mem_beforeNegA,
      Dyck.reverseEdgeRelabeling_word b form.beforeOutsideB
        form.b_not_mem_beforeOutsideB,
      Dyck.reverseEdgeRelabeling_word b form.remainder
        form.b_not_mem_remainder]
    convert List.IsRotated.refl _ using 1
    all_goals
      simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- A certified interleaved pair produces an adjacent handle block through the existing
three-Dyck normalization chain.  If the inner occurrence of `b` is negative, the chain begins by
reversing the orientation assigned to `b`. -/
theorem InterleavedOccurrenceForm.exists_normalizationEquivalent_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a b : Fin n}
    (form : InterleavedOccurrenceForm word a b)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.groupedWord, validGrouped⟩ := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  let validDisplayed :
      (Dyck.oneFace form.displayedWord).IsSurfaceValid :=
    sourceRotation.isSurfaceValid valid
  have hToDisplayed :
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.displayedWord, validDisplayed⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  cases horientation : form.bNegativeInside
  · have hsource :
        Dyck.oneFace form.displayedWord =
          Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder := by
      simp [InterleavedOccurrenceForm.displayedWord,
        Handle.source, Dyck.source, dart, horientation,
        List.cons_append, List.append_assoc]
    let validSource :
        (Handle.source a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      hsource ▸ validDisplayed
    let validTarget :
        (Handle.target a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      Handle.target_isSurfaceValid a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder validSource
    have hHandle :
        NormalizationEquivalent
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩
          ⟨Handle.target a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validTarget⟩ :=
      Handle.normalizationEquivalent a b
        form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder
        form.edge_ne
        form.a_not_mem_beforeB form.a_not_mem_beforeNegA
        form.a_not_mem_beforeOutsideB form.a_not_mem_remainder
        form.b_not_mem_beforeB form.b_not_mem_beforeNegA
        form.b_not_mem_beforeOutsideB form.b_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (Handle.target_boundary_isRotated_handle a b
          form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace form.displayedWord, validDisplayed⟩ :
          ValidPresentation) =
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hHandle.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩
  · let signIso := form.negativeInsideSignedIso horientation
    let validSource :
        (Handle.source a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      signIso.isSurfaceValid validDisplayed
    let validTarget :
        (Handle.target a b form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder).IsSurfaceValid :=
      Handle.target_isSurfaceValid a b form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder validSource
    have hHandle :
        NormalizationEquivalent
          ⟨Handle.source a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validSource⟩
          ⟨Handle.target a b form.beforeB form.beforeNegA
            form.beforeOutsideB form.remainder, validTarget⟩ :=
      Handle.normalizationEquivalent a b
        form.beforeB form.beforeNegA
        form.beforeOutsideB form.remainder
        form.edge_ne
        form.a_not_mem_beforeB form.a_not_mem_beforeNegA
        form.a_not_mem_beforeOutsideB form.a_not_mem_remainder
        form.b_not_mem_beforeB form.b_not_mem_beforeNegA
        form.b_not_mem_beforeOutsideB form.b_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (Handle.target_boundary_isRotated_handle a b
          form.beforeB form.beforeNegA
          form.beforeOutsideB form.remainder)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    exact ⟨validGrouped,
      hToDisplayed.trans
        ((NormalizationEquivalent.ofSignedIso signIso).trans
          (hHandle.trans
            (NormalizationEquivalent.ofSignedIso targetRotation)))⟩

/-- The cyclic spelling obtained by displaying a boundary edge at the head of its word. -/
def BoundaryOccurrenceForm.headWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : BoundaryOccurrenceForm word a) :
    List (SignedDart (Fin n)) :=
  dart a form.negative :: form.remainder

/-- Displaying a certified boundary occurrence at the head is already a normalization
equivalence: it is only a cyclic change of the distinguished face word. -/
theorem BoundaryOccurrenceForm.exists_normalizationEquivalent_head {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : BoundaryOccurrenceForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validHead : (Dyck.oneFace form.headWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.headWord, validHead⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  let validHead :
      (Dyck.oneFace form.headWord).IsSurfaceValid :=
    rotation.isSurfaceValid valid
  exact ⟨validHead, NormalizationEquivalent.ofSignedIso rotation⟩

/-- The grouped spelling produced from a certified crosscap occurrence.  The segment after the
second occurrence is reversed, exactly as in the Gallier--Xu crosscap rewrite. -/
def CrosscapOccurrenceForm.groupedWord {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a) :
    List (SignedDart (Fin n)) :=
  [dart a form.negative, dart a form.negative] ++
    inverseWord form.remainder ++ form.between

/-- The positive crosscap target is cyclically the chosen grouped spelling. -/
theorem CrosscapOccurrenceForm.positiveTarget_isRotated_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (hpositive : form.negative = false) :
    (Crosscap.target a form.between form.remainder).boundary 0 |>.IsRotated
      form.groupedWord := by
  simp only [Crosscap.target, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := form.between)
      (l' := [SignedDart.pos a, SignedDart.pos a] ++
        inverseWord form.remainder)) using 1
  all_goals
    simp [CrosscapOccurrenceForm.groupedWord, dart, hpositive,
      List.cons_append, List.append_assoc]

/-- The negative crosscap target is cyclically the chosen grouped spelling. -/
theorem CrosscapOccurrenceForm.negativeTarget_isRotated_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (hnegative : form.negative = true) :
    (Crosscap.negativeTarget a form.between form.remainder).boundary 0 |>.IsRotated
      form.groupedWord := by
  simp only [Crosscap.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := form.between)
      (l' := [SignedDart.neg a, SignedDart.neg a] ++
        inverseWord form.remainder)) using 1
  all_goals
    simp [CrosscapOccurrenceForm.groupedWord, dart, hnegative,
      List.cons_append, List.append_assoc]

/-- A certified equally oriented pair can be moved to an adjacent crosscap block by an exact
normalization chain.  Both signs are supported; the grouped block retains the input sign. -/
theorem CrosscapOccurrenceForm.exists_normalizationEquivalent_grouped {n : ℕ}
    {word : List (SignedDart (Fin n))} {a : Fin n}
    (form : CrosscapOccurrenceForm word a)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ∃ validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace form.groupedWord, validGrouped⟩ := by
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated form.rotated
  have hToDisplayed :
      NormalizationEquivalent
        ⟨Dyck.oneFace word, valid⟩
        ⟨Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder),
          sourceRotation.isSurfaceValid valid⟩ :=
    NormalizationEquivalent.ofSignedIso sourceRotation
  cases horientation : form.negative
  · have hsource :
        Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder) =
          Crosscap.source a form.between form.remainder := by
      simp [Crosscap.source, dart, horientation,
        List.cons_append]
    let validSource :
        (Crosscap.source a form.between form.remainder).IsSurfaceValid :=
      hsource ▸ sourceRotation.isSurfaceValid valid
    let validTarget :
        (Crosscap.target a form.between form.remainder).IsSurfaceValid :=
      Crosscap.target_isSurfaceValid a form.between form.remainder validSource
    have hCrosscap :
        NormalizationEquivalent
          ⟨Crosscap.source a form.between form.remainder, validSource⟩
          ⟨Crosscap.target a form.between form.remainder, validTarget⟩ :=
      Crosscap.normalizationEquivalent a form.between form.remainder
        form.edge_not_mem_between form.edge_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (form.positiveTarget_isRotated_grouped horientation)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace
              (dart a form.negative :: form.between ++
                dart a form.negative :: form.remainder),
            sourceRotation.isSurfaceValid valid⟩ :
          ValidPresentation) =
          ⟨Crosscap.source a form.between form.remainder, validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hCrosscap.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩
  · have hsource :
        Dyck.oneFace
            (dart a form.negative :: form.between ++
              dart a form.negative :: form.remainder) =
          Crosscap.negativeSource a form.between form.remainder := by
      simp [Crosscap.negativeSource, dart, horientation,
        List.cons_append]
    let validSource :
        (Crosscap.negativeSource a form.between form.remainder).IsSurfaceValid :=
      hsource ▸ sourceRotation.isSurfaceValid valid
    let validTarget :
        (Crosscap.negativeTarget a form.between form.remainder).IsSurfaceValid :=
      Crosscap.negativeTarget_isSurfaceValid
        a form.between form.remainder validSource
    have hCrosscap :
        NormalizationEquivalent
          ⟨Crosscap.negativeSource a form.between form.remainder, validSource⟩
          ⟨Crosscap.negativeTarget a form.between form.remainder, validTarget⟩ :=
      Crosscap.negativeNormalizationEquivalent
        a form.between form.remainder
        form.edge_not_mem_between form.edge_not_mem_remainder
        validSource validTarget
    let targetRotation :=
      Dyck.oneFaceSignedIsoOfIsRotated
        (form.negativeTarget_isRotated_grouped horientation)
    let validGrouped :
        (Dyck.oneFace form.groupedWord).IsSurfaceValid :=
      targetRotation.isSurfaceValid validTarget
    have hDisplayed :
        (⟨Dyck.oneFace
              (dart a form.negative :: form.between ++
                dart a form.negative :: form.remainder),
            sourceRotation.isSurfaceValid valid⟩ :
          ValidPresentation) =
          ⟨Crosscap.negativeSource a form.between form.remainder,
            validSource⟩ :=
      ValidPresentation.ext hsource
    rw [hDisplayed] at hToDisplayed
    exact ⟨validGrouped,
      hToDisplayed.trans
        (hCrosscap.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩

/-- Each local extraction target is definitionally its extracted block followed by the residual
word used by the global recursion. -/
theorem ActionablePairReductionFeature.block_word_append_residualWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word) :
    feature.block.word ++ feature.residualWord =
      match feature with
      | .boundary _ form => form.headWord
      | .crosscap _ form => form.groupedWord
      | .handle _ _ form => form.groupedWord := by
  cases feature <;>
    simp [ActionablePairReductionFeature.block,
      ExtractedBlock.word,
      ActionablePairReductionFeature.residualWord,
      BoundaryOccurrenceForm.headWord,
      CrosscapOccurrenceForm.groupedWord,
      InterleavedOccurrenceForm.groupedWord,
      List.append_assoc]

/-- A proof-producing result of acting on one certified pairing feature.  The constructor records
the exact extracted spelling, its transported validity, and the normalization chain from the
original word. -/
inductive ActionablePairReductionResult {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
      (validHead : (Dyck.oneFace form.headWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.headWord, validHead⟩)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
      (validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.groupedWord, validGrouped⟩)
  | handle (a b : Fin n) (form : InterleavedOccurrenceForm word a b)
      (validGrouped : (Dyck.oneFace form.groupedWord).IsSurfaceValid)
      (equivalent :
        NormalizationEquivalent
          ⟨Dyck.oneFace word, valid⟩
          ⟨Dyck.oneFace form.groupedWord, validGrouped⟩)

namespace ActionablePairReductionResult

/-- Feature whose local normalization chain was executed. -/
def feature {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid} :
    ActionablePairReductionResult word valid →
      ActionablePairReductionFeature word
  | .boundary a form _ _ => .boundary a form
  | .crosscap a form _ _ => .crosscap a form
  | .handle a b form _ _ => .handle a b form

/-- Exact block-plus-residual word reached by an executed extraction. -/
def targetWord {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    List (SignedDart (Fin n)) :=
  result.feature.block.word ++ result.feature.residualWord

/-- Valid presentation reached by one actionable extraction. -/
def target {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid} :
    ActionablePairReductionResult word valid → ValidPresentation
  | .boundary _ form validHead _ =>
      ⟨Dyck.oneFace form.headWord, validHead⟩
  | .crosscap _ form validGrouped _ =>
      ⟨Dyck.oneFace form.groupedWord, validGrouped⟩
  | .handle _ _ form validGrouped _ =>
      ⟨Dyck.oneFace form.groupedWord, validGrouped⟩

/-- The stored target presentation is the one-face presentation on `targetWord`. -/
theorem target_presentation_eq_oneFace_targetWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    result.target.presentation = Dyck.oneFace result.targetWord := by
  cases result <;>
    simp [target, targetWord, feature,
      ActionablePairReductionFeature.block_word_append_residualWord]

/-- Validity witness for the exact block-plus-residual target word. -/
theorem targetWordValid {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    (Dyck.oneFace result.targetWord).IsSurfaceValid :=
  result.target_presentation_eq_oneFace_targetWord ▸ result.target.valid

/-- Normalization equivalence certified by one actionable extraction. -/
theorem equivalent {n : ℕ} {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, valid⟩ result.target := by
  cases result with
  | boundary _ _ _ equivalent => exact equivalent
  | crosscap _ _ _ equivalent => exact equivalent
  | handle _ _ _ _ equivalent => exact equivalent

/-- Normalization equivalence to the stable exact block-plus-residual spelling. -/
theorem equivalent_to_targetWord {n : ℕ}
    {word : List (SignedDart (Fin n))}
    {valid : (Dyck.oneFace word).IsSurfaceValid}
    (result : ActionablePairReductionResult word valid) :
    NormalizationEquivalent
      ⟨Dyck.oneFace word, valid⟩
      ⟨Dyck.oneFace result.targetWord, result.targetWordValid⟩ := by
  have hnode :
      result.target =
        ⟨Dyck.oneFace result.targetWord,
          result.targetWordValid⟩ := by
    apply ValidPresentation.ext
    exact result.target_presentation_eq_oneFace_targetWord
  rw [← hnode]
  exact result.equivalent

end ActionablePairReductionResult

/-- Execute an actionable pairing feature using the corresponding proof-producing rewrite
endpoint. -/
noncomputable def ActionablePairReductionFeature.extract {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (feature : ActionablePairReductionFeature word)
    (valid : (Dyck.oneFace word).IsSurfaceValid) :
    ActionablePairReductionResult word valid := by
  cases feature with
  | boundary a form =>
      let witness :=
        form.exists_normalizationEquivalent_head valid
      let validHead := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .boundary a form validHead equivalent
  | crosscap a form =>
      let witness :=
        form.exists_normalizationEquivalent_grouped valid
      let validGrouped := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .crosscap a form validGrouped equivalent
  | handle a b form =>
      let witness :=
        form.exists_normalizationEquivalent_grouped valid
      let validGrouped := Classical.choose witness
      let equivalent := Classical.choose_spec witness
      exact .handle a b form validGrouped equivalent

/-- The local feature exposed at a selected edge of a pair-reduced valid word. -/
inductive PairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
  | boundary (a : Fin n) (form : BoundaryOccurrenceForm word a)
  | crosscap (a : Fin n) (form : CrosscapOccurrenceForm word a)
  | opposite (a : Fin n) (form : OppositeOccurrenceForm word a)
      (between_nonempty : form.between ≠ [])

/-- Every pair-reduced valid word with at least one edge exposes either a boundary dart, an
equally oriented crosscap pair, or a nondegenerate opposite pair. -/
theorem exists_pairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    Nonempty (PairReductionFeature word) := by
  let a : Fin n := ⟨0, hn⟩
  let pattern := Classical.choice (exists_edgePattern word valid a)
  cases pattern with
  | boundary hcount =>
      let form :=
        Classical.choice
          (exists_boundaryOccurrenceForm word a hcount)
      exact ⟨.boundary a form⟩
  | positiveCrosscap hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_positiveCrosscapOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.crosscap a form⟩
  | negativeCrosscap hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_negativeCrosscapOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.crosscap a form⟩
  | opposite hpositive hnegative =>
      let form :=
        Classical.choice
          (exists_oppositeOccurrenceForm
            word a hpositive hnegative)
      exact ⟨.opposite a form (form.between_ne_nil reduced)⟩

/-- Every nonempty pair-reduced valid word exposes a feature with a complete local normalization
chain: a boundary edge, a crosscap pair, or an interleaved pair ready for handle extraction. -/
theorem exists_actionablePairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    Nonempty (ActionablePairReductionFeature word) := by
  let feature :=
    Classical.choice
      (exists_pairReductionFeature word valid reduced hn)
  cases feature with
  | boundary a form =>
      exact ⟨.boundary a form⟩
  | crosscap a form =>
      exact ⟨.crosscap a form⟩
  | opposite a form _ =>
      exact ⟨form.toArc.findActionable valid reduced⟩

/-- Residual form of actionable-feature existence.  It needs only a nonempty residual word,
surface multiplicities for names still used there, and pair reduction; already-grouped ambient
edge names may be absent. -/
theorem exists_actionablePairReductionFeature_of_usedMultiplicities {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word)
    (hne : word ≠ []) :
    Nonempty (ActionablePairReductionFeature word) := by
  cases word with
  | nil =>
      exact (hne rfl).elim
  | cons d tail =>
      let a : Fin n := edgeOfDart d
      have ha : a ∈ (d :: tail).map edgeOfDart := by
        simp [a]
      let pattern :=
        Classical.choice
          (exists_edgePattern_of_multiplicity
            (d :: tail) a (multiplicities a ha))
      cases pattern with
      | boundary hcount =>
          let form :=
            Classical.choice
              (exists_boundaryOccurrenceForm (d :: tail) a hcount)
          exact ⟨.boundary a form⟩
      | positiveCrosscap hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_positiveCrosscapOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨.crosscap a form⟩
      | negativeCrosscap hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_negativeCrosscapOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨.crosscap a form⟩
      | opposite hpositive hnegative =>
          let form :=
            Classical.choice
              (exists_oppositeOccurrenceForm
                (d :: tail) a hpositive hnegative)
          exact ⟨form.toArc.findActionableOfUsedMultiplicities
            multiplicities reduced⟩

/-- Fuel-bounded decomposition of a pair-reduced residual word into boundary, crosscap, and handle
blocks.  Pair cancellation after each extraction restores the induction hypothesis. -/
noncomputable def decomposeResidualFuel (fuel : ℕ) {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    word.length ≤ fuel → ResidualDecomposition word := by
  classical
  intro hbound
  by_cases hnil : word = []
  · subst word
    exact .done
  · let feature :=
      Classical.choice
        (exists_actionablePairReductionFeature_of_usedMultiplicities
          word multiplicities reduced hnil)
    let residualMultiplicities :=
      feature.hasValidUsedMultiplicities_residualWord
        multiplicities
    let reduction :=
      reduceResidualPairs feature.residualWord
        residualMultiplicities
    have hshort :
        reduction.reducedWord.length < word.length :=
      reduction.length_le.trans_lt feature.residualWord_length_lt
    have hfuelPositive : 0 < fuel := by
      omega
    have htailBound :
        reduction.reducedWord.length ≤ fuel - 1 := by
      omega
    exact .step feature reduction
      (decomposeResidualFuel (fuel - 1)
        reduction.reducedWord reduction.multiplicities
        reduction.reduced htailBound)
termination_by fuel
decreasing_by
  apply Nat.sub_lt
  · exact hfuelPositive
  · omega

/-- Every pair-reduced residual word with valid used-edge multiplicities admits a terminating
block decomposition. -/
noncomputable def decomposeResidual {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (multiplicities : HasValidUsedMultiplicities word)
    (reduced : IsPairReduced word) :
    ResidualDecomposition word :=
  decomposeResidualFuel word.length word multiplicities
    reduced (le_refl _)

/-- Surface-valid pair-reduced one-face words admit the residual block decomposition needed by the
global Gallier--Xu normalization recursion. -/
noncomputable def decomposePairReduced {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    ResidualDecomposition word :=
  decomposeResidual word
    (hasValidUsedMultiplicities_of_isSurfaceValid word valid)
    reduced

/-- Normal-form parameters computed from the certified decomposition of a pair-reduced valid
one-face word. -/
noncomputable def pairReducedNormalForm {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) : NormalForm :=
  (decomposePairReduced word valid reduced).normalForm

/-- The normal-form parameters selected from a pair-reduced valid word satisfy the exact
Lean-Eval admissibility predicate. -/
theorem pairReducedNormalForm_isEvalAdmissible {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word) :
    (pairReducedNormalForm word valid reduced).IsEvalAdmissible := by
  apply
    (decomposePairReduced word valid reduced).normalForm_isEvalAdmissible_of_word_ne_nil
  simpa only [Dyck.oneFace_boundary] using
    valid.2.1 (0 : (Dyck.oneFace word).Face)

/-- Find and execute one certified normalization step on any nonempty pair-reduced valid word. -/
noncomputable def extractPairReductionFeature {n : ℕ}
    (word : List (SignedDart (Fin n)))
    (valid : (Dyck.oneFace word).IsSurfaceValid)
    (reduced : IsPairReduced word)
    (hn : 0 < n) :
    ActionablePairReductionResult word valid :=
  (Classical.choice
    (exists_actionablePairReductionFeature word valid reduced hn)).extract valid

end Pairing

end WordReduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
