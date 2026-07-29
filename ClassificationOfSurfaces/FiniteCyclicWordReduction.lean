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
