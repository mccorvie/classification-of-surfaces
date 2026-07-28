/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicNormalization

/-!
# Derived Gallier--Xu word rewrites

This file builds the repeated word transformations used after the primitive P1/P2 phase of the
normalization proof.  It starts with proof-producing infrastructure for one-face cyclic words:

* cyclic rotation is a signed presentation isomorphism;
* validity transports across any permutation of the underlying unoriented edge occurrences;
* the Dyck rewrite is available with either orientation of its distinguished edge.

These lemmas keep intermediate validity witnesses out of the public derived-chain APIs.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Dyck

/-- The unique face of an explicitly indexed one-face presentation. -/
theorem oneFace_face_eq_zero {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    f = 0 := by
  change (show Fin 1 from f) = (0 : Fin 1)
  exact Fin.eq_zero _

@[simp]
theorem oneFace_boundary {n : ℕ}
    (word : List (SignedDart (Fin n))) (f : (oneFace word).Face) :
    (oneFace word).boundary f = word := by
  rw [oneFace_face_eq_zero word f]
  rfl

/-- The edge multiplicity of a one-face presentation is the count in its displayed word. -/
@[simp]
theorem oneFace_edgeMultiplicity {n : ℕ}
    (word : List (SignedDart (Fin n))) (e : Fin n) :
    (oneFace word).edgeMultiplicity e =
      (word.map edgeOfDart).count e := by
  classical
  simp [edgeMultiplicity, faceEdgeMultiplicity, oneFace]

/-- A permutation of the unoriented edge occurrences preserves one-face surface validity.
Orientation signs and cyclic positions are intentionally irrelevant here. -/
theorem oneFace_isSurfaceValid_of_edgePerm {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hperm :
      (sourceWord.map edgeOfDart).Perm
        (targetWord.map edgeOfDart))
    (validSource : (oneFace sourceWord).IsSurfaceValid) :
    (oneFace targetWord).IsSurfaceValid := by
  classical
  have hsourceNonempty : sourceWord ≠ [] := by
    simpa using validSource.2.1 (0 : (oneFace sourceWord).Face)
  have htargetNonempty : targetWord ≠ [] := by
    intro htarget
    have hlength := hperm.length_eq
    simp only [List.length_map, htarget, List.length_nil] at hlength
    exact hsourceNonempty (List.length_eq_zero_iff.mp hlength)
  refine ⟨⟨0⟩, ?_, ?_, ?_⟩
  · intro f
    simpa using htargetNonempty
  · intro f g _h
    rw [oneFace_face_eq_zero targetWord f,
      oneFace_face_eq_zero targetWord g]
  · intro e
    rw [oneFace_edgeMultiplicity]
    rw [← hperm.count_eq e]
    simpa only [oneFace_edgeMultiplicity] using validSource.2.2.2 e

/-- A cyclic rotation of one displayed face word is a signed presentation isomorphism. -/
def oneFaceSignedIsoOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord) :
    SignedPresentationIso (oneFace sourceWord) (oneFace targetWord) where
  edgeRelabeling := EdgeRelabeling.refl _
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl,
      oneFace_boundary, oneFace_boundary]
    exact hrotated

/-- A cyclic rotation of ordinary-valid one-face words is a normalization equivalence. -/
theorem normalizationEquivalentOfIsRotated {n : ℕ}
    {sourceWord targetWord : List (SignedDart (Fin n))}
    (hrotated : sourceWord.IsRotated targetWord)
    (validSource : (oneFace sourceWord).IsSurfaceValid)
    (validTarget : (oneFace targetWord).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨oneFace sourceWord, validSource⟩
      ⟨oneFace targetWord, validTarget⟩ :=
  NormalizationEquivalent.ofSignedIso
    (oneFaceSignedIsoOfIsRotated hrotated)

/-- The Dyck rewrite preserves the unoriented edge-occurrence multiset, hence ordinary validity. -/
theorem target_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (source a U V X).IsSurfaceValid) :
    (target a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- Reverse exactly one named edge orientation. -/
def reverseEdgeRelabeling {n : ℕ} (a : Fin n) :
    EdgeRelabeling (Fin n) (Fin n) where
  edgeEquiv := Equiv.refl _
  reverse := fun e ↦ decide (e = a)

@[simp]
theorem reverseEdgeRelabeling_pos {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.pos a) = .neg a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

@[simp]
theorem reverseEdgeRelabeling_neg {n : ℕ} (a : Fin n) :
    (reverseEdgeRelabeling a).mapDart (.neg a) = .pos a := by
  simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart]

theorem reverseEdgeRelabeling_of_ne {n : ℕ} (a e : Fin n)
    (h : e ≠ a) (orientation : Bool) :
    (reverseEdgeRelabeling a).mapDart
        (if orientation then .neg e else .pos e) =
      if orientation then .neg e else .pos e := by
  cases orientation <;>
    simp [reverseEdgeRelabeling, EdgeRelabeling.mapDart, h]

theorem reverseEdgeRelabeling_word {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n)))
    (ha : a ∉ word.map edgeOfDart) :
    word.map (reverseEdgeRelabeling a).mapDart = word := by
  induction word with
  | nil =>
      rfl
  | cons d word ih =>
      have hda : edgeOfDart d ≠ a := by
        intro h
        apply ha
        simp [h]
      have htail : a ∉ word.map edgeOfDart := by
        intro h
        exact ha (by simp [h])
      rw [List.map_cons, ih htail]
      congr 1
      cases d with
      | pos e =>
          exact reverseEdgeRelabeling_of_ne a e hda false
      | neg e =>
          exact reverseEdgeRelabeling_of_ne a e hda true

/-- The negatively oriented spelling of the Dyck source. -/
@[reducible]
def negativeSource {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace (([.neg a] ++ U) ++ (V ++ [.pos a] ++ X))

/-- The corresponding negatively oriented target spelling. -/
@[reducible]
def negativeTarget {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  oneFace ((U ++ [.pos a]) ++ (X ++ [.neg a] ++ V))

/-- Reversing `a` identifies the negative source spelling with the positive source spelling. -/
def negativeSourceSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeSource a U V X) (source a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_neg, reverseEdgeRelabeling_pos]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a V haV,
      reverseEdgeRelabeling_word a X haX]

/-- Reversing `a` identifies the negative target spelling with the positive target spelling. -/
def negativeTargetSignedIso {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart) :
    SignedPresentationIso
      (negativeTarget a U V X) (target a U V X) where
  edgeRelabeling := reverseEdgeRelabeling a
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro f
    rw [oneFace_boundary, oneFace_boundary]
    simp only [List.map_append, List.map_singleton,
      reverseEdgeRelabeling_pos, reverseEdgeRelabeling_neg]
    rw [reverseEdgeRelabeling_word a U haU,
      reverseEdgeRelabeling_word a X haX,
      reverseEdgeRelabeling_word a V haV]

/-- The negatively spelled Dyck rewrite also preserves ordinary validity. -/
theorem negativeTarget_isSurfaceValid {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (validSource : (negativeSource a U V X).IsSurfaceValid) :
    (negativeTarget a U V X).IsSurfaceValid := by
  apply oneFace_isSurfaceValid_of_edgePerm ?_ validSource
  rw [List.perm_iff_count]
  intro e
  simp only [List.map_append, List.map_singleton, edgeOfDart,
    List.count_append, List.count_cons, List.count_nil]
  omega

/-- The generic Dyck rewrite with the distinguished edge displayed negative first. -/
theorem negativeNormalizationEquivalent {n : ℕ} (a : Fin n)
    (U V X : List (SignedDart (Fin n)))
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (validSource : (negativeSource a U V X).IsSurfaceValid)
    (validTarget : (negativeTarget a U V X).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨negativeSource a U V X, validSource⟩
      ⟨negativeTarget a U V X, validTarget⟩ := by
  let sourceIso := negativeSourceSignedIso a U V X haU haV haX
  let targetIso := negativeTargetSignedIso a U V X haU haV haX
  let validPositiveSource : (source a U V X).IsSurfaceValid :=
    sourceIso.isSurfaceValid validSource
  let validPositiveTarget : (target a U V X).IsSurfaceValid :=
    targetIso.isSurfaceValid validTarget
  exact
    (NormalizationEquivalent.ofSignedIso sourceIso).trans
      ((normalizationEquivalent a U V X haU haV haX
          validPositiveSource validPositiveTarget).trans
        (NormalizationEquivalent.ofSignedIso targetIso).symm)

end Dyck

namespace Handle

/-- The source spelling for Gallier--Xu handle extraction. -/
@[reducible]
def source {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- The result of the first Dyck rewrite. -/
@[reducible]
def afterFirst {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target a U ([.pos b] ++ V) (X ++ [.neg b] ++ Y)

/-- A cyclic spelling of `afterFirst` exposing the two occurrences of `b`. -/
@[reducible]
def secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.source b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- The result of the second Dyck rewrite. -/
@[reducible]
def afterSecond {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.target b (V ++ U) ([.neg a] ++ X) (Y ++ [.pos a])

/-- A cyclic spelling of `afterSecond` exposing `a⁻¹` before `a`. -/
@[reducible]
def thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- The target spelling contains the handle `a b a⁻¹ b⁻¹`, followed cyclically by
`Y X V U`. -/
@[reducible]
def target {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a (X ++ V ++ U) ([.neg b] ++ Y) [.pos b]

/-- The chosen target spelling is cyclically the handle
`a b a⁻¹ b⁻¹`, followed by `Y X V U`. -/
theorem target_boundary_isRotated_handle {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (target a b U V X Y).boundary 0 |>.IsRotated
      ([.pos a, .pos b, .neg a, .neg b] ++ Y ++ X ++ V ++ U) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X ++ V ++ U)
      (l' := [SignedDart.pos a, SignedDart.pos b,
        SignedDart.neg a, SignedDart.neg b] ++ Y)) using 1 <;>
    simp only [List.nil_append, List.cons_append, List.append_assoc]

/-- Rotate the first Dyck target to expose the second distinguished edge. -/
theorem afterFirst_isRotated_secondSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterFirst a b U V X Y).boundary 0 |>.IsRotated
      ((secondSource a b U V X Y).boundary 0) := by
  simp only [afterFirst, secondSource, Dyck.target, Dyck.source,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := U ++ [SignedDart.neg a] ++ X ++
        [SignedDart.neg b] ++ Y ++ [SignedDart.pos a])
      (l' := [SignedDart.pos b] ++ V)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Rotate the second Dyck target to expose `a` in the opposite orientation. -/
theorem afterSecond_isRotated_thirdSource {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n))) :
    (afterSecond a b U V X Y).boundary 0 |>.IsRotated
      ((thirdSource a b U V X Y).boundary 0) := by
  simp only [afterSecond, thirdSource, Dyck.target, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := V ++ U ++ [SignedDart.neg b] ++ Y ++
        [SignedDart.pos a] ++ [SignedDart.pos b])
      (l' := [SignedDart.neg a] ++ X)) using 1 <;>
    simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu's three-Dyck chain extracts the interleaved opposite pairs as a handle. -/
theorem normalizationEquivalent {n : ℕ} (a b : Fin n)
    (U V X Y : List (SignedDart (Fin n)))
    (hab : a ≠ b)
    (haU : a ∉ U.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haY : a ∉ Y.map edgeOfDart)
    (hbU : b ∉ U.map edgeOfDart)
    (hbV : b ∉ V.map edgeOfDart)
    (hbX : b ∉ X.map edgeOfDart)
    (hbY : b ∉ Y.map edgeOfDart)
    (validSource : (source a b U V X Y).IsSurfaceValid)
    (validTarget : (target a b U V X Y).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a b U V X Y, validSource⟩
      ⟨target a b U V X Y, validTarget⟩ := by
  have haBV :
      a ∉ ([SignedDart.pos b] ++ V).map edgeOfDart := by
    simp [edgeOfDart, hab, haV]
  have haXbY :
      a ∉ (X ++ [SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, haX, hab, haY]
  let validAfterFirst : (afterFirst a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) validSource
  have hFirst :
      NormalizationEquivalent
        ⟨source a b U V X Y, validSource⟩
        ⟨afterFirst a b U V X Y, validAfterFirst⟩ :=
    Dyck.normalizationEquivalent a U ([SignedDart.pos b] ++ V)
      (X ++ [SignedDart.neg b] ++ Y) haU haBV haXbY
      validSource validAfterFirst
  let firstRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterFirst_isRotated_secondSource a b U V X Y)
  let validSecondSource : (secondSource a b U V X Y).IsSurfaceValid :=
    firstRotation.isSurfaceValid validAfterFirst
  have hRotateFirst :
      NormalizationEquivalent
        ⟨afterFirst a b U V X Y, validAfterFirst⟩
        ⟨secondSource a b U V X Y, validSecondSource⟩ :=
    NormalizationEquivalent.ofSignedIso firstRotation
  have hbVU : b ∉ (V ++ U).map edgeOfDart := by
    simp [hbV, hbU]
  have hbNegAX :
      b ∉ ([SignedDart.neg a] ++ X).map edgeOfDart := by
    simp [edgeOfDart, hab.symm, hbX]
  have hbYPosA :
      b ∉ (Y ++ [SignedDart.pos a]).map edgeOfDart := by
    simp [edgeOfDart, hbY, hab.symm]
  let validAfterSecond : (afterSecond a b U V X Y).IsSurfaceValid :=
    Dyck.target_isSurfaceValid b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) validSecondSource
  have hSecond :
      NormalizationEquivalent
        ⟨secondSource a b U V X Y, validSecondSource⟩
        ⟨afterSecond a b U V X Y, validAfterSecond⟩ :=
    Dyck.normalizationEquivalent b (V ++ U) ([SignedDart.neg a] ++ X)
      (Y ++ [SignedDart.pos a]) hbVU hbNegAX hbYPosA
      validSecondSource validAfterSecond
  let secondRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (afterSecond_isRotated_thirdSource a b U V X Y)
  let validThirdSource : (thirdSource a b U V X Y).IsSurfaceValid :=
    secondRotation.isSurfaceValid validAfterSecond
  have hRotateSecond :
      NormalizationEquivalent
        ⟨afterSecond a b U V X Y, validAfterSecond⟩
        ⟨thirdSource a b U V X Y, validThirdSource⟩ :=
    NormalizationEquivalent.ofSignedIso secondRotation
  have haXVU : a ∉ (X ++ V ++ U).map edgeOfDart := by
    simp [haX, haV, haU]
  have haNegBY :
      a ∉ ([SignedDart.neg b] ++ Y).map edgeOfDart := by
    simp [edgeOfDart, hab, haY]
  have haPosB :
      a ∉ ([SignedDart.pos b] : List (SignedDart (Fin n))).map edgeOfDart := by
    simp [edgeOfDart, hab]
  have hThird :
      NormalizationEquivalent
        ⟨thirdSource a b U V X Y, validThirdSource⟩
        ⟨target a b U V X Y, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a
      (X ++ V ++ U) ([SignedDart.neg b] ++ Y) [SignedDart.pos b]
      haXVU haNegBY haPosB validThirdSource validTarget
  exact hFirst.trans
    (hRotateFirst.trans
      (hSecond.trans (hRotateSecond.trans hThird)))

end Handle

namespace LoopGrouping

/-- A cyclic word with the loop block `a H a⁻¹`, a separating word `X`, and a block `V` to
move next to the loop. -/
@[reducible]
def source {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.oneFace (([.pos a] ++ H) ++ ([.neg a] ++ X ++ V))

/-- Rotate the source to expose the negative occurrence of `a` first. -/
@[reducible]
def rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeSource a X V H

/-- The target is cyclically `a H a⁻¹ V X`, so `V` has crossed the separating word `X`. -/
@[reducible]
def target {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Dyck.negativeTarget a X V H

theorem source_isRotated_rotatedSource {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (source a H X V).boundary 0 |>.IsRotated
      ((rotatedSource a H X V).boundary 0) := by
  simp only [source, rotatedSource, Dyck.negativeSource,
    Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := [SignedDart.pos a] ++ H)
      (l' := [SignedDart.neg a] ++ X ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- The target spelling displays the moved block immediately after the loop. -/
theorem target_boundary_isRotated_grouped {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n))) :
    (target a H X V).boundary 0 |>.IsRotated
      ([.pos a] ++ H ++ [.neg a] ++ V ++ X) := by
  simp only [target, Dyck.negativeTarget, Dyck.oneFace_boundary_zero]
  convert
    (List.isRotated_append
      (l := X)
      (l' := [SignedDart.pos a] ++ H ++
        [SignedDart.neg a] ++ V)) using 1
  all_goals simp only [List.cons_append, List.append_assoc]

/-- Gallier--Xu loop grouping is one negative Dyck rewrite after a cyclic rotation. -/
theorem normalizationEquivalent {n : ℕ} (a : Fin n)
    (H X V : List (SignedDart (Fin n)))
    (haH : a ∉ H.map edgeOfDart)
    (haX : a ∉ X.map edgeOfDart)
    (haV : a ∉ V.map edgeOfDart)
    (validSource : (source a H X V).IsSurfaceValid)
    (validTarget : (target a H X V).IsSurfaceValid) :
    NormalizationEquivalent
      ⟨source a H X V, validSource⟩
      ⟨target a H X V, validTarget⟩ := by
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated
      (source_isRotated_rotatedSource a H X V)
  let validRotatedSource : (rotatedSource a H X V).IsSurfaceValid :=
    rotation.isSurfaceValid validSource
  have hRotate :
      NormalizationEquivalent
        ⟨source a H X V, validSource⟩
        ⟨rotatedSource a H X V, validRotatedSource⟩ :=
    NormalizationEquivalent.ofSignedIso rotation
  have hDyck :
      NormalizationEquivalent
        ⟨rotatedSource a H X V, validRotatedSource⟩
        ⟨target a H X V, validTarget⟩ :=
    Dyck.negativeNormalizationEquivalent a X V H
      haX haV haH validRotatedSource validTarget
  exact hRotate.trans hDyck

end LoopGrouping

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
