/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.FiniteCyclicNormalizationResult

/-!
# Combinatorial selections for finite-cyclic reduction

This file supplies the finite graph and cyclic-list selections used by the recursive
Gallier--Xu normalization.  In particular, connected presentations with more than one face expose
a genuinely adjacent pair, and either occurrence of their common edge can be placed at the head
of a suitably oriented cyclic boundary.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace Reduction

/-- A nontrivial reflexive-transitive path contains a genuinely non-reflexive step. -/
theorem exists_ne_step_of_reflTransGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) (hne : a ≠ b) :
    ∃ x y, r x y ∧ x ≠ y := by
  induction h with
  | refl =>
      exact (hne rfl).elim
  | @tail b c hab hbc ih =>
      by_cases hbcne : b ≠ c
      · exact ⟨b, c, hbc, hbcne⟩
      · have hbcEq : b = c := not_ne_iff.mp hbcne
        subst c
        exact ih hne

/-- Face adjacency is symmetric. -/
theorem faceAdjacent_comm
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.FaceAdjacent f g ↔ P.FaceAdjacent g f := by
  constructor
  · rintro ⟨e, hef, heg⟩
    exact ⟨e, heg, hef⟩
  · rintro ⟨e, heg, hef⟩
    exact ⟨e, hef, heg⟩

/-- A connected presentation with at least two faces contains two distinct adjacent faces. -/
theorem exists_distinct_faceAdjacent
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ f g : P.Face, f ≠ g ∧ P.FaceAdjacent f g := by
  let f : P.Face := ⟨0, by omega⟩
  let g : P.Face := ⟨1, hmany⟩
  have hfg : f ≠ g := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 at hval
    omega
  rcases exists_ne_step_of_reflTransGen
      (connected.2 f g) hfg with
    ⟨x, y, hxy, hxyne⟩
  exact ⟨x, y, hxyne, hxy⟩

/-- Any member of a linear list can be moved to its head by a cyclic rotation. -/
theorem exists_tail_isRotated_cons_of_mem
    {α : Type*} {a : α} {word : List α}
    (ha : a ∈ word) :
    ∃ tail, word.IsRotated (a :: tail) := by
  rw [List.mem_iff_append] at ha
  rcases ha with ⟨left, right, rfl⟩
  refine ⟨right ++ left, ?_⟩
  simpa only [List.cons_append, List.append_assoc] using
    (List.isRotated_append
      (l := left) (l' := a :: right))

/-- Recover a signed occurrence from membership in the projected unoriented edge word. -/
theorem exists_dart_of_mem_map_edgeOfDart
    {α : Type*} {e : α} {word : List (SignedDart α)}
    (he : e ∈ word.map edgeOfDart) :
    ∃ d ∈ word, edgeOfDart d = e := by
  rcases List.mem_map.mp he with ⟨d, hd, hde⟩
  exact ⟨d, hd, hde⟩

/-- A common edge displayed positively at the head of an oriented cyclic face boundary. -/
structure PositiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.pos e :: tail)

/-- A common edge displayed negatively at the head of an oriented cyclic face boundary. -/
structure NegativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) where
  orientedFace : P.OrientedFace
  face_eq : orientedFace.face = f
  tail : List P.Dart
  boundary_rotated :
    (P.orientedBoundary orientedFace).IsRotated (.neg e :: tail)

/-- Choose the traversal orientation which displays a selected edge occurrence positively. -/
theorem exists_positiveOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (PositiveOccurrence P f e) := by
  rcases exists_dart_of_mem_map_edgeOfDart he with
    ⟨d, hd, hde⟩
  cases d with
  | pos a =>
      change a = e at hde
      subst e
      rcases exists_tail_isRotated_cons_of_mem hd with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, false⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩
  | neg a =>
      change a = e at hde
      subst e
      have hpositive :
          SignedDart.pos a ∈ inverseWord (P.boundary f) := by
        rw [inverseWord]
        exact List.mem_map.mpr
          ⟨.neg a, by simpa using hd, rfl⟩
      rcases exists_tail_isRotated_cons_of_mem hpositive with
        ⟨tail, hrotated⟩
      exact ⟨
        { orientedFace := ⟨f, true⟩
          face_eq := rfl
          tail := tail
          boundary_rotated := by
            simpa [FiniteCyclicPresentation.orientedBoundary] using
              hrotated }⟩

/-- Reverse a positive displayed occurrence to obtain a negative displayed occurrence. -/
def PositiveOccurrence.flip
    {P : FiniteCyclicPresentation} {f : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e) :
    NegativeOccurrence P f e where
  orientedFace := occurrence.orientedFace.flip
  face_eq := occurrence.face_eq
  tail := inverseWord occurrence.tail
  boundary_rotated := by
    rw [P.orientedBoundary_flip]
    have hhead :
        (inverseWord (.pos e :: occurrence.tail)).IsRotated
          (.neg e :: inverseWord occurrence.tail) := by
      simpa [inverseWord, SignedDart.flip] using
        (List.isRotated_concat (.neg e) (inverseWord occurrence.tail))
    exact
      (inverseWord_isRotated occurrence.boundary_rotated).trans hhead

/-- Choose the traversal orientation which displays a selected edge occurrence negatively. -/
theorem exists_negativeOccurrence
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge)
    (he : e ∈ (P.boundary f).map edgeOfDart) :
    Nonempty (NegativeOccurrence P f e) := by
  rcases exists_positiveOccurrence P f e he with ⟨occurrence⟩
  exact ⟨occurrence.flip⟩

/-- A distinct adjacent pair can always be oriented with positive and negative occurrences of
the same separator displayed at the heads of its two cyclic boundaries. -/
theorem exists_oppositelyDisplayedAdjacentFaces
    (P : FiniteCyclicPresentation)
    (connected : P.IsConnected)
    (hmany : 1 < P.faces.length) :
    ∃ (f g : P.Face) (e : P.Edge),
      f ≠ g ∧
        Nonempty (PositiveOccurrence P f e) ∧
        Nonempty (NegativeOccurrence P g e) := by
  rcases exists_distinct_faceAdjacent P connected hmany with
    ⟨f, g, hfg, e, hef, heg⟩
  exact
    ⟨f, g, e, hfg,
      exists_positiveOccurrence P f e hef,
      exists_negativeOccurrence P g e heg⟩

end Reduction

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
