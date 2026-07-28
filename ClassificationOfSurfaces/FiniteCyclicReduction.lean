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

/-- Build an unoriented presentation isomorphism from equations stated using oriented source
faces and stored target faces. Reversing both sides converts this convenient input convention to
the target-oriented convention of `UnorientedPresentationIso`. -/
def unorientedIsoOfOrientedBoundaries
    {P Q : FiniteCyclicPresentation}
    (edgeRelabeling : EdgeRelabeling P.Edge Q.Edge)
    (faceEquiv : P.Face ≃ Q.Face)
    (reverseFace : P.Face → Bool)
    (boundary_rotated :
      ∀ f,
        ((P.orientedBoundary ⟨f, reverseFace f⟩).map
          edgeRelabeling.mapDart).IsRotated
            (Q.boundary (faceEquiv f))) :
    UnorientedPresentationIso P Q where
  edgeRelabeling := edgeRelabeling
  faceEquiv := faceEquiv
  reverseFace := reverseFace
  boundary_rotated := by
    intro f
    cases hreverse : reverseFace f with
    | false =>
        simpa [FiniteCyclicPresentation.orientedBoundary, hreverse] using
          boundary_rotated f
    | true =>
        have hinverse :=
          inverseWord_isRotated (boundary_rotated f)
        simpa only [FiniteCyclicPresentation.orientedBoundary,
          hreverse, if_true, inverseWord_inverseWord,
          EdgeRelabeling.inverseWord_map_mapDart] using hinverse

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

/-- The contributions of two distinct faces are bounded by the total edge multiplicity. -/
theorem add_faceEdgeMultiplicity_le_edgeMultiplicity
    (P : FiniteCyclicPresentation)
    (f g : P.Face) (e : P.Edge) (hfg : f ≠ g) :
    P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
      P.edgeMultiplicity e := by
  classical
  unfold edgeMultiplicity
  have hsubset :
      ({f, g} : Finset P.Face) ⊆ Finset.univ := by
    intro x hx
    simp
  have hsum :=
    Finset.sum_le_sum_of_subset
      (f := fun q ↦ P.faceEdgeMultiplicity q e) hsubset
  simpa [hfg] using hsum

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

/-- In two distinct incident faces, the displayed occurrence consumes the entire multiplicity
contributed by its face, so the same edge does not occur again in its tail. -/
theorem PositiveOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : PositiveOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  classical
  have hmapRotated :=
    occurrence.boundary_rotated.map edgeOfDart
  have hpositive :
      e ∈ (P.orientedBoundary occurrence.orientedFace).map edgeOfDart := by
    exact hmapRotated.mem_iff.mpr (by simp [edgeOfDart])
  have hfpos : 0 < P.faceEdgeMultiplicity f e := by
    have horiented :=
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
    rw [← occurrence.face_eq, ← horiented]
    exact List.count_pos_iff.mpr hpositive
  have hgpos : 0 < P.faceEdgeMultiplicity g e := by
    exact List.count_pos_iff.mpr heg
  have htwo :
      P.faceEdgeMultiplicity f e + P.faceEdgeMultiplicity g e ≤
        P.edgeMultiplicity e :=
    add_faceEdgeMultiplicity_le_edgeMultiplicity P f g e hfg
  have htotal := valid.2.2.2 e
  have hfaceOne : P.faceEdgeMultiplicity f e = 1 := by
    rcases htotal with htotal | htotal <;> omega
  have horientedCount :
      ((P.orientedBoundary occurrence.orientedFace).map edgeOfDart).count e =
        P.faceEdgeMultiplicity f e := by
    simpa only [occurrence.face_eq] using
      P.orientedBoundary_edgeMultiplicity occurrence.orientedFace e
  have hrotatedCount := hmapRotated.perm.count_eq e
  have htailCount :
      (occurrence.tail.map edgeOfDart).count e = 0 := by
    rw [horientedCount, hfaceOne] at hrotatedCount
    simpa [edgeOfDart] using hrotatedCount.symm
  exact List.count_eq_zero.mp htailCount

/-- The corresponding no-second-occurrence statement for a negatively displayed face. -/
theorem NegativeOccurrence.edge_not_mem_tail
    {P : FiniteCyclicPresentation} {f g : P.Face} {e : P.Edge}
    (occurrence : NegativeOccurrence P f e)
    (valid : P.IsSurfaceValid)
    (hfg : f ≠ g)
    (heg : e ∈ (P.boundary g).map edgeOfDart) :
    e ∉ occurrence.tail.map edgeOfDart := by
  let positive : PositiveOccurrence P f e :=
    { orientedFace := occurrence.orientedFace.flip
      face_eq := occurrence.face_eq
      tail := inverseWord occurrence.tail
      boundary_rotated := by
        rw [P.orientedBoundary_flip]
        have hhead :
            (inverseWord (.neg e :: occurrence.tail)).IsRotated
              (.pos e :: inverseWord occurrence.tail) := by
          simpa [inverseWord, SignedDart.flip] using
            (List.isRotated_concat (.pos e) (inverseWord occurrence.tail))
        exact
          (inverseWord_isRotated occurrence.boundary_rotated).trans hhead }
  have hpositive :=
    positive.edge_not_mem_tail valid hfg heg
  simpa [positive, map_edgeOfDart_inverseWord] using hpositive

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
