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

/-! ### Deleting a selected edge name -/

/-- The edge count after deleting one selected edge. -/
def edgeCountAfterDelete
    (P : FiniteCyclicPresentation) : ℕ :=
  P.edgeCount - 1

theorem edgeCountAfterDelete_add_one
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeCountAfterDelete P + 1 = P.edgeCount := by
  have hpositive : 0 < P.edgeCount := Nat.zero_lt_of_lt e.isLt
  exact Nat.sub_add_cancel hpositive

/-- Rename an arbitrary selected edge to the last position of the one-larger edge type. -/
def edgeToLast
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    P.Edge ≃ Fin (edgeCountAfterDelete P + 1) := by
  let castCount :
      P.Edge ≃ Fin (edgeCountAfterDelete P + 1) :=
    finCongr (edgeCountAfterDelete_add_one P e).symm
  exact castCount.trans (Cancellation.moveToLast (castCount e))

@[simp]
theorem edgeToLast_selected
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    edgeToLast P e e =
      P1.freshEdge (edgeCountAfterDelete P) := by
  simp [edgeToLast, Cancellation.moveToLast, P1.freshEdge]

/-- Rename a word after moving the selected edge to the fresh-last index. -/
def renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P + 1))) :=
  word.map (SignedDart.mapEquiv (edgeToLast P e))

/-- Contract the now-unused last edge name from a renamed word. -/
def lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart) :
    List (SignedDart (Fin (edgeCountAfterDelete P))) :=
  P1.contractWord (renamedTail P e word)

theorem freshEdge_not_mem_renamedTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P1.freshEdge (edgeCountAfterDelete P) ∉
      (renamedTail P e word).map edgeOfDart := by
  intro hfresh
  rcases List.mem_map.mp hfresh with ⟨d, hd, hedge⟩
  rcases List.mem_map.mp hd with ⟨old, hold, rfl⟩
  rw [edgeOfDart_mapEquiv] at hedge
  have holdEdge : edgeOfDart old = e := by
    apply (edgeToLast P e).injective
    rw [hedge, edgeToLast_selected]
  exact he (List.mem_map.mpr ⟨old, hold, holdEdge⟩)

/-- Lowering and re-embedding a renamed word which avoids the selected edge recovers that exact
renamed word. -/
theorem retainWord_lowerTail
    (P : FiniteCyclicPresentation) (e : P.Edge)
    (word : List P.Dart)
    (he : e ∉ word.map edgeOfDart) :
    P2.retainWord (lowerTail P e word) =
      renamedTail P e word :=
  Cancellation.retainWord_contractWord_of_fresh_not_mem
    (renamedTail P e word)
    (freshEdge_not_mem_renamedTail P e word he)

/-! ### Moving a selected face pair to the endpoints -/

/-- The last face index, using an existing face to certify nonemptiness. -/
def lastFace
    (P : FiniteCyclicPresentation) (f : P.Face) :
    P.Face :=
  ⟨P.faces.length - 1, by
    have hf := f.isLt
    omega⟩

/-- Move `f` to index zero and a distinct `g` to the final index. -/
def faceToEndpoints
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    P.Face ≃ P.Face :=
  let moveFirst :=
    Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  moveFirst.trans (Equiv.swap (moveFirst g) (lastFace P f))

@[simp]
theorem faceToEndpoints_selected
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    faceToEndpoints P f g f =
      ⟨0, Nat.zero_lt_of_lt f.isLt⟩ := by
  let zero : P.Face := ⟨0, Nat.zero_lt_of_lt f.isLt⟩
  let moveFirst := Equiv.swap f zero
  have hgf : moveFirst g ≠ moveFirst f := by
    intro h
    exact hfg (moveFirst.injective h.symm)
  have hgzero : moveFirst g ≠ zero := by
    simpa [moveFirst] using hgf
  have hvalues : f.val ≠ g.val := by
    exact fun h ↦ hfg (Fin.ext h)
  have hmany : 1 < P.faces.length := by
    omega
  have hlastZero : lastFace P f ≠ zero := by
    intro h
    have hval := congrArg Fin.val h
    change P.faces.length - 1 = 0 at hval
    omega
  change
    (Equiv.swap (moveFirst g) (lastFace P f)) (moveFirst f) =
      zero
  rw [show moveFirst f = zero by simp [moveFirst]]
  exact Equiv.swap_apply_of_ne_of_ne hgzero.symm hlastZero.symm

@[simp]
theorem faceToEndpoints_right
    (P : FiniteCyclicPresentation) (f g : P.Face) :
    faceToEndpoints P f g g = lastFace P f := by
  change
    (Equiv.swap
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g)
      (lastFace P f))
      ((Equiv.swap f ⟨0, Nat.zero_lt_of_lt f.isLt⟩) g) =
        lastFace P f
  exact Equiv.swap_apply_left _ _

/-- Number of untouched faces after selecting two distinct endpoints. -/
def faceCountBetween
    (P : FiniteCyclicPresentation) : ℕ :=
  P.faces.length - 2

/-- The `i`th interior position between zero and the final face index. -/
def middleFacePosition
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  ⟨i.val + 1, by
    have hvalues : f.val ≠ g.val :=
      fun h ↦ hfg (Fin.ext h)
    have hmany : 1 < P.faces.length := by
      omega
    have hi := i.isLt
    change i.val < P.faces.length - 2 at hi
    change i.val + 1 < P.faces.length
    omega⟩

/-- The original face occupying an interior position after moving the selected pair to the
endpoints. -/
def middleOriginalFace
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) (i : Fin (faceCountBetween P)) :
    P.Face :=
  (faceToEndpoints P f g).symm
    (middleFacePosition P f g hfg i)

/-- Enumerate the original faces not selected as endpoints, in their transported order. -/
def middleOriginalFaces
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    List P.Face :=
  List.ofFn (middleOriginalFace P f g hfg)

@[simp]
theorem middleOriginalFaces_length
    (P : FiniteCyclicPresentation) (f g : P.Face)
    (hfg : f ≠ g) :
    (middleOriginalFaces P f g hfg).length =
      faceCountBetween P := by
  simp [middleOriginalFaces]

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
