/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplexQuotient
import ClassificationOfSurfaces.Representatives

/-!
# Canonical normal-form boundary words

This file gives finite signed-dart presentations for the orientable and nonorientable boundary
words encoded by the vendored `OrientableRel` and `NonOrientableRel`. It records their exact
lengths and edge multiplicities, then packages them as connected, incidence-valid one-face cell
complexes.

For Eval-admissible parameters, the words are nonempty and therefore also satisfy
`SurfaceCellComplex.OccurrencePairingValid`. These are combinatorial and polygonal-pairing
certificates only: no claim is made about the arbitrary stored `SurfaceCellComplex.Realization`.
The remaining topological step is to compare their faithful polygonal realizations with the
closed-disc quotients defined in `LeanEval/ChallengeDeps.lean`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

/-- Counting boundary positions by edge name agrees with counting the edge names in the word. -/
theorem wordEdgeOccurrences_card_eq_count_edgeName
    {Edge : Type} [DecidableEq Edge]
    (word : List (SignedDart Edge)) (e : Edge) :
    (wordEdgeOccurrences word e).card =
      (word.map SignedDart.edgeName).count e := by
  let v : List.Vector (SignedDart Edge) word.length := ⟨word, rfl⟩
  simpa [wordEdgeOccurrences, v, List.Vector.get, List.Vector.map, List.Vector.toList] using
    (Fin.card_filter_univ_eq_vector_get_eq_count e
      (v.map SignedDart.edgeName))

end SurfaceCellComplex

namespace NormalForm

open SurfaceCellComplex

/-- Edge names in the canonical orientable normal-form word. -/
inductive OrientableEdge (p n : ℕ)
  | a : Fin p → OrientableEdge p n
  | b : Fin p → OrientableEdge p n
  | c : Fin n → OrientableEdge p n
  | h : Fin n → OrientableEdge p n
  deriving DecidableEq, Repr, Fintype

/-- Edge names in the canonical nonorientable normal-form word. -/
inductive NonOrientableEdge (p n : ℕ)
  | a : Fin p → NonOrientableEdge p n
  | c : Fin n → NonOrientableEdge p n
  | h : Fin n → NonOrientableEdge p n
  deriving DecidableEq, Repr, Fintype

/-- The commutator block `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹`. -/
def orientableHandleBlock {p n : ℕ} (i : Fin p) :
    List (SignedDart (OrientableEdge p n)) :=
  [.pos (.a i), .pos (.b i), .neg (.a i), .neg (.b i)]

/-- The boundary block `cᵢ hᵢ cᵢ⁻¹` in the orientable word. -/
def orientableBoundaryBlock {p n : ℕ} (i : Fin n) :
    List (SignedDart (OrientableEdge p n)) :=
  [.pos (.c i), .pos (.h i), .neg (.c i)]

/-- The square block `aᵢ aᵢ` in the nonorientable word. -/
def nonOrientableCrosscapBlock {p n : ℕ} (i : Fin p) :
    List (SignedDart (NonOrientableEdge p n)) :=
  [.pos (.a i), .pos (.a i)]

/-- The boundary block `cᵢ hᵢ cᵢ⁻¹` in the nonorientable word. -/
def nonOrientableBoundaryBlock {p n : ℕ} (i : Fin n) :
    List (SignedDart (NonOrientableEdge p n)) :=
  [.pos (.c i), .pos (.h i), .neg (.c i)]

/-- The canonical orientable signed boundary word. -/
def orientableBoundaryWord (p n : ℕ) : List (SignedDart (OrientableEdge p n)) :=
  (List.ofFn (fun i : Fin p ↦ orientableHandleBlock (n := n) i)).flatten ++
    (List.ofFn (fun i : Fin n ↦ orientableBoundaryBlock (p := p) i)).flatten

/-- The canonical nonorientable signed boundary word. -/
def nonOrientableBoundaryWord (p n : ℕ) :
    List (SignedDart (NonOrientableEdge p n)) :=
  (List.ofFn (fun i : Fin p ↦ nonOrientableCrosscapBlock (n := n) i)).flatten ++
    (List.ofFn (fun i : Fin n ↦ nonOrientableBoundaryBlock (p := p) i)).flatten

theorem orientableBoundaryWord_length (p n : ℕ) :
    (orientableBoundaryWord p n).length = 4 * p + 3 * n := by
  simp [orientableBoundaryWord, orientableHandleBlock, orientableBoundaryBlock, List.sum_ofFn,
    Nat.mul_comm]

theorem nonOrientableBoundaryWord_length (p n : ℕ) :
    (nonOrientableBoundaryWord p n).length = 2 * p + 3 * n := by
  simp [nonOrientableBoundaryWord, nonOrientableCrosscapBlock, nonOrientableBoundaryBlock,
    List.sum_ofFn, Nat.mul_comm]

theorem orientableBoundaryWord_edge_occurrences (p n : ℕ) (e : OrientableEdge p n) :
    (wordEdgeOccurrences (orientableBoundaryWord p n) e).card =
      match e with
      | .a _ => 2
      | .b _ => 2
      | .c _ => 2
      | .h _ => 1 := by
  rw [wordEdgeOccurrences_card_eq_count_edgeName]
  cases e <;>
    simp [orientableBoundaryWord, orientableHandleBlock, orientableBoundaryBlock,
      SignedDart.edgeName, List.count_flatten, List.sum_ofFn, List.count_cons,
      List.count_nil, beq_iff_eq, Finset.sum_add_distrib]

theorem nonOrientableBoundaryWord_edge_occurrences (p n : ℕ)
    (e : NonOrientableEdge p n) :
    (wordEdgeOccurrences (nonOrientableBoundaryWord p n) e).card =
      match e with
      | .a _ => 2
      | .c _ => 2
      | .h _ => 1 := by
  rw [wordEdgeOccurrences_card_eq_count_edgeName]
  cases e <;>
    simp [nonOrientableBoundaryWord, nonOrientableCrosscapBlock,
      nonOrientableBoundaryBlock, SignedDart.edgeName, List.count_flatten, List.sum_ofFn,
      List.count_cons, List.count_nil, beq_iff_eq, Finset.sum_add_distrib]

/-- The one-face incidence presentation carried by the canonical orientable word. -/
def orientableCellComplex (p n : ℕ) : SurfaceCellComplex :=
  oneFacePresentation (OrientableEdge p n) (orientableBoundaryWord p n)

/-- The one-face incidence presentation carried by the canonical nonorientable word. -/
def nonOrientableCellComplex (p n : ℕ) : SurfaceCellComplex :=
  oneFacePresentation (NonOrientableEdge p n) (nonOrientableBoundaryWord p n)

@[simp]
theorem orientableCellComplex_boundary (p n : ℕ) :
    (orientableCellComplex p n).boundary PUnit.unit = orientableBoundaryWord p n := rfl

@[simp]
theorem nonOrientableCellComplex_boundary (p n : ℕ) :
    (nonOrientableCellComplex p n).boundary PUnit.unit =
      nonOrientableBoundaryWord p n := rfl

@[simp]
theorem orientableCellComplex_faceBoundaryLength (p n : ℕ) :
    (orientableCellComplex p n).faceBoundaryLength PUnit.unit = 4 * p + 3 * n :=
  orientableBoundaryWord_length p n

@[simp]
theorem nonOrientableCellComplex_faceBoundaryLength (p n : ℕ) :
    (nonOrientableCellComplex p n).faceBoundaryLength PUnit.unit = 2 * p + 3 * n :=
  nonOrientableBoundaryWord_length p n

theorem orientableCellComplex_isConnected (p n : ℕ) :
    (orientableCellComplex p n).IsConnected :=
  oneFacePresentation_isConnected _ _

theorem nonOrientableCellComplex_isConnected (p n : ℕ) :
    (nonOrientableCellComplex p n).IsConnected :=
  oneFacePresentation_isConnected _ _

theorem orientableCellComplex_isSurfaceValid (p n : ℕ) :
    (orientableCellComplex p n).IsSurfaceValid := by
  apply oneFacePresentation_isSurfaceValid
  intro e
  rw [orientableBoundaryWord_edge_occurrences]
  cases e <;> simp

theorem nonOrientableCellComplex_isSurfaceValid (p n : ℕ) :
    (nonOrientableCellComplex p n).IsSurfaceValid := by
  apply oneFacePresentation_isSurfaceValid
  intro e
  rw [nonOrientableBoundaryWord_edge_occurrences]
  cases e <;> simp

theorem orientableBoundaryWord_ne_nil {p n : ℕ} (h : 1 ≤ p ∨ 1 ≤ n) :
    orientableBoundaryWord p n ≠ [] := by
  intro hnil
  have hlength := orientableBoundaryWord_length p n
  rw [hnil] at hlength
  simp only [List.length_nil] at hlength
  omega

theorem nonOrientableBoundaryWord_ne_nil {p n : ℕ} (h : 1 ≤ p) :
    nonOrientableBoundaryWord p n ≠ [] := by
  intro hnil
  have hlength := nonOrientableBoundaryWord_length p n
  rw [hnil] at hlength
  simp only [List.length_nil] at hlength
  omega

theorem orientableCellComplex_occurrencePairingValid {p n : ℕ}
    (h : 1 ≤ p ∨ 1 ≤ n) :
    (orientableCellComplex p n).OccurrencePairingValid := by
  apply oneFacePresentation_occurrencePairingValid
  · exact orientableBoundaryWord_ne_nil h
  · intro e
    rw [orientableBoundaryWord_edge_occurrences]
    cases e <;> simp

theorem nonOrientableCellComplex_occurrencePairingValid {p n : ℕ}
    (h : 1 ≤ p) :
    (nonOrientableCellComplex p n).OccurrencePairingValid := by
  apply oneFacePresentation_occurrencePairingValid
  · exact nonOrientableBoundaryWord_ne_nil h
  · intro e
    rw [nonOrientableBoundaryWord_edge_occurrences]
    cases e <;> simp

/-- The canonical incidence presentation attached to a named normal form. -/
def canonicalCellComplex : NormalForm → SurfaceCellComplex
  | .sphere => SurfaceCellComplex.sphere
  | .orientable p n => orientableCellComplex p n
  | .nonOrientable p n => nonOrientableCellComplex p n

theorem canonicalCellComplex_isSurfaceValid (N : NormalForm) :
    N.canonicalCellComplex.IsSurfaceValid := by
  cases N with
  | sphere => exact SurfaceCellComplex.sphere_isSurfaceValid
  | orientable p n => exact orientableCellComplex_isSurfaceValid p n
  | nonOrientable p n => exact nonOrientableCellComplex_isSurfaceValid p n

theorem canonicalCellComplex_isConnected (N : NormalForm) :
    N.canonicalCellComplex.IsConnected := by
  cases N with
  | sphere => exact SurfaceCellComplex.sphere_isConnected
  | orientable p n => exact orientableCellComplex_isConnected p n
  | nonOrientable p n => exact nonOrientableCellComplex_isConnected p n

end NormalForm

end ClassificationOfSurfaces
end Topology
end LeanEval
