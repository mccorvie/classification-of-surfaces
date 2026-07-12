/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.PolygonalJordan
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Positive anchors for the Moise plane structures

Concrete instances required by the definition-faithfulness rules
(`docs/AUTOFORMALIZATION_GUIDE.md`): the standard triangle with vertices `(0,0)`, `(1,0)`,
`(0,1)` realizes

* a `PolygonalCircle` (`standardTriangleCircle`): its boundary as a polygonal simple closed
  curve with three vertices and three edges; and
* a `PlaneComplex` (`standardTrianglePlaneComplex`): the full simplicial complex of the closed
  triangle, with three vertices, three edges and one 2-face (all seven nonempty vertex subsets).

Both geometric side conditions (`consecutive_inter`, `face_inter`) reduce to
`AffineIndependent.convexHull_inter`: convex hulls of subfamilies of an affinely independent
family intersect in the hull of the shared vertices.  The only genuinely geometric input is the
affine independence of the three vertices, proved from non-collinearity by coordinate
computation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The vertices of the standard triangle: `(0,0)`, `(1,0)`, `(0,1)`. -/
def standardTriangleVertex : Fin 3 → Plane :=
  ![!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]]

/-- The vertices of the standard triangle are not collinear. -/
theorem standardTriangle_not_collinear :
    ¬ Collinear ℝ ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(0 : ℝ), 1]} : Set Plane) := by
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert _ _)).mp hcol
  obtain ⟨rB, hB⟩ := hv !₂[(1 : ℝ), 0] (by simp)
  obtain ⟨rC, hC⟩ := hv !₂[(0 : ℝ), 1] (by simp)
  have hB0 := congrArg (fun p : Plane => p 0) hB
  have hC0 := congrArg (fun p : Plane => p 0) hC
  have hC1 := congrArg (fun p : Plane => p 1) hC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_zero] at hB0 hC0 hC1
  rcases mul_eq_zero.mp hC0.symm with h | h
  · rw [h, zero_mul] at hC1
    exact one_ne_zero hC1
  · rw [h, mul_zero] at hB0
    exact one_ne_zero hB0

/-- The vertices of the standard triangle are affinely independent. -/
theorem standardTriangleVertex_affineIndependent :
    AffineIndependent ℝ standardTriangleVertex :=
  affineIndependent_iff_not_collinear_set.mpr standardTriangle_not_collinear

theorem standardTriangleVertex_injective :
    Function.Injective standardTriangleVertex :=
  standardTriangleVertex_affineIndependent.injective

/-- Any relabelling of the standard triangle vertices by an injective index vector is affinely
independent. -/
theorem standardTriangleVertex_triple_affineIndependent (a b c : Fin 3)
    (h : Function.Injective ![a, b, c]) :
    AffineIndependent ℝ
      ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c] := by
  have he : ![standardTriangleVertex a, standardTriangleVertex b, standardTriangleVertex c]
      = standardTriangleVertex ∘ ![a, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [he]
  exact standardTriangleVertex_affineIndependent.comp_embedding ⟨![a, b, c], h⟩

/-- **Positive anchor** for `PolygonalCircle`: the boundary of the standard triangle with
vertices `(0,0)`, `(1,0)`, `(0,1)` is a polygonal simple closed curve. -/
def standardTriangleCircle : PolygonalCircle where
  n := 3
  three_le := le_rfl
  vertex := standardTriangleVertex
  adjacent_ne := fun i =>
    standardTriangleVertex_injective.ne ((by decide : ∀ j : ZMod 3, j ≠ j + 1) i)
  consecutive_inter := by
    intro i
    have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases hcase with rfl | rfl | rfl
    · rw [show (0 : ZMod 3) + 1 = 1 by decide, show (0 : ZMod 3) + 2 = 2 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 0 1 2 (by decide))
    · rw [show (1 : ZMod 3) + 1 = 2 by decide, show (1 : ZMod 3) + 2 = 0 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 1 2 0 (by decide))
    · rw [show (2 : ZMod 3) + 1 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]
      exact segment_inter_segment_of_affineIndependent
        (standardTriangleVertex_triple_affineIndependent 2 0 1 (by decide))
  nonadjacent_disjoint := fun i j h₁ h₂ h₃ =>
    absurd ((by decide : ∀ i j : ZMod 3, i ≠ j → i ≠ j + 1 → j = i + 1) i j h₁ h₂) h₃

/-- **Positive anchor** for `PlaneComplex`: the closed standard triangle as a simplicial
complex, with the seven nonempty subsets of its three vertices as faces. -/
noncomputable def standardTrianglePlaneComplex : PlaneComplex where
  Vertex := Fin 3
  position := standardTriangleVertex
  position_injective := standardTriangleVertex_injective
  simplexes := Finset.univ.powerset.filter (·.Nonempty)
  nonempty_of_mem := fun _ hs => (Finset.mem_filter.mp hs).2
  card_le_three := by decide
  down_closed := by decide
  affineIndependent := fun s _ =>
    standardTriangleVertex_affineIndependent.comp_embedding (Function.Embedding.subtype _)
  face_inter := by
    intro s _ t _
    classical
    have hS : AffineIndependent ℝ
        ((↑) : (Finset.univ.image standardTriangleVertex) → Plane) :=
      affineIndependent_finset_coe standardTriangleVertex_affineIndependent fun a ha => by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        exact ⟨i, hi⟩
    have hmain := hS.convexHull_inter
      (t₁ := s.image standardTriangleVertex) (t₂ := t.image standardTriangleVertex)
      (Finset.image_subset_image (Finset.subset_univ s))
      (Finset.image_subset_image (Finset.subset_univ t))
    rw [← Finset.coe_inter, ← Finset.image_inter s t standardTriangleVertex_injective] at hmain
    simpa [Finset.coe_image] using hmain.symm

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
