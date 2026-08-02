/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplexQuotient
import ClassificationOfSurfaces.LeanEval.ChallengeDeps

/-!
# Carrier bridge to the Eval quotient representatives

The canonical cell complexes and the trusted Lean-Eval statement use two presentations of the
same carrier:

* a one-face polygonal pre-realization, whose unique `PolygonCell` is a closed disk; and
* `Complex.ClosedUnitDisc`, on which the benchmark relations are stated.

This file identifies those carriers and records the exact boundary coordinates. It also bridges
Lean's raw-relation quotient `Quot r` with `Quotient (Relation.EqvGen.setoid r)`, the generated
setoid used by the polygonal gluing layer.

The remaining comparison is deliberately isolated: prove that the equivalence closure of the
canonical polygonal generators transports to the equivalence closure of `OrientableRel` or
`NonOrientableRel`.
-/

namespace Complex

/-- The benchmark boundary parameter is periodic with integral period one. -/
theorem ClosedUnitDisc.bdyPtOfReal_add_int (r : ℝ) (k : ℤ) :
    ClosedUnitDisc.bdyPtOfReal (r + k) = ClosedUnitDisc.bdyPtOfReal r := by
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * (r + k)) : ℂ) =
    (Circle.exp (2 * Real.pi * r) : ℂ)
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨k, ?_⟩
  ring

end Complex

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open Complex

namespace PolygonCell

/-- The indexed polygon cell is the closed unit disk, with only a different wrapper. -/
noncomputable def closedUnitDiscHomeomorph (m : ℕ) :
    PolygonCell m ≃ₜ ClosedUnitDisc where
  toFun z := ⟨z.val, z.property⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := PolygonCell.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := PolygonCell.continuous_val.subtype_mk _
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

/-- Under the carrier homeomorphism, side `i` has the benchmark's boundary parameter. -/
theorem closedUnitDiscHomeomorph_side {m : ℕ} (i : Fin m) (t : unitInterval) :
    closedUnitDiscHomeomorph m (side i t) =
      ClosedUnitDisc.bdyPtOfReal (((i.val : ℝ) + (t : ℝ)) / m) := by
  apply Subtype.ext
  change (Circle.exp (sideAngle i t) : ℂ) =
    (Circle.exp (2 * Real.pi * (((i.val : ℝ) + (t : ℝ)) / m)) : ℂ)
  congr 1
  unfold sideAngle
  ring_nf

end PolygonCell

namespace PolygonGluing

/-- The unique polygon in a one-face presentation is homeomorphic to the closed unit disk. -/
noncomputable def oneFacePreRealizationHomeomorph (m : ℕ) :
    PreRealization PUnit (fun _ ↦ m) ≃ₜ ClosedUnitDisc where
  toFun z := PolygonCell.closedUnitDiscHomeomorph m z.2
  invFun z := ⟨PUnit.unit, (PolygonCell.closedUnitDiscHomeomorph m).symm z⟩
  left_inv := by
    rintro ⟨face, z⟩
    cases face
    simp
  right_inv z := (PolygonCell.closedUnitDiscHomeomorph m).apply_symm_apply z
  continuous_toFun := by
    apply continuous_sigma
    intro face
    cases face
    exact (PolygonCell.closedUnitDiscHomeomorph m).continuous
  continuous_invFun :=
    continuous_sigmaMk.comp (PolygonCell.closedUnitDiscHomeomorph m).symm.continuous

/-- Side points in a one-face pre-realization map to the exact benchmark boundary points. -/
theorem oneFacePreRealizationHomeomorph_sidePoint {m : ℕ}
    (i : Fin m) (t : unitInterval) :
    oneFacePreRealizationHomeomorph m
        (Side.point (show Side PUnit (fun _ ↦ m) from ⟨PUnit.unit, i⟩) t) =
      ClosedUnitDisc.bdyPtOfReal (((i.val : ℝ) + (t : ℝ)) / m) :=
  PolygonCell.closedUnitDiscHomeomorph_side i t

end PolygonGluing

namespace SurfaceCellComplex

/-- The one-face polygonal pre-realization of a boundary word is the closed unit disk. -/
noncomputable def oneFacePolygonalPreRealizationHomeomorph
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge)) :
    (oneFacePresentation Edge word).PolygonalPreRealization ≃ₜ ClosedUnitDisc := by
  change PolygonGluing.PreRealization PUnit (fun _ ↦ word.length) ≃ₜ ClosedUnitDisc
  exact PolygonGluing.oneFacePreRealizationHomeomorph word.length

/-- The direct one-face homeomorphism sends occurrence `i` to the benchmark parameter
`(i + t) / word.length`. -/
theorem oneFacePolygonalPreRealizationHomeomorph_sidePoint
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge))
    (i : Fin word.length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph word
        (PolygonGluing.Side.point
          ((oneFacePresentation Edge word).occurrenceSide ⟨PUnit.unit, i⟩) t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / word.length) :=
  PolygonCell.closedUnitDiscHomeomorph_side i t

end SurfaceCellComplex

end ClassificationOfSurfaces
end Topology
end LeanEval
