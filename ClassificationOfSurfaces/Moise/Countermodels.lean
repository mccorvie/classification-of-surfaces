/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.Anchors
import ClassificationOfSurfaces.Moise.IntrinsicCloseCellwiseExtension
import ClassificationOfSurfaces.Moise.ChartInduction
import ClassificationOfSurfaces.CellComplex
import Mathlib.Topology.Instances.Rat

/-!
# Countermodels and semantic anchors

This file is the executable half of the Definition Faithfulness rules in
`docs/AUTOFORMALIZATION_GUIDE.md`.  It must stay in the default build target: if a definition is
weakened until junk witnesses satisfy it, something in this file stops compiling (or a negation
in this file becomes provable *and* its positive counterpart does too, which the trivial-closure
review catches).

Contents:

* positive anchor: the standard 2-simplex carries a geometric triangulation with one face;
* must-imply anchors are proved at the definition site
  (`GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`);
* non-examples: `ℝ` and `ℚ` admit no geometric triangulation;
* cell-complex non-examples: an unused dart orbit and disconnected face systems;
* a record of the vacuity failure of the retiring `SurfaceTriangulable` predicate, kept as
  documentation of why `GeometricTriangulation` replaces it (see `docs/KNOWN_WEAK.md`).
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Countermodels

/-! ## Positive anchor -/

/-- The one-face complex on three vertices realizes exactly the standard 2-simplex. -/
theorem geometricRealization_single_face :
    GeometricRealization (Fin 3) {Finset.univ} = stdSimplex ℝ (Fin 3) := by
  ext x
  simp [GeometricRealization]

/-- The standard 2-simplex carries a geometric triangulation with a single face. -/
noncomputable def stdSimplexTriangulation :
    GeometricTriangulation (stdSimplex ℝ (Fin 3)) where
  Vertex := Fin 3
  faces := {Finset.univ}
  faces_card := by
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    simp
  homeo := Homeomorph.setCongr geometricRealization_single_face

/-! ## Non-examples

A faithful notion of finite triangulation must fail for non-compact spaces.  The previous
`SurfaceTriangulable` predicate passed both of these with the empty triangulation. -/

example : ¬ Nonempty (GeometricTriangulation ℝ) := by
  rintro ⟨T⟩
  have hcompact := T.compactSpace
  exact not_compactSpace_iff.mpr inferInstance hcompact

example : ¬ Nonempty (GeometricTriangulation ℚ) := by
  rintro ⟨T⟩
  have hcompact := T.compactSpace
  exact not_compactSpace_iff.mpr inferInstance hcompact

/-! ## Cell-complex incidence countermodels -/

open SurfaceCellComplex.SignedDart

/-- A one-face presentation with an edge orbit omitted from every boundary word. -/
def unusedDartOrbit : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation PUnit []

/-- Incidence validity rejects an edge orbit with zero boundary occurrences. -/
theorem unusedDartOrbit_not_isSurfaceValid :
    ¬ unusedDartOrbit.IsSurfaceValid := by
  rintro ⟨_, _, _, hedges⟩
  rcases hedges (pos PUnit.unit) with hone | htwo
  · rcases hone with ⟨⟨f, i⟩, _⟩
    cases f
    exact Fin.elim0 i
  · rcases htwo with ⟨⟨f, i⟩, _⟩
    cases f
    exact Fin.elim0 i

/-- Two otherwise plausible one-edge faces sharing only a stored vertex, but no edge orbit. -/
def disconnectedBoundaryFaces : SurfaceCellComplex where
  Face := Bool
  Dart := SurfaceCellComplex.SignedDart Bool
  Vertex := PUnit
  realization := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  realizationTop := inferInstance
  inv := SurfaceCellComplex.SignedDart.flipEquiv Bool
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun f => [pos f]
  inv_involutive := SurfaceCellComplex.SignedDart.flip_flip
  inv_source := by intro d; rfl
  inv_target := by intro d; rfl

/-- The disconnected fixture is locally valid: each of its two edge orbits occurs exactly once. -/
theorem disconnectedBoundaryFaces_isSurfaceValid :
    disconnectedBoundaryFaces.IsSurfaceValid := by
  refine ⟨⟨false⟩, ?_, ?_, ?_⟩
  · intro f g h
    change [pos f] ~r [pos g] at h
    have hmem : pos f ∈ [pos g] := h.mem_iff.mp (by simp)
    exact SurfaceCellComplex.SignedDart.pos.inj (List.mem_singleton.mp hmem)
  · intro d
    cases d with
    | pos b =>
        change neg b ≠ pos b
        intro h
        cases h
    | neg b =>
        change pos b ≠ neg b
        intro h
        cases h
  · intro d
    left
    cases d with
    | pos b =>
        let o : disconnectedBoundaryFaces.BoundaryOccurrence :=
          ⟨b, ⟨0, by simp [disconnectedBoundaryFaces]⟩⟩
        refine ⟨o, Or.inl rfl, ?_⟩
        rintro ⟨f, i⟩ hi
        have hfb : f = b := by
          have hi' : f = b ∨
              pos f = disconnectedBoundaryFaces.inv (pos b) := by
            simpa [SurfaceCellComplex.Occurs, SurfaceCellComplex.SameEdge,
              SurfaceCellComplex.BoundaryOccurrence.dart, disconnectedBoundaryFaces] using hi
          rcases hi' with hi' | hi'
          · exact hi'
          · change pos f = neg b at hi'
            cases hi'
        cases hfb
        dsimp [o]
        apply Sigma.ext_iff.mpr
        refine ⟨rfl, heq_of_eq ?_⟩
        change Fin 1 at i
        exact Fin.eq_zero i
    | neg b =>
        let o : disconnectedBoundaryFaces.BoundaryOccurrence :=
          ⟨b, ⟨0, by simp [disconnectedBoundaryFaces]⟩⟩
        refine ⟨o, Or.inr rfl, ?_⟩
        rintro ⟨f, i⟩ hi
        have hfb : f = b := by
          have hi' : pos f = disconnectedBoundaryFaces.inv (neg b) := by
            simpa [SurfaceCellComplex.Occurs, SurfaceCellComplex.SameEdge,
              SurfaceCellComplex.BoundaryOccurrence.dart, disconnectedBoundaryFaces] using hi
          change pos f = pos b at hi'
          exact SurfaceCellComplex.SignedDart.pos.inj hi'
        cases hfb
        dsimp [o]
        apply Sigma.ext_iff.mpr
        refine ⟨rfl, heq_of_eq ?_⟩
        change Fin 1 at i
        exact Fin.eq_zero i

/-- Face-edge connectedness rejects two face systems even when the stored vertex type is a point. -/
theorem disconnectedBoundaryFaces_not_isConnected :
    ¬ disconnectedBoundaryFaces.IsConnected := by
  rintro ⟨_, hconnected⟩
  have adjacent_eq :
      ∀ f g, disconnectedBoundaryFaces.FaceAdjacent f g → f = g := by
    intro f g h
    rcases h with ⟨d, hd, e, he, hsame⟩
    have hd' : d = pos f := List.mem_singleton.mp hd
    have he' : e = pos g := List.mem_singleton.mp he
    subst d
    subst e
    rcases hsame with hsame | hsame
    · exact (SurfaceCellComplex.SignedDart.pos.inj hsame).symm
    · change pos g = neg f at hsame
      cases hsame
  have reach_eq : ∀ {f g},
      Relation.ReflTransGen disconnectedBoundaryFaces.FaceAdjacent f g → f = g := by
    intro f g h
    induction h with
    | refl => rfl
    | tail _hfg hgh ih => exact ih.trans (adjacent_eq _ _ hgh)
  exact Bool.false_ne_true (reach_eq (hconnected false true))

/-! ## Vacuity record

The legacy predicate `SurfaceTriangulable` was satisfied by **every** topological space via the
empty triangulation, because its `realization` field was arbitrary and unlinked to the
combinatorial data.  The predicate and the machine-checked vacuity proof were deleted together
(per the Definition Faithfulness rules); the proof is preserved in git history on the commit that
introduced this file.  If you find yourself able to write such a proof for
`GeometricTriangulation`, the definition has been broken. -/

end Countermodels
end ClassificationOfSurfaces
end Topology
end LeanEval
