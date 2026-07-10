/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.Anchors
import ClassificationOfSurfaces.Moise.ChartInduction
import ClassificationOfSurfaces.Triangulation
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
