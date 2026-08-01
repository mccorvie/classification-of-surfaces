import Schoenflies.TrimmedHairCrosscuts

/-!
# Extracting finite broken lines from canonical PL subpaths

The Chapter 6 parameterization of a resolved broken line traverses its
ordered polygonal carrier from start to finish.  This file exposes the
monotone scalar coordinate of that traversal.  It is the key input for
turning the hair-trimmed subpaths of Moise 9.5 back into explicit finite
broken-line data.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace SimpleBrokenLine

variable {J : JordanCircle} {U : Set Plane} {p q : Plane}

/-- The ordered real coordinate along the resolved carrier, evaluated on
the canonical path of a simple broken line. -/
noncomputable def pathScalar (B : SimpleBrokenLine U p q) (hne : p ≠ q)
    (t : unitInterval) : ℝ :=
  B.data.resolvedGlobalParameter (B.toPath hne t)

private theorem resolvedGlobalParameter_continuousOn
    (B : SimpleBrokenLine U p q) :
    ContinuousOn B.data.resolvedGlobalParameter B.data.resolvedCarrier := by
  have hpl : IsPLOn B.data.resolvedComplex B.data.resolvedStraighten :=
    ⟨B.data.resolvedComplex, PlaneComplex.Subdivides.refl _,
      B.data.resolvedStraighten_affineOn_faces⟩
  have hstraight : ContinuousOn B.data.resolvedStraighten
      B.data.resolvedCarrier := by
    rw [← B.data.resolvedComplex_support]
    exact hpl.continuousOn
  have hcoord : B.data.resolvedGlobalParameter =
      fun x => B.data.resolvedStraighten x 0 := by
    funext x
    rfl
  rw [hcoord]
  have heval : Continuous fun v : Plane => v 0 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)
  exact heval.continuousOn.comp hstraight (fun _ _ => mem_univ _)

theorem continuous_pathScalar (B : SimpleBrokenLine U p q) (hne : p ≠ q) :
    Continuous (B.pathScalar hne) := by
  rw [← continuousOn_univ]
  apply B.resolvedGlobalParameter_continuousOn.comp
    (B.toPath hne).continuous.continuousOn
  intro t _
  rw [← B.range_toPath hne]
  exact ⟨t, rfl⟩

theorem pathScalar_zero (B : SimpleBrokenLine U p q) (hne : p ≠ q) :
    B.pathScalar hne 0 = 0 := by
  have hstart : B.toPath hne 0 = B.data.resolvedVertex 0 := by
    calc
      B.toPath hne 0 = p := (B.toPath hne).source
      _ = B.data.start := B.start_eq.symm
      _ = B.data.resolvedVertex 0 := B.data.resolvedVertex_start.symm
  rw [pathScalar, hstart, B.data.resolvedGlobalParameter_start]

theorem pathScalar_one (B : SimpleBrokenLine U p q) (hne : p ≠ q) :
    B.pathScalar hne 1 = B.data.resolvedWalk.length := by
  have hfinish : B.toPath hne 1 =
      B.data.resolvedVertex (Fin.last B.data.resolvedWalk.length) := by
    calc
      B.toPath hne 1 = q := (B.toPath hne).target
      _ = B.data.finish := B.finish_eq.symm
      _ = B.data.resolvedVertex (Fin.last B.data.resolvedWalk.length) :=
        B.data.resolvedVertex_finish.symm
  rw [pathScalar, hfinish, B.data.resolvedGlobalParameter_finish]

/-- The canonical path follows the intrinsic ordering of the resolved
polygonal carrier. -/
theorem strictMono_pathScalar (B : SimpleBrokenLine U p q) (hne : p ≠ q) :
    StrictMono (B.pathScalar hne) := by
  have hinj : Injective (B.pathScalar hne) := by
    intro s t hst
    apply B.toPath_injective hne
    apply B.data.resolvedGlobalParameter_injectiveOn
    · rw [← B.range_toPath hne]
      exact ⟨s, rfl⟩
    · rw [← B.range_toPath hne]
      exact ⟨t, rfl⟩
    exact hst
  rcases (B.continuous_pathScalar hne).strictMono_of_inj hinj with hmono | hanti
  · exact hmono
  · exfalso
    have hbad := hanti (show (0 : unitInterval) < 1 by norm_num)
    rw [B.pathScalar_zero hne, B.pathScalar_one hne] at hbad
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hbad

/-- A trimmed subpath of the canonical polygonal parameterization is exactly
the portion of the resolved carrier between the scalar coordinates of its
two endpoints.  This is the order-theoretic form used to extract a finite
broken line from the trimmed path. -/
theorem mem_range_hairTrimmedPath_iff
    (B : SimpleBrokenLine U p q) (hne : p ≠ q)
    {rbase lbase : Plane}
    {HR : J.InsideAccessHair rbase} {HL : J.InsideAccessHair lbase}
    (T : Path.HairTrimData (B.toPath hne) HR HL) (x : Plane) :
    x ∈ range T.trimmedPath ↔
      x ∈ B.data.resolvedCarrier ∧
        B.pathScalar hne T.rightTime ≤
          B.data.resolvedGlobalParameter x ∧
        B.data.resolvedGlobalParameter x ≤
          B.pathScalar hne T.leftTime := by
  constructor
  · intro hx
    unfold Path.HairTrimData.trimmedPath at hx
    rw [Path.range_subpath_of_le (B.toPath hne) T.rightTime T.leftTime
      T.right_lt_left.le] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · rw [← B.range_toPath hne]
      exact ⟨t, rfl⟩
    · exact (B.strictMono_pathScalar hne).monotone ht.1
    · exact (B.strictMono_pathScalar hne).monotone ht.2
  · rintro ⟨hxCarrier, hxLower, hxUpper⟩
    rw [← B.range_toPath hne] at hxCarrier
    obtain ⟨t, rfl⟩ := hxCarrier
    have hright : T.rightTime ≤ t :=
      (B.strictMono_pathScalar hne).le_iff_le.mp hxLower
    have hleft : t ≤ T.leftTime :=
      (B.strictMono_pathScalar hne).le_iff_le.mp hxUpper
    unfold Path.HairTrimData.trimmedPath
    rw [Path.range_subpath_of_le (B.toPath hne) T.rightTime T.leftTime
      T.right_lt_left.le]
    exact ⟨t, ⟨hright, hleft⟩, rfl⟩

/-- Set-level version of `mem_range_hairTrimmedPath_iff`. -/
theorem range_hairTrimmedPath
    (B : SimpleBrokenLine U p q) (hne : p ≠ q)
    {rbase lbase : Plane}
    {HR : J.InsideAccessHair rbase} {HL : J.InsideAccessHair lbase}
    (T : Path.HairTrimData (B.toPath hne) HR HL) :
    range T.trimmedPath =
      {x | x ∈ B.data.resolvedCarrier ∧
        B.pathScalar hne T.rightTime ≤
          B.data.resolvedGlobalParameter x ∧
        B.data.resolvedGlobalParameter x ≤
          B.pathScalar hne T.leftTime} := by
  ext x
  exact B.mem_range_hairTrimmedPath_iff hne T x

end SimpleBrokenLine
end JordanCircle

end Schoenflies
