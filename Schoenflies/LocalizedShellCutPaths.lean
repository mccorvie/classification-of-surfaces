import Schoenflies.LocalizedShellCrosscuts

/-!
# Embedded path form of the localized shell cuts

The point-set crosscuts constructed in `LocalizedShellCrosscuts` are straight
segments.  This file packages them as injective paths whose open parameter
interval lies in the open shell.  That is the form needed by the finite
annular cyclic-order argument.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev outerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

/-- The two endpoints of a localized shell cut lie on disjoint boundary
components. -/
theorem levelLocalizedShellCut_endpoints_ne (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedOuterBoundaryMark k a ≠
      I.levelLocalizedPolygonalBoundaryMark k a := by
  intro h
  have hInnerClosed : I.levelLocalizedOuterBoundaryMark k a ∈
      (I.innerDisk k).closedRegion := by
    rw [h, (I.innerDisk k).closedRegion_eq_union]
    exact Or.inr (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
  have hOuterInterior : I.levelLocalizedOuterBoundaryMark k a ∈
      (I.outerDisk k).interiorRegion :=
    I.localizedMarkedPolygonalDisk_strictly_nested (k + 1) hInnerClosed
  exact Set.disjoint_left.mp
    (PolygonalCircle.carrier_disjoint_interiorRegion (I.outerDisk k))
    (I.levelLocalizedOuterBoundaryMark_mem_carrier k a) hOuterInterior

/-- A retained straight shell cut, oriented from the outer polygon to the
inner polygon. -/
noncomputable def levelLocalizedShellCutPath (k : ℕ)
    (a : LevelAddress k) :
    Path (I.levelLocalizedOuterBoundaryMark k a)
      (I.levelLocalizedPolygonalBoundaryMark k a) :=
  Path.segment (I.levelLocalizedOuterBoundaryMark k a)
    (I.levelLocalizedPolygonalBoundaryMark k a)

theorem levelLocalizedShellCutPath_injective (k : ℕ)
    (a : LevelAddress k) :
    Injective (I.levelLocalizedShellCutPath k a) :=
  Path.segment_injective_of_ne
    (I.levelLocalizedShellCut_endpoints_ne k a)

theorem range_levelLocalizedShellCutPath (k : ℕ)
    (a : LevelAddress k) :
    range (I.levelLocalizedShellCutPath k a) =
      I.levelLocalizedShellCut k a := by
  unfold levelLocalizedShellCutPath levelLocalizedShellCut
  rw [Path.range_segment]

/-- Except for its outer endpoint, a shell-cut path misses the outer
polygonal boundary. -/
theorem levelLocalizedShellCutPath_not_mem_outerCarrier_of_ne_zero
    (k : ℕ) (a : LevelAddress k) {t : unitInterval}
    (ht : t ≠ 0) :
    I.levelLocalizedShellCutPath k a t ∉ (I.outerDisk k).carrier := by
  intro hCarrier
  have hCut : I.levelLocalizedShellCutPath k a t ∈
      I.levelLocalizedShellCut k a := by
    rw [← I.range_levelLocalizedShellCutPath k a]
    exact ⟨t, rfl⟩
  have hPoint := Set.mem_singleton_iff.mp <|
    (Set.ext_iff.mp (I.levelLocalizedShellCut_inter_outerCarrier k a)
      (I.levelLocalizedShellCutPath k a t)).mp ⟨hCut, hCarrier⟩
  have hZero : t = 0 :=
    I.levelLocalizedShellCutPath_injective k a <| by
      simpa only [Path.source] using hPoint
  exact ht hZero

/-- Except for its inner endpoint, a shell-cut path misses the inner
polygonal boundary. -/
theorem levelLocalizedShellCutPath_not_mem_innerCarrier_of_ne_one
    (k : ℕ) (a : LevelAddress k) {t : unitInterval}
    (ht : t ≠ 1) :
    I.levelLocalizedShellCutPath k a t ∉ (I.innerDisk k).carrier := by
  intro hCarrier
  have hCut : I.levelLocalizedShellCutPath k a t ∈
      I.levelLocalizedShellCut k a := by
    rw [← I.range_levelLocalizedShellCutPath k a]
    exact ⟨t, rfl⟩
  have hPoint := Set.mem_singleton_iff.mp <|
    (Set.ext_iff.mp (I.levelLocalizedShellCut_inter_innerCarrier k a)
      (I.levelLocalizedShellCutPath k a t)).mp ⟨hCut, hCarrier⟩
  have hOne : t = 1 :=
    I.levelLocalizedShellCutPath_injective k a <| by
      simpa only [Path.target] using hPoint
  exact ht hOne

/-- The relative interior of a retained cut lies in the open stratum of the
polygonal shell. -/
theorem levelLocalizedShellCutPath_mem_openShell
    (k : ℕ) (a : LevelAddress k) {t : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    I.levelLocalizedShellCutPath k a t ∈
      PolygonalCircle.openShell (I.innerDisk k) (I.outerDisk k) := by
  have hCut : I.levelLocalizedShellCutPath k a t ∈
      I.levelLocalizedShellCut k a := by
    rw [← I.range_levelLocalizedShellCutPath k a]
    exact ⟨t, rfl⟩
  have hClosed := I.levelLocalizedShellCut_subset_closedShell k a hCut
  change I.levelLocalizedShellCutPath k a t ∈
      (I.outerDisk k).closedRegion ∧
    I.levelLocalizedShellCutPath k a t ∉
      (I.innerDisk k).interiorRegion at hClosed
  refine ⟨?_, ?_⟩
  · rw [(I.outerDisk k).closedRegion_eq_union] at hClosed
    exact hClosed.1.resolve_right
      (I.levelLocalizedShellCutPath_not_mem_outerCarrier_of_ne_zero
        k a ht0)
  · intro hInnerClosed
    rw [(I.innerDisk k).closedRegion_eq_union] at hInnerClosed
    rcases hInnerClosed with hInterior | hCarrier
    · exact hClosed.2 hInterior
    · exact I.levelLocalizedShellCutPath_not_mem_innerCarrier_of_ne_one
        k a ht1 hCarrier

/-- Distinct localized shell-cut paths have disjoint ranges. -/
theorem pairwise_disjoint_range_levelLocalizedShellCutPath (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint (range (I.levelLocalizedShellCutPath k a))
        (range (I.levelLocalizedShellCutPath k b)) := by
  intro a b hab
  simpa only [I.range_levelLocalizedShellCutPath] using
    I.pairwise_disjoint_levelLocalizedShellCut k hab

end JordanCircle.InitialAngularArcs

end

end Schoenflies
