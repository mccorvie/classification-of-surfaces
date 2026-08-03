import Schoenflies.LocalizedAnnularCrosscuts
import Schoenflies.PolygonalAnnularCellDecomposition

/-!
# The polygonal-annulus crosscut theorem for localized level cuts

This file instantiates the generic polygonal theta theorem with the straight,
pairwise-disjoint shell cuts supplied by the localized polygonal exhaustion.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev outerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

/-- Synchronized complementary separators selected from two distinct
localized level cuts. -/
noncomputable def levelLocalizedSeparatorPair (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) :
    PolygonalCircle.AnnularCrosscut.SeparatorPair
      (I.levelLocalizedAnnularCrosscut k a)
      (I.levelLocalizedAnnularCrosscut k b) :=
  Classical.choice <|
    PolygonalCircle.AnnularCrosscut.exists_separatorPair
      (I.levelLocalizedAnnularCrosscut k a)
      (I.levelLocalizedAnnularCrosscut k b)
      (by
        intro h
        exact hab (I.levelLocalizedOuterBoundaryMark_injective k h))
      (by
        intro h
        exact hab (I.levelLocalizedPolygonalBoundaryMark_injective k h))

/-- The first localized separator closed by one outer boundary arc. -/
noncomputable def levelLocalizedSeparatorCircle₀ (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) : JordanCircle :=
  (I.levelLocalizedSeparatorPair k hab).circle₀
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)

/-- The complementary localized separator with the same common bridge. -/
noncomputable def levelLocalizedSeparatorCircle₁ (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) : JordanCircle :=
  (I.levelLocalizedSeparatorPair k hab).circle₁
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)

/-- The two selected localized cuts, with all the exact data needed by the
polygonal two-cell filling theorem. -/
noncomputable def levelLocalizedAnnularCellDecomposition (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) :
    PolygonalCircle.AnnularCellDecomposition (I.innerDisk k) (I.outerDisk k) where
  first := I.levelLocalizedAnnularCrosscut k a
  second := I.levelLocalizedAnnularCrosscut k b
  separator := I.levelLocalizedSeparatorPair k hab
  nested := I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)
  disjoint := I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab
  outerPoints_ne := fun h =>
    hab (I.levelLocalizedOuterBoundaryMark_injective k h)
  innerPoints_ne := fun h =>
    hab (I.levelLocalizedPolygonalBoundaryMark_injective k h)
  first_segment := by
    change range (Path.segment
        (I.levelLocalizedOuterBoundaryMark k a)
        (I.levelLocalizedPolygonalBoundaryMark k a)) = _
    exact Path.range_segment _ _
  second_segment := by
    change range (Path.segment
        (I.levelLocalizedOuterBoundaryMark k b)
        (I.levelLocalizedPolygonalBoundaryMark k b)) = _
    exact Path.range_segment _ _

/-- The complementary localized separator regions fill the entire closed
outer polygonal disk. -/
theorem closure_localizedOuterInterior_eq_union_separatorInteriors
    (k : ℕ) {a b : LevelAddress k} (hab : a ≠ b) :
    closure (I.outerDisk k).interiorRegion =
      closure (I.levelLocalizedSeparatorCircle₀ k hab).inside ∪
        closure (I.levelLocalizedSeparatorCircle₁ k hab).inside := by
  let A := I.levelLocalizedAnnularCrosscut k a
  let B := I.levelLocalizedAnnularCrosscut k b
  let S := I.levelLocalizedSeparatorPair k hab
  have hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint := by
    change range (Path.segment
      (I.levelLocalizedOuterBoundaryMark k a)
      (I.levelLocalizedPolygonalBoundaryMark k a)) =
        segment ℝ (I.levelLocalizedOuterBoundaryMark k a)
          (I.levelLocalizedPolygonalBoundaryMark k a)
    exact Path.range_segment _ _
  have hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint := by
    change range (Path.segment
      (I.levelLocalizedOuterBoundaryMark k b)
      (I.levelLocalizedPolygonalBoundaryMark k b)) =
        segment ℝ (I.levelLocalizedOuterBoundaryMark k b)
          (I.levelLocalizedPolygonalBoundaryMark k b)
    exact Path.range_segment _ _
  change closure (I.outerDisk k).interiorRegion =
    closure (S.circle₀
      (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∪
    closure (S.circle₁
      (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside
  exact S.closure_outerInterior_eq_union_separatorInteriors
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)
    hAsegment hBsegment

end JordanCircle.InitialAngularArcs

end

end Schoenflies
