import Schoenflies.AnnularCrosscutSeparators
import Schoenflies.LocalizedShellCutPaths

/-!
# Localized shell cuts as annular-crosscut data

This file connects the retained-hair construction to the generic annular
separator theorem.  Every localized radial cut satisfies the exact endpoint
and boundary-intersection interface, and any two distinct cuts therefore
determine a Jordan separator through the shell.
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

/-- The generic annular-crosscut record carried by one retained level hair. -/
noncomputable def levelLocalizedAnnularCrosscut (k : ℕ)
    (a : LevelAddress k) :
    PolygonalCircle.AnnularCrosscut (I.innerDisk k) (I.outerDisk k) where
  outerPoint := I.levelLocalizedOuterBoundaryMark k a
  innerPoint := I.levelLocalizedPolygonalBoundaryMark k a
  path := I.levelLocalizedShellCutPath k a
  path_injective := I.levelLocalizedShellCutPath_injective k a
  outerPoint_mem := I.levelLocalizedOuterBoundaryMark_mem_carrier k a
  innerPoint_mem := I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a
  range_inter_outer := by
    rw [I.range_levelLocalizedShellCutPath]
    exact I.levelLocalizedShellCut_inter_outerCarrier k a
  range_inter_inner := by
    rw [I.range_levelLocalizedShellCutPath]
    exact I.levelLocalizedShellCut_inter_innerCarrier k a

theorem pairwise_disjoint_levelLocalizedAnnularCrosscut (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint (range (I.levelLocalizedAnnularCrosscut k a).path)
        (range (I.levelLocalizedAnnularCrosscut k b).path) := by
  exact I.pairwise_disjoint_range_levelLocalizedShellCutPath k

/-- Any two distinct retained radial cuts, closed by one arc on each
polygonal boundary, yield a Jordan separator with an exact four-piece
carrier. -/
theorem exists_levelLocalized_jordanSeparator (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) :
    ∃ innerArc : Path
        (I.levelLocalizedAnnularCrosscut k a).innerPoint
        (I.levelLocalizedAnnularCrosscut k b).innerPoint,
      ∃ outerArc : Path
          (I.levelLocalizedAnnularCrosscut k b).outerPoint
          (I.levelLocalizedAnnularCrosscut k a).outerPoint,
        ∃ K : JordanCircle,
          Injective innerArc ∧ Injective outerArc ∧
          range innerArc ⊆ (I.innerDisk k).carrier ∧
          range outerArc ⊆ (I.outerDisk k).carrier ∧
          K.carrier =
            range (I.levelLocalizedAnnularCrosscut k a).path ∪
              range innerArc ∪
              range (I.levelLocalizedAnnularCrosscut k b).path ∪
              range outerArc := by
  apply PolygonalCircle.AnnularCrosscut.exists_jordanSeparator
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.levelLocalizedAnnularCrosscut k a)
    (I.levelLocalizedAnnularCrosscut k b)
  · exact I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab
  · intro h
    exact hab (I.levelLocalizedOuterBoundaryMark_injective k h)
  · intro h
    exact hab (I.levelLocalizedPolygonalBoundaryMark_injective k h)

end JordanCircle.InitialAngularArcs

end

end Schoenflies
