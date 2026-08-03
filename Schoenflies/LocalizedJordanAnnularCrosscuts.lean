import Schoenflies.FiniteJordanAnnularCrosscutOrder
import Schoenflies.LocalizedMarkedHairCrossings

/-!
# Crosscuts from the original Jordan curve to a localized exhaustion level

The initial portions of the retained access hairs run from their original
Jordan anchors to their first crossings with a localized polygonal disk.
This file packages those portions as a finite family of mixed-annulus
crosscuts.  It is the bridge which lets cyclic order on an exhaustion
boundary control cyclic order on the original Jordan curve.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

/-- The retained access-hair prefix, viewed as a crosscut from the original
Jordan curve to localized polygonal disk `k + 1`. -/
noncomputable def levelLocalizedJordanAnnularCrosscut (k : ℕ)
    (a : LevelAddress k) :
    PolygonalCircle.JordanAnnularCrosscut (I.innerDisk k) J where
  outerPoint := (J.curvePoint (I.levelArc a).left : Plane)
  innerPoint := I.levelLocalizedPolygonalBoundaryMark k a
  path := I.levelLocalizedExteriorHairPrefixPath k a
  path_injective := I.levelLocalizedExteriorHairPrefixPath_injective k a
  outerPoint_mem := (J.curvePoint (I.levelArc a).left).2
  innerPoint_mem := I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a
  range_inter_outer := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxPrefix, hxJ⟩
      have hxHair : x ∈ (I.levelLeftHair a).carrier :=
        I.levelLocalizedExteriorHairPrefix_subset_leftHair k a <|
          (I.range_levelLocalizedExteriorHairPrefixPath k a ▸ hxPrefix)
      have hxIntersection :
          x ∈ (I.levelLeftHair a).carrier ∩ J.carrier :=
        ⟨hxHair, hxJ⟩
      rw [(I.levelLeftHair a).carrier_inter_curve
        (J.curvePoint (I.levelArc a).left).2] at hxIntersection
      exact hxIntersection
    · intro x hx
      have hxEq : x = (J.curvePoint (I.levelArc a).left : Plane) :=
        Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨Path.source_mem_range _,
        (J.curvePoint (I.levelArc a).left).2⟩
  range_inter_inner := by
    rw [I.range_levelLocalizedExteriorHairPrefixPath k a]
    exact I.levelLocalizedExteriorHairPrefix_inter_polygonalCarrier k a
  range_subset_closedShell := by
    intro x hx
    have hxPrefix : x ∈ I.levelLocalizedExteriorHairPrefix k a := by
      rw [← I.range_levelLocalizedExteriorHairPrefixPath k a]
      exact hx
    refine ⟨?_, ?_⟩
    · have hxHair : x ∈ (I.levelLeftHair a).carrier :=
        I.levelLocalizedExteriorHairPrefix_subset_leftHair k a hxPrefix
      rcases (I.levelLeftHair a).carrier_subset hxHair with hxInside | hxBase
      · exact Or.inl hxInside
      · exact Or.inr <| hxBase ▸
          (J.curvePoint (I.levelArc a).left).2
    · intro hxInterior
      rcases I.levelLocalizedExteriorHairPrefix_subset_exterior_union_mark
          k a hxPrefix with hxExterior | hxMark
      · exact Set.disjoint_left.mp (I.innerDisk k).disjoint_interior_exterior
          hxInterior hxExterior
      · have hxEq : x = I.levelLocalizedPolygonalBoundaryMark k a :=
          Set.mem_singleton_iff.mp hxMark
        subst x
        exact Set.disjoint_left.mp
          (PolygonalCircle.carrier_disjoint_interiorRegion (I.innerDisk k))
          (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
          hxInterior

theorem pairwise_disjoint_levelLocalizedJordanAnnularCrosscut (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint
        (range (I.levelLocalizedJordanAnnularCrosscut k a).path)
        (range (I.levelLocalizedJordanAnnularCrosscut k b).path) := by
  intro a b hab
  change Disjoint
    (range (I.levelLocalizedExteriorHairPrefixPath k a))
    (range (I.levelLocalizedExteriorHairPrefixPath k b))
  rw [I.range_levelLocalizedExteriorHairPrefixPath k a,
    I.range_levelLocalizedExteriorHairPrefixPath k b]
  exact I.pairwise_disjoint_levelLocalizedExteriorHairPrefix k hab

theorem levelLocalizedJordanAnnularCrosscut_innerPoint_injective (k : ℕ) :
    Injective fun a : LevelAddress k =>
      (I.levelLocalizedJordanAnnularCrosscut k a).innerPoint :=
  I.levelLocalizedPolygonalBoundaryMark_injective k

theorem levelLocalizedJordanAnnularCrosscut_outerPoint_injective (k : ℕ) :
    Injective fun a : LevelAddress k =>
      (I.levelLocalizedJordanAnnularCrosscut k a).outerPoint :=
  I.levelLeftPoint_injective

theorem range_levelLocalizedJordanAnnularCrosscut_eq_segment
    (k : ℕ) (a : LevelAddress k) :
    range (I.levelLocalizedJordanAnnularCrosscut k a).path =
      segment ℝ
        (I.levelLocalizedJordanAnnularCrosscut k a).outerPoint
        (I.levelLocalizedJordanAnnularCrosscut k a).innerPoint :=
  I.range_levelLocalizedExteriorHairPrefixPath_eq_segment k a

end JordanCircle.InitialAngularArcs

end

end Schoenflies
