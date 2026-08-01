import Schoenflies.LocalizedMarkedHairCrossings
import Schoenflies.PolygonalShells

/-!
# Retained-hair crosscuts of localized polygonal shells

The same level hair meets both boundaries of the shell between localized
stages `k + 1` and `k + 2`.  Because a nonconvex polygon may meet a straight
hair several times, the useful outer mark is the *last* outer-boundary
crossing before the first inner-boundary crossing.  The intervening straight
segment then lies in the closed shell.  This is the radial cut used to split
the finite annulus into polygonal disk cells.
-/

namespace Schoenflies

open Metric Set Function AffineMap
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev outerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

/-- Outer-boundary crossings no later than the first crossing of the inner
boundary. -/
def shellOuterCrossingParameters (k : ℕ) (a : LevelAddress k) :
    Set unitInterval :=
  (I.levelLeftHair a).polygonalCrossingParameters (I.outerDisk k) ∩
    Set.Iic (I.levelLocalizedFirstPolygonalCrossing k a).parameter

theorem isCompact_shellOuterCrossingParameters (k : ℕ)
    (a : LevelAddress k) :
    IsCompact (I.shellOuterCrossingParameters k a) :=
  ((I.levelLeftHair a).isClosed_polygonalCrossingParameters
      (I.outerDisk k)).inter isClosed_Iic |>.isCompact

/-- The first crossing of the outer disk occurs no later than the first
crossing of the inner disk. -/
theorem firstOuterCrossing_le_innerCrossing (k : ℕ)
    (a : LevelAddress k)
    (C : (I.levelLeftHair a).FirstPolygonalCrossing (I.outerDisk k)) :
    C.parameter ≤
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter := by
  apply le_of_not_gt
  intro hlt
  have hxOuterExterior := C.before_mem_exterior
    (I.localizedMarkedPolygonalDisk_closedRegion_subset_inside (k + 2))
    (J.curvePoint (I.levelArc a).left).2 hlt
  have hxInnerClosed : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.innerDisk k).closedRegion := by
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inr (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
  have hxOuterInterior : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.outerDisk k).interiorRegion :=
    I.localizedMarkedPolygonalDisk_strictly_nested (k + 1) hxInnerClosed
  exact Set.disjoint_left.mp
    (I.outerDisk k).disjoint_interior_exterior
    hxOuterInterior hxOuterExterior

theorem shellOuterCrossingParameters_nonempty (k : ℕ)
    (a : LevelAddress k) :
    (I.shellOuterCrossingParameters k a).Nonempty := by
  have htipInner : (I.levelLeftHair a).tip ∈
      (I.innerDisk k).interiorRegion :=
    I.levelLeftHairTips_subset_localizedMarkedPolygonalDisk_succ k ⟨a, rfl⟩
  have htipInnerClosed : (I.levelLeftHair a).tip ∈
      (I.innerDisk k).closedRegion := by
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inl htipInner
  have htipOuter : (I.levelLeftHair a).tip ∈
      (I.outerDisk k).interiorRegion :=
    I.localizedMarkedPolygonalDisk_strictly_nested (k + 1) htipInnerClosed
  let C : (I.levelLeftHair a).FirstPolygonalCrossing (I.outerDisk k) :=
    Classical.choice <| (I.levelLeftHair a).nonempty_firstPolygonalCrossing
      (I.outerDisk k)
      (I.localizedMarkedPolygonalDisk_closedRegion_subset_inside (k + 2))
      (J.curvePoint (I.levelArc a).left).2 htipOuter
  exact ⟨C.parameter, C.isLeast.1,
    I.firstOuterCrossing_le_innerCrossing k a C⟩

/-- The last outer-boundary crossing before the first inner-boundary
crossing.  Choosing the last crossing is essential for nonconvex polygons. -/
noncomputable def levelLocalizedLastOuterCrossing (k : ℕ)
    (a : LevelAddress k) : unitInterval :=
  Classical.choose <|
    (I.isCompact_shellOuterCrossingParameters k a).exists_isGreatest
      (I.shellOuterCrossingParameters_nonempty k a)

theorem levelLocalizedLastOuterCrossing_isGreatest (k : ℕ)
    (a : LevelAddress k) :
    IsGreatest (I.shellOuterCrossingParameters k a)
      (I.levelLocalizedLastOuterCrossing k a) :=
  Classical.choose_spec <|
    (I.isCompact_shellOuterCrossingParameters k a).exists_isGreatest
      (I.shellOuterCrossingParameters_nonempty k a)

/-- The outer endpoint of the radial shell cut. -/
noncomputable def levelLocalizedOuterBoundaryMark (k : ℕ)
    (a : LevelAddress k) : Plane :=
  Path.segment (J.curvePoint (I.levelArc a).left : Plane)
    (I.levelLeftHair a).tip (I.levelLocalizedLastOuterCrossing k a)

theorem levelLocalizedOuterBoundaryMark_mem_carrier (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedOuterBoundaryMark k a ∈ (I.outerDisk k).carrier :=
  (I.levelLocalizedLastOuterCrossing_isGreatest k a).1.1

theorem levelLocalizedLastOuterCrossing_le_innerCrossing (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedLastOuterCrossing k a ≤
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter :=
  (I.levelLocalizedLastOuterCrossing_isGreatest k a).1.2

theorem levelLocalizedLastOuterCrossing_lt_innerCrossing (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedLastOuterCrossing k a <
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter := by
  refine (I.levelLocalizedLastOuterCrossing_le_innerCrossing k a).lt_of_ne ?_
  intro heq
  have hpoint : I.levelLocalizedOuterBoundaryMark k a =
      I.levelLocalizedPolygonalBoundaryMark k a := by
    unfold levelLocalizedOuterBoundaryMark levelLocalizedPolygonalBoundaryMark
    exact congrArg _ heq
  have hxOuterCarrier : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.outerDisk k).carrier := hpoint ▸
    I.levelLocalizedOuterBoundaryMark_mem_carrier k a
  have hxInnerClosed : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.innerDisk k).closedRegion := by
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inr (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
  have hxOuterInterior : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.outerDisk k).interiorRegion :=
    I.localizedMarkedPolygonalDisk_strictly_nested (k + 1) hxInnerClosed
  exact Set.disjoint_left.mp
    (PolygonalCircle.carrier_disjoint_interiorRegion (I.outerDisk k))
    hxOuterCarrier hxOuterInterior

theorem levelLocalizedOuterBoundaryMark_mem_leftHair (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedOuterBoundaryMark k a ∈ (I.levelLeftHair a).carrier := by
  rw [JordanCircle.InsideAccessHair.carrier, ← Path.range_segment]
  exact ⟨I.levelLocalizedLastOuterCrossing k a, rfl⟩

theorem levelLocalizedOuterBoundaryMark_injective (k : ℕ) :
    Injective (I.levelLocalizedOuterBoundaryMark k) := by
  intro a b hab
  by_contra hne
  exact Set.disjoint_left.mp
    (I.disjoint_levelLeftHairs_of_ne a b hne)
    (I.levelLocalizedOuterBoundaryMark_mem_leftHair k a)
    (hab ▸ I.levelLocalizedOuterBoundaryMark_mem_leftHair k b)

theorem levelLeftHair_afterLastOuter_beforeInner_mem_interior (k : ℕ)
    (a : LevelAddress k) {t : unitInterval}
    (houter : I.levelLocalizedLastOuterCrossing k a < t)
    (hinner : t ≤
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter) :
    Path.segment (J.curvePoint (I.levelArc a).left : Plane)
        (I.levelLeftHair a).tip t ∈
      (I.outerDisk k).interiorRegion := by
  let f := Path.segment (J.curvePoint (I.levelArc a).left : Plane)
    (I.levelLeftHair a).tip
  have havoid : ∀ u ∈ Set.Icc t
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter,
      f u ∉ (I.outerDisk k).toJordanCircle.carrier := by
    intro u hu huCarrier
    have huCrossing : u ∈ I.shellOuterCrossingParameters k a := by
      refine ⟨?_, hu.2⟩
      rwa [(I.outerDisk k).carrier_toJordanCircle] at huCarrier
    have hule :=
      (I.levelLocalizedLastOuterCrossing_isGreatest k a).2 huCrossing
    exact (not_le_of_gt (houter.trans_le hu.1)) hule
  have hsides := (I.outerDisk k).toJordanCircle.interval_image_same_side
    f.continuous hinner havoid
  have hxInnerClosed : I.levelLocalizedPolygonalBoundaryMark k a ∈
      (I.innerDisk k).closedRegion := by
    rw [(I.innerDisk k).closedRegion_eq_union]
    exact Or.inr (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
  have hxInner : f
      (I.levelLocalizedFirstPolygonalCrossing k a).parameter ∈
      (I.outerDisk k).toJordanCircle.inside := by
    rw [(I.outerDisk k).inside_toJordanCircle]
    exact I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)
      hxInnerClosed
  rcases hsides with hinside | houtside
  · rw [← (I.outerDisk k).inside_toJordanCircle]
    exact hinside.1
  · exact False.elim <| Set.disjoint_left.mp
      (I.outerDisk k).toJordanCircle.inside_disjoint_outside
      hxInner houtside.2

/-- Every point of a shell cut has a parameter between its two selected
crossing parameters on the original straight hair. -/
theorem exists_levelLeftHair_parameter_of_mem_shellCut (k : ℕ)
    (a : LevelAddress k) {x : Plane}
    (hx : x ∈ segment ℝ (I.levelLocalizedOuterBoundaryMark k a)
      (I.levelLocalizedPolygonalBoundaryMark k a)) :
    ∃ t : unitInterval,
      I.levelLocalizedLastOuterCrossing k a ≤ t ∧
        t ≤ (I.levelLocalizedFirstPolygonalCrossing k a).parameter ∧
        Path.segment (J.curvePoint (I.levelArc a).left : Plane)
          (I.levelLeftHair a).tip t = x := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  let outer : ℝ := I.levelLocalizedLastOuterCrossing k a
  let inner : ℝ := (I.levelLocalizedFirstPolygonalCrossing k a).parameter
  let tval : ℝ := lineMap outer inner s
  have houterInner : outer ≤ inner := by
    exact_mod_cast I.levelLocalizedLastOuterCrossing_le_innerCrossing k a
  have htBetween : tval ∈ Set.Icc outer inner := by
    rw [← segment_eq_Icc houterInner]
    exact lineMap_mem_segment ℝ outer inner hs
  have htUnit : tval ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨(I.levelLocalizedLastOuterCrossing k a).2.1.trans htBetween.1,
      htBetween.2.trans
        (I.levelLocalizedFirstPolygonalCrossing k a).parameter.2.2⟩
  let t : unitInterval := ⟨tval, htUnit⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · exact_mod_cast htBetween.1
  · exact_mod_cast htBetween.2
  · unfold levelLocalizedOuterBoundaryMark
      levelLocalizedPolygonalBoundaryMark
    let q : Plane := (J.curvePoint (I.levelArc a).left : Plane)
    let p : Plane := (I.levelLeftHair a).tip
    have hline :
        lineMap (lineMap q p outer) (lineMap q p inner) s =
          lineMap q p (lineMap outer inner s) := by
      simp only [lineMap_apply_module]
      module
    simpa only [Path.segment_apply,
      JordanCircle.InsideAccessHair.FirstPolygonalCrossing.point,
      q, p, t, tval, outer, inner] using hline.symm

/-- The closed straight segment of a retained hair between the outer and
inner polygonal boundaries. -/
noncomputable def levelLocalizedShellCut (k : ℕ)
    (a : LevelAddress k) : Set Plane :=
  segment ℝ (I.levelLocalizedOuterBoundaryMark k a)
    (I.levelLocalizedPolygonalBoundaryMark k a)

theorem levelLocalizedShellCut_subset_closedShell (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedShellCut k a ⊆
      PolygonalCircle.closedShell (I.innerDisk k) (I.outerDisk k) := by
  intro x hx
  obtain ⟨t, htOuter, htInner, rfl⟩ :=
    I.exists_levelLeftHair_parameter_of_mem_shellCut k a hx
  refine ⟨?_, ?_⟩
  · rcases htOuter.eq_or_lt with rfl | hlt
    · rw [(I.outerDisk k).closedRegion_eq_union]
      exact Or.inr (I.levelLocalizedOuterBoundaryMark_mem_carrier k a)
    · rw [(I.outerDisk k).closedRegion_eq_union]
      exact Or.inl <|
        I.levelLeftHair_afterLastOuter_beforeInner_mem_interior
          k a hlt htInner
  · intro hxInnerInterior
    rcases htInner.eq_or_lt with rfl | hlt
    · exact Set.disjoint_left.mp
        (PolygonalCircle.carrier_disjoint_interiorRegion (I.innerDisk k))
        (I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a)
        hxInnerInterior
    · have hxExterior :=
        I.levelLeftHair_beforeLocalizedBoundaryMark_mem_exterior k a hlt
      exact Set.disjoint_left.mp
        (I.innerDisk k).disjoint_interior_exterior
        hxInnerInterior hxExterior

theorem levelLocalizedShellCut_inter_outerCarrier (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedShellCut k a ∩ (I.outerDisk k).carrier =
      {I.levelLocalizedOuterBoundaryMark k a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxCut, hxCarrier⟩
    obtain ⟨t, htOuter, htInner, htx⟩ :=
      I.exists_levelLeftHair_parameter_of_mem_shellCut k a hxCut
    have htCrossing : t ∈ I.shellOuterCrossingParameters k a := by
      refine ⟨?_, htInner⟩
      change Path.segment (J.curvePoint (I.levelArc a).left : Plane)
          (I.levelLeftHair a).tip t ∈ (I.outerDisk k).carrier
      rw [htx]
      exact hxCarrier
    have htLe :=
      (I.levelLocalizedLastOuterCrossing_isGreatest k a).2 htCrossing
    have htEq : t = I.levelLocalizedLastOuterCrossing k a :=
      le_antisymm htLe htOuter
    exact mem_singleton_iff.mpr <| by
      rw [← htx, htEq]
      rfl
  · intro x hx
    have hxEq : x = I.levelLocalizedOuterBoundaryMark k a :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨left_mem_segment ℝ _ _,
      I.levelLocalizedOuterBoundaryMark_mem_carrier k a⟩

theorem levelLocalizedShellCut_inter_innerCarrier (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedShellCut k a ∩ (I.innerDisk k).carrier =
      {I.levelLocalizedPolygonalBoundaryMark k a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxCut, hxCarrier⟩
    obtain ⟨t, htOuter, htInner, htx⟩ :=
      I.exists_levelLeftHair_parameter_of_mem_shellCut k a hxCut
    have htCrossing : t ∈
        (I.levelLeftHair a).polygonalCrossingParameters (I.innerDisk k) := by
      change Path.segment (J.curvePoint (I.levelArc a).left : Plane)
          (I.levelLeftHair a).tip t ∈ (I.innerDisk k).carrier
      rw [htx]
      exact hxCarrier
    have htGe :=
      (I.levelLocalizedFirstPolygonalCrossing k a).isLeast.2 htCrossing
    have htEq : t =
        (I.levelLocalizedFirstPolygonalCrossing k a).parameter :=
      le_antisymm htInner htGe
    exact mem_singleton_iff.mpr <| by
      rw [← htx, htEq]
      rfl
  · intro x hx
    have hxEq : x = I.levelLocalizedPolygonalBoundaryMark k a :=
      mem_singleton_iff.mp hx
    subst x
    exact ⟨right_mem_segment ℝ _ _,
      I.levelLocalizedPolygonalBoundaryMark_mem_carrier k a⟩

theorem pairwise_disjoint_levelLocalizedShellCut (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint (I.levelLocalizedShellCut k a)
        (I.levelLocalizedShellCut k b) := by
  intro a b hab
  apply (I.disjoint_levelLeftHairs_of_ne a b hab).mono
  · exact (convex_segment _ _).segment_subset
      (I.levelLocalizedOuterBoundaryMark_mem_leftHair k a)
      (I.levelLocalizedPolygonalBoundaryMark_mem_leftHair k a)
  · exact (convex_segment _ _).segment_subset
      (I.levelLocalizedOuterBoundaryMark_mem_leftHair k b)
      (I.levelLocalizedPolygonalBoundaryMark_mem_leftHair k b)

end JordanCircle.InitialAngularArcs

end

end Schoenflies
