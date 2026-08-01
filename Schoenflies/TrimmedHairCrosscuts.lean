import Schoenflies.ShrinkingCollars

/-!
# Trimming controlled crosscuts at their endpoint hairs

Moise 9.5 silently shortens a selected polygonal arc so that it meets each
prescribed access interval only at its endpoint.  This file isolates the
topological core of that operation.  For an injective path, take its last
parameter on the first hair and its first later parameter on the second.
Compactness of the two parameter sets supplies the extrema.
-/

namespace Schoenflies

open Metric Set Function

namespace JordanCircle
namespace Path

variable {J : JordanCircle} {p q rbase lbase : Plane}

/-- Parameters cutting an injective path down to the portion between its
last visit to the right hair and its first subsequent visit to the left
hair. -/
structure HairTrimData (P : Path p q)
    (HR : J.InsideAccessHair rbase) (HL : J.InsideAccessHair lbase) where
  rightTime : unitInterval
  leftTime : unitInterval
  right_lt_left : rightTime < leftTime
  right_mem : P rightTime ∈ HR.carrier
  left_mem : P leftTime ∈ HL.carrier
  right_greatest : ∀ t, P t ∈ HR.carrier → t ≤ rightTime
  left_least_after : ∀ t, rightTime ≤ t → P t ∈ HL.carrier →
    leftTime ≤ t

/-- The retained portion of a path between its two trimming parameters. -/
def HairTrimData.trimmedPath {P : Path p q}
    {HR : J.InsideAccessHair rbase} {HL : J.InsideAccessHair lbase}
    (T : HairTrimData P HR HL) : Path (P T.rightTime) (P T.leftTime) :=
  P.subpath T.rightTime T.leftTime

/-- The required trimming parameters exist for two disjoint closed hairs
met by the endpoints of the path. -/
theorem nonempty_hairTrimData (P : Path p q)
    (HR : J.InsideAccessHair rbase) (HL : J.InsideAccessHair lbase)
    (hdisjoint : Disjoint HR.carrier HL.carrier)
    (hp : p ∈ HR.carrier) (hq : q ∈ HL.carrier) :
    Nonempty (HairTrimData P HR HL) := by
  let E : Set unitInterval := P ⁻¹' HR.carrier
  have hEclosed : IsClosed E := HR.isClosed_carrier.preimage P.continuous
  have hEcompact : IsCompact E := hEclosed.isCompact
  have hEne : E.Nonempty := by
    refine ⟨0, ?_⟩
    change P 0 ∈ HR.carrier
    simpa only [P.source] using hp
  obtain ⟨u, huE, huGreatest⟩ := hEcompact.exists_isGreatest hEne
  have huOne : u < (⊤ : unitInterval) := by
    apply lt_of_le_of_ne le_top
    intro hu
    have huLeft : P u ∈ HL.carrier := by
      rw [hu]
      change P 1 ∈ HL.carrier
      rw [P.target]
      exact hq
    exact Set.disjoint_left.mp hdisjoint huE huLeft
  let F : Set unitInterval := (P ⁻¹' HL.carrier) ∩ Ici u
  have hFclosed : IsClosed F :=
    (HL.isClosed_carrier.preimage P.continuous).inter isClosed_Ici
  have hFcompact : IsCompact F := hFclosed.isCompact
  have hFne : F.Nonempty := by
    refine ⟨⊤, ?_⟩
    constructor
    · change P 1 ∈ HL.carrier
      rw [P.target]
      exact hq
    · change u ≤ (⊤ : unitInterval)
      exact le_top
  obtain ⟨v, hvF, hvLeast⟩ := hFcompact.exists_isLeast hFne
  have huv : u < v := by
    apply lt_of_le_of_ne hvF.2
    intro huv
    apply Set.disjoint_left.mp hdisjoint huE
    rw [huv]
    exact hvF.1
  exact ⟨{
    rightTime := u
    leftTime := v
    right_lt_left := huv
    right_mem := huE
    left_mem := hvF.1
    right_greatest := fun t ht => huGreatest ht
    left_least_after := fun t hut ht => hvLeast ⟨ht, hut⟩ }⟩

namespace HairTrimData

variable {P : Path p q} {HR : J.InsideAccessHair rbase}
  {HL : J.InsideAccessHair lbase}

/-- Restricting an injective path to a nondegenerate parameter interval
remains injective. -/
theorem trimmedPath_injective (T : HairTrimData P HR HL)
    (hP : Injective P) : Injective T.trimmedPath := by
  intro s t hst
  have hparam :
      Icc.convexComb T.rightTime T.leftTime s =
        Icc.convexComb T.rightTime T.leftTime t := by
    apply hP
    exact hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hparam
  simp only [Icc.coe_convexComb] at hval
  have huv : (T.rightTime : ℝ) < T.leftTime := T.right_lt_left
  nlinarith

/-- The trimmed range stays in every set containing the original path. -/
theorem range_trimmedPath_subset (T : HairTrimData P HR HL) {U : Set Plane}
    (hP : range P ⊆ U) : range T.trimmedPath ⊆ U := by
  unfold trimmedPath
  rw [Path.range_subpath_of_le P T.rightTime T.leftTime
    T.right_lt_left.le]
  rintro x ⟨t, -, rfl⟩
  exact hP ⟨t, rfl⟩

/-- After trimming, the right hair meets the retained path only at its
initial endpoint. -/
theorem range_trimmedPath_inter_rightHair
    (T : HairTrimData P HR HL) :
    range T.trimmedPath ∩ HR.carrier = {P T.rightTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxRange, hxHair⟩
    unfold trimmedPath at hxRange
    rw [Path.range_subpath_of_le P T.rightTime T.leftTime
      T.right_lt_left.le] at hxRange
    obtain ⟨t, ht, rfl⟩ := hxRange
    have htu : t ≤ T.rightTime := T.right_greatest t hxHair
    have ht : t = T.rightTime := le_antisymm htu ht.1
    rw [ht]
    exact mem_singleton _
  · rintro x hx
    have hx : x = P T.rightTime := mem_singleton_iff.mp hx
    subst x
    refine ⟨?_, T.right_mem⟩
    refine ⟨0, ?_⟩
    simp [trimmedPath]

/-- After trimming, the left hair meets the retained path only at its final
endpoint. -/
theorem range_trimmedPath_inter_leftHair
    (T : HairTrimData P HR HL) :
    range T.trimmedPath ∩ HL.carrier = {P T.leftTime} := by
  apply Subset.antisymm
  · rintro x ⟨hxRange, hxHair⟩
    unfold trimmedPath at hxRange
    rw [Path.range_subpath_of_le P T.rightTime T.leftTime
      T.right_lt_left.le] at hxRange
    obtain ⟨t, ht, rfl⟩ := hxRange
    have hvt : T.leftTime ≤ t := T.left_least_after t ht.1 hxHair
    have ht : t = T.leftTime := le_antisymm ht.2 hvt
    rw [ht]
    exact mem_singleton _
  · rintro x hx
    have hx : x = P T.leftTime := mem_singleton_iff.mp hx
    subst x
    refine ⟨?_, T.left_mem⟩
    refine ⟨1, ?_⟩
    simp [trimmedPath]

end HairTrimData
end Path

namespace InitialAngularArcs
namespace LevelInsideJoinData

variable {J : JordanCircle} {I : J.InitialAngularArcs} {n : ℕ}
  {a : LevelAddress n} {epsilon : ℝ} {hepsilon : 0 < epsilon}

/-- The two endpoints chosen on disjoint retained hairs are distinct. -/
theorem endpoints_ne (D : I.LevelInsideJoinData a epsilon hepsilon) :
    D.rightPoint ≠ D.leftPoint := by
  intro h
  exact Set.disjoint_left.mp
    (I.disjoint_levelEndpointHairsNear a hepsilon)
    D.leftPoint_mem (h ▸ D.rightPoint_mem)

/-- The canonical injective PL realization of the chosen finite join. -/
noncomputable def originalPath
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    Path D.rightPoint D.leftPoint :=
  D.line.toPath D.endpoints_ne

/-- Canonical last/first intersection parameters for the two retained
endpoint hairs. -/
noncomputable def hairTrimData
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    JordanCircle.Path.HairTrimData D.originalPath
      (I.levelRightHairNear a hepsilon)
      (I.levelLeftHairNear a hepsilon) :=
  Classical.choice <| JordanCircle.Path.nonempty_hairTrimData D.originalPath
    (I.levelRightHairNear a hepsilon)
    (I.levelLeftHairNear a hepsilon)
    (I.disjoint_levelEndpointHairsNear a hepsilon).symm
    D.rightPoint_mem D.leftPoint_mem

/-- Initial endpoint of the crosscut after removing all later contacts with
the right hair. -/
noncomputable def trimmedRightPoint
    (D : I.LevelInsideJoinData a epsilon hepsilon) : Plane :=
  D.originalPath D.hairTrimData.rightTime

/-- Final endpoint of the crosscut after removing all earlier subsequent
contacts with the left hair. -/
noncomputable def trimmedLeftPoint
    (D : I.LevelInsideJoinData a epsilon hepsilon) : Plane :=
  D.originalPath D.hairTrimData.leftTime

/-- The retained injective subpath between the exact hair intersections. -/
noncomputable def trimmedLinePath
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    Path D.trimmedRightPoint D.trimmedLeftPoint :=
  D.hairTrimData.trimmedPath

theorem trimmedLinePath_injective
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    Injective D.trimmedLinePath := by
  exact D.hairTrimData.trimmedPath_injective
    (D.line.toPath_injective D.endpoints_ne)

theorem range_trimmedLinePath_subset_controlled
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    range D.trimmedLinePath ⊆
      J.inside ∩ thickening epsilon (I.levelArc a).curveArcPlane := by
  exact D.hairTrimData.range_trimmedPath_subset
    (D.line.range_toPath_subset D.endpoints_ne)

theorem range_trimmedLinePath_inter_rightHair
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    range D.trimmedLinePath ∩
        (I.levelRightHairNear a hepsilon).carrier =
      {D.trimmedRightPoint} :=
  D.hairTrimData.range_trimmedPath_inter_rightHair

theorem range_trimmedLinePath_inter_leftHair
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    range D.trimmedLinePath ∩
        (I.levelLeftHairNear a hepsilon).carrier =
      {D.trimmedLeftPoint} :=
  D.hairTrimData.range_trimmedPath_inter_leftHair

theorem trimmedRightPoint_mem
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    D.trimmedRightPoint ∈ (I.levelRightHairNear a hepsilon).carrier :=
  D.hairTrimData.right_mem

theorem trimmedLeftPoint_mem
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    D.trimmedLeftPoint ∈ (I.levelLeftHairNear a hepsilon).carrier :=
  D.hairTrimData.left_mem

/-- The exact three-piece boundary facing a level arc.  Unlike the untrimmed
version, its middle path meets either hair only at the displayed endpoint. -/
noncomputable def trimmedCollarBoundarySet
    (D : I.LevelInsideJoinData a epsilon hepsilon) : Set Plane :=
  segment ℝ (J.curvePoint (I.levelArc a).right) D.trimmedRightPoint ∪
    range D.trimmedLinePath ∪
    segment ℝ D.trimmedLeftPoint
      (J.curvePoint (I.levelArc a).left)

theorem trimmedCollarBoundarySet_subset_thickening
    (D : I.LevelInsideJoinData a epsilon hepsilon) :
    D.trimmedCollarBoundarySet ⊆
      thickening epsilon (I.levelArc a).curveArcPlane := by
  rintro x ((hxRight | hxLine) | hxLeft)
  · apply I.levelRightHairNear_carrier_subset_thickening a hepsilon
    exact (convex_segment
      (J.curvePoint (I.levelArc a).right : Plane)
      (I.levelRightHairNear a hepsilon).tip).segment_subset
        (left_mem_segment ℝ _ _) D.trimmedRightPoint_mem hxRight
  · exact (D.range_trimmedLinePath_subset_controlled hxLine).2
  · apply I.levelLeftHairNear_carrier_subset_thickening a hepsilon
    exact (convex_segment
      (J.curvePoint (I.levelArc a).left : Plane)
      (I.levelLeftHairNear a hepsilon).tip).segment_subset
        D.trimmedLeftPoint_mem (left_mem_segment ℝ _ _) hxLeft

/-- The exact trimmed boundary obeys the same shrinking metric estimate as
the initially selected join. -/
theorem trimmedCollarBoundarySet_subset_ball_left
    (D : I.LevelInsideJoinData a epsilon hepsilon) {delta : ℝ}
    (hsmall : ∀ t ∈ Icc (I.levelArc a).left (I.levelArc a).right,
      dist (J.curvePoint t) (J.curvePoint (I.levelArc a).left) < delta) :
    D.trimmedCollarBoundarySet ⊆
      ball (J.curvePoint (I.levelArc a).left) (epsilon + delta) := by
  intro x hx
  obtain ⟨z, hzArc, hxz⟩ := mem_thickening_iff.mp
    (D.trimmedCollarBoundarySet_subset_thickening hx)
  obtain ⟨t, ht, htz⟩ := hzArc
  obtain ⟨r, hr, hrt⟩ := ht
  have hzr : z = (J.curvePoint r : Plane) :=
    htz.symm.trans (congrArg Subtype.val hrt).symm
  have hzsmall : dist z (J.curvePoint (I.levelArc a).left) < delta := by
    rw [hzr]
    exact hsmall r hr
  rw [mem_ball]
  exact (dist_triangle x z
    (J.curvePoint (I.levelArc a).left)).trans_lt
      (add_lt_add hxz hzsmall)

end LevelInsideJoinData
end InitialAngularArcs
end JordanCircle

end Schoenflies
