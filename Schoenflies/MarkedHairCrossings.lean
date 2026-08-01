import Schoenflies.MarkedPolygonalDiskExhaustion
import Schoenflies.LevelEndpointIncidence

/-!
# First retained-hair crossings of marked polygonal disks

Each marked successor disk contains the tips of a finite pairwise-disjoint
family of access hairs, while the hair bases lie on the original Jordan
curve, hence on the exterior side of the polygonal disk.  The compact set of
crossing parameters therefore has a least element.  The initial hair segment
before that element lies entirely in the polygonal exterior.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InsideAccessHair

variable {J : JordanCircle} {q : Plane}

/-- Parameters at which an access hair meets a polygonal carrier. -/
def polygonalCrossingParameters (H : J.InsideAccessHair q)
    (P : PolygonalCircle) : Set unitInterval :=
  {t | Path.segment q H.tip t ∈ P.carrier}

theorem isClosed_polygonalCrossingParameters
    (H : J.InsideAccessHair q) (P : PolygonalCircle) :
    IsClosed (H.polygonalCrossingParameters P) :=
  P.isClosed_carrier.preimage (Path.segment q H.tip).continuous

theorem isCompact_polygonalCrossingParameters
    (H : J.InsideAccessHair q) (P : PolygonalCircle) :
    IsCompact (H.polygonalCrossingParameters P) :=
  (H.isClosed_polygonalCrossingParameters P).isCompact

theorem polygonalCrossingParameters_nonempty
    (H : J.InsideAccessHair q) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside)
    (hq : q ∈ J.carrier) (htip : H.tip ∈ P.interiorRegion) :
    (H.polygonalCrossingParameters P).Nonempty := by
  have hmeet := J.path_range_inter_polygonalCarrier_nonempty
    P hPinside (Path.segment q H.tip) hq htip
  obtain ⟨x, ⟨⟨t, htx⟩, hxCarrier⟩⟩ := hmeet
  refine ⟨t, ?_⟩
  change Path.segment q H.tip t ∈ P.carrier
  rwa [htx]

/-- The least crossing parameter of an access hair and a polygonal carrier. -/
structure FirstPolygonalCrossing (H : J.InsideAccessHair q)
    (P : PolygonalCircle) where
  parameter : unitInterval
  isLeast : IsLeast (H.polygonalCrossingParameters P) parameter

theorem nonempty_firstPolygonalCrossing
    (H : J.InsideAccessHair q) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside)
    (hq : q ∈ J.carrier) (htip : H.tip ∈ P.interiorRegion) :
    Nonempty (H.FirstPolygonalCrossing P) := by
  obtain ⟨t, ht⟩ :=
    (H.isCompact_polygonalCrossingParameters P).exists_isLeast
      (H.polygonalCrossingParameters_nonempty P hPinside hq htip)
  exact ⟨⟨t, ht⟩⟩

namespace FirstPolygonalCrossing

variable {H : J.InsideAccessHair q} {P : PolygonalCircle}

/-- The first crossing as a point of the plane. -/
def point (C : H.FirstPolygonalCrossing P) : Plane :=
  Path.segment q H.tip C.parameter

theorem point_mem_polygonalCarrier (C : H.FirstPolygonalCrossing P) :
    C.point ∈ P.carrier :=
  C.isLeast.1

theorem point_mem_hair (C : H.FirstPolygonalCrossing P) :
    C.point ∈ H.carrier := by
  rw [InsideAccessHair.carrier, ← Path.range_segment]
  exact ⟨C.parameter, rfl⟩

theorem parameter_pos (C : H.FirstPolygonalCrossing P)
    (hPinside : P.closedRegion ⊆ J.inside) (hq : q ∈ J.carrier) :
    (⊥ : unitInterval) < C.parameter := by
  have hbaseExterior :=
    J.carrier_subset_polygonalExterior_of_closedRegion_subset_inside
      P hPinside hq
  have hbaseNotCarrier : q ∉ P.carrier := by
    intro hqP
    have hqComplement : q ∈ P.carrierᶜ := by
      rw [← P.interior_union_exterior]
      exact Or.inr hbaseExterior
    exact hqComplement hqP
  exact lt_of_le_of_ne bot_le fun hzero => by
    have hparameter : Path.segment q H.tip C.parameter ∈ P.carrier :=
      C.point_mem_polygonalCarrier
    have hsource : Path.segment q H.tip (⊥ : unitInterval) = q := by
      rw [show (⊥ : unitInterval) = 0 by rfl,
        (Path.segment q H.tip).source]
    apply hbaseNotCarrier
    rw [← hsource, hzero]
    exact hparameter

/-- Every point strictly before the least crossing is on the exterior side
of the polygon. -/
theorem before_mem_exterior (C : H.FirstPolygonalCrossing P)
    (hPinside : P.closedRegion ⊆ J.inside) (hq : q ∈ J.carrier)
    {t : unitInterval} (ht : t < C.parameter) :
    Path.segment q H.tip t ∈ P.exteriorRegion := by
  let f := Path.segment q H.tip
  have havoid : ∀ u ∈ Icc (⊥ : unitInterval) t,
      f u ∉ P.toJordanCircle.carrier := by
    intro u hu huCarrier
    have huCrossing : u ∈ H.polygonalCrossingParameters P := by
      change f u ∈ P.carrier
      rwa [P.carrier_toJordanCircle] at huCarrier
    have hleast : C.parameter ≤ u := C.isLeast.2 huCrossing
    exact (not_le_of_gt ht) (hleast.trans hu.2)
  have hsides := P.toJordanCircle.interval_image_same_side
    f.continuous (show (⊥ : unitInterval) ≤ t from bot_le) havoid
  have hbaseExterior : q ∈ P.exteriorRegion :=
    J.carrier_subset_polygonalExterior_of_closedRegion_subset_inside
      P hPinside hq
  have hbaseOutside : f ⊥ ∈ P.toJordanCircle.outside := by
    rw [P.outside_toJordanCircle]
    change Path.segment q H.tip (⊥ : unitInterval) ∈ P.exteriorRegion
    rw [show (⊥ : unitInterval) = 0 by rfl,
      (Path.segment q H.tip).source]
    exact hbaseExterior
  rcases hsides with hsides | hsides
  · exact False.elim <| Set.disjoint_left.mp
      P.toJordanCircle.inside_disjoint_outside hsides.1 hbaseOutside
  · rw [← P.outside_toJordanCircle]
    exact hsides.2

/-- The initial part of the hair, from its Jordan base through the first
polygonal crossing. -/
def prefixCarrier (C : H.FirstPolygonalCrossing P) : Set Plane :=
  Path.segment q H.tip '' Icc (⊥ : unitInterval) C.parameter

theorem base_mem_prefixCarrier (C : H.FirstPolygonalCrossing P) :
    q ∈ C.prefixCarrier := by
  refine ⟨⊥, ⟨le_rfl, bot_le⟩, ?_⟩
  rw [show (⊥ : unitInterval) = 0 by rfl,
    (Path.segment q H.tip).source]

theorem point_mem_prefixCarrier (C : H.FirstPolygonalCrossing P) :
    C.point ∈ C.prefixCarrier :=
  ⟨C.parameter, ⟨bot_le, le_rfl⟩, rfl⟩

theorem prefixCarrier_subset_hair (C : H.FirstPolygonalCrossing P) :
    C.prefixCarrier ⊆ H.carrier := by
  rintro x ⟨t, _ht, rfl⟩
  rw [InsideAccessHair.carrier, ← Path.range_segment]
  exact ⟨t, rfl⟩

theorem isCompact_prefixCarrier (C : H.FirstPolygonalCrossing P) :
    IsCompact C.prefixCarrier :=
  isCompact_Icc.image_of_continuousOn
    (Path.segment q H.tip).continuous.continuousOn

theorem isPreconnected_prefixCarrier (C : H.FirstPolygonalCrossing P) :
    IsPreconnected C.prefixCarrier :=
  Set.ordConnected_Icc.isPreconnected.image
    (Path.segment q H.tip)
    (Path.segment q H.tip).continuous.continuousOn

/-- The prefix meets the polygonal carrier exactly at its final point. -/
theorem prefixCarrier_inter_polygonalCarrier
    (C : H.FirstPolygonalCrossing P) :
    C.prefixCarrier ∩ P.carrier = {C.point} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t, ht, rfl⟩, htCarrier⟩
    have htCrossing : t ∈ H.polygonalCrossingParameters P := htCarrier
    have hleast : C.parameter ≤ t := C.isLeast.2 htCrossing
    have hteq : t = C.parameter := le_antisymm ht.2 hleast
    exact mem_singleton_iff.mpr (congrArg (Path.segment q H.tip) hteq)
  · intro x hx
    have hxEq : x = C.point := mem_singleton_iff.mp hx
    subst x
    exact ⟨C.point_mem_prefixCarrier, C.point_mem_polygonalCarrier⟩

/-- Apart from its terminal crossing, the prefix lies in the polygonal
exterior. -/
theorem prefixCarrier_subset_exterior_union_point
    (C : H.FirstPolygonalCrossing P)
    (hPinside : P.closedRegion ⊆ J.inside) (hq : q ∈ J.carrier) :
    C.prefixCarrier ⊆ P.exteriorRegion ∪ {C.point} := by
  rintro x ⟨t, ht, rfl⟩
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact Or.inl (C.before_mem_exterior hPinside hq hlt)
  · exact Or.inr (mem_singleton C.point)

/-- The prefix, parametrized from its Jordan-curve base to its first
polygonal crossing. -/
noncomputable def prefixPath (C : H.FirstPolygonalCrossing P) :
    Path q C.point :=
  ((Path.segment q H.tip).subpath (⊥ : unitInterval) C.parameter).cast
    (by simp) (by rfl : C.point = Path.segment q H.tip C.parameter)

/-- The path parametrization has exactly the previously defined prefix as
its range. -/
theorem range_prefixPath (C : H.FirstPolygonalCrossing P) :
    range C.prefixPath = C.prefixCarrier := by
  change range ((Path.segment q H.tip).subpath
    (⊥ : unitInterval) C.parameter) = C.prefixCarrier
  rw [Path.range_subpath_of_le _ _ _ bot_le]
  rfl

/-- A positive first-crossing parameter makes the prefix path an embedded
arc. -/
theorem prefixPath_injective (C : H.FirstPolygonalCrossing P)
    (hPinside : P.closedRegion ⊆ J.inside) (hq : q ∈ J.carrier) :
    Injective C.prefixPath := by
  intro s t hst
  have hsegment : Injective (Path.segment q H.tip) :=
    Path.segment_injective_of_ne H.tip_ne_base.symm
  have hcomb :
      Set.Icc.convexComb (⊥ : unitInterval) C.parameter s =
        Set.Icc.convexComb (⊥ : unitInterval) C.parameter t := by
    apply hsegment
    exact hst
  have hval := congrArg Subtype.val hcomb
  simp [Set.Icc.convexComb] at hval
  rcases hval with hstVal | hzero
  · exact Subtype.ext hstVal
  · exact False.elim <|
      (C.parameter_pos hPinside hq).ne' hzero

end FirstPolygonalCrossing
end InsideAccessHair

namespace InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The first crossing of the level-`k` left access hair with marked disk
`k + 1`. -/
noncomputable def levelFirstPolygonalCrossing (k : ℕ)
    (a : LevelAddress k) :
    (I.levelLeftHair a).FirstPolygonalCrossing
      (I.markedPolygonalDiskExhaustion (k + 1)) :=
  Classical.choice <| (I.levelLeftHair a).nonempty_firstPolygonalCrossing
    (I.markedPolygonalDiskExhaustion (k + 1))
    (I.markedPolygonalDiskExhaustion_closedRegion_subset_inside (k + 1))
    (J.curvePoint (I.levelArc a).left).2
    (I.levelLeftHairTips_subset_markedPolygonalDiskExhaustion_succ k
      ⟨a, rfl⟩)

/-- The corresponding marked point on the polygonal boundary. -/
noncomputable def levelPolygonalBoundaryMark (k : ℕ)
    (a : LevelAddress k) : Plane :=
  (I.levelFirstPolygonalCrossing k a).point

theorem levelPolygonalBoundaryMark_mem_carrier (k : ℕ)
    (a : LevelAddress k) :
    I.levelPolygonalBoundaryMark k a ∈
      (I.markedPolygonalDiskExhaustion (k + 1)).carrier :=
  (I.levelFirstPolygonalCrossing k a).point_mem_polygonalCarrier

theorem levelPolygonalBoundaryMark_mem_leftHair (k : ℕ)
    (a : LevelAddress k) :
    I.levelPolygonalBoundaryMark k a ∈ (I.levelLeftHair a).carrier :=
  (I.levelFirstPolygonalCrossing k a).point_mem_hair

/-- Distinct retained hairs give distinct marked points on the polygonal
boundary. -/
theorem levelPolygonalBoundaryMark_injective (k : ℕ) :
    Injective (I.levelPolygonalBoundaryMark k) := by
  intro a b hab
  by_contra hne
  exact Set.disjoint_left.mp
    (I.disjoint_levelLeftHairs_of_ne a b hne)
    (I.levelPolygonalBoundaryMark_mem_leftHair k a)
    (hab ▸ I.levelPolygonalBoundaryMark_mem_leftHair k b)

theorem levelPolygonalBoundaryMark_parameter_pos (k : ℕ)
    (a : LevelAddress k) :
    (⊥ : unitInterval) <
      (I.levelFirstPolygonalCrossing k a).parameter :=
  (I.levelFirstPolygonalCrossing k a).parameter_pos
    (I.markedPolygonalDiskExhaustion_closedRegion_subset_inside (k + 1))
    (J.curvePoint (I.levelArc a).left).2

theorem levelLeftHair_beforeBoundaryMark_mem_exterior (k : ℕ)
    (a : LevelAddress k) {t : unitInterval}
    (ht : t < (I.levelFirstPolygonalCrossing k a).parameter) :
    Path.segment (J.curvePoint (I.levelArc a).left : Plane)
        (I.levelLeftHair a).tip t ∈
      (I.markedPolygonalDiskExhaustion (k + 1)).exteriorRegion :=
  (I.levelFirstPolygonalCrossing k a).before_mem_exterior
    (I.markedPolygonalDiskExhaustion_closedRegion_subset_inside (k + 1))
    (J.curvePoint (I.levelArc a).left).2 ht

/-- The initial retained-hair crosscut from a level anchor to its marked
polygonal boundary point. -/
noncomputable def levelExteriorHairPrefix (k : ℕ)
    (a : LevelAddress k) : Set Plane :=
  (I.levelFirstPolygonalCrossing k a).prefixCarrier

/-- The embedded path underlying a level exterior hair prefix. -/
noncomputable def levelExteriorHairPrefixPath (k : ℕ)
    (a : LevelAddress k) :
    Path (J.curvePoint (I.levelArc a).left : Plane)
      (I.levelPolygonalBoundaryMark k a) :=
  (I.levelFirstPolygonalCrossing k a).prefixPath

theorem range_levelExteriorHairPrefixPath (k : ℕ)
    (a : LevelAddress k) :
    range (I.levelExteriorHairPrefixPath k a) =
      I.levelExteriorHairPrefix k a :=
  (I.levelFirstPolygonalCrossing k a).range_prefixPath

theorem levelExteriorHairPrefixPath_injective (k : ℕ)
    (a : LevelAddress k) :
    Injective (I.levelExteriorHairPrefixPath k a) :=
  (I.levelFirstPolygonalCrossing k a).prefixPath_injective
    (I.markedPolygonalDiskExhaustion_closedRegion_subset_inside (k + 1))
    (J.curvePoint (I.levelArc a).left).2

theorem levelExteriorHairPrefix_subset_leftHair (k : ℕ)
    (a : LevelAddress k) :
    I.levelExteriorHairPrefix k a ⊆ (I.levelLeftHair a).carrier :=
  (I.levelFirstPolygonalCrossing k a).prefixCarrier_subset_hair

theorem levelExteriorHairPrefix_inter_polygonalCarrier (k : ℕ)
    (a : LevelAddress k) :
    I.levelExteriorHairPrefix k a ∩
        (I.markedPolygonalDiskExhaustion (k + 1)).carrier =
      {I.levelPolygonalBoundaryMark k a} :=
  (I.levelFirstPolygonalCrossing k a).prefixCarrier_inter_polygonalCarrier

theorem levelExteriorHairPrefix_subset_exterior_union_mark (k : ℕ)
    (a : LevelAddress k) :
    I.levelExteriorHairPrefix k a ⊆
      (I.markedPolygonalDiskExhaustion (k + 1)).exteriorRegion ∪
        {I.levelPolygonalBoundaryMark k a} :=
  (I.levelFirstPolygonalCrossing k a)
    |>.prefixCarrier_subset_exterior_union_point
      (I.markedPolygonalDiskExhaustion_closedRegion_subset_inside (k + 1))
      (J.curvePoint (I.levelArc a).left).2

theorem pairwise_disjoint_levelExteriorHairPrefix (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint (I.levelExteriorHairPrefix k a)
        (I.levelExteriorHairPrefix k b) := by
  intro a b hab
  exact (I.disjoint_levelLeftHairs_of_ne a b hab).mono
    (I.levelExteriorHairPrefix_subset_leftHair k a)
    (I.levelExteriorHairPrefix_subset_leftHair k b)

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
