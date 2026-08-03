import Schoenflies.JordanAnnularTheta

/-!
# Cyclic compatibility in a mixed Jordan annulus

Disjoint straight crosscuts between a polygonal inner boundary and an
arbitrary Jordan outer boundary have the same cyclic endpoint order on both
components.  This is the order-preservation theorem needed for retained
access hairs.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.JordanAnnularCrosscut.SeparatorPair

variable {P : PolygonalCircle} {J : JordanCircle}
  {A B C : JordanAnnularCrosscut P J} (S : SeparatorPair A B)

private theorem innerPoint_not_mem_commonBridge_of_mem_second
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint) :
    C.innerPoint ∉ range S.commonBridge := by
  change C.innerPoint ∉ range (bridgePath A B S.innerSplit.first)
  rw [range_bridgePath]
  rintro ((hA | hInner) | hB)
  · exact Set.disjoint_left.mp hCA (Path.target_mem_range C.path) hA
  · have hEnds : C.innerPoint ∈
        ({A.innerPoint, B.innerPoint} : Set Plane) := by
      rw [← S.innerSplit.overlap]
      exact ⟨hInner, hCInner⟩
    rcases hEnds with hEq | hEq
    · exact hCInnerA hEq
    · exact hCInnerB (Set.mem_singleton_iff.mp hEq)
  · exact Set.disjoint_left.mp hCB (Path.target_mem_range C.path) hB

private theorem outerPoint_not_mem_outerArc₁_of_mem_outerArc₀
    (hCOuter : C.outerPoint ∈ range S.outerArc₀)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    C.outerPoint ∉ range S.outerArc₁ := by
  intro hOuter₁
  have hEnds : C.outerPoint ∈
      ({A.outerPoint, B.outerPoint} : Set Plane) := by
    rw [← S.outerSplit.overlap]
    refine ⟨?_, hCOuter⟩
    simpa only [outerArc₁, Path.symm_range] using hOuter₁
  rcases hEnds with hEq | hEq
  · exact hCOuterA hEq
  · exact hCOuterB (Set.mem_singleton_iff.mp hEq)

private theorem outerPoint_not_mem_outerArc₀_of_mem_outerArc₁
    (hCOuter : C.outerPoint ∈ range S.outerArc₁)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    C.outerPoint ∉ range S.outerArc₀ := by
  intro hOuter₀
  have hEnds : C.outerPoint ∈
      ({A.outerPoint, B.outerPoint} : Set Plane) := by
    rw [← S.outerSplit.overlap]
    refine ⟨?_, hOuter₀⟩
    simpa only [outerArc₁, Path.symm_range] using hCOuter
  rcases hEnds with hEq | hEq
  · exact hCOuterA hEq
  · exact hCOuterB (Set.mem_singleton_iff.mp hEq)

theorem disjoint_range_circle₁_of_innerSecond_outerArc₀
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCOuter : C.outerPoint ∈ range S.outerArc₀)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    Disjoint (range C.path) (S.circle₁ hPJ hAB).carrier := by
  rw [Set.disjoint_left]
  intro x hxC hxCircle
  rw [S.carrier_circle₁ hPJ hAB] at hxCircle
  rcases hxCircle with hxBridge | hxOuter₁
  · change x ∈ range (bridgePath A B S.innerSplit.first) at hxBridge
    rw [range_bridgePath] at hxBridge
    rcases hxBridge with (hxA | hxInner) | hxB
    · exact Set.disjoint_left.mp hCA hxC hxA
    · have hxP : x ∈ P.carrier := S.innerFirst_range_subset hxInner
      have hxMeet : x ∈ range C.path ∩ P.carrier := ⟨hxC, hxP⟩
      rw [C.range_inter_inner] at hxMeet
      have hxEq : x = C.innerPoint := Set.mem_singleton_iff.mp hxMeet
      subst x
      exact S.innerPoint_not_mem_commonBridge_of_mem_second hCA hCB
        hCInner hCInnerA hCInnerB (by
          change C.innerPoint ∈ range (bridgePath A B S.innerSplit.first)
          rw [range_bridgePath]
          exact Or.inl (Or.inr hxInner))
    · exact Set.disjoint_left.mp hCB hxC hxB
  · have hxJ : x ∈ J.carrier := S.outerArc₁_range_subset hxOuter₁
    have hxMeet : x ∈ range C.path ∩ J.carrier := ⟨hxC, hxJ⟩
    rw [C.range_inter_outer] at hxMeet
    have hxEq : x = C.outerPoint := Set.mem_singleton_iff.mp hxMeet
    subst x
    exact S.outerPoint_not_mem_outerArc₁_of_mem_outerArc₀
      hCOuter hCOuterA hCOuterB hxOuter₁

theorem disjoint_range_circle₀_of_innerSecond_outerArc₁
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCOuter : C.outerPoint ∈ range S.outerArc₁)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    Disjoint (range C.path) (S.circle₀ hPJ hAB).carrier := by
  rw [Set.disjoint_left]
  intro x hxC hxCircle
  rw [S.carrier_circle₀ hPJ hAB] at hxCircle
  rcases hxCircle with hxBridge | hxOuter₀
  · change x ∈ range (bridgePath A B S.innerSplit.first) at hxBridge
    rw [range_bridgePath] at hxBridge
    rcases hxBridge with (hxA | hxInner) | hxB
    · exact Set.disjoint_left.mp hCA hxC hxA
    · have hxP : x ∈ P.carrier := S.innerFirst_range_subset hxInner
      have hxMeet : x ∈ range C.path ∩ P.carrier := ⟨hxC, hxP⟩
      rw [C.range_inter_inner] at hxMeet
      have hxEq : x = C.innerPoint := Set.mem_singleton_iff.mp hxMeet
      subst x
      exact S.innerPoint_not_mem_commonBridge_of_mem_second hCA hCB
        hCInner hCInnerA hCInnerB (by
          change C.innerPoint ∈ range (bridgePath A B S.innerSplit.first)
          rw [range_bridgePath]
          exact Or.inl (Or.inr hxInner))
    · exact Set.disjoint_left.mp hCB hxC hxB
  · have hxJ : x ∈ J.carrier := S.outerArc₀_range_subset hxOuter₀
    have hxMeet : x ∈ range C.path ∩ J.carrier := ⟨hxC, hxJ⟩
    rw [C.range_inter_outer] at hxMeet
    have hxEq : x = C.outerPoint := Set.mem_singleton_iff.mp hxMeet
    subst x
    exact S.outerPoint_not_mem_outerArc₀_of_mem_outerArc₁
      hCOuter hCOuterA hCOuterB hxOuter₀

private theorem endpoints_same_side_of_disjoint_range
    (K : JordanCircle)
    (hdisjoint : Disjoint (range C.path) K.carrier)
    (hOuter : C.outerPoint ∈ K.outside) :
    C.innerPoint ∈ K.outside := by
  have hsides := K.interval_image_same_side C.path.continuous
    (a := (0 : unitInterval)) (b := (1 : unitInterval)) (by simp)
    (by
      intro t _ht htCarrier
      exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ htCarrier)
  rcases hsides with hInside | hOutside
  · exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      (by simpa only [Path.source] using hInside.1) hOuter
  · simpa only [Path.target] using hOutside.2

private theorem interiorRegion_subset_separatorSide
    {K : JordanCircle}
    (hK : K.carrier ⊆ jordanClosedShell P J) :
    P.interiorRegion ⊆ K.inside ∨ P.interiorRegion ⊆ K.outside := by
  have hregions : P.interiorRegion ⊆ K.inside ∪ K.outside := by
    rw [K.inside_union_outside]
    intro x hxInterior hxK
    exact (hK hxK).2 hxInterior
  exact P.isConnected_interiorRegion.isPreconnected.subset_or_subset
    K.inside_isOpen K.outside_isOpen K.inside_disjoint_outside hregions

theorem innerInterior_subset_circle₁Outside_of_outerArc₀
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCOuter : C.outerPoint ∈ range S.outerArc₀)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    P.interiorRegion ⊆ (S.circle₁ hPJ hAB).outside := by
  let K := S.circle₁ hPJ hAB
  have hdisjoint := S.disjoint_range_circle₁_of_innerSecond_outerArc₀
    hPJ hAB hCA hCB hCInner hCOuter hCInnerA hCInnerB hCOuterA hCOuterB
  have hOuter : C.outerPoint ∈ K.outside := by
    apply J.carrier_sdiff_subset_outside_of_carrier_subset K
      (fun x hx =>
        (S.circle₁_carrier_subset_jordanClosedShell hPJ hAB hx).1)
    exact ⟨C.outerPoint_mem,
      fun hCarrier => Set.disjoint_left.mp hdisjoint
        (Path.source_mem_range C.path) hCarrier⟩
  have hInner : C.innerPoint ∈ K.outside :=
    endpoints_same_side_of_disjoint_range (C := C) K hdisjoint hOuter
  rcases interiorRegion_subset_separatorSide
      (S.circle₁_carrier_subset_jordanClosedShell hPJ hAB) with
      hInside | hOutside
  · have hBoundaryInside :=
      innerCarrier_sdiff_subset_inside_of_interior_subset_inside hInside
        ⟨C.innerPoint_mem, fun hCarrier =>
          Set.disjoint_left.mp hdisjoint (Path.target_mem_range C.path)
            hCarrier⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      hBoundaryInside hInner
  · exact hOutside

theorem innerInterior_subset_circle₀Outside_of_outerArc₁
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCOuter : C.outerPoint ∈ range S.outerArc₁)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    P.interiorRegion ⊆ (S.circle₀ hPJ hAB).outside := by
  let K := S.circle₀ hPJ hAB
  have hdisjoint := S.disjoint_range_circle₀_of_innerSecond_outerArc₁
    hPJ hAB hCA hCB hCInner hCOuter hCInnerA hCInnerB hCOuterA hCOuterB
  have hOuter : C.outerPoint ∈ K.outside := by
    apply J.carrier_sdiff_subset_outside_of_carrier_subset K
      (fun x hx =>
        (S.circle₀_carrier_subset_jordanClosedShell hPJ hAB hx).1)
    exact ⟨C.outerPoint_mem,
      fun hCarrier => Set.disjoint_left.mp hdisjoint
        (Path.source_mem_range C.path) hCarrier⟩
  have hInner : C.innerPoint ∈ K.outside :=
    endpoints_same_side_of_disjoint_range (C := C) K hdisjoint hOuter
  rcases interiorRegion_subset_separatorSide
      (S.circle₀_carrier_subset_jordanClosedShell hPJ hAB) with
      hInside | hOutside
  · have hBoundaryInside :=
      innerCarrier_sdiff_subset_inside_of_interior_subset_inside hInside
        ⟨C.innerPoint_mem, fun hCarrier =>
          Set.disjoint_left.mp hdisjoint (Path.target_mem_range C.path)
            hCarrier⟩
    exact False.elim <| Set.disjoint_left.mp K.inside_disjoint_outside
      hBoundaryInside hInner
  · exact hOutside

/-- Exactly one complementary separator disk contains the inner polygon. -/
theorem innerInterior_separatorSide_dichotomy
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint) :
    (P.interiorRegion ⊆ (S.circle₀ hPJ hAB).inside ∧
        P.interiorRegion ⊆ (S.circle₁ hPJ hAB).outside) ∨
      (P.interiorRegion ⊆ (S.circle₀ hPJ hAB).outside ∧
        P.interiorRegion ⊆ (S.circle₁ hPJ hAB).inside) := by
  let K₀ := S.circle₀ hPJ hAB
  let K₁ := S.circle₁ hPJ hAB
  have hdisjoint : Disjoint K₀.inside K₁.inside :=
    S.disjoint_separatorInteriors hPJ hAB
  have hcover : closure J.inside =
      closure K₀.inside ∪ closure K₁.inside :=
    S.closure_outerInside_eq_union_separatorInteriors hPJ hAB
      hAsegment hBsegment
  rcases interiorRegion_subset_separatorSide
      (S.circle₀_carrier_subset_jordanClosedShell hPJ hAB) with
      hK₀Inside | hK₀Outside
  · left
    refine ⟨hK₀Inside, ?_⟩
    rcases interiorRegion_subset_separatorSide
        (S.circle₁_carrier_subset_jordanClosedShell hPJ hAB) with
        hK₁Inside | hK₁Outside
    · intro x hxP
      exact False.elim <| Set.disjoint_left.mp hdisjoint
        (hK₀Inside hxP) (hK₁Inside hxP)
    · exact hK₁Outside
  · right
    refine ⟨hK₀Outside, ?_⟩
    intro x hxP
    have hxPClosed : x ∈ P.closedRegion := by
      rw [P.closedRegion_eq_union]
      exact Or.inl hxP
    have hxJ : x ∈ J.inside := hPJ hxPClosed
    have hxCover : x ∈ closure K₀.inside ∪ closure K₁.inside := by
      rw [← hcover]
      exact subset_closure hxJ
    rcases hxCover with hxK₀ | hxK₁
    · rw [K₀.closure_inside] at hxK₀
      rcases hxK₀ with hxInside | hxCarrier
      · exact False.elim <| Set.disjoint_left.mp
          K₀.inside_disjoint_outside hxInside (hK₀Outside hxP)
      · exact False.elim <|
          (S.circle₀_carrier_subset_jordanClosedShell hPJ hAB hxCarrier).2
            hxP
    · rw [K₁.closure_inside] at hxK₁
      rcases hxK₁ with hxInside | hxCarrier
      · exact hxInside
      · exact False.elim <|
          (S.circle₁_carrier_subset_jordanClosedShell hPJ hAB hxCarrier).2
            hxP

/-- A third cut ending on the unused inner arc has its outer endpoint on the
corresponding outer arc selected by the separator containing the inner disk. -/
theorem outerEndpoint_mem_correspondingArc
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    (P.interiorRegion ⊆ (S.circle₀ hPJ hAB).inside →
        C.outerPoint ∈ range S.outerArc₀) ∧
      (P.interiorRegion ⊆ (S.circle₁ hPJ hAB).inside →
        C.outerPoint ∈ range S.outerArc₁) := by
  have hOuterUnion : C.outerPoint ∈
      range S.outerArc₀ ∪ range S.outerArc₁ := by
    rw [← S.outer_carrier_eq_union]
    exact C.outerPoint_mem
  constructor
  · intro hPInside₀
    rcases hOuterUnion with hOuter₀ | hOuter₁
    · exact hOuter₀
    · have hPOutside₀ :=
        S.innerInterior_subset_circle₀Outside_of_outerArc₁
          hPJ hAB hCA hCB hCInner hOuter₁ hCInnerA hCInnerB
            hCOuterA hCOuterB
      let p := P.toJordanCircle.insidePoint
      have hpP : p ∈ P.interiorRegion := by
        rw [← P.inside_toJordanCircle]
        exact P.toJordanCircle.insidePoint_mem_inside
      exact False.elim <| Set.disjoint_left.mp
        (S.circle₀ hPJ hAB).inside_disjoint_outside
        (hPInside₀ hpP) (hPOutside₀ hpP)
  · intro hPInside₁
    rcases hOuterUnion with hOuter₀ | hOuter₁
    · have hPOutside₁ :=
        S.innerInterior_subset_circle₁Outside_of_outerArc₀
          hPJ hAB hCA hCB hCInner hOuter₀ hCInnerA hCInnerB
            hCOuterA hCOuterB
      let p := P.toJordanCircle.insidePoint
      have hpP : p ∈ P.interiorRegion := by
        rw [← P.inside_toJordanCircle]
        exact P.toJordanCircle.insidePoint_mem_inside
      exact False.elim <| Set.disjoint_left.mp
        (S.circle₁ hPJ hAB).inside_disjoint_outside
        (hPInside₁ hpP) (hPOutside₁ hpP)
    · exact hOuter₁

theorem thirdCrosscut_cyclicCompatibility
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path))
    (hCA : Disjoint (range C.path) (range A.path))
    (hCB : Disjoint (range C.path) (range B.path))
    (hAsegment : range A.path = segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path = segment ℝ B.outerPoint B.innerPoint)
    (hCInner : C.innerPoint ∈ range S.innerSplit.second)
    (hCInnerA : C.innerPoint ≠ A.innerPoint)
    (hCInnerB : C.innerPoint ≠ B.innerPoint)
    (hCOuterA : C.outerPoint ≠ A.outerPoint)
    (hCOuterB : C.outerPoint ≠ B.outerPoint) :
    (P.interiorRegion ⊆ (S.circle₀ hPJ hAB).inside ∧
        C.outerPoint ∈ range S.outerArc₀) ∨
      (P.interiorRegion ⊆ (S.circle₁ hPJ hAB).inside ∧
        C.outerPoint ∈ range S.outerArc₁) := by
  have hmatch := S.outerEndpoint_mem_correspondingArc hPJ hAB hCA hCB
    hCInner hCInnerA hCInnerB hCOuterA hCOuterB
  rcases S.innerInterior_separatorSide_dichotomy hPJ hAB
      hAsegment hBsegment with h₀ | h₁
  · exact Or.inl ⟨h₀.1, hmatch.1 h₀.1⟩
  · exact Or.inr ⟨h₁.2, hmatch.2 h₁.2⟩

end PolygonalCircle.JordanAnnularCrosscut.SeparatorPair

end

end Schoenflies
