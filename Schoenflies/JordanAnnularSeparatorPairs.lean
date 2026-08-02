import Schoenflies.JordanAnnularCrosscutSeparators

/-!
# Complementary separators in a mixed Jordan annulus

Two disjoint mixed annular crosscuts and complementary arcs on the inner
polygon and outer Jordan curve form two Jordan circles with a common bridge.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.JordanAnnularCrosscut

variable {P : PolygonalCircle} {J : JordanCircle}

/-- Compatible complementary boundary arcs for two mixed annular cuts. -/
structure SeparatorPair (A B : JordanAnnularCrosscut P J) where
  innerSplit : P.toJordanCircle.TwoBoundaryArcPaths A.innerPoint B.innerPoint
  outerSplit : J.TwoBoundaryArcPaths A.outerPoint B.outerPoint

namespace SeparatorPair

variable {A B : JordanAnnularCrosscut P J} (S : SeparatorPair A B)

def commonBridge : Path A.outerPoint B.outerPoint :=
  bridgePath A B S.innerSplit.first

def outerArc₀ : Path B.outerPoint A.outerPoint := S.outerSplit.second

def outerArc₁ : Path B.outerPoint A.outerPoint := S.outerSplit.first.symm

theorem innerFirst_range_subset :
    range S.innerSplit.first ⊆ P.carrier := by
  intro x hx
  rw [← P.carrier_toJordanCircle, ← S.innerSplit.cover]
  exact Or.inl hx

theorem innerSecond_range_subset :
    range S.innerSplit.second ⊆ P.carrier := by
  intro x hx
  rw [← P.carrier_toJordanCircle, ← S.innerSplit.cover]
  exact Or.inr hx

theorem outerArc₀_range_subset : range S.outerArc₀ ⊆ J.carrier := by
  intro x hx
  rw [← S.outerSplit.cover]
  exact Or.inr hx

theorem outerArc₁_range_subset : range S.outerArc₁ ⊆ J.carrier := by
  intro x hx
  rw [← S.outerSplit.cover]
  left
  simpa only [outerArc₁, Path.symm_range] using hx

theorem commonBridge_injective
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    Injective S.commonBridge :=
  bridgePath_injective hPJ A B hAB S.innerSplit.first
    S.innerSplit.first_injective S.innerFirst_range_subset

theorem commonBridge_inter_outerArc₀
    (hPJ : P.closedRegion ⊆ J.inside) :
    range S.commonBridge ∩ range S.outerArc₀ =
      {A.outerPoint, B.outerPoint} :=
  range_bridgePath_inter_outerArc hPJ A B S.innerSplit.first
    S.innerFirst_range_subset S.outerArc₀ S.outerArc₀_range_subset

theorem commonBridge_inter_outerArc₁
    (hPJ : P.closedRegion ⊆ J.inside) :
    range S.commonBridge ∩ range S.outerArc₁ =
      {A.outerPoint, B.outerPoint} :=
  range_bridgePath_inter_outerArc hPJ A B S.innerSplit.first
    S.innerFirst_range_subset S.outerArc₁ S.outerArc₁_range_subset

def circle₀
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) : JordanCircle :=
  TwoArcJordan.toJordanCircle S.commonBridge S.outerArc₀
    (S.commonBridge_injective hPJ hAB) S.outerSplit.second_injective
    (S.commonBridge_inter_outerArc₀ hPJ)

def circle₁
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) : JordanCircle :=
  TwoArcJordan.toJordanCircle S.commonBridge S.outerArc₁
    (S.commonBridge_injective hPJ hAB)
    (S.outerSplit.first_injective.comp unitInterval.symm_bijective.injective)
    (S.commonBridge_inter_outerArc₁ hPJ)

theorem carrier_circle₀
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (S.circle₀ hPJ hAB).carrier =
      range S.commonBridge ∪ range S.outerArc₀ :=
  TwoArcJordan.carrier_toJordanCircle _ _ _ _ _

theorem carrier_circle₁
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (S.circle₁ hPJ hAB).carrier =
      range S.commonBridge ∪ range S.outerArc₁ :=
  TwoArcJordan.carrier_toJordanCircle _ _ _ _ _

theorem outer_carrier_eq_union :
    J.carrier = range S.outerArc₀ ∪ range S.outerArc₁ := by
  rw [← S.outerSplit.cover]
  simp only [outerArc₀, outerArc₁, Path.symm_range, union_comm]

private theorem midpoint_mem_range_sdiff_endpoints
    {a b : Plane} (p : Path a b) (hp : Injective p) :
    p ⟨1 / 2, by norm_num⟩ ∈ range p \ {a, b} := by
  refine ⟨⟨⟨1 / 2, by norm_num⟩, rfl⟩, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro h
    have ht : (⟨1 / 2, by norm_num⟩ : unitInterval) = 0 :=
      hp (h.trans p.source.symm)
    have := congrArg Subtype.val ht
    norm_num at this
  · intro h
    have ht : (⟨1 / 2, by norm_num⟩ : unitInterval) = 1 :=
      hp (h.trans p.target.symm)
    have := congrArg Subtype.val ht
    norm_num at this

theorem outerArc₀_sdiff_circle₁_nonempty
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (range S.outerArc₀ \ (S.circle₁ hPJ hAB).carrier).Nonempty := by
  let x := S.outerArc₀ ⟨1 / 2, by norm_num⟩
  have hx := midpoint_mem_range_sdiff_endpoints S.outerArc₀
    S.outerSplit.second_injective
  refine ⟨x, hx.1, ?_⟩
  rw [S.carrier_circle₁ hPJ hAB]
  rintro (hxBridge | hxOuter)
  · have hxEnds : x ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
      rw [← S.commonBridge_inter_outerArc₀ hPJ]
      exact ⟨hxBridge, hx.1⟩
    exact hx.2 (by
      simpa only [x, mem_insert_iff, mem_singleton_iff, or_comm] using hxEnds)
  · have hxEnds : x ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
      rw [← S.outerSplit.overlap]
      refine ⟨?_, hx.1⟩
      simpa only [outerArc₁, Path.symm_range] using hxOuter
    exact hx.2 (by
      simpa only [x, mem_insert_iff, mem_singleton_iff, or_comm] using hxEnds)

theorem outerArc₁_sdiff_circle₀_nonempty
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (range S.outerArc₁ \ (S.circle₀ hPJ hAB).carrier).Nonempty := by
  let x := S.outerArc₁ ⟨1 / 2, by norm_num⟩
  have hx := midpoint_mem_range_sdiff_endpoints S.outerArc₁
    (S.outerSplit.first_injective.comp unitInterval.symm_bijective.injective)
  refine ⟨x, hx.1, ?_⟩
  rw [S.carrier_circle₀ hPJ hAB]
  rintro (hxBridge | hxOuter)
  · have hxEnds : x ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
      rw [← S.commonBridge_inter_outerArc₁ hPJ]
      exact ⟨hxBridge, hx.1⟩
    exact hx.2 (by
      simpa only [x, mem_insert_iff, mem_singleton_iff, or_comm] using hxEnds)
  · have hxEnds : x ∈ ({A.outerPoint, B.outerPoint} : Set Plane) := by
      rw [← S.outerSplit.overlap]
      refine ⟨?_, hxOuter⟩
      simpa only [x, outerArc₁, Path.symm_range] using hx.1
    exact hx.2 (by
      simpa only [x, mem_insert_iff, mem_singleton_iff, or_comm] using hxEnds)

theorem circle₀_carrier_subset_jordanClosedShell
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (S.circle₀ hPJ hAB).carrier ⊆ jordanClosedShell P J := by
  rw [S.carrier_circle₀ hPJ hAB]
  change (range (bridgePath A B S.innerSplit.first) ∪
    range S.outerArc₀) ⊆ jordanClosedShell P J
  rw [range_bridgePath]
  exact Set.union_subset
    (Set.union_subset
      (Set.union_subset A.range_subset_closedShell
        (S.innerFirst_range_subset.trans
          (innerCarrier_subset_jordanClosedShell hPJ)))
      B.range_subset_closedShell)
    (S.outerArc₀_range_subset.trans
      (outerCarrier_subset_jordanClosedShell hPJ))

theorem circle₁_carrier_subset_jordanClosedShell
    (hPJ : P.closedRegion ⊆ J.inside)
    (hAB : Disjoint (range A.path) (range B.path)) :
    (S.circle₁ hPJ hAB).carrier ⊆ jordanClosedShell P J := by
  rw [S.carrier_circle₁ hPJ hAB]
  change (range (bridgePath A B S.innerSplit.first) ∪
    range S.outerArc₁) ⊆ jordanClosedShell P J
  rw [range_bridgePath]
  exact Set.union_subset
    (Set.union_subset
      (Set.union_subset A.range_subset_closedShell
        (S.innerFirst_range_subset.trans
          (innerCarrier_subset_jordanClosedShell hPJ)))
      B.range_subset_closedShell)
    (S.outerArc₁_range_subset.trans
      (outerCarrier_subset_jordanClosedShell hPJ))

end SeparatorPair

theorem exists_separatorPair (A B : JordanAnnularCrosscut P J)
    (hOuterPoints : A.outerPoint ≠ B.outerPoint)
    (hInnerPoints : A.innerPoint ≠ B.innerPoint) :
    Nonempty (SeparatorPair A B) := by
  refine ⟨{
    innerSplit := Classical.choice <|
      P.toJordanCircle.exists_twoBoundaryArcPaths
        (by simpa only [P.carrier_toJordanCircle] using A.innerPoint_mem)
        (by simpa only [P.carrier_toJordanCircle] using B.innerPoint_mem)
        hInnerPoints
    outerSplit := Classical.choice <|
      J.exists_twoBoundaryArcPaths A.outerPoint_mem B.outerPoint_mem
        hOuterPoints
  }⟩

end PolygonalCircle.JordanAnnularCrosscut

end

end Schoenflies
