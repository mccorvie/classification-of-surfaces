import Schoenflies.AnnularSeparatorPairs
import Schoenflies.PolygonalTwoArcCycle

/-!
# Exact polygonal cells in a cut polygonal annulus

The order argument produces Jordan separators described by two crosscuts and
one arc on each polygonal boundary.  This file proves that those separators
are themselves polygonal circles, with exactly the same point-set carrier.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle

/-- Either intrinsic arc of a polygonal boundary split is a finite broken
line after carrier-preserving endpoint refinement. -/
theorem joinedByBrokenLine_firstBoundaryArc
    (P : PolygonalCircle) {x y : Plane} (hxy : x ≠ y)
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y) :
    JoinedByBrokenLine (range S.first) x y := by
  obtain ⟨R, k, _hcarrier, hzero, hkVertex, hkpos, hklt, hpaths⟩ :=
    exists_normalization_twoBoundaryArcPaths P hxy S
  rcases hpaths with hpaths | hpaths
  · have h := _root_.LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.ProperChord.joinedByBrokenLine_forwardArc
      (J := R) (k := k)
    simpa only [hpaths.1, hzero, hkVertex] using h
  · have h := _root_.LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.ProperChord.joinedByBrokenLine_backwardArc
      (J := R) (k := k) hklt
    simpa only [hpaths.1, hzero, hkVertex] using h.symm

theorem joinedByBrokenLine_secondBoundaryArc
    (P : PolygonalCircle) {x y : Plane} (hxy : x ≠ y)
    (S : P.toJordanCircle.TwoBoundaryArcPaths x y) :
    JoinedByBrokenLine (range S.second) y x := by
  obtain ⟨R, k, _hcarrier, hzero, hkVertex, hkpos, hklt, hpaths⟩ :=
    exists_normalization_twoBoundaryArcPaths P hxy S
  rcases hpaths with hpaths | hpaths
  · have h := _root_.LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.ProperChord.joinedByBrokenLine_backwardArc
      (J := R) (k := k) hklt
    simpa only [hpaths.2, hzero, hkVertex] using h
  · have h := _root_.LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.ProperChord.joinedByBrokenLine_forwardArc
      (J := R) (k := k)
    simpa only [hpaths.2, hzero, hkVertex] using h.symm

namespace AnnularCrosscut.SeparatorPair

variable {P Q : PolygonalCircle} {A B : AnnularCrosscut P Q}
  (S : SeparatorPair A B)

/-- The three-piece bridge through two straight crosscuts and a polygonal
inner-boundary arc is a finite broken line with its exact path range as
permitted carrier. -/
theorem joinedByBrokenLine_commonBridge
    (hInnerPoints : A.innerPoint ≠ B.innerPoint)
    (hAsegment : range A.path =
      segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path =
      segment ℝ B.outerPoint B.innerPoint) :
    JoinedByBrokenLine (range S.commonBridge)
      A.outerPoint B.outerPoint := by
  have hA : JoinedByBrokenLine (range S.commonBridge)
      A.outerPoint A.innerPoint := by
    apply JoinedByBrokenLine.of_segment
    intro z hz
    rw [commonBridge, AnnularCrosscut.range_bridgePath]
    left
    left
    rwa [hAsegment]
  have hInner₀ := joinedByBrokenLine_firstBoundaryArc P
    hInnerPoints S.innerSplit
  have hInner : JoinedByBrokenLine (range S.commonBridge)
      A.innerPoint B.innerPoint := hInner₀.mono (by
    intro z hz
    rw [commonBridge, AnnularCrosscut.range_bridgePath]
    exact Or.inl (Or.inr hz))
  have hB : JoinedByBrokenLine (range S.commonBridge)
      B.innerPoint B.outerPoint := by
    apply JoinedByBrokenLine.of_segment
    intro z hz
    rw [commonBridge, AnnularCrosscut.range_bridgePath]
    right
    rw [hBsegment, segment_symm]
    exact hz
  exact (hA.trans hInner).trans hB

theorem joinedByBrokenLine_outerArc₀
    (hOuterPoints : A.outerPoint ≠ B.outerPoint) :
    JoinedByBrokenLine (range S.outerArc₀)
      B.outerPoint A.outerPoint := by
  have h := joinedByBrokenLine_secondBoundaryArc Q
    hOuterPoints S.outerSplit
  exact h

theorem joinedByBrokenLine_outerArc₁
    (hOuterPoints : A.outerPoint ≠ B.outerPoint) :
    JoinedByBrokenLine (range S.outerArc₁)
      B.outerPoint A.outerPoint := by
  have h := (joinedByBrokenLine_firstBoundaryArc Q
    hOuterPoints S.outerSplit).symm
  simpa only [outerArc₁, Path.symm_range] using h

/-- The first complementary annular separator has an exact polygonal-circle
presentation. -/
theorem exists_polygonalCircle_circle₀
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hAB : Disjoint (range A.path) (range B.path))
    (hOuterPoints : A.outerPoint ≠ B.outerPoint)
    (hInnerPoints : A.innerPoint ≠ B.innerPoint)
    (hAsegment : range A.path =
      segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path =
      segment ℝ B.outerPoint B.innerPoint) :
    ∃ R : PolygonalCircle,
      R.carrier = (S.circle₀ hPQ hAB).carrier := by
  obtain ⟨R, hR⟩ := exists_polygonalCircle_of_two_joined_paths
    hOuterPoints S.commonBridge S.outerArc₀
    (S.commonBridge_injective hPQ hAB)
    S.outerSplit.second_injective
    (S.commonBridge_inter_outerArc₀ hPQ)
    (S.joinedByBrokenLine_commonBridge hInnerPoints hAsegment hBsegment)
    (S.joinedByBrokenLine_outerArc₀ hOuterPoints)
  refine ⟨R, ?_⟩
  rw [hR, S.carrier_circle₀ hPQ hAB]

/-- The second complementary annular separator has an exact polygonal-circle
presentation. -/
theorem exists_polygonalCircle_circle₁
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hAB : Disjoint (range A.path) (range B.path))
    (hOuterPoints : A.outerPoint ≠ B.outerPoint)
    (hInnerPoints : A.innerPoint ≠ B.innerPoint)
    (hAsegment : range A.path =
      segment ℝ A.outerPoint A.innerPoint)
    (hBsegment : range B.path =
      segment ℝ B.outerPoint B.innerPoint) :
    ∃ R : PolygonalCircle,
      R.carrier = (S.circle₁ hPQ hAB).carrier := by
  have hOuterInj : Injective S.outerArc₁ :=
    S.outerSplit.first_injective.comp
      unitInterval.symm_bijective.injective
  obtain ⟨R, hR⟩ := exists_polygonalCircle_of_two_joined_paths
    hOuterPoints S.commonBridge S.outerArc₁
    (S.commonBridge_injective hPQ hAB) hOuterInj
    (S.commonBridge_inter_outerArc₁ hPQ)
    (S.joinedByBrokenLine_commonBridge hInnerPoints hAsegment hBsegment)
    (S.joinedByBrokenLine_outerArc₁ hOuterPoints)
  refine ⟨R, ?_⟩
  rw [hR, S.carrier_circle₁ hPQ hAB]

end AnnularCrosscut.SeparatorPair

end PolygonalCircle

end

end Schoenflies
