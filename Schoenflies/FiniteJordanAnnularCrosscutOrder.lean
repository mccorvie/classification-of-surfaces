import Schoenflies.JordanAnnularCrosscutOrder

/-!
# Finite mixed-annulus crosscut families

The three-crosscut rule globalizes to a finite family.  If the selected
inner arc is endpoint-free, the corresponding outer Jordan arc is
endpoint-free as well.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.JordanAnnularCrosscut.SeparatorPair

variable {P : PolygonalCircle} {J : JordanCircle} {ι : Type*}
  (F : ι → JordanAnnularCrosscut P J) {a b : ι}
  (S : SeparatorPair (F a) (F b))

theorem family_cyclicCompatibility
    (hab : a ≠ b)
    (hPJ : P.closedRegion ⊆ J.inside)
    (hpairwise : Pairwise fun i j : ι =>
      Disjoint (range (F i).path) (range (F j).path))
    (hinnerInjective : Injective fun i => (F i).innerPoint)
    (houterInjective : Injective fun i => (F i).outerPoint)
    (hAsegment : range (F a).path =
      segment ℝ (F a).outerPoint (F a).innerPoint)
    (hBsegment : range (F b).path =
      segment ℝ (F b).outerPoint (F b).innerPoint)
    (hinnerSecond : ∀ c : ι, c ≠ a → c ≠ b →
      (F c).innerPoint ∈ range S.innerSplit.second) :
    (P.interiorRegion ⊆
          (S.circle₀ hPJ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∈ range S.outerArc₀) ∨
      (P.interiorRegion ⊆
          (S.circle₁ hPJ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∈ range S.outerArc₁) := by
  let hAB := hpairwise hab
  rcases S.innerInterior_separatorSide_dichotomy hPJ hAB
      hAsegment hBsegment with hside₀ | hside₁
  · left
    refine ⟨hside₀.1, ?_⟩
    intro c hca hcb
    have hCA : Disjoint (range (F c).path) (range (F a).path) :=
      hpairwise hca
    have hCB : Disjoint (range (F c).path) (range (F b).path) :=
      hpairwise hcb
    have hmatch := S.outerEndpoint_mem_correspondingArc hPJ hAB hCA hCB
      (hinnerSecond c hca hcb)
      (fun h => hca (hinnerInjective h))
      (fun h => hcb (hinnerInjective h))
      (fun h => hca (houterInjective h))
      (fun h => hcb (houterInjective h))
    exact hmatch.1 hside₀.1
  · right
    refine ⟨hside₁.2, ?_⟩
    intro c hca hcb
    have hCA : Disjoint (range (F c).path) (range (F a).path) :=
      hpairwise hca
    have hCB : Disjoint (range (F c).path) (range (F b).path) :=
      hpairwise hcb
    have hmatch := S.outerEndpoint_mem_correspondingArc hPJ hAB hCA hCB
      (hinnerSecond c hca hcb)
      (fun h => hca (hinnerInjective h))
      (fun h => hcb (hinnerInjective h))
      (fun h => hca (houterInjective h))
      (fun h => hcb (houterInjective h))
    exact hmatch.2 hside₁.2

/-- Cut-free form: the separator not containing the inner polygon uses an
outer arc with no remaining outer endpoints. -/
theorem family_cutFreeArcs
    (hab : a ≠ b)
    (hPJ : P.closedRegion ⊆ J.inside)
    (hpairwise : Pairwise fun i j : ι =>
      Disjoint (range (F i).path) (range (F j).path))
    (hinnerInjective : Injective fun i => (F i).innerPoint)
    (houterInjective : Injective fun i => (F i).outerPoint)
    (hAsegment : range (F a).path =
      segment ℝ (F a).outerPoint (F a).innerPoint)
    (hBsegment : range (F b).path =
      segment ℝ (F b).outerPoint (F b).innerPoint)
    (hinnerSecond : ∀ c : ι, c ≠ a → c ≠ b →
      (F c).innerPoint ∈ range S.innerSplit.second) :
    (P.interiorRegion ⊆
          (S.circle₀ hPJ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∉ range S.outerArc₁) ∨
      (P.interiorRegion ⊆
          (S.circle₁ hPJ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∉ range S.outerArc₀) := by
  rcases S.family_cyclicCompatibility F hab hPJ hpairwise
      hinnerInjective houterInjective hAsegment hBsegment hinnerSecond with
    h₀ | h₁
  · left
    refine ⟨h₀.1, ?_⟩
    intro c hca hcb hOuter₁
    have hEnds : (F c).outerPoint ∈
        ({(F a).outerPoint, (F b).outerPoint} : Set Plane) := by
      rw [← S.outerSplit.overlap]
      refine ⟨?_, h₀.2 c hca hcb⟩
      simpa only [outerArc₁, Path.symm_range] using hOuter₁
    rcases hEnds with hEq | hEq
    · exact hca (houterInjective hEq)
    · exact hcb (houterInjective (Set.mem_singleton_iff.mp hEq))
  · right
    refine ⟨h₁.1, ?_⟩
    intro c hca hcb hOuter₀
    have hEnds : (F c).outerPoint ∈
        ({(F a).outerPoint, (F b).outerPoint} : Set Plane) := by
      rw [← S.outerSplit.overlap]
      refine ⟨?_, hOuter₀⟩
      simpa only [outerArc₁, Path.symm_range] using h₁.2 c hca hcb
    rcases hEnds with hEq | hEq
    · exact hca (houterInjective hEq)
    · exact hcb (houterInjective (Set.mem_singleton_iff.mp hEq))

end PolygonalCircle.JordanAnnularCrosscut.SeparatorPair

end

end Schoenflies
