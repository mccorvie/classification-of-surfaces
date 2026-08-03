import Schoenflies.AnnularCrosscutOrder
import Schoenflies.FiniteJordanArcOrder

/-!
# Cyclic compatibility for a family of annular crosscuts

The three-crosscut noninterlacing theorem globalizes without any additional
topology.  If one of the two inner boundary arcs between a selected pair of
cuts contains every other inner endpoint, then one corresponding outer arc
contains every other outer endpoint.  Equivalently, the complementary inner
and outer arcs bound a cut-free polygonal disk cell.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace PolygonalCircle.AnnularCrosscut.SeparatorPair

variable {P Q : PolygonalCircle} {ι : Type*}
  (F : ι → AnnularCrosscut P Q) {a b : ι}
  (S : SeparatorPair (F a) (F b))

/-- Family form of cyclic compatibility.  The assertion is deliberately
orientation-free: `circle₀` or `circle₁` may be the separator containing
the inner disk, and that choice determines which outer arc contains all
remaining endpoints. -/
theorem family_cyclicCompatibility
    (hab : a ≠ b)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
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
          (S.circle₀ hPQ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∈ range S.outerArc₀) ∨
      (P.interiorRegion ⊆
          (S.circle₁ hPQ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∈ range S.outerArc₁) := by
  let hAB := hpairwise hab
  rcases S.innerInterior_separatorSide_dichotomy hPQ hAB
      hAsegment hBsegment with hside₀ | hside₁
  · left
    refine ⟨hside₀.1, ?_⟩
    intro c hca hcb
    have hCA : Disjoint (range (F c).path) (range (F a).path) :=
      hpairwise hca
    have hCB : Disjoint (range (F c).path) (range (F b).path) :=
      hpairwise hcb
    have hmatch := S.outerEndpoint_mem_correspondingArc hPQ hAB hCA hCB
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
    have hmatch := S.outerEndpoint_mem_correspondingArc hPQ hAB hCA hCB
      (hinnerSecond c hca hcb)
      (fun h => hca (hinnerInjective h))
      (fun h => hcb (hinnerInjective h))
      (fun h => hca (houterInjective h))
      (fun h => hcb (houterInjective h))
    exact hmatch.2 hside₁.2

/-- Cut-free-arc form of the family theorem.  If `innerSplit.first` has no
remaining inner endpoints, then the separator which does not contain the
inner disk also uses an outer arc with no remaining outer endpoints. -/
theorem family_cutFreeArcs
    (hab : a ≠ b)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
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
          (S.circle₀ hPQ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∉ range S.outerArc₁) ∨
      (P.interiorRegion ⊆
          (S.circle₁ hPQ (hpairwise hab)).inside ∧
        ∀ c : ι, c ≠ a → c ≠ b →
          (F c).outerPoint ∉ range S.outerArc₀) := by
  rcases S.family_cyclicCompatibility F hab hPQ hpairwise
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

/-- Starting from any prescribed member of a finite annular-crosscut family,
choose its next inner-boundary neighbor.  The matching outer arc is cut-free
as well, so the pair bounds one genuine collar cell. -/
theorem exists_cutFreeArcFrom
    [Fintype ι]
    (hcard : 2 ≤ Fintype.card ι)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hpairwise : Pairwise fun i j : ι =>
      Disjoint (range (F i).path) (range (F j).path))
    (hinnerInjective : Injective fun i => (F i).innerPoint)
    (houterInjective : Injective fun i => (F i).outerPoint)
    (hsegment : ∀ i : ι, range (F i).path =
      segment ℝ (F i).outerPoint (F i).innerPoint)
    (a : ι) :
    ∃ b : ι, ∃ hab : a ≠ b, ∃ S : SeparatorPair (F a) (F b),
      (P.interiorRegion ⊆
            (S.circle₀ hPQ (hpairwise hab)).inside ∧
          ∀ c : ι, c ≠ a → c ≠ b →
            (F c).outerPoint ∉ range S.outerArc₁) ∨
        (P.interiorRegion ⊆
            (S.circle₁ hPQ (hpairwise hab)).inside ∧
          ∀ c : ι, c ≠ a → c ≠ b →
            (F c).outerPoint ∉ range S.outerArc₀) := by
  classical
  obtain ⟨b, hab, innerSplit, hinnerSecond⟩ :=
    P.toJordanCircle.exists_next_twoBoundaryArcPaths
      (fun i => (F i).innerPoint)
      (fun i => by
        simpa only [P.carrier_toJordanCircle] using (F i).innerPoint_mem)
      hinnerInjective hcard a
  have hOuterNe : (F a).outerPoint ≠ (F b).outerPoint := by
    intro h
    exact hab (houterInjective h)
  let outerSplit := Classical.choice <|
    Q.toJordanCircle.exists_twoBoundaryArcPaths
      (by simpa only [Q.carrier_toJordanCircle] using (F a).outerPoint_mem)
      (by simpa only [Q.carrier_toJordanCircle] using (F b).outerPoint_mem)
      hOuterNe
  let S : SeparatorPair (F a) (F b) := ⟨innerSplit, outerSplit⟩
  refine ⟨b, hab, S, ?_⟩
  exact S.family_cutFreeArcs F hab hPQ hpairwise
    hinnerInjective houterInjective (hsegment a) (hsegment b)
    hinnerSecond

/-- A finite family with at least two crosscuts has a pair bounding a cut-free
cell.  The inner split is chosen by finite cyclic order; the three-crosscut
theorem forces the corresponding outer arc to be cut-free as well. -/
theorem exists_cutFreeArcs
    [Fintype ι]
    (hcard : 2 ≤ Fintype.card ι)
    (hPQ : P.closedRegion ⊆ Q.interiorRegion)
    (hpairwise : Pairwise fun i j : ι =>
      Disjoint (range (F i).path) (range (F j).path))
    (hinnerInjective : Injective fun i => (F i).innerPoint)
    (houterInjective : Injective fun i => (F i).outerPoint)
    (hsegment : ∀ i : ι, range (F i).path =
      segment ℝ (F i).outerPoint (F i).innerPoint) :
    ∃ a b : ι, ∃ hab : a ≠ b, ∃ S : SeparatorPair (F a) (F b),
      (P.interiorRegion ⊆
            (S.circle₀ hPQ (hpairwise hab)).inside ∧
          ∀ c : ι, c ≠ a → c ≠ b →
            (F c).outerPoint ∉ range S.outerArc₁) ∨
        (P.interiorRegion ⊆
            (S.circle₁ hPQ (hpairwise hab)).inside ∧
          ∀ c : ι, c ≠ a → c ≠ b →
            (F c).outerPoint ∉ range S.outerArc₀) := by
  classical
  have hnonempty : Nonempty ι :=
    Fintype.card_pos_iff.mp (by omega)
  let a : ι := Classical.choice hnonempty
  obtain ⟨b, hab, S, hS⟩ :=
    PolygonalCircle.AnnularCrosscut.SeparatorPair.exists_cutFreeArcFrom
      F hcard hPQ hpairwise hinnerInjective houterInjective hsegment a
  exact ⟨a, b, hab, S, hS⟩

end PolygonalCircle.AnnularCrosscut.SeparatorPair

end

end Schoenflies
