import Schoenflies.FiniteAnnularCrosscutOrder
import Schoenflies.FiniteJordanCyclicOrder
import Schoenflies.LocalizedAnnularTheta

/-!
# Cyclic compatibility of the localized shell cuts

This file instantiates the finite-family annular order theorem with every
retained straight hair at a localized exhaustion level.  The only remaining
input for a concrete cell is the purely one-dimensional assertion that the
chosen inner boundary arc contains all the other marked endpoints.
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

theorem range_levelLocalizedAnnularCrosscut_eq_segment
    (k : ℕ) (a : LevelAddress k) :
    range (I.levelLocalizedAnnularCrosscut k a).path =
      segment ℝ (I.levelLocalizedAnnularCrosscut k a).outerPoint
        (I.levelLocalizedAnnularCrosscut k a).innerPoint := by
  change range (Path.segment
      (I.levelLocalizedOuterBoundaryMark k a)
      (I.levelLocalizedPolygonalBoundaryMark k a)) =
    segment ℝ (I.levelLocalizedOuterBoundaryMark k a)
      (I.levelLocalizedPolygonalBoundaryMark k a)
  exact Path.range_segment _ _

private theorem two_le_card_levelAddress (k : ℕ) :
    2 ≤ Fintype.card (LevelAddress k) := by
  rw [levelAddress_card]
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) :=
      pow_le_pow_right' (by norm_num) (by omega)

/-- The localized inner-boundary marks, equipped with one canonical cyclic
order shared by every cell at this shell level. -/
noncomputable def levelLocalizedInnerMarking (k : ℕ) :
    (I.innerDisk k).toJordanCircle.FiniteMarking (LevelAddress k) where
  point := fun a => (I.levelLocalizedAnnularCrosscut k a).innerPoint
  point_mem := fun a => by
    simpa only [(I.innerDisk k).carrier_toJordanCircle] using
      (I.levelLocalizedAnnularCrosscut k a).innerPoint_mem
  point_injective := I.levelLocalizedPolygonalBoundaryMark_injective k
  two_le_card := two_le_card_levelAddress k

/-- The next retained cut in the actual cyclic order of the localized inner
polygonal boundary. -/
noncomputable def levelLocalizedSuccessor (k : ℕ)
    (a : LevelAddress k) : LevelAddress k :=
  (I.levelLocalizedInnerMarking k).successor a

/-- The preceding retained cut in the same canonical cyclic order. -/
noncomputable def levelLocalizedPredecessor (k : ℕ)
    (a : LevelAddress k) : LevelAddress k :=
  (I.levelLocalizedInnerMarking k).predecessor a

@[simp] theorem levelLocalizedSuccessor_predecessor (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedSuccessor k (I.levelLocalizedPredecessor k a) = a :=
  (I.levelLocalizedInnerMarking k).successor_predecessor a

@[simp] theorem levelLocalizedPredecessor_successor (k : ℕ)
    (a : LevelAddress k) :
    I.levelLocalizedPredecessor k (I.levelLocalizedSuccessor k a) = a :=
  (I.levelLocalizedInnerMarking k).predecessor_successor a

theorem levelLocalizedSuccessor_bijective (k : ℕ) :
    Function.Bijective (I.levelLocalizedSuccessor k) :=
  (I.levelLocalizedInnerMarking k).successor_bijective

theorem levelLocalizedSuccessor_ne (k : ℕ) (a : LevelAddress k) :
    I.levelLocalizedSuccessor k a ≠ a :=
  (I.levelLocalizedInnerMarking k).successor_ne a

theorem three_le_card_levelAddress (k : ℕ) (hk : 1 ≤ k) :
    3 ≤ Fintype.card (LevelAddress k) := by
  rw [levelAddress_card]
  calc
    3 ≤ 4 := by norm_num
    _ = 2 ^ (1 + 1) := by norm_num
    _ ≤ 2 ^ (k + 1) :=
      pow_le_pow_right' (by norm_num) (by omega)

/-- From the first genuine refinement onward there are at least four retained
cuts, so advancing twice in their cyclic order cannot return to the starting
cut.  The level-zero two-cut shell is intentionally handled separately. -/
theorem levelLocalizedSuccessor_successor_ne (k : ℕ) (hk : 1 ≤ k)
    (a : LevelAddress k) :
    I.levelLocalizedSuccessor k (I.levelLocalizedSuccessor k a) ≠ a := by
  apply (I.levelLocalizedInnerMarking k).successor_successor_ne
  exact three_le_card_levelAddress k hk

/-- The canonical successor pair bounds a cut-free cell.  This is the
coherent version of `exists_levelLocalized_cutFreeArcFrom`: all starting
cuts use the same cyclic successor permutation. -/
theorem exists_levelLocalized_cutFreeArcToSuccessor
    (k : ℕ) (a : LevelAddress k) :
    ∃ S : PolygonalCircle.AnnularCrosscut.SeparatorPair
        (I.levelLocalizedAnnularCrosscut k a)
        (I.levelLocalizedAnnularCrosscut k
          (I.levelLocalizedSuccessor k a)),
      (∀ c : LevelAddress k, c ≠ a →
          c ≠ I.levelLocalizedSuccessor k a →
        (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
          range S.innerSplit.second) ∧
      (((I.innerDisk k).interiorRegion ⊆
            (S.circle₀
              (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
              (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k
                (I.levelLocalizedSuccessor_ne k a).symm)).inside ∧
          ∀ c : LevelAddress k, c ≠ a →
              c ≠ I.levelLocalizedSuccessor k a →
            (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
              range S.outerArc₁) ∨
        ((I.innerDisk k).interiorRegion ⊆
            (S.circle₁
              (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
              (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k
                (I.levelLocalizedSuccessor_ne k a).symm)).inside ∧
          ∀ c : LevelAddress k, c ≠ a →
              c ≠ I.levelLocalizedSuccessor k a →
            (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
              range S.outerArc₀)) := by
  let M := I.levelLocalizedInnerMarking k
  obtain ⟨innerSplit, hinnerSplit⟩ :=
    M.exists_successor_twoBoundaryArcPaths a
  have hinnerSecond := hinnerSplit.2
  have hab : a ≠ I.levelLocalizedSuccessor k a :=
    (I.levelLocalizedSuccessor_ne k a).symm
  have hOuterNe :
      (I.levelLocalizedAnnularCrosscut k a).outerPoint ≠
        (I.levelLocalizedAnnularCrosscut k
          (I.levelLocalizedSuccessor k a)).outerPoint := by
    intro h
    exact hab (I.levelLocalizedOuterBoundaryMark_injective k h)
  let outerSplit := Classical.choice <|
    (I.outerDisk k).toJordanCircle.exists_twoBoundaryArcPaths
      (by simpa only [(I.outerDisk k).carrier_toJordanCircle] using
        (I.levelLocalizedAnnularCrosscut k a).outerPoint_mem)
      (by simpa only [(I.outerDisk k).carrier_toJordanCircle] using
        (I.levelLocalizedAnnularCrosscut k
          (I.levelLocalizedSuccessor k a)).outerPoint_mem)
      hOuterNe
  let S : PolygonalCircle.AnnularCrosscut.SeparatorPair
      (I.levelLocalizedAnnularCrosscut k a)
      (I.levelLocalizedAnnularCrosscut k
        (I.levelLocalizedSuccessor k a)) :=
    ⟨innerSplit, outerSplit⟩
  refine ⟨S, hinnerSecond, ?_⟩
  exact S.family_cutFreeArcs (I.levelLocalizedAnnularCrosscut k) hab
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k)
    (I.levelLocalizedPolygonalBoundaryMark_injective k)
    (I.levelLocalizedOuterBoundaryMark_injective k)
    (I.range_levelLocalizedAnnularCrosscut_eq_segment k a)
    (I.range_levelLocalizedAnnularCrosscut_eq_segment k
      (I.levelLocalizedSuccessor k a)) hinnerSecond

/-- At a localized shell level, an endpoint-free inner arc has a matching
endpoint-free outer arc.  The alternative in the conclusion says which of
the two complementary separators contains the inner polygonal disk. -/
theorem levelLocalized_cutFreeArcs
    (k : ℕ) {a b : LevelAddress k} (hab : a ≠ b)
    (hinnerSecond : ∀ c : LevelAddress k, c ≠ a → c ≠ b →
      (I.levelLocalizedAnnularCrosscut k c).innerPoint ∈
        range (I.levelLocalizedSeparatorPair k hab).innerSplit.second) :
    ((I.innerDisk k).interiorRegion ⊆
          ((I.levelLocalizedSeparatorPair k hab).circle₀
            (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
            (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ b →
          (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
            range (I.levelLocalizedSeparatorPair k hab).outerArc₁) ∨
      ((I.innerDisk k).interiorRegion ⊆
          ((I.levelLocalizedSeparatorPair k hab).circle₁
            (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
            (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ b →
          (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
            range (I.levelLocalizedSeparatorPair k hab).outerArc₀) := by
  let F := I.levelLocalizedAnnularCrosscut k
  let S := I.levelLocalizedSeparatorPair k hab
  change ((I.innerDisk k).interiorRegion ⊆
        (S.circle₀
          (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
          (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
      ∀ c : LevelAddress k, c ≠ a → c ≠ b →
        (F c).outerPoint ∉ range S.outerArc₁) ∨
    ((I.innerDisk k).interiorRegion ⊆
        (S.circle₁
          (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
          (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
      ∀ c : LevelAddress k, c ≠ a → c ≠ b →
        (F c).outerPoint ∉ range S.outerArc₀)
  exact S.family_cutFreeArcs F hab
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
    (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k)
    (I.levelLocalizedPolygonalBoundaryMark_injective k)
    (I.levelLocalizedOuterBoundaryMark_injective k)
    (I.range_levelLocalizedAnnularCrosscut_eq_segment k a)
    (I.range_levelLocalizedAnnularCrosscut_eq_segment k b)
    hinnerSecond

/-- Every prescribed retained cut has a next neighbor on the inner polygon,
and the two cuts bound a cell whose corresponding outer arc contains no
other retained endpoint. -/
theorem exists_levelLocalized_cutFreeArcFrom
    (k : ℕ) (a : LevelAddress k) :
    ∃ b : LevelAddress k, ∃ hab : a ≠ b,
      ∃ S : PolygonalCircle.AnnularCrosscut.SeparatorPair
          (I.levelLocalizedAnnularCrosscut k a)
          (I.levelLocalizedAnnularCrosscut k b),
        ((I.innerDisk k).interiorRegion ⊆
              (S.circle₀
                (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
                (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
            ∀ c : LevelAddress k, c ≠ a → c ≠ b →
              (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
                range S.outerArc₁) ∨
          ((I.innerDisk k).interiorRegion ⊆
              (S.circle₁
                (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
                (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
            ∀ c : LevelAddress k, c ≠ a → c ≠ b →
              (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
                range S.outerArc₀) := by
  let F := I.levelLocalizedAnnularCrosscut k
  exact
    PolygonalCircle.AnnularCrosscut.SeparatorPair.exists_cutFreeArcFrom F
      (two_le_card_levelAddress k)
      (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
      (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k)
      (I.levelLocalizedPolygonalBoundaryMark_injective k)
      (I.levelLocalizedOuterBoundaryMark_injective k)
      (I.range_levelLocalizedAnnularCrosscut_eq_segment k) a

/-- Every localized shell level has a pair of retained cuts bounding a
cut-free cell.  No cyclic-order assumption remains: the inner pair and its
controlled split are selected by the finite Jordan-circle theorem. -/
theorem exists_levelLocalized_cutFreeArcs (k : ℕ) :
    ∃ a b : LevelAddress k, ∃ hab : a ≠ b,
      ∃ S : PolygonalCircle.AnnularCrosscut.SeparatorPair
          (I.levelLocalizedAnnularCrosscut k a)
          (I.levelLocalizedAnnularCrosscut k b),
        ((I.innerDisk k).interiorRegion ⊆
              (S.circle₀
                (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
                (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
            ∀ c : LevelAddress k, c ≠ a → c ≠ b →
              (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
                range S.outerArc₁) ∨
          ((I.innerDisk k).interiorRegion ⊆
              (S.circle₁
                (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1))
                (I.pairwise_disjoint_levelLocalizedAnnularCrosscut k hab)).inside ∧
            ∀ c : LevelAddress k, c ≠ a → c ≠ b →
              (I.levelLocalizedAnnularCrosscut k c).outerPoint ∉
                range S.outerArc₀) := by
  classical
  let a : LevelAddress k := Classical.choice <|
    Fintype.card_pos_iff.mp (by
      have := two_le_card_levelAddress k
      omega)
  obtain ⟨b, hab, S, hS⟩ :=
    I.exists_levelLocalized_cutFreeArcFrom k a
  exact ⟨a, b, hab, S, hS⟩

end JordanCircle.InitialAngularArcs

end

end Schoenflies
