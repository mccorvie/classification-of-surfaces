import Schoenflies.FiniteAnnularCrosscutOrder
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

private theorem range_levelLocalizedAnnularCrosscut_eq_segment
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
