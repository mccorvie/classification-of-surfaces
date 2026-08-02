import Schoenflies.LocalizedCutFreeCells
import Schoenflies.LocalizedJordanAnnularCrosscuts

/-!
# Boundary coherence for localized cut-free cells

A localized polygonal shell cell uses a canonical successor pair on its
inner boundary.  The same inner split can be combined with the retained
access-hair prefixes reaching all the way to the original Jordan curve.
Mixed-annulus cyclic order then selects the corresponding cut-free arc of
the original curve.  In particular, the polygonal cell and its eventual
target cell share one boundary labelling rather than making independent
complementary-arc choices.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev innerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

namespace LocalizedCutFreeCellData

variable {I : J.InitialAngularArcs} {k : ℕ} {a : LevelAddress k}
  (C : I.LocalizedCutFreeCellData k a)

theorem jordanOuterPoints_ne :
    (I.levelLocalizedJordanAnnularCrosscut k a).outerPoint ≠
      (I.levelLocalizedJordanAnnularCrosscut k C.next).outerPoint := by
  intro h
  exact C.next_ne
    (I.levelLocalizedJordanAnnularCrosscut_outerPoint_injective k h)

/-- The complementary arcs of the original Jordan curve at the two
canonical cell labels. -/
noncomputable def jordanOuterSplit :
    J.TwoBoundaryArcPaths
      (I.levelLocalizedJordanAnnularCrosscut k a).outerPoint
      (I.levelLocalizedJordanAnnularCrosscut k C.next).outerPoint :=
  Classical.choice <| J.exists_twoBoundaryArcPaths
    (I.levelLocalizedJordanAnnularCrosscut k a).outerPoint_mem
    (I.levelLocalizedJordanAnnularCrosscut k C.next).outerPoint_mem
    C.jordanOuterPoints_ne

/-- A mixed separator using exactly the inner split already chosen for the
localized polygonal shell cell. -/
noncomputable def jordanSeparator :
    PolygonalCircle.JordanAnnularCrosscut.SeparatorPair
      (I.levelLocalizedJordanAnnularCrosscut k a)
      (I.levelLocalizedJordanAnnularCrosscut k C.next) where
  innerSplit := C.separator.innerSplit
  outerSplit := C.jordanOuterSplit

@[simp] theorem jordanSeparator_innerSplit :
    C.jordanSeparator.innerSplit = C.separator.innerSplit := rfl

@[simp] theorem jordanSeparator_outerSplit :
    C.jordanSeparator.outerSplit = C.jordanOuterSplit := rfl

/-- The original Jordan arc corresponding to the exposed side of the
canonical inner split contains no third retained boundary anchor. -/
theorem jordan_cutFreeArcs :
    ((I.innerDisk k).interiorRegion ⊆
          (C.jordanSeparator.circle₀
            (I.localizedMarkedPolygonalDisk_closedRegion_subset_inside
              (k + 1))
            (I.pairwise_disjoint_levelLocalizedJordanAnnularCrosscut k
              C.next_ne)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
          (I.levelLocalizedJordanAnnularCrosscut k c).outerPoint ∉
            range C.jordanSeparator.outerArc₁) ∨
      ((I.innerDisk k).interiorRegion ⊆
          (C.jordanSeparator.circle₁
            (I.localizedMarkedPolygonalDisk_closedRegion_subset_inside
              (k + 1))
            (I.pairwise_disjoint_levelLocalizedJordanAnnularCrosscut k
              C.next_ne)).inside ∧
        ∀ c : LevelAddress k, c ≠ a → c ≠ C.next →
          (I.levelLocalizedJordanAnnularCrosscut k c).outerPoint ∉
            range C.jordanSeparator.outerArc₀) := by
  exact C.jordanSeparator.family_cutFreeArcs
    (I.levelLocalizedJordanAnnularCrosscut k)
    C.next_ne
    (I.localizedMarkedPolygonalDisk_closedRegion_subset_inside (k + 1))
    (I.pairwise_disjoint_levelLocalizedJordanAnnularCrosscut k)
    (I.levelLocalizedJordanAnnularCrosscut_innerPoint_injective k)
    (I.levelLocalizedJordanAnnularCrosscut_outerPoint_injective k)
    (I.range_levelLocalizedJordanAnnularCrosscut_eq_segment k a)
    (I.range_levelLocalizedJordanAnnularCrosscut_eq_segment k C.next)
    C.inner_second

end LocalizedCutFreeCellData

end JordanCircle.InitialAngularArcs

end

end Schoenflies
