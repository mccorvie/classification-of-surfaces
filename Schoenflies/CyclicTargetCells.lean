import Schoenflies.IndexedStandardCrosscuts
import Schoenflies.AnnularCellAttachments
import Schoenflies.FiniteAnnularCrosscutOrder

/-!
# Canonically indexed cells in a standard radial shell

At a binary address level, the cell labelled `a` is bounded by the radial
cuts at `a` and `nextLevelAddress n a`.  Its two circular sides are obtained
by transporting the actual elementary Jordan arc to the two standard target
boundaries.  Thus the target cells have exactly the cyclic nerve of the
recursive Moise cells, independently of the radial shell index.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Transport the canonical elementary level split to target boundary `m`. -/
noncomputable def indexedTargetBoundarySplit (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    (disk m).toJordanCircle.TwoBoundaryArcPaths
      (I.indexedTargetMark m a)
      (I.indexedTargetMark m (nextLevelAddress n a)) :=
  ((I.levelBoundarySplit a).mapCarrier
      (jordanToDiskBoundaryHomeomorph J m)).cast
    (by
      simp only [jordanToDiskBoundaryHomeomorph_apply]
      rfl)
    (by
      simp only [jordanToDiskBoundaryHomeomorph_apply]
      rfl)

/-- Every third retained radial mark lies on the complementary target path. -/
theorem other_indexedTargetMark_mem_boundarySplit_second
    (m : ℕ) {n : ℕ} (a c : LevelAddress n)
    (hca : c ≠ a) (hcnext : c ≠ nextLevelAddress n a) :
    I.indexedTargetMark m c ∈
      range (I.indexedTargetBoundarySplit m a).second := by
  obtain ⟨t, ht⟩ :=
    I.other_levelLeftPoint_mem_levelBoundarySplit_second a c hca hcnext
  refine ⟨t, ?_⟩
  change (jordanToDiskBoundaryHomeomorph J m
      ⟨(I.levelBoundarySplit a).second t, _⟩ : Plane) = _
  rw [jordanToDiskBoundaryHomeomorph_apply]
  congr 1
  have hsub :
      (⟨(I.levelBoundarySplit a).second t,
        (I.levelBoundarySplit a).second_range_subset_carrier
          ⟨t, rfl⟩⟩ : J.carrier) =
        J.curvePoint (I.levelArc c).left :=
    Subtype.ext ht
  rw [hsub]
  rfl

/-- The two radial cuts and the same transported elementary split at both
radii. -/
noncomputable def cyclicTargetSeparator (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    PolygonalCircle.AnnularCrosscut.SeparatorPair
      (I.indexedTargetAnnularCrosscut m a)
      (I.indexedTargetAnnularCrosscut m (nextLevelAddress n a)) where
  innerSplit := I.indexedTargetBoundarySplit m a
  outerSplit := I.indexedTargetBoundarySplit (m + 1) a

/-- The standard radial annulus cut along two cyclically consecutive binary
labels. -/
noncomputable def cyclicTargetDecomposition (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    PolygonalCircle.AnnularCellDecomposition (disk m) (disk (m + 1)) where
  first := I.indexedTargetAnnularCrosscut m a
  second := I.indexedTargetAnnularCrosscut m (nextLevelAddress n a)
  separator := I.cyclicTargetSeparator m a
  nested := disk_strictlyNested m
  disjoint := I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
    (nextLevelAddress_ne n a).symm
  outerPoints_ne := by
    exact (I.indexedTargetMark_injective (m + 1) n).ne
      (nextLevelAddress_ne n a).symm
  innerPoints_ne := by
    exact (I.indexedTargetMark_injective m n).ne
      (nextLevelAddress_ne n a).symm
  first_segment := by
    change range (Path.segment
      (I.indexedTargetMark (m + 1) a)
      (I.indexedTargetMark m a)) = _
    exact Path.range_segment _ _
  second_segment := by
    change range (Path.segment
      (I.indexedTargetMark (m + 1) (nextLevelAddress n a))
      (I.indexedTargetMark m (nextLevelAddress n a))) = _
    exact Path.range_segment _ _

def CyclicTargetFirstAlternative (m : ℕ) {n : ℕ}
    (a : LevelAddress n) : Prop :=
  (disk m).interiorRegion ⊆
    ((I.cyclicTargetSeparator m a).circle₀
      (disk_strictlyNested m)
      (I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
        (nextLevelAddress_ne n a).symm)).inside

theorem cyclicTarget_separatorSide (m : ℕ) {n : ℕ}
    (a : LevelAddress n) :
    I.CyclicTargetFirstAlternative m a ∨
      (disk m).interiorRegion ⊆
        ((I.cyclicTargetSeparator m a).circle₁
          (disk_strictlyNested m)
          (I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
            (nextLevelAddress_ne n a).symm)).inside := by
  rcases (I.cyclicTargetSeparator m a).innerInterior_separatorSide_dichotomy
      (disk_strictlyNested m)
      (I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
        (nextLevelAddress_ne n a).symm)
      (I.cyclicTargetDecomposition m a).first_segment
      (I.cyclicTargetDecomposition m a).second_segment with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

/-- With at least three retained labels, the transported elementary arc is
the side away from the inner disk. -/
theorem cyclicTargetFirstAlternative_of_one_le
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) (a : LevelAddress n) :
    I.CyclicTargetFirstAlternative m a := by
  have hinnerInjective : Injective fun c : LevelAddress n =>
      (I.indexedTargetAnnularCrosscut m c).innerPoint :=
    I.indexedTargetMark_injective m n
  have houterInjective : Injective fun c : LevelAddress n =>
      (I.indexedTargetAnnularCrosscut m c).outerPoint :=
    I.indexedTargetMark_injective (m + 1) n
  have hinnerSecond : ∀ c : LevelAddress n, c ≠ a →
      c ≠ nextLevelAddress n a →
      (I.indexedTargetAnnularCrosscut m c).innerPoint ∈
        range (I.cyclicTargetSeparator m a).innerSplit.second := by
    intro c hca hcnext
    exact I.other_indexedTargetMark_mem_boundarySplit_second
      m a c hca hcnext
  have hcyclic := (I.cyclicTargetSeparator m a).family_cyclicCompatibility
    (I.indexedTargetAnnularCrosscut m)
    (nextLevelAddress_ne n a).symm
    (disk_strictlyNested m)
    (I.pairwise_disjoint_indexedTargetAnnularCrosscut m n)
    hinnerInjective houterInjective
    (I.cyclicTargetDecomposition m a).first_segment
    (I.cyclicTargetDecomposition m a).second_segment hinnerSecond
  rcases hcyclic with hfirst | hsecond
  · exact hfirst.1
  · have hpairCard :
        ({a, nextLevelAddress n a} : Finset (LevelAddress n)).card <
          (Finset.univ : Finset (LevelAddress n)).card := by
      rw [Finset.card_univ]
      calc
        ({a, nextLevelAddress n a} : Finset (LevelAddress n)).card ≤
            ({nextLevelAddress n a} : Finset (LevelAddress n)).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp
        _ < Fintype.card (LevelAddress n) := by
          rw [levelAddress_card]
          calc
            2 < 4 := by norm_num
            _ = 2 ^ (1 + 1) := by norm_num
            _ ≤ 2 ^ (n + 1) :=
              pow_le_pow_right' (by norm_num) (by omega)
    obtain ⟨c, _hcuniv, hc⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hpairCard
    have hc' : c ≠ a ∧ c ≠ nextLevelAddress n a := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hc
    have hcFirst :
        (I.indexedTargetAnnularCrosscut m c).outerPoint ∈
          range (I.indexedTargetBoundarySplit (m + 1) a).first := by
      have h := hsecond.2 c hc'.1 hc'.2
      change (I.indexedTargetAnnularCrosscut m c).outerPoint ∈
        range (I.indexedTargetBoundarySplit (m + 1) a).first.symm at h
      simpa only [Path.symm_range] using h
    have hcSecond :
        (I.indexedTargetAnnularCrosscut m c).outerPoint ∈
          range (I.indexedTargetBoundarySplit (m + 1) a).second :=
      I.other_indexedTargetMark_mem_boundarySplit_second
        (m + 1) a c hc'.1 hc'.2
    have hcEnds :
        (I.indexedTargetAnnularCrosscut m c).outerPoint ∈
          ({I.indexedTargetMark (m + 1) a,
            I.indexedTargetMark (m + 1) (nextLevelAddress n a)} :
              Set Plane) := by
      rw [← (I.indexedTargetBoundarySplit (m + 1) a).overlap]
      exact ⟨hcFirst, hcSecond⟩
    rcases hcEnds with hca | hcnext
    · exact False.elim (hc'.1 (houterInjective hca))
    · exact False.elim
        (hc'.2 (houterInjective (Set.mem_singleton_iff.mp hcnext)))

theorem cyclicTargetSecondAlternative_of_not_first
    (m : ℕ) {n : ℕ} (a : LevelAddress n)
    (h : ¬ I.CyclicTargetFirstAlternative m a) :
    (disk m).interiorRegion ⊆
      ((I.cyclicTargetSeparator m a).circle₁
        (disk_strictlyNested m)
        (I.pairwise_disjoint_indexedTargetAnnularCrosscut m n
          (nextLevelAddress_ne n a).symm)).inside :=
  (I.cyclicTarget_separatorSide m a).resolve_left h

/-- The canonical target sector, presented as a disk attached to the inner
standard target disk. -/
noncomputable def cyclicTargetAttachmentPresentation
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    PolygonalDiskAttachment.Presentation (disk m).closedRegion := by
  classical
  exact if h : I.CyclicTargetFirstAlternative m a then
      (I.cyclicTargetDecomposition m a).attachmentPresentation₁ h
    else
      (I.cyclicTargetDecomposition m a).attachmentPresentation₀
        (I.cyclicTargetSecondAlternative_of_not_first m a h)

theorem cyclicTargetAttachmentPresentation_exposedSecondCoordinate
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (t : unitInterval) :
    (I.cyclicTargetAttachmentPresentation m a).exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedSecondCoordinate t) =
      (I.cyclicTargetDecomposition m a).second.path.symm t := by
  classical
  by_cases h : I.CyclicTargetFirstAlternative m a
  · rw [cyclicTargetAttachmentPresentation, dif_pos h]
    exact (I.cyclicTargetDecomposition m a).exposedPath_exposedSecondCoordinate
      _ t
  · rw [cyclicTargetAttachmentPresentation, dif_neg h]
    exact (I.cyclicTargetDecomposition m a).exposedPath_exposedSecondCoordinate
      _ t

theorem cyclicTargetAttachmentPresentation_exposedFirstCoordinate
    (m : ℕ) {n : ℕ} (a : LevelAddress n) (t : unitInterval) :
    (I.cyclicTargetAttachmentPresentation m a).exposed
        (PolygonalCircle.AnnularCellDecomposition.exposedFirstCoordinate t) =
      (I.cyclicTargetDecomposition m a).first.path t := by
  classical
  by_cases h : I.CyclicTargetFirstAlternative m a
  · rw [cyclicTargetAttachmentPresentation, dif_pos h]
    exact (I.cyclicTargetDecomposition m a).exposedPath_exposedFirstCoordinate
      _ t
  · rw [cyclicTargetAttachmentPresentation, dif_neg h]
    exact (I.cyclicTargetDecomposition m a).exposedPath_exposedFirstCoordinate
      _ t

theorem range_cyclicTargetAttachmentPresentation_shared
    (m : ℕ) {n : ℕ} (a : LevelAddress n) :
    range (I.cyclicTargetAttachmentPresentation m a).shared =
      range (I.indexedTargetBoundarySplit m a).first := by
  classical
  by_cases h : I.CyclicTargetFirstAlternative m a
  · rw [cyclicTargetAttachmentPresentation, dif_pos h]
    rfl
  · rw [cyclicTargetAttachmentPresentation, dif_neg h]
    rfl

/-- At a genuine binary refinement level, the complementary boundary of a
canonical target cell is its successor radial cut, its outer elementary arc,
and its initial radial cut. -/
theorem range_cyclicTargetAttachmentPresentation_exposed
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) (a : LevelAddress n) :
    range (I.cyclicTargetAttachmentPresentation m a).exposed =
      range (I.cyclicTargetDecomposition m a).second.path ∪
        (range (I.indexedTargetBoundarySplit (m + 1) a).first ∪
          range (I.cyclicTargetDecomposition m a).first.path) := by
  classical
  by_cases h : I.CyclicTargetFirstAlternative m a
  · rw [cyclicTargetAttachmentPresentation, dif_pos h]
    change range ((I.cyclicTargetDecomposition m a).exposedPath
        (I.cyclicTargetSeparator m a).outerArc₁) = _
    rw [(I.cyclicTargetDecomposition m a).range_exposedPath]
    change range (I.cyclicTargetDecomposition m a).second.path ∪
        (range (I.indexedTargetBoundarySplit (m + 1) a).first.symm ∪
          range (I.cyclicTargetDecomposition m a).first.path) = _
    rw [Path.symm_range]
  · exact False.elim (h (I.cyclicTargetFirstAlternative_of_one_le m hn a))

end JordanCircle.InitialAngularArcs

end

end Schoenflies
