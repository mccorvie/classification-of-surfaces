import Schoenflies.HierarchicalCollarStages

/-!
# A shrinking recursive sequence of polygonal collars

Moise Chapter 9 uses a countable sequence of finite polygonal collars.  The
one-step API already supplies a later collar avoiding the preceding closed
polygonal disk.  This file makes the choices recursively and, importantly,
forces the separation buffers to tend to zero.

The unresolved nesting theorem (that the preceding disk is on the bounded
side of the next collar) is deliberately not built into `InsideCollarStage`.
The sequence below records all of the choice, avoidance, depth, and metric
facts independently of that remaining planar-side argument.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- One synchronized polygonal collar, hiding the dependent subdivision
level and control scale behind a stable sequence-friendly interface. -/
structure InsideCollarStage where
  level : ℕ
  one_le_level : 1 ≤ level
  epsilon : ℝ
  family : I.LevelAvoidingJoinFamily level epsilon

namespace InsideCollarStage

/-- The polygonal circle carried by a packaged collar stage. -/
noncomputable def circle (S : I.InsideCollarStage) : PolygonalCircle :=
  S.family.synchronizedPolygonalCircle S.one_le_level

theorem circle_closedRegion_subset_inside (S : I.InsideCollarStage) :
    S.circle.closedRegion ⊆ J.inside :=
  S.family.closedRegion_synchronizedPolygonalCircle_subset_inside
    S.one_le_level

/-- Forget the obstacle certificate of a recursive step and package its
new synchronized collar as an independent stage. -/
noncomputable def ofLater (S : I.InsideCollarStage)
    (L : RecursiveInsideCollarStep.Later S.family S.one_le_level) :
    I.InsideCollarStage where
  level := L.next.level
  one_le_level := L.next.one_le_level
  epsilon := (L.next.buffer / 4) / 4
  family := L.next.family.forgetObstacle

@[simp] theorem ofLater_level (S : I.InsideCollarStage)
    (L : RecursiveInsideCollarStep.Later S.family S.one_le_level) :
    (InsideCollarStage.ofLater I S L).level = L.next.level := rfl

@[simp] theorem ofLater_family (S : I.InsideCollarStage)
    (L : RecursiveInsideCollarStep.Later S.family S.one_le_level) :
    (InsideCollarStage.ofLater I S L).family =
      L.next.family.forgetObstacle := rfl

@[simp] theorem circle_ofLater (S : I.InsideCollarStage)
    (L : RecursiveInsideCollarStep.Later S.family S.one_le_level) :
    (InsideCollarStage.ofLater I S L).circle = L.next.circle := rfl

end InsideCollarStage

/-- The first collar; later stages carry all quantitative shrinking data, so
any fixed positive control scale is sufficient here. -/
noncomputable def initialInsideCollarStage : I.InsideCollarStage where
  level := 1
  one_le_level := le_rfl
  epsilon := 1
  family := Classical.choice (I.nonempty_levelAvoidingJoinFamily 1 one_pos)

/-- The prescribed upper bound for the buffer used to choose successor
number `k + 1`. -/
def successorBufferBound (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ)⁻¹

theorem successorBufferBound_pos (k : ℕ) :
    0 < successorBufferBound k := by
  unfold successorBufferBound
  positivity

/-- Choose a later avoiding collar whose buffer satisfies the prescribed
shrinking bound. -/
noncomputable def nextInsideCollarLater (k : ℕ)
    (S : I.InsideCollarStage) :
    RecursiveInsideCollarStep.Later S.family S.one_le_level :=
  Classical.choose <|
    RecursiveInsideCollarStep.exists_later_buffer_le
      S.family S.one_le_level (I := I) (successorBufferBound_pos k)

theorem nextInsideCollarLater_buffer_le (k : ℕ)
    (S : I.InsideCollarStage) :
    (I.nextInsideCollarLater k S).next.buffer ≤
      successorBufferBound k :=
  Classical.choose_spec
    (RecursiveInsideCollarStep.exists_later_buffer_le
      S.family S.one_le_level (I := I) (successorBufferBound_pos k))

/-- The successor operation on packaged stages. -/
noncomputable def nextInsideCollarStage (k : ℕ)
    (S : I.InsideCollarStage) : I.InsideCollarStage :=
  InsideCollarStage.ofLater I S (I.nextInsideCollarLater k S)

/-- Moise's recursively chosen sequence of polygonal collars. -/
noncomputable def shrinkingInsideCollarStage : ℕ → I.InsideCollarStage
  | 0 => I.initialInsideCollarStage
  | k + 1 => I.nextInsideCollarStage k (shrinkingInsideCollarStage k)

@[simp] theorem shrinkingInsideCollarStage_zero :
    I.shrinkingInsideCollarStage 0 = I.initialInsideCollarStage := rfl

@[simp] theorem shrinkingInsideCollarStage_succ (k : ℕ) :
    I.shrinkingInsideCollarStage k.succ =
      I.nextInsideCollarStage k (I.shrinkingInsideCollarStage k) := rfl

/-- Subdivision depth strictly increases at every recursive step. -/
theorem shrinkingInsideCollarStage_level_strict (k : ℕ) :
    (I.shrinkingInsideCollarStage k).level <
      (I.shrinkingInsideCollarStage (k + 1)).level := by
  rw [I.shrinkingInsideCollarStage_succ k]
  exact (I.nextInsideCollarLater k
    (I.shrinkingInsideCollarStage k)).later

/-- The next polygonal carrier is disjoint from the whole preceding closed
polygonal disk, not only from its frontier. -/
theorem shrinkingInsideCollarStage_disjoint_next_carrier (k : ℕ) :
    Disjoint
      (I.shrinkingInsideCollarStage k).circle.closedRegion
      (I.shrinkingInsideCollarStage (k + 1)).circle.carrier := by
  rw [I.shrinkingInsideCollarStage_succ k]
  exact (I.nextInsideCollarLater k
    (I.shrinkingInsideCollarStage k)).next.carrier_disjoint

/-- Every successor carrier lies in a closed neighborhood of the Jordan
curve whose radius is bounded explicitly by `1 / (4 * (k+1))`. -/
theorem shrinkingInsideCollarStage_next_carrier_subset_cthickening (k : ℕ) :
    (I.shrinkingInsideCollarStage (k + 1)).circle.carrier ⊆
      cthickening (successorBufferBound k / 4) J.carrier := by
  let S := I.shrinkingInsideCollarStage k
  let L := I.nextInsideCollarLater k S
  have hnear : L.next.circle.carrier ⊆
      cthickening (L.next.buffer / 4) J.carrier :=
    L.next.circle_carrier_subset_cthickening_quarter
  have hbuffer : L.next.buffer ≤ successorBufferBound k :=
    I.nextInsideCollarLater_buffer_le k S
  have hresult := hnear.trans (cthickening_mono
    (div_le_div_of_nonneg_right hbuffer (by norm_num : (0 : ℝ) ≤ 4))
    J.carrier)
  simpa [S, L, nextInsideCollarStage] using hresult

/-- The successor polygonal carriers eventually lie in every prescribed
positive closed neighborhood of the Jordan curve. -/
theorem eventually_shrinkingInsideCollarStage_next_carrier_subset_cthickening
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (I.shrinkingInsideCollarStage (k + 1)).circle.carrier ⊆
        cthickening δ J.carrier := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, ?_⟩
  intro k hk
  have hmono : successorBufferBound k ≤ successorBufferBound N := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right hk 1
  have hsmall : successorBufferBound N < δ := by
    simpa [successorBufferBound, one_div] using hN
  have hradius : successorBufferBound k / 4 ≤ δ := by
    have hkpos := successorBufferBound_pos k
    calc
      successorBufferBound k / 4 ≤ successorBufferBound k := by
        nlinarith
      _ ≤ successorBufferBound N := hmono
      _ ≤ δ := hsmall.le
  exact (I.shrinkingInsideCollarStage_next_carrier_subset_cthickening k).trans
    (cthickening_mono hradius J.carrier)

/-- Every stage bounds a polygonal disk contained in the original Jordan
inside. -/
theorem shrinkingInsideCollarStage_closedRegion_subset_inside (k : ℕ) :
    (I.shrinkingInsideCollarStage k).circle.closedRegion ⊆ J.inside :=
  (I.shrinkingInsideCollarStage k).circle_closedRegion_subset_inside

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
