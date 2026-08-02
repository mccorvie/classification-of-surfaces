import Schoenflies.MoiseBandCellBounds
import Schoenflies.NestedCollarStages

/-!
# Uniformly shrinking cells in the recursive Moise bands

This specializes the two-step band estimate to the recursively selected
collars.  Bands after the initial one shrink at the explicit harmonic rate
used by `shrinkingInsideCollarStage`.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- Starting from any packaged stage, first take successor `k`, and then
successor `k+1`.  Every Moise cell in the band between those two successors
is bounded by the sum of their prescribed quarter-buffer bounds. -/
theorem nextInsideCollarMoiseBandClosedRegion_subset_closedBall
    (k : ℕ) (S : I.InsideCollarStage)
    (a : LevelAddress (I.nextInsideCollarLater k S).next.level) :
    let S₁ := InsideCollarStage.ofLater I S
      (I.nextInsideCollarLater k S)
    let L₁ := I.nextInsideCollarLater (k + 1) S₁
    (L₁.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4) := by
  dsimp only
  let L₀ := I.nextInsideCollarLater k S
  let T := L₀.next
  let S₁ := InsideCollarStage.ofLater I S L₀
  let L₁ := I.nextInsideCollarLater (k + 1) S₁
  have hcell : (L₁.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (T.buffer / 4 + L₁.next.buffer / 4) := by
    exact T.moiseBandClosedRegion_subset_closedBall L₁ a
  have h₀ : T.buffer ≤ successorBufferBound k := by
    exact I.nextInsideCollarLater_buffer_le k S
  have h₁ : L₁.next.buffer ≤ successorBufferBound (k + 1) := by
    exact I.nextInsideCollarLater_buffer_le (k + 1) S₁
  exact hcell.trans (closedBall_subset_closedBall (by linarith))

/-- The actual recursive sequence has the same bound on the band between
stages `k+1` and `k+2`. -/
theorem shrinkingMoiseBandClosedRegion_subset_closedBall
    (k : ℕ)
    (a : LevelAddress
      (I.nextInsideCollarLater k
        (I.shrinkingInsideCollarStage k)).next.level) :
    let S₁ := InsideCollarStage.ofLater I
      (I.shrinkingInsideCollarStage k)
      (I.nextInsideCollarLater k (I.shrinkingInsideCollarStage k))
    let L := I.nextInsideCollarLater (k + 1) S₁
    (L.moiseBandPolygonalCircle a).closedRegion ⊆
      closedBall (J.curvePoint (I.levelArc a).left : Plane)
        (successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4) := by
  exact I.nextInsideCollarMoiseBandClosedRegion_subset_closedBall k
    (I.shrinkingInsideCollarStage k) a

/-- Uniform shrinking of all cells in sufficiently late Moise bands.  This
is the metric input for continuity of the eventual cellwise map at the
original Jordan boundary. -/
theorem eventually_shrinkingMoiseBandClosedRegion_subset_closedBall
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ a : LevelAddress
        (I.nextInsideCollarLater k
          (I.shrinkingInsideCollarStage k)).next.level,
      let S₁ := InsideCollarStage.ofLater I
        (I.shrinkingInsideCollarStage k)
        (I.nextInsideCollarLater k (I.shrinkingInsideCollarStage k))
      let L := I.nextInsideCollarLater (k + 1) S₁
      (L.moiseBandPolygonalCircle a).closedRegion ⊆
        closedBall (J.curvePoint (I.levelArc a).left : Plane) rho := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hrho
  refine ⟨N, ?_⟩
  intro k hk a
  have hmonotone : successorBufferBound k ≤ successorBufferBound N := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right hk 1
  have hsmall : successorBufferBound N < rho := by
    simpa [successorBufferBound, one_div] using hN
  have hnext : successorBufferBound (k + 1) ≤
      successorBufferBound k := by
    unfold successorBufferBound
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    norm_num
  have hkpos := successorBufferBound_pos k
  have hradius : successorBufferBound k / 4 +
      successorBufferBound (k + 1) / 4 ≤ rho := by
    calc
      successorBufferBound k / 4 +
          successorBufferBound (k + 1) / 4 ≤
          successorBufferBound k / 4 +
            successorBufferBound k / 4 := by linarith
      _ ≤ successorBufferBound k := by linarith
      _ ≤ successorBufferBound N := hmonotone
      _ ≤ rho := hsmall.le
  exact (I.shrinkingMoiseBandClosedRegion_subset_closedBall k a).trans
    (closedBall_subset_closedBall hradius)

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
