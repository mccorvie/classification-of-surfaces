import Schoenflies.AngularDriftBounds
import Schoenflies.MoiseBandCrosscutLocalization

/-!
# Angular drift between consecutive raw Moise bands

On their shared polygonal carrier, the outer parametrization of one raw
Moise band and the inner parametrization of the next need not agree
pointwise.  Conjugating their discrepancy to the standard unit circle gives
a circle homeomorphism.  Coarse-window localization shows that this
homeomorphism, and therefore also its inverse, moves every point by at most
twice the largest angular window at the older subdivision level.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}
  (L : RecursiveInsideCollarStep.Later F hn)

private abbrev G (M : RecursiveInsideCollarStep.Later F hn) :
    I.LevelAvoidingJoinFamily M.next.level
      ((M.next.buffer / 4) / 4) :=
  M.next.family.forgetObstacle

variable
  (L₁ : RecursiveInsideCollarStep.Later (G L) L.next.one_le_level)

/-- The angular discrepancy between the raw outer boundary map of `L` and
the raw inner boundary map of the next band `L₁`. -/
def rawAngularBoundaryMismatch
    (m : ℕ)
    (houtward₀ : ∀ c : LevelAddress n,
      (F.synchronizedPolygonalCircle hn).closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (houtward₁ : ∀ c : LevelAddress L.next.level,
      ((G L).synchronizedPolygonalCircle
            L.next.one_le_level).closedRegion ∩
          (L₁.moiseBandPolygonalCircle c).closedRegion =
        range ((G L).synchronizedCrosscutPath c)) :
    sphere (0 : Plane) 1 ≃ₜ sphere (0 : Plane) 1 :=
  sphereToMasterHomeomorph.trans <|
    (diskBoundaryHomeomorph (m + 1)).trans <|
      ((L₁.markedMoiseRawInnerBoundaryHomeomorph (m + 1) houtward₁).symm.trans <|
        (L.markedMoiseRawOuterBoundaryHomeomorph m houtward₀).trans <|
          (diskBoundaryHomeomorph (m + 1)).symm.trans
            sphereToMasterHomeomorph.symm)

/-- Expanded point formula for the raw angular mismatch. -/
theorem rawAngularBoundaryMismatch_apply
    (m : ℕ)
    (houtward₀ : ∀ c : LevelAddress n,
      (F.synchronizedPolygonalCircle hn).closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (houtward₁ : ∀ c : LevelAddress L.next.level,
      ((G L).synchronizedPolygonalCircle
            L.next.one_le_level).closedRegion ∩
          (L₁.moiseBandPolygonalCircle c).closedRegion =
        range ((G L).synchronizedCrosscutPath c))
    (u : sphere (0 : Plane) 1) :
    rawAngularBoundaryMismatch L L₁ m houtward₀ houtward₁ u =
      normalizedTargetBoundaryPoint (m + 1)
        (L.markedMoiseRawOuterBoundaryHomeomorph m houtward₀
          ((L₁.markedMoiseRawInnerBoundaryHomeomorph (m + 1)
              houtward₁).symm
            (diskBoundaryHomeomorph (m + 1)
              (sphereToMasterHomeomorph u)))) := by
  rfl

/-- **One-step drift bound.**  The discrepancy of consecutive raw boundary
parametrizations moves no angular point by more than twice the largest
window at the older level. -/
theorem dist_rawAngularBoundaryMismatch_apply_le
    (m : ℕ)
    (houtward₀ : ∀ c : LevelAddress n,
      (F.synchronizedPolygonalCircle hn).closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (houtward₁ : ∀ c : LevelAddress L.next.level,
      ((G L).synchronizedPolygonalCircle
            L.next.one_le_level).closedRegion ∩
          (L₁.moiseBandPolygonalCircle c).closedRegion =
        range ((G L).synchronizedCrosscutPath c))
    (u : sphere (0 : Plane) 1) :
    dist (rawAngularBoundaryMismatch L L₁ m houtward₀ houtward₁ u) u ≤
      2 * ((2 / 3 : ℝ) ^ n * max I.first.width I.second.width) := by
  let y : (disk (m + 1)).carrier :=
    diskBoundaryHomeomorph (m + 1) (sphereToMasterHomeomorph u)
  let x : ((G L).synchronizedPolygonalCircle
      L.next.one_le_level).carrier :=
    (L₁.markedMoiseRawInnerBoundaryHomeomorph (m + 1) houtward₁).symm y
  obtain ⟨a, hOuter, hInner⟩ :=
    L.rawBoundary_mem_masterArcImage_tripled L₁ m houtward₀ houtward₁ x
  have hbound := I.dist_normalizedTargetBoundaryPoint_le_two_mul_levelMax
    (m + 1) a
    (L.markedMoiseRawOuterBoundaryHomeomorph m houtward₀ x)
    (L₁.markedMoiseRawInnerBoundaryHomeomorph (m + 1) houtward₁ x)
    (by
      change (L.markedMoiseRawOuterBoundaryHomeomorph m houtward₀ x : Plane) ∈ _
      exact hOuter)
    (by
      change (L₁.markedMoiseRawInnerBoundaryHomeomorph
        (m + 1) houtward₁ x : Plane) ∈ _
      exact hInner)
  rw [rawAngularBoundaryMismatch_apply L L₁ m houtward₀ houtward₁]
  change dist
    (normalizedTargetBoundaryPoint (m + 1)
      (L.markedMoiseRawOuterBoundaryHomeomorph m houtward₀ x)) u ≤ _
  have hnew :
      normalizedTargetBoundaryPoint (m + 1)
        (L₁.markedMoiseRawInnerBoundaryHomeomorph (m + 1) houtward₁ x) = u := by
    simp only [normalizedTargetBoundaryPoint, x, y,
      Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  rwa [hnew] at hbound

/-- The inverse discrepancy satisfies the same displacement bound. -/
theorem dist_rawAngularBoundaryMismatch_symm_apply_le
    (m : ℕ)
    (houtward₀ : ∀ c : LevelAddress n,
      (F.synchronizedPolygonalCircle hn).closedRegion ∩
          (L.moiseBandPolygonalCircle c).closedRegion =
        range (F.synchronizedCrosscutPath c))
    (houtward₁ : ∀ c : LevelAddress L.next.level,
      ((G L).synchronizedPolygonalCircle
            L.next.one_le_level).closedRegion ∩
          (L₁.moiseBandPolygonalCircle c).closedRegion =
        range ((G L).synchronizedCrosscutPath c))
    (u : sphere (0 : Plane) 1) :
    dist ((rawAngularBoundaryMismatch L L₁ m houtward₀ houtward₁).symm u) u ≤
      2 * ((2 / 3 : ℝ) ^ n * max I.first.width I.second.width) := by
  let v := (rawAngularBoundaryMismatch L L₁ m houtward₀ houtward₁).symm u
  have h := dist_rawAngularBoundaryMismatch_apply_le L L₁ m
    houtward₀ houtward₁ v
  rw [Homeomorph.apply_symm_apply, dist_comm] at h
  exact h

end JordanCircle.InitialAngularArcs

end

end Schoenflies
