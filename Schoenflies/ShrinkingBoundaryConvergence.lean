import Schoenflies.DampedTargetCellBounds
import Schoenflies.ShrinkingInteriorHomeomorphism
import Schoenflies.ShrinkingMoiseBandCells

/-!
# Boundary convergence of the shrinking interior homeomorphism

The source and target cells of sufficiently late compatible Moise bands are
uniformly small about corresponding Jordan and master boundary points.  This
file transfers the damped-shell estimate through the recursive closed-disk
stages to the open direct-limit homeomorphism.
-/

namespace Schoenflies

open Metric Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The actual compatible source cells shrink uniformly about their indexed
Jordan boundary points. -/
theorem eventually_shrinkingCompatibleBandClosedRegion_subset_closedBall
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : LevelAddress
        (I.shrinkingCompatibleBandParentStage n).level,
      ((I.shrinkingCompatibleBand n).moiseBandPolygonalCircle a).closedRegion ⊆
        closedBall (J.curvePoint (I.levelArc a).left : Plane) rho := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingMoiseBandClosedRegion_subset_closedBall hrho
  refine ⟨N, fun n hn a => ?_⟩
  let k := I.shrinkingCompatibleBandIndex n
  have hNk : N ≤ k := hn.trans (I.le_shrinkingCompatibleBandIndex n)
  exact hN k hNk a

/-- On every sufficiently late compatible cell, the open direct-limit map
is close to the corresponding limiting master boundary point. -/
theorem eventually_shrinkingInsideMap_apply_cell_dist_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (a : LevelAddress
          (I.shrinkingCompatibleBandParentStage n).level)
        (x : J.inside)
        (hxShell : (x : Plane) ∈ PolygonalCircle.closedShell
          (I.shrinkingCompatibleStageSourceDisk n)
          (I.shrinkingCompatibleStageSourceDisk (n + 1)))
        (hxCell : (x : Plane) ∈
          ((I.shrinkingCompatibleBand n)
            |>.moiseBandPolygonalCircle a).closedRegion),
      dist (I.shrinkingInsideMap x : Plane)
          (masterPoint (I.levelArc a).left) < epsilon := by
  obtain ⟨N, hN⟩ :=
    I.eventually_shrinkingCompatibleActualBandHomeomorph_apply_cell_dist_lt
      hepsilon
  refine ⟨N, fun n hn a x hxShell hxCell => ?_⟩
  have hxClosed : (x : Plane) ∈
      (I.shrinkingCompatibleStageSourceDisk (n + 1)).closedRegion :=
    hxShell.1
  calc
    dist (I.shrinkingInsideMap x : Plane)
        (masterPoint (I.levelArc a).left) =
      dist
        ((I.shrinkingCompatibleClosedDiskHomeomorphStage (n + 1)).homeomorph
          ⟨x, hxClosed⟩ : Plane)
        (masterPoint (I.levelArc a).left) := by
          rw [I.shrinkingInsideMap_eq_stage (n + 1) x hxClosed]
    _ = dist
        (I.shrinkingCompatibleActualBandHomeomorph n ⟨x, hxShell⟩ : Plane)
        (masterPoint (I.levelArc a).left) := by
          congr 1
          let xs : PolygonalCircle.closedShell
              (I.shrinkingCompatibleStageSourceDisk n)
              (I.shrinkingCompatibleStageSourceDisk (n + 1)) :=
            ⟨x, hxShell⟩
          simpa only [xs] using
            I.shrinkingCompatibleClosedDiskHomeomorphStage_succ_apply_shell n xs
    _ < epsilon := hN n hn a hxShell hxCell

/-- Late source cells and their direct-limit images are simultaneously
small about paired points on the source and target boundary curves. -/
theorem eventually_shrinkingBoundaryCell_pair
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (a : LevelAddress
          (I.shrinkingCompatibleBandParentStage n).level)
        (x : J.inside)
        (hxShell : (x : Plane) ∈ PolygonalCircle.closedShell
          (I.shrinkingCompatibleStageSourceDisk n)
          (I.shrinkingCompatibleStageSourceDisk (n + 1)))
        (hxCell : (x : Plane) ∈
          ((I.shrinkingCompatibleBand n)
            |>.moiseBandPolygonalCircle a).closedRegion),
      dist (x : Plane) (J.curvePoint (I.levelArc a).left : Plane) ≤ rho ∧
        dist (I.shrinkingInsideMap x : Plane)
          (masterPoint (I.levelArc a).left) < epsilon := by
  obtain ⟨Ns, hNs⟩ :=
    I.eventually_shrinkingCompatibleBandClosedRegion_subset_closedBall hrho
  obtain ⟨Nt, hNt⟩ :=
    I.eventually_shrinkingInsideMap_apply_cell_dist_lt hepsilon
  refine ⟨max Ns Nt, fun n hn a x hxShell hxCell => ?_⟩
  constructor
  · simpa only [mem_closedBall] using
      hNs n ((le_max_left _ _).trans hn) a hxCell
  · exact hNt n ((le_max_right _ _).trans hn) a x hxShell hxCell

end JordanCircle.InitialAngularArcs

end

end Schoenflies
