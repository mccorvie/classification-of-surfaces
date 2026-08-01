import Schoenflies.AvoidingLevelCollars
import Schoenflies.ExactSynchronizedCollarCells
import Schoenflies.SideConstancy

/-!
# Recursive synchronized collar stages

This packages the quantitative induction step in Moise's Chapter 9
construction.  Given an earlier polygonal disk in the Jordan inside, the next
stage is selected close enough to the Jordan boundary that both its complete
polygonal carrier and every closed boundary cell avoid the earlier disk.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle}

/-- A synchronized collar level selected relative to an earlier polygonal
disk. -/
structure RecursiveInsideCollarStep (I : J.InitialAngularArcs)
    (P : PolygonalCircle) where
  buffer : ℝ
  buffer_pos : 0 < buffer
  level : ℕ
  one_le_level : 1 ≤ level
  family : I.LevelAvoidingJoinFamilyOver level
    ((buffer / 2) / 4) P.closedRegion
  carrier_disjoint : Disjoint P.closedRegion
    (family.forgetObstacle.synchronizedPolygonalCircle one_le_level).carrier
  cell_disjoint : ∀ a : LevelAddress level,
    Disjoint P.closedRegion
      (closure
        (family.forgetObstacle.exactSynchronizedAuxiliaryJordanCircle a).inside)

namespace RecursiveInsideCollarStep

variable {I : J.InitialAngularArcs} {P : PolygonalCircle}
  (S : I.RecursiveInsideCollarStep P)

/-- The polygonal circle supplied by the new collar stage. -/
noncomputable def circle : PolygonalCircle :=
  S.family.forgetObstacle.synchronizedPolygonalCircle S.one_le_level

theorem circle_carrier_disjoint :
    Disjoint P.closedRegion S.circle.carrier :=
  S.carrier_disjoint

theorem circle_closedRegion_subset_inside :
    S.circle.closedRegion ⊆ J.inside :=
  LevelAvoidingJoinFamily.closedRegion_synchronizedPolygonalCircle_subset_inside
    S.family.forgetObstacle S.one_le_level

/-- Since the old polygonal disk is connected and avoids the new collar, it
lies wholly on one side of that collar.  The remaining nesting argument only
has to rule out the exterior alternative. -/
theorem old_closedRegion_side_dichotomy :
    P.closedRegion ⊆ S.circle.interiorRegion ∨
      P.closedRegion ⊆ S.circle.exteriorRegion := by
  have hcomplement : P.closedRegion ⊆ S.circle.toJordanCircle.carrierᶜ := by
    rw [S.circle.carrier_toJordanCircle]
    intro x hxClosed hxCarrier
    exact Set.disjoint_left.mp S.circle_carrier_disjoint
      hxClosed hxCarrier
  rcases P.isConnected_closedRegion.isPreconnected.subset_or_subset
      S.circle.toJordanCircle.inside_isOpen
      S.circle.toJordanCircle.outside_isOpen
      S.circle.toJordanCircle.inside_disjoint_outside
      (by
        rw [S.circle.toJordanCircle.inside_union_outside]
        exact hcomplement) with hinside | houtside
  · left
    simpa only [S.circle.inside_toJordanCircle] using hinside
  · right
    simpa only [S.circle.outside_toJordanCircle] using houtside

theorem original_path_disjoint (i : Fin (levelAddressCount S.level)) :
    Disjoint (range (S.family.forgetObstacle.path i)) P.closedRegion :=
  S.family.range_forgetObstacle_path_disjoint i

theorem trimmed_path_disjoint (i : Fin (levelAddressCount S.level)) :
    Disjoint (range (S.family.forgetObstacle.trimmedPath i)) P.closedRegion :=
  S.family.range_forgetObstacle_trimmedPath_disjoint i

end RecursiveInsideCollarStep

/-- Every polygonal disk already contained in the Jordan inside admits a
recursive collar step with both carrier avoidance and closed-cell avoidance. -/
theorem nonempty_recursiveInsideCollarStep
    (I : J.InitialAngularArcs) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    Nonempty (I.RecursiveInsideCollarStep P) := by
  obtain ⟨buffer, hbuffer, hseparated⟩ :=
    exists_thickening_carrier_disjoint_closedRegion P hPinside
  have hhalf : 0 < buffer / 2 := half_pos hbuffer
  obtain ⟨Ncarrier, hNcarrierPos, hNcarrier⟩ :=
    I.eventually_carrier_synchronizedPolygonalCircle_subset_thickening hhalf
  obtain ⟨Ncell, hNcell⟩ :=
    LevelAvoidingJoinFamily.eventually_closure_inside_exactSynchronizedAuxiliary_subset_ball
      I hhalf
  let N := max Ncarrier Ncell
  have hNpos : 1 ≤ N := hNcarrierPos.trans (le_max_left _ _)
  let G : I.LevelAvoidingJoinFamilyOver N
      ((buffer / 2) / 4) P.closedRegion :=
    Classical.choice (I.nonempty_levelAvoidingJoinFamilyOver_closedRegion
      P hPinside N (by positivity))
  let F : I.LevelAvoidingJoinFamily N ((buffer / 2) / 4) :=
    G.forgetObstacle
  have hcarrierNear :
      (F.synchronizedPolygonalCircle hNpos).carrier ⊆
        thickening buffer J.carrier := by
    exact (hNcarrier N (le_max_left _ _) hNpos F).trans
      (thickening_mono (by linarith : buffer / 2 ≤ buffer) _)
  have hcarrierDisjoint : Disjoint P.closedRegion
      (F.synchronizedPolygonalCircle hNpos).carrier :=
    hseparated.mono_right hcarrierNear
  have hcellDisjoint : ∀ a : LevelAddress N,
      Disjoint P.closedRegion
        (closure (F.exactSynchronizedAuxiliaryJordanCircle a).inside) := by
    intro a
    apply hseparated.mono_right
    exact (hNcell N (le_max_right _ _) F a).trans <| by
      exact (closedBall_subset_ball (half_lt_self hbuffer)).trans
        (ball_subset_thickening
          ((I.levelArc a).curveArcPlane_subset_carrier J
            (I.levelArc a).left_mem_curveArcPlane) buffer)
  exact ⟨{
    buffer := buffer
    buffer_pos := hbuffer
    level := N
    one_le_level := hNpos
    family := G
    carrier_disjoint := hcarrierDisjoint
    cell_disjoint := hcellDisjoint }⟩

end InitialAngularArcs
end JordanCircle

end Schoenflies
