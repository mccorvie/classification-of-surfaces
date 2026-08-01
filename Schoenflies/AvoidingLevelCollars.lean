import Schoenflies.SynchronizedPolygonalCircle

/-!
# Finite collar levels avoiding an earlier closed core

The one-level construction normally starts with no obstacle.  Moise's
recursive Chapter 9 construction instead chooses every new level outside the
already constructed polygonal core.  The underlying finite greedy theorem
already supports an arbitrary closed obstacle; this file exposes that
specialization and a forgetful map back to the existing one-level API.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle}

/-- A complete finite level whose selected crosscuts avoid a fixed set. -/
noncomputable abbrev LevelAvoidingJoinFamilyOver
    (I : J.InitialAngularArcs) (n : ℕ) (epsilon : ℝ) (K : Set Plane) :=
  J.FiniteAvoidingJoinFamily (levelAddressCount n)
    (fun i => I.levelArc (levelAddressAt n i))
    (fun i => I.levelLeftHair (levelAddressAt n i))
    (fun i => I.levelRightHair (levelAddressAt n i))
    (fun i => thickening epsilon
        (I.levelArc (levelAddressAt n i)).curveArcPlane ∩
      (I.nonEndpointHairCarrier (levelAddressAt n i))ᶜ)
    K

theorem nonempty_levelAvoidingJoinFamilyOver
    (I : J.InitialAngularArcs) (n : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (K : Set Plane) (hKclosed : IsClosed K)
    (hKarc : ∀ a : LevelAddress n,
      Disjoint K (I.levelArc a).curveArcPlane) :
    Nonempty (I.LevelAvoidingJoinFamilyOver n epsilon K) := by
  apply J.nonempty_finiteAvoidingJoinFamily
  · intro i
    exact I.disjoint_levelEndpointHairs (levelAddressAt n i)
  · intro i
    exact Metric.isOpen_thickening.inter
      (I.isClosed_nonEndpointHairCarrier
        (levelAddressAt n i)).isOpen_compl
  · intro i x hx
    exact ⟨self_subset_thickening hepsilon _ hx,
      I.curveArcPlane_subset_compl_nonEndpointHairCarrier
        (levelAddressAt n i) hx⟩
  · exact hKclosed
  · intro i
    exact hKarc (levelAddressAt n i)

/-- Any polygonal disk already known to lie in the Jordan inside is a valid
obstacle for selecting a new complete level.  Its closedness is supplied by
compactness, and its disjointness from every boundary arc follows from the
Jordan inside/carrier separation. -/
theorem nonempty_levelAvoidingJoinFamilyOver_closedRegion
    (I : J.InitialAngularArcs) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (I.LevelAvoidingJoinFamilyOver n epsilon P.closedRegion) := by
  apply I.nonempty_levelAvoidingJoinFamilyOver n hepsilon P.closedRegion
  · exact P.isCompact_closedRegion.isClosed
  · intro a
    rw [Set.disjoint_left]
    intro x hxClosed hxArc
    exact (J.inside_subset_compl (hPinside hxClosed))
      ((I.levelArc a).curveArcPlane_subset_carrier J hxArc)

/-- In particular, a synchronized collar supplies the closed obstacle for
choosing an arbitrary later level.  This is the selection step used in the
recursive Chapter 9 construction. -/
theorem nonempty_levelAvoidingJoinFamilyOver_synchronizedClosedRegion
    (I : J.InitialAngularArcs) {m : ℕ} {delta : ℝ}
    (F : I.LevelAvoidingJoinFamily m delta) (hm : 1 ≤ m)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (I.LevelAvoidingJoinFamilyOver n epsilon
      (F.synchronizedPolygonalCircle hm).closedRegion) :=
  I.nonempty_levelAvoidingJoinFamilyOver_closedRegion
    (F.synchronizedPolygonalCircle hm)
    (LevelAvoidingJoinFamily.closedRegion_synchronizedPolygonalCircle_subset_inside
      F hm)
    n hepsilon

/-- At sufficiently fine levels, the complete polygonal collar lies in any
prescribed metric thickening of the original Jordan carrier. -/
theorem eventually_carrier_synchronizedPolygonalCircle_subset_thickening
    (I : J.InitialAngularArcs) {rho : ℝ} (hrho : 0 < rho) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ hn : 1 ≤ n, ∀ (F : I.LevelAvoidingJoinFamily n (rho / 4)),
        (F.synchronizedPolygonalCircle hn).carrier ⊆
          thickening rho J.carrier := by
  obtain ⟨N₀, hN₀⟩ :=
    LevelAvoidingJoinFamily.eventually_synchronizedReturnSet_subset_ball
      I hrho
  refine ⟨max 1 N₀, le_max_left _ _, ?_⟩
  intro n hn hnpos F
  have hn₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  rw [LevelAvoidingJoinFamily.carrier_synchronizedPolygonalCircle F hnpos]
  intro x hx
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
  have hxReturn : x ∈ F.synchronizedReturnSet a :=
    Or.inl (Or.inr (F.range_synchronizedCrosscutPath_subset a hxa))
  have hxBall := hN₀ n hn₀ F a hxReturn
  rw [mem_thickening_iff]
  refine ⟨(J.curvePoint (I.levelArc a).left : Plane), ?_, ?_⟩
  · exact (I.levelArc a).curveArcPlane_subset_carrier J
      (I.levelArc a).left_mem_curveArcPlane
  · simpa [mem_ball] using hxBall

/-- A compact polygonal disk contained in the Jordan inside has a uniform
boundary collar disjoint from it. -/
theorem exists_thickening_carrier_disjoint_closedRegion
    (P : PolygonalCircle) (hPinside : P.closedRegion ⊆ J.inside) :
    ∃ rho : ℝ, 0 < rho ∧
      Disjoint P.closedRegion (thickening rho J.carrier) := by
  have hdisjoint : Disjoint P.closedRegion J.carrier := by
    rw [Set.disjoint_left]
    intro x hxClosed hxCarrier
    exact J.inside_subset_compl (hPinside hxClosed) hxCarrier
  have hcarrierCompact : IsCompact J.carrier :=
    JordanCurve.jordanCurve_isCompact J.parametrization J.continuous
  obtain ⟨rho, hrho, hthickenings⟩ :=
    hdisjoint.exists_thickenings P.isCompact_closedRegion
      hcarrierCompact.isClosed
  exact ⟨rho, hrho,
    hthickenings.mono_left (self_subset_thickening hrho _)⟩

namespace LevelAvoidingJoinFamilyOver

variable {I : J.InitialAngularArcs} {n : ℕ} {epsilon : ℝ} {K : Set Plane}
  (G : I.LevelAvoidingJoinFamilyOver n epsilon K)

/-- Forget the extra obstacle certificate while retaining literally the same
selected points, paths, and polygonal lines. -/
noncomputable def forgetObstacle : I.LevelAvoidingJoinFamily n epsilon where
  rightPoint := G.rightPoint
  leftPoint := G.leftPoint
  rightPoint_mem := G.rightPoint_mem
  leftPoint_mem := G.leftPoint_mem
  rightPoint_inside := G.rightPoint_inside
  leftPoint_inside := G.leftPoint_inside
  endpoint_ne := G.endpoint_ne
  sourceAmbient := G.sourceAmbient
  sourceLine := G.sourceLine
  path := G.path
  path_eq_sourceLine := G.path_eq_sourceLine
  path_injective := G.path_injective
  sourceAmbient_subset := G.sourceAmbient_subset
  carrierLine := G.carrierLine
  segmentCarrier_carrierLine_eq_range := G.segmentCarrier_carrierLine_eq_range
  controlled := G.controlled
  avoids := fun _ => Set.disjoint_empty _
  pairwise_disjoint := G.pairwise_disjoint

@[simp] theorem forgetObstacle_rightPoint
    (i : Fin (levelAddressCount n)) :
    G.forgetObstacle.rightPoint i = G.rightPoint i := rfl

@[simp] theorem forgetObstacle_leftPoint
    (i : Fin (levelAddressCount n)) :
    G.forgetObstacle.leftPoint i = G.leftPoint i := rfl

@[simp] theorem forgetObstacle_path
    (i : Fin (levelAddressCount n)) :
    G.forgetObstacle.path i = G.path i := rfl

@[simp] theorem forgetObstacle_sourceLine
    (i : Fin (levelAddressCount n)) :
    G.forgetObstacle.sourceLine i = G.sourceLine i := rfl

theorem range_forgetObstacle_path_disjoint
    (i : Fin (levelAddressCount n)) :
    Disjoint (range (G.forgetObstacle.path i)) K := by
  change Disjoint (range (G.path i)) K
  exact G.avoids i

theorem range_forgetObstacle_trimmedPath_disjoint
    (i : Fin (levelAddressCount n)) :
    Disjoint (range (G.forgetObstacle.trimmedPath i)) K :=
  (G.range_forgetObstacle_path_disjoint i).mono_left
    (G.forgetObstacle.range_trimmedPath_subset_path i)

end LevelAvoidingJoinFamilyOver

/-- One honest recursive collar step.  Starting from a polygonal disk in the
Jordan inside, choose a sufficiently fine synchronized level whose original
middle paths avoid that disk and whose *entire* polygonal carrier (including
the synchronized retained-hair extensions) is disjoint from the disk. -/
theorem exists_avoiding_synchronizedPolygonalCircle
    (I : J.InitialAngularArcs) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ (n : ℕ) (hn : 1 ≤ n)
        (G : I.LevelAvoidingJoinFamilyOver n (rho / 4) P.closedRegion),
        Disjoint P.closedRegion
          (G.forgetObstacle.synchronizedPolygonalCircle hn).carrier := by
  obtain ⟨rho, hrho, hseparated⟩ :=
    exists_thickening_carrier_disjoint_closedRegion P hPinside
  obtain ⟨N, hNpos, hN⟩ :=
    I.eventually_carrier_synchronizedPolygonalCircle_subset_thickening hrho
  let G : I.LevelAvoidingJoinFamilyOver N (rho / 4) P.closedRegion :=
    Classical.choice (I.nonempty_levelAvoidingJoinFamilyOver_closedRegion
      P hPinside N (by positivity))
  refine ⟨rho, hrho, N, hNpos, G, ?_⟩
  exact hseparated.mono_right (hN N le_rfl hNpos G.forgetObstacle)

end InitialAngularArcs
end JordanCircle

end Schoenflies
