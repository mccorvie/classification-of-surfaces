import Schoenflies.DampedShellAdjustment
import Schoenflies.CyclicTargetCellGeometry
import Schoenflies.JordanConvexHull
import Schoenflies.CompatibleShrinkingMoiseDiskStages

/-!
# Uniform metric control of the damped target cells

The canonical target cell over a sufficiently fine angular window is small:
its two circular sides lie over one small master arc and its radial sides lie
in a shell whose width tends to zero.  The damped boundary correction is then
uniformly close to the identity by the short-isotopy estimate.
-/

namespace Schoenflies

open Metric Set Function Filter
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open StandardPolygonalCollars

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The fixed standard triangle carrier has a positive uniform norm bound
about the selected radial center. -/
theorem exists_masterCarrier_norm_sub_center_le :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ standardTriangleCircle.carrier,
      ‖p - StandardPolygonalCollars.center‖ ≤ C := by
  obtain ⟨R, hR⟩ :=
    standardTriangleCircle.isCompact_carrier.isBounded.subset_closedBall
      StandardPolygonalCollars.center
  refine ⟨|R| + 1, by positivity, ?_⟩
  intro p hp
  have h := hR hp
  rw [mem_closedBall, dist_eq_norm] at h
  exact h.trans (le_add_of_le_of_nonneg (le_abs_self R) zero_le_one)

/-- The radial deficit of the standard exhaustion tends uniformly to zero
against any fixed positive carrier bound. -/
theorem eventually_one_sub_radius_mul_lt
    {C epsilon : ℝ} (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (1 - radius m) * C < epsilon := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hepsilon hC)
  refine ⟨N, fun m hm => ?_⟩
  have hden : (N + 1 : ℝ) ≤ (m + 2 : ℝ) := by
    exact_mod_cast (by omega : N + 1 ≤ m + 2)
  have hmono : 1 / (m + 2 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact hden
  have hsmall : (1 / (N + 1 : ℝ)) * C < epsilon := by
    rw [lt_div_iff₀ hC] at hN
    simpa [mul_comm] using hN
  change (1 - (1 - 1 / (m + 2 : ℝ))) * C < epsilon
  nlinarith

/-- A homothetic point in shell `m` is close to its limiting master boundary
point, uniformly over the carrier. -/
theorem dist_homothetyPoint_master_le
    {C : ℝ}
    (hC : ∀ p ∈ standardTriangleCircle.carrier,
      ‖p - StandardPolygonalCollars.center‖ ≤ C)
    (m : ℕ) {s : ℝ} (hs : s ∈ Icc (radius m) 1)
    {p : Plane} (hp : p ∈ standardTriangleCircle.carrier) :
    dist (homothetyPoint s p) p ≤ (1 - radius m) * C := by
  rw [dist_homothetyPoint_self, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact mul_le_mul (by linarith [hs.1]) (hC p hp)
    (norm_nonneg _) (sub_nonneg.mpr (radius_lt_one m).le)

/-- Quantitative containment of one raw canonical target cell. -/
theorem cyclicTargetCell_closedRegion_subset_closedBall
    (m : ℕ) {k : ℕ} (hk : 1 ≤ k) (a : LevelAddress k)
    {C eta : ℝ}
    (hC : ∀ p ∈ standardTriangleCircle.carrier,
      ‖p - StandardPolygonalCollars.center‖ ≤ C)
    (heta : ∀ s ∈ Icc (I.levelArc a).left (I.levelArc a).right,
      dist (masterPoint s) (masterPoint (I.levelArc a).left) ≤ eta) :
    (I.cyclicTargetAttachmentPresentation m a).disk.closedRegion ⊆
      closedBall (masterPoint (I.levelArc a).left)
        ((1 - radius m) * C + eta) := by
  apply (I.cyclicTargetAttachmentPresentation m a).disk
    |>.closedRegion_subset_closedBall_of_carrier_subset
  intro x hx
  rw [(I.cyclicTargetAttachmentPresentation m a).carrier_eq,
    I.range_cyclicTargetAttachmentPresentation_shared,
    I.range_cyclicTargetAttachmentPresentation_exposed m hk] at hx
  have hleftMem : masterPoint (I.levelArc a).left ∈
      standardTriangleCircle.carrier := by
    rw [← boundaryPoint_curvePoint_eq_masterPoint J]
    exact boundaryPoint_mem J _
  have heta0 : 0 ≤ eta := by
    have h := heta _
      (left_mem_Icc.mpr (I.levelArc a).left_lt_right.le)
    simpa only [dist_self] using h
  have hpoint {r : ℕ} {t : ℝ}
      (ht : t ∈ Icc (I.levelArc a).left (I.levelArc a).right)
      (hrm : m ≤ r) :
      dist (masterImagePoint r t) (masterPoint (I.levelArc a).left) ≤
        (1 - radius m) * C + eta := by
    calc
      dist (masterImagePoint r t) (masterPoint (I.levelArc a).left) ≤
          dist (masterImagePoint r t) (masterPoint t) +
            dist (masterPoint t) (masterPoint (I.levelArc a).left) :=
        dist_triangle _ _ _
      _ ≤ (1 - radius m) * C + eta := by
        apply add_le_add
        · unfold masterImagePoint
          apply dist_homothetyPoint_master_le hC m
          · have hden : (m + 2 : ℝ) ≤ (r + 2 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hrm 2
            have hinv : 1 / (r + 2 : ℝ) ≤ 1 / (m + 2 : ℝ) := by
              apply one_div_le_one_div_of_le (by positivity)
              exact hden
            exact ⟨by
              unfold radius
              linarith, (radius_lt_one r).le⟩
          · rw [← boundaryPoint_curvePoint_eq_masterPoint J]
            exact boundaryPoint_mem J _
        · exact heta t ht
  rcases hx with hxInner | hxSecond | hxOuter | hxFirst
  · have hArc :=
      I.range_indexedTargetBoundarySplit_first_subset_masterArcImage m a hxInner
    rw [I.masterArcImage_eq_image_Icc] at hArc
    obtain ⟨t, ht, rfl⟩ := hArc
    exact hpoint ht le_rfl
  · change x ∈ range
      (I.indexedTargetAnnularCrosscut m (nextLevelAddress k a)).path at hxSecond
    rw [I.range_indexedTargetAnnularCrosscut] at hxSecond
    have hnext :
        I.levelTargetBoundaryPoint (nextLevelAddress k a) =
          masterPoint (I.levelArc a).right := by
      have hcurve : J.curvePoint (I.levelArc a).right =
          J.curvePoint (I.levelArc (nextLevelAddress k a)).left :=
        Subtype.ext (I.levelAdjacent_nextLevelAddress k a)
      unfold levelTargetBoundaryPoint
      rw [← hcurve, boundaryPoint_curvePoint_eq_masterPoint]
    rw [radialBand] at hxSecond
    have houter : I.indexedTargetMark (m + 1) (nextLevelAddress k a) ∈
        closedBall (masterPoint (I.levelArc a).left)
          ((1 - radius m) * C + eta) := by
      rw [mem_closedBall, indexedTargetMark, hnext]
      exact hpoint (right_mem_Icc.mpr (I.levelArc a).left_lt_right.le)
        (Nat.le_succ m)
    have hinner : I.indexedTargetMark m (nextLevelAddress k a) ∈
        closedBall (masterPoint (I.levelArc a).left)
          ((1 - radius m) * C + eta) := by
      rw [mem_closedBall, indexedTargetMark, hnext]
      exact hpoint (right_mem_Icc.mpr (I.levelArc a).left_lt_right.le) le_rfl
    exact (convex_closedBall _ _).segment_subset houter hinner hxSecond
  · have hArc :=
      I.range_indexedTargetBoundarySplit_first_subset_masterArcImage (m + 1) a hxOuter
    rw [I.masterArcImage_eq_image_Icc] at hArc
    obtain ⟨t, ht, rfl⟩ := hArc
    exact hpoint ht (Nat.le_succ m)
  · change x ∈ range (I.indexedTargetAnnularCrosscut m a).path at hxFirst
    rw [I.range_indexedTargetAnnularCrosscut] at hxFirst
    have hleft : I.levelTargetBoundaryPoint a =
        masterPoint (I.levelArc a).left := by
      unfold levelTargetBoundaryPoint
      rw [boundaryPoint_curvePoint_eq_masterPoint]
    rw [hleft] at hxFirst
    rw [radialBand] at hxFirst
    have houter : homothetyPoint (radius (m + 1))
          (masterPoint (I.levelArc a).left) ∈
        closedBall (masterPoint (I.levelArc a).left)
          ((1 - radius m) * C + eta) := by
      rw [mem_closedBall]
      exact (dist_homothetyPoint_master_le hC m
        ⟨(radius_lt_succ m).le, (radius_lt_one (m + 1)).le⟩ hleftMem).trans
          (le_add_of_nonneg_right heta0)
    have hinner : homothetyPoint (radius m)
          (masterPoint (I.levelArc a).left) ∈
        closedBall (masterPoint (I.levelArc a).left)
          ((1 - radius m) * C + eta) := by
      rw [mem_closedBall]
      exact (dist_homothetyPoint_master_le hC m
        ⟨le_rfl, (radius_lt_one m).le⟩ hleftMem).trans
          (le_add_of_nonneg_right heta0)
    exact (convex_closedBall _ _).segment_subset houter hinner hxFirst

/-- Raw canonical target cells shrink uniformly when both their radial shell
index and their angular subdivision level tend to infinity. -/
theorem eventually_cyclicTargetCell_closedRegion_subset_closedBall
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ m k : ℕ, N ≤ m → N ≤ k → ∀ a : LevelAddress k,
      (I.cyclicTargetAttachmentPresentation m a).disk.closedRegion ⊆
        closedBall (masterPoint (I.levelArc a).left) epsilon := by
  obtain ⟨C, hCpos, hC⟩ := exists_masterCarrier_norm_sub_center_le
  obtain ⟨Nr, hNr⟩ := eventually_one_sub_radius_mul_lt hCpos (half_pos hepsilon)
  obtain ⟨Na, hNa⟩ := I.eventually_masterPoint_dist_lt (half_pos hepsilon)
  let N := max 1 (max Nr Na)
  refine ⟨N, fun m k hm hk a => ?_⟩
  have hlevel : 1 ≤ k := (le_max_left 1 (max Nr Na)).trans hk
  have hr : (1 - radius m) * C < epsilon / 2 :=
    hNr m ((le_max_left Nr Na).trans (le_max_right 1 (max Nr Na)) |>.trans hm)
  have ha : ∀ s ∈ Icc (I.levelArc a).left (I.levelArc a).right,
      dist (masterPoint s) (masterPoint (I.levelArc a).left) ≤ epsilon / 2 := by
    intro s hs
    exact (hNa k
      ((le_max_right Nr Na).trans (le_max_right 1 (max Nr Na)) |>.trans hk)
      a s hs (I.levelArc a).left
      (left_mem_Icc.mpr (I.levelArc a).left_lt_right.le)).le
  exact (I.cyclicTargetCell_closedRegion_subset_closedBall m hlevel a hC ha).trans
    (closedBall_subset_closedBall (by linarith))

/-- Uniform smallness of an angular correction implies uniform smallness of
its damped extension throughout every standard polygonal shell. -/
theorem exists_angular_bound_for_dampedAdjustment
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (n : ℕ) (q : (disk n).carrier ≃ₜ (disk n).carrier)
        (hshort : ∀ u, angularBoundaryCorrection n q u ≠
          SphereShortIsotopy.antipode u),
        (∀ u, dist (angularBoundaryCorrection n q u) u < delta) →
        ∀ x : PolygonalCircle.closedShell (disk n) (disk (n + 1)),
          dist (dampedStandardShellBoundaryAdjustment n q hshort x : Plane)
            (x : Plane) < epsilon := by
  have hu : UniformContinuous
      (fun u : sphere (0 : Plane) 1 =>
        (sphereToMasterHomeomorph u : Plane)) :=
    CompactSpace.uniformContinuous_of_continuous
      (continuous_subtype_val.comp sphereToMasterHomeomorph.continuous)
  obtain ⟨eta, heta, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp hu) epsilon hepsilon
  let K : ℝ := Real.pi / 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  let delta := eta / (K + 1)
  have hdelta : 0 < delta := div_pos heta (by linarith)
  refine ⟨delta, hdelta, fun n q hshort hq x => ?_⟩
  let p := shellToAngularPolar n x
  let u' := SphereShortIsotopy.interpolation (angularBoundaryCorrection n q)
    hshort
    (DampedAnnulus.shellTime (radius n) (radius (n + 1))
      (radius_lt_succ n) p.2) p.1
  have hangular : dist u' p.1 < eta := by
    have hle := SphereShortIsotopy.dist_interpolation_self_le
      (angularBoundaryCorrection n q) hshort
      (DampedAnnulus.shellTime (radius n) (radius (n + 1))
        (radius_lt_succ n) p.2) p.1
    have hmove := hq p.1
    have hratio : K * delta < eta := by
      dsimp only [delta]
      have hden : 0 < K + 1 := by linarith
      rw [div_eq_mul_inv]
      calc
        K * (eta * (K + 1)⁻¹) = eta * (K / (K + 1)) := by field_simp
        _ < eta * 1 := by
          gcongr
          exact (div_lt_one hden).mpr (by linarith)
        _ = eta := mul_one _
    exact hle.trans_lt ((mul_lt_mul_of_pos_left hmove hKpos).trans hratio)
  have hmaster :
      dist (sphereToMasterHomeomorph u' : Plane)
        (sphereToMasterHomeomorph p.1 : Plane) < epsilon :=
    hmod hangular
  have hx : (x : Plane) =
      homothetyPoint (p.2 : ℝ) (sphereToMasterHomeomorph p.1 : Plane) := by
    have h := shellToAngularPolar_symm_apply n p
    rw [show (shellToAngularPolar n).symm p = x from
      (shellToAngularPolar n).symm_apply_apply x] at h
    exact h
  rw [dampedStandardShellBoundaryAdjustment_apply, hx]
  change dist
      (homothetyPoint (p.2 : ℝ) (sphereToMasterHomeomorph u' : Plane))
      (homothetyPoint (p.2 : ℝ) (sphereToMasterHomeomorph p.1 : Plane)) < epsilon
  have hhom := dist_homothetyPoint_homothetyPoint
    (p.2 : ℝ) (p.2 : ℝ)
    (sphereToMasterHomeomorph u' : Plane)
    (sphereToMasterHomeomorph p.1 : Plane)
  have hs0 : 0 ≤ (p.2 : ℝ) :=
    (radius_pos n).le.trans p.2.2.1
  have hs1 : (p.2 : ℝ) ≤ 1 :=
    p.2.2.2.trans (radius_lt_one (n + 1)).le
  rw [sub_self, abs_zero, zero_mul, add_zero, abs_of_nonneg hs0] at hhom
  exact hhom.trans_lt <| (mul_le_of_le_one_left (dist_nonneg) hs1).trans_lt hmaster

set_option maxRecDepth 2000 in
/-- On every sufficiently late compatible source cell, the actual damped
shell map is uniformly close to the limiting master boundary point indexed
by that cell.  This is the quantitative bridge from the recursive finite
stages to continuity at the original Jordan carrier. -/
theorem eventually_shrinkingCompatibleActualBandHomeomorph_apply_cell_dist_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (a : LevelAddress
          (I.shrinkingCompatibleBandParentStage n).level)
        {x : Plane}
        (hxShell : x ∈ PolygonalCircle.closedShell
          (I.shrinkingCompatibleStageSourceDisk n)
          (I.shrinkingCompatibleStageSourceDisk (n + 1)))
        (hxCell : x ∈
          ((I.shrinkingCompatibleBand n)
            |>.moiseBandPolygonalCircle a).closedRegion),
      dist
          (I.shrinkingCompatibleActualBandHomeomorph n
            ⟨x, hxShell⟩ : Plane)
          (masterPoint (I.levelArc a).left) < epsilon := by
  obtain ⟨delta, hdelta, hadjust⟩ :=
    exists_angular_bound_for_dampedAdjustment (half_pos hepsilon)
  obtain ⟨Nq, hNq⟩ :=
    I.eventually_shrinkingCompatibleBoundaryCorrection_dist_lt hdelta
  obtain ⟨Nc, hNc⟩ :=
    I.eventually_cyclicTargetCell_closedRegion_subset_closedBall
      (half_pos hepsilon)
  refine ⟨max Nq Nc, fun n hn a x hxShell hxCell => ?_⟩
  let D := I.shrinkingCompatibleClosedDiskHomeomorphStage n
  let q := (I.shrinkingCompatibleRawInnerBoundaryHomeomorph n).symm.trans
    D.boundaryHomeomorph
  have hboundary : D.boundaryHomeomorph =
      I.shrinkingCompatibleExpectedBoundaryHomeomorph n := by
    exact (I.shrinkingCompatibleClosedDiskStage n).boundary_eq
  have hshort : ∀ u, angularBoundaryCorrection n q u ≠
      SphereShortIsotopy.antipode u := by
    dsimp only [q]
    rw [hboundary]
    exact I.shrinkingCompatibleExpectedBoundaryCorrection_short n
  let y := (I.shrinkingCompatibleBand n).markedMoiseBandHomeomorph n
    (I.shrinkingCompatibleBand_outward n) ⟨x, hxShell⟩
  have hyCell : (y : Plane) ∈
      (I.cyclicTargetAttachmentPresentation n a).disk.closedRegion := by
    have hmap := (I.shrinkingCompatibleBand n)
      |>.markedMoiseBandHomeomorph_apply n
        (I.shrinkingCompatibleBand_outward n) a hxShell hxCell
    rw [hmap]
    exact ((I.shrinkingCompatibleBand n)
      |>.markedMoiseCellHomeomorph n a ⟨x, hxCell⟩).2
  have hq : ∀ u, dist (angularBoundaryCorrection n q u) u < delta := by
    intro u
    exact hNq n ((le_max_left _ _).trans hn) u
  have hmove :
      dist (dampedStandardShellBoundaryAdjustment n q hshort y : Plane)
        (y : Plane) < epsilon / 2 :=
    hadjust n q hshort hq y
  have hlevel : Nc ≤
      (I.shrinkingCompatibleBandParentStage n).level :=
    (le_max_right _ _).trans hn |>.trans
      (I.le_shrinkingCompatibleBandParentStage_level n)
  have hyMaster : dist (y : Plane)
      (masterPoint (I.levelArc a).left) ≤ epsilon / 2 := by
    simpa only [mem_closedBall] using
      hNc n (I.shrinkingCompatibleBandParentStage n).level
        ((le_max_right _ _).trans hn) hlevel a hyCell
  have hactual :
      (I.shrinkingCompatibleActualBandHomeomorph n ⟨x, hxShell⟩ : Plane) =
        (dampedStandardShellBoundaryAdjustment n q hshort y : Plane) := by
    rfl
  rw [hactual]
  exact (dist_triangle _ (y : Plane) _).trans_lt (by linarith)

end JordanCircle.InitialAngularArcs

end

end Schoenflies
