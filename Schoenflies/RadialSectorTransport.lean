import Schoenflies.StandardRadialCollars

/-!
# Radial sector transport under standard shell adjustments

The standard shell boundary adjustment is a conjugated Alexander radial
extension, so it acts by one fixed angular map at every radius.  This file
makes that precise on homothetic coordinates: on any point written as a
positive homothety of a master triangle-boundary point, the adjustment
replaces the master point by its image under one master self-homeomorphism
of the standard triangle boundary and keeps the homothety scale unchanged.

Consequently the adjustment maps every radial sector over a master arc
exactly onto the sector over the image arc.  This is the target-side half of
the marked-sector control needed for boundary continuity of the shrinking
Moise construction.
-/

namespace Schoenflies

open Metric Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace StandardPolygonalCollars

/-- Homothety scales in the closed shell interval land in the radial band. -/
theorem homothetyPoint_mem_radialBand (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (radius n) (radius (n + 1))) (p : Plane) :
    homothetyPoint s p ∈ radialBand n p := by
  have hD : 0 < radius (n + 1) - radius n := sub_pos.mpr (radius_lt_succ n)
  refine ⟨(s - radius n) / (radius (n + 1) - radius n),
    (radius (n + 1) - s) / (radius (n + 1) - radius n),
    div_nonneg (sub_nonneg.mpr hs.1) hD.le,
    div_nonneg (sub_nonneg.mpr hs.2) hD.le, ?_, ?_⟩
  · field_simp
    ring
  · have hcombine :
        ((s - radius n) / (radius (n + 1) - radius n)) •
            homothetyPoint (radius (n + 1)) p +
          ((radius (n + 1) - s) / (radius (n + 1) - radius n)) •
            homothetyPoint (radius n) p =
        ((s - radius n) / (radius (n + 1) - radius n) * radius (n + 1) +
            (radius (n + 1) - s) / (radius (n + 1) - radius n) * radius n) •
            (p - center) +
          ((s - radius n) / (radius (n + 1) - radius n) +
            (radius (n + 1) - s) / (radius (n + 1) - radius n)) • center := by
      simp only [homothetyPoint]
      module
    rw [hcombine]
    have hscale :
        (s - radius n) / (radius (n + 1) - radius n) * radius (n + 1) +
          (radius (n + 1) - s) / (radius (n + 1) - radius n) * radius n = s := by
      field_simp
      ring
    have hsum :
        (s - radius n) / (radius (n + 1) - radius n) +
          (radius (n + 1) - s) / (radius (n + 1) - radius n) = 1 := by
      field_simp
      ring
    rw [hscale, hsum, one_smul]
    rfl

/-- Homothetic points over master boundary points fill the closed shell. -/
theorem homothetyPoint_mem_closedShell (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (radius n) (radius (n + 1))) {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    homothetyPoint s p ∈
      PolygonalCircle.closedShell (disk n) (disk (n + 1)) :=
  radialBand_subset_closedShell n hp (homothetyPoint_mem_radialBand n hs p)

/-- The gauge straightening sends master boundary points to the unit
sphere. -/
theorem triangleToBall_mem_unitSphere {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    triangleToBall p ∈ sphere (0 : Plane) 1 := by
  rw [← triangleToBall_image_standardCarrier]
  exact mem_image_of_mem _ hp

/-- The inverse of the shell straightening is the restricted inverse
gauge. -/
theorem shellToRoundClosedShell_symm_apply (n : ℕ)
    (z : roundClosedShell (radius n) (radius (n + 1))) :
    ((shellToRoundClosedShell n).symm z : Plane) =
      triangleToBall.symm z := by
  apply triangleToBall.injective
  rw [Homeomorph.apply_symm_apply]
  exact ((shellToRoundClosedShell_apply n
    ((shellToRoundClosedShell n).symm z)).symm.trans
    (congrArg Subtype.val ((shellToRoundClosedShell n).apply_symm_apply z)))

/-- The master angular map of a standard shell adjustment: the prescribed
inner boundary self-homeomorphism, conjugated back to the standard triangle
boundary by the homothety identification. -/
def masterShellAdjustment (n : ℕ)
    (q : (disk n).carrier ≃ₜ (disk n).carrier) :
    standardTriangleCircle.carrier ≃ₜ standardTriangleCircle.carrier :=
  (diskBoundaryHomeomorph n).trans (q.trans (diskBoundaryHomeomorph n).symm)

@[simp] theorem masterShellAdjustment_apply (n : ℕ)
    (q : (disk n).carrier ≃ₜ (disk n).carrier)
    (x : standardTriangleCircle.carrier) :
    masterShellAdjustment n q x =
      (diskBoundaryHomeomorph n).symm (q (diskBoundaryHomeomorph n x)) :=
  rfl

/-- **Radial sector transport.**  On a homothetic point of the closed shell,
the standard shell boundary adjustment keeps the homothety scale and applies
the master angular map to the master boundary point.  In particular the
adjustment maps each radial sector over a master arc exactly onto the sector
over the image arc, at every intermediate radius simultaneously. -/
theorem standardShellBoundaryAdjustment_apply_homothetyPoint
    (n : ℕ) (q : (disk n).carrier ≃ₜ (disk n).carrier)
    {s : ℝ} (hs : s ∈ Icc (radius n) (radius (n + 1)))
    {p : Plane} (hp : p ∈ standardTriangleCircle.carrier) :
    (standardShellBoundaryAdjustment n q
        ⟨homothetyPoint s p, homothetyPoint_mem_closedShell n hs hp⟩ :
      Plane) =
      homothetyPoint s (masterShellAdjustment n q ⟨p, hp⟩ : Plane) := by
  have hspos : 0 < s := lt_of_lt_of_le (radius_pos n) hs.1
  have hu : triangleToBall p ∈ sphere (0 : Plane) 1 :=
    triangleToBall_mem_unitSphere hp
  set u : sphere (0 : Plane) 1 := ⟨triangleToBall p, hu⟩ with hu_def
  set p' : standardTriangleCircle.carrier :=
    masterShellAdjustment n q ⟨p, hp⟩ with hp'_def
  -- the inner mark below `p` and its image mark below `p'`
  have hPn_mem : homothetyPoint (radius n) p ∈ (disk n).carrier := by
    rw [disk_carrier]
    exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩
  set Pn : (disk n).carrier := ⟨homothetyPoint (radius n) p, hPn_mem⟩
    with hPn_def
  have hPn_eq : diskBoundaryHomeomorph n ⟨p, hp⟩ = Pn := by
    apply Subtype.ext
    rw [diskBoundaryHomeomorph_apply]
  have hq' : diskBoundaryHomeomorph n p' = q Pn := by
    rw [hp'_def, masterShellAdjustment_apply,
      Homeomorph.apply_symm_apply, hPn_eq]
  -- the conjugated sphere map used by the adjustment
  set g : sphere (0 : Plane) (radius n) ≃ₜ sphere (0 : Plane) (radius n) :=
    (diskCarrierToSphere n).symm.trans (q.trans (diskCarrierToSphere n))
    with hg_def
  -- the unit-sphere conjugate applied to `u` gives the gauge image of `p'`
  have hgu :
      (((RadialBoundaryAdjustment.sphereScale (radius n)
            (radius_pos n)).trans
          (g.trans (RadialBoundaryAdjustment.sphereScale (radius n)
            (radius_pos n)).symm)) u : Plane) =
        triangleToBall (p' : Plane) := by
    have hA : RadialBoundaryAdjustment.sphereScale (radius n)
        (radius_pos n) u = diskCarrierToSphere n Pn := by
      apply Subtype.ext
      rw [RadialBoundaryAdjustment.sphereScale_apply,
        diskCarrierToSphere_apply]
      exact (triangleToBall_homothetyPoint (radius_pos n).le p).symm
    have hgA : g (diskCarrierToSphere n Pn) =
        diskCarrierToSphere n (diskBoundaryHomeomorph n p') := by
      rw [hg_def]
      simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
      rw [hq']
    simp only [Homeomorph.trans_apply]
    rw [hA, hgA,
      RadialBoundaryAdjustment.sphereScale_symm_apply,
      diskCarrierToSphere_apply, diskBoundaryHomeomorph_apply,
      triangleToBall_homothetyPoint (radius_pos n).le,
      smul_smul, inv_mul_cancel₀ (radius_pos n).ne', one_smul]
  -- assemble the three-stage composition
  rw [standardShellBoundaryAdjustment]
  simp only [Homeomorph.trans_apply]
  rw [shellToRoundClosedShell_symm_apply, Homeomorph.symm_apply_eq]
  rw [RadialBoundaryAdjustment.roundClosedShellHomeomorph_apply]
  have hZ : (shellToRoundClosedShell n
      ⟨homothetyPoint s p, homothetyPoint_mem_closedShell n hs hp⟩ :
        Plane) = s • (u : Plane) := by
    rw [shellToRoundClosedShell_apply]
    exact triangleToBall_homothetyPoint hspos.le p
  rw [hZ, RadialBoundaryAdjustment.extendSphereHomeomorph,
    PlaneAlexander.ambientRadialHomeomorph_smul_ofSphere _ hspos u,
    hgu, triangleToBall_homothetyPoint hspos.le]

/-- The induced outer boundary adjustment likewise applies the same master
angular map at the outer radius.  This is the exact statement needed to
propagate the marked-arc invariant from one shrinking stage to the next. -/
theorem standardShellOuterBoundaryAdjustment_apply_homothetyPoint
    (n : ℕ) (q : (disk n).carrier ≃ₜ (disk n).carrier)
    {p : Plane} (hp : p ∈ standardTriangleCircle.carrier) :
    (standardShellOuterBoundaryAdjustment n q
        (diskBoundaryHomeomorph (n + 1) ⟨p, hp⟩) : Plane) =
      homothetyPoint (radius (n + 1))
        (masterShellAdjustment n q ⟨p, hp⟩ : Plane) := by
  have hsMem : radius (n + 1) ∈ Icc (radius n) (radius (n + 1)) :=
    ⟨(radius_lt_succ n).le, le_rfl⟩
  have houterMem : homothetyPoint (radius (n + 1)) p ∈
      (disk (n + 1)).carrier := by
    rw [disk_carrier]
    exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩
  have hx_eq : diskBoundaryHomeomorph (n + 1) ⟨p, hp⟩ =
      (⟨homothetyPoint (radius (n + 1)) p, houterMem⟩ :
        (disk (n + 1)).carrier) := by
    apply Subtype.ext
    rw [diskBoundaryHomeomorph_apply]
  have hshell := standardShellBoundaryAdjustment_apply_outerCarrier n q
    ⟨homothetyPoint (radius (n + 1)) p, houterMem⟩
  have hcarrier :
      outerCarrierInClosedShell n
          (⟨homothetyPoint (radius (n + 1)) p, houterMem⟩ :
            (disk (n + 1)).carrier) =
        ⟨homothetyPoint (radius (n + 1)) p,
          homothetyPoint_mem_closedShell n hsMem hp⟩ := by
    apply Subtype.ext
    rw [outerCarrierInClosedShell_val]
  rw [hx_eq, ← hshell, hcarrier]
  exact standardShellBoundaryAdjustment_apply_homothetyPoint n q hsMem hp

/-- Every point of a standard closed shell is the homothety of a master
boundary point at a scale within the shell interval.  This inverts the
containment of homothetic sectors and lets every shell point be tracked in
master coordinates. -/
theorem exists_homothetyPoint_of_mem_closedShell (n : ℕ) {x : Plane}
    (hx : x ∈ PolygonalCircle.closedShell (disk n) (disk (n + 1))) :
    ∃ s ∈ Icc (radius n) (radius (n + 1)),
      ∃ p ∈ standardTriangleCircle.carrier, x = homothetyPoint s p := by
  have hy : triangleToBall x ∈
      roundClosedShell (radius n) (radius (n + 1)) := by
    rw [← triangleToBall_image_closedShell n]
    exact mem_image_of_mem _ hx
  obtain ⟨hyOuter, hyInner⟩ := hy
  set r := ‖triangleToBall x‖ with hr_def
  have hrIcc : r ∈ Icc (radius n) (radius (n + 1)) := by
    constructor
    · exact le_of_not_gt fun h => hyInner (by
        rwa [mem_ball, dist_zero_right])
    · rwa [mem_closedBall, dist_zero_right] at hyOuter
  have hrpos : 0 < r := lt_of_lt_of_le (radius_pos n) hrIcc.1
  set u : Plane := r⁻¹ • triangleToBall x with hu_def
  have hu : u ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere, dist_zero_right, hu_def, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hrpos, ← hr_def,
      inv_mul_cancel₀ hrpos.ne']
  have hpCarrier : triangleToBall.symm u ∈
      standardTriangleCircle.carrier := by
    have humem := hu
    rw [← triangleToBall_image_standardCarrier] at humem
    obtain ⟨q, hq, hqu⟩ := humem
    rw [← hqu, Homeomorph.symm_apply_apply]
    exact hq
  refine ⟨r, hrIcc, triangleToBall.symm u, hpCarrier, ?_⟩
  apply triangleToBall.injective
  rw [triangleToBall_homothetyPoint hrpos.le,
    Homeomorph.apply_symm_apply, hu_def, smul_smul,
    mul_inv_cancel₀ hrpos.ne', one_smul]

/-- Distance between homothetic points, split into an angular and a radial
contribution.  Combined with the transport theorem this bounds the diameter
of any adjusted sector by the master arc diameter plus the shell width. -/
theorem dist_homothetyPoint_homothetyPoint (s t : ℝ) (p q : Plane) :
    dist (homothetyPoint s p) (homothetyPoint t q) ≤
      |s| * ‖p - q‖ + |s - t| * ‖q - center‖ := by
  have hsplit : homothetyPoint s p - homothetyPoint t q =
      s • (p - q) + (s - t) • (q - center) := by
    simp only [homothetyPoint]
    module
  rw [dist_eq_norm, hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- A homothetic point converges to its master point as the scale tends to
one, at an exactly linear rate. -/
theorem dist_homothetyPoint_self (s : ℝ) (p : Plane) :
    dist (homothetyPoint s p) p = |1 - s| * ‖p - center‖ := by
  have hsplit : homothetyPoint s p - p = -((1 - s) • (p - center)) := by
    simp only [homothetyPoint]
    module
  rw [dist_eq_norm, hsplit, norm_neg, norm_smul, Real.norm_eq_abs]

end StandardPolygonalCollars

end

end Schoenflies
