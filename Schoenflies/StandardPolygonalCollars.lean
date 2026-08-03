import Schoenflies.LocalizedAnnularTheta
import Schoenflies.BoundaryPathTransport
import ClassificationOfSurfaces.Moise.ConeExtension

/-!
# Nested standard polygonal collars

The target of the shrinking-cell construction is a fixed standard triangle.
Positive homotheties about an interior point give a canonical exhaustion of
its interior by strictly nested polygonal disks.  Points of the original
Jordan curve determine radial marks on these disks through the prescribed
boundary parametrization.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace StandardPolygonalCollars

/-- The closed standard triangle, in the form used by its polygonal circle. -/
def triangleBody : Set Plane :=
  convexHull ℝ (Set.range standardTriangleVertex)

theorem triangleBody_isCompact : IsCompact triangleBody :=
  (Set.finite_range standardTriangleVertex).isCompact_convexHull ℝ

theorem triangleBody_isConvex : Convex ℝ triangleBody :=
  convex_convexHull ℝ _

theorem triangleBody_interior_nonempty : (interior triangleBody).Nonempty := by
  let hT : IsTriangle triangleBody :=
    ⟨standardTriangleVertex, standardTriangleVertex_affineIndependent, rfl⟩
  exact hT.infinite_interior.nonempty

theorem standardTriangle_closedRegion :
    standardTriangleCircle.closedRegion = triangleBody := by
  symm
  apply standardTriangleCircle.eq_closedRegion_of_isCompact_frontier_eq
    triangleBody_isCompact
  · exact standardTriangleCircle_carrier.symm
  · exact triangleBody_interior_nonempty

/-- A fixed point strictly inside the standard triangle. -/
def center : Plane := Classical.choose triangleBody_interior_nonempty

theorem center_mem_triangleInterior : center ∈ interior triangleBody :=
  Classical.choose_spec triangleBody_interior_nonempty

theorem center_mem_standardInterior :
    center ∈ standardTriangleCircle.interiorRegion := by
  rw [← standardTriangleCircle.interior_closedRegion,
    standardTriangle_closedRegion]
  exact center_mem_triangleInterior

/-- Homothety about the fixed triangle center, written as a point map so it
also makes sense at scale zero. -/
def homothetyPoint (r : ℝ) (x : Plane) : Plane :=
  r • (x - center) + center

/-- At nonzero scale the homothety is an ambient homeomorphism. -/
def homothetyHomeomorph (r : ℝ) (hr : r ≠ 0) : Plane ≃ₜ Plane :=
  (Homeomorph.addRight (-center)).trans <|
    (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addRight center)

@[simp] theorem homothetyHomeomorph_apply (r : ℝ) (hr : r ≠ 0)
    (x : Plane) : homothetyHomeomorph r hr x = homothetyPoint r x := by
  simp [homothetyHomeomorph, homothetyPoint, sub_eq_add_neg]

/-- The same homothety as an affine map, used to transport polygon edges. -/
def homothetyAffineMap (r : ℝ) : Plane →ᵃ[ℝ] Plane :=
  AffineMap.mk' (homothetyPoint r) (r • LinearMap.id) center (by
    intro x
    simp only [homothetyPoint, vsub_eq_sub, vadd_eq_add,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    module)

@[simp] theorem homothetyAffineMap_apply (r : ℝ) (x : Plane) :
    homothetyAffineMap r x = homothetyPoint r x := rfl

theorem homothety_image_segment (r : ℝ) (hr : r ≠ 0)
    (a b : Plane) :
    homothetyHomeomorph r hr '' segment ℝ a b =
      segment ℝ (homothetyHomeomorph r hr a)
        (homothetyHomeomorph r hr b) := by
  simpa only [homothetyHomeomorph_apply, homothetyAffineMap_apply] using
    image_segment ℝ (homothetyAffineMap r) a b

/-- A convenient increasing sequence of scales in `(0,1)`. -/
def radius (n : ℕ) : ℝ := 1 - 1 / (n + 2 : ℝ)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  dsimp [radius]
  have hn : (1 : ℝ) < n + 2 := by exact_mod_cast (by omega : 1 < n + 2)
  have hden : (0 : ℝ) < n + 2 := by positivity
  rw [sub_pos, div_lt_one hden]
  exact hn

theorem radius_lt_one (n : ℕ) : radius n < 1 := by
  dsimp [radius]
  have hden : (0 : ℝ) < n + 2 := by positivity
  have : 0 < 1 / (n + 2 : ℝ) := one_div_pos.mpr hden
  linarith

theorem radius_lt_succ (n : ℕ) : radius n < radius (n + 1) := by
  dsimp [radius]
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hn3 : (0 : ℝ) < n + 3 := by positivity
  have hlt : (n + 2 : ℝ) < n + 3 := by norm_num
  have hinv : 1 / (n + 3 : ℝ) < 1 / (n + 2 : ℝ) := by
    exact one_div_lt_one_div_of_lt hn2 hlt
  convert sub_lt_sub_left hinv 1 using 1 <;> norm_num <;> ring

/-- The standard polygonal disk at exhaustion level `n`. -/
def disk (n : ℕ) : PolygonalCircle :=
  standardTriangleCircle.mapHomeomorph
    (homothetyHomeomorph (radius n) (radius_pos n).ne')
    (fun i => homothety_image_segment (radius n) (radius_pos n).ne'
      (standardTriangleCircle.vertex i)
      (standardTriangleCircle.vertex (i + 1)))

theorem disk_carrier (n : ℕ) :
    (disk n).carrier =
      homothetyHomeomorph (radius n) (radius_pos n).ne' ''
        standardTriangleCircle.carrier := by
  exact standardTriangleCircle.mapHomeomorph_carrier
    (homothetyHomeomorph (radius n) (radius_pos n).ne')
    (fun i => homothety_image_segment (radius n) (radius_pos n).ne'
      (standardTriangleCircle.vertex i)
      (standardTriangleCircle.vertex (i + 1)))

theorem disk_interiorRegion (n : ℕ) :
    (disk n).interiorRegion =
      homothetyHomeomorph (radius n) (radius_pos n).ne' ''
        standardTriangleCircle.interiorRegion := by
  symm
  exact PolygonalTransport.image_interiorRegion standardTriangleCircle
    (disk n) (homothetyHomeomorph (radius n) (radius_pos n).ne')
    (disk_carrier n).symm

theorem disk_closedRegion (n : ℕ) :
    (disk n).closedRegion =
      homothetyHomeomorph (radius n) (radius_pos n).ne' ''
        standardTriangleCircle.closedRegion := by
  rw [(disk n).closedRegion_eq_union,
    standardTriangleCircle.closedRegion_eq_union, image_union,
    ← disk_interiorRegion, ← disk_carrier]

private theorem homothetyPoint_mem_larger_interior
    {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    {p : Plane} (hp : p ∈ standardTriangleCircle.closedRegion) :
    homothetyPoint r p ∈
      homothetyHomeomorph s (hr.trans hrs).ne' ''
        standardTriangleCircle.interiorRegion := by
  let t : ℝ := r / s
  have hs : 0 < s := hr.trans hrs
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨div_pos hr hs, (div_lt_one hs).mpr hrs⟩
  let q : Plane := AffineMap.lineMap center p t
  have hqBody : q ∈ interior triangleBody := by
    apply triangleBody_isConvex.openSegment_interior_closure_subset_interior
      center_mem_triangleInterior
    · rw [← standardTriangle_closedRegion]
      exact subset_closure hp
    · exact lineMap_mem_openSegment ℝ center p ht
  have hq : q ∈ standardTriangleCircle.interiorRegion := by
    rw [← standardTriangleCircle.interior_closedRegion,
      standardTriangle_closedRegion]
    exact hqBody
  refine ⟨q, hq, ?_⟩
  rw [homothetyHomeomorph_apply]
  have hhom (u : ℝ) (z : Plane) :
      homothetyPoint u z = AffineMap.lineMap center z u := by
    simp only [homothetyPoint, AffineMap.lineMap_apply_module]
    module
  rw [hhom, hhom]
  have hcompose : AffineMap.lineMap center q s =
      AffineMap.lineMap center p (s * t) := by
    simp only [q, AffineMap.lineMap_apply_module]
    module
  rw [hcompose]
  congr 1
  dsimp [t]
  field_simp [hs.ne']

/-- Consecutive standard target disks are strictly nested. -/
theorem disk_strictlyNested (n : ℕ) :
    (disk n).closedRegion ⊆ (disk (n + 1)).interiorRegion := by
  rw [disk_closedRegion, disk_interiorRegion]
  rintro x ⟨p, hp, rfl⟩
  simpa only [homothetyHomeomorph_apply] using
    homothetyPoint_mem_larger_interior (radius_pos n)
      (radius_lt_succ n) hp

/-- The point of the standard triangle boundary prescribed by the original
Jordan parametrization. -/
def boundaryPoint (J : JordanCircle) (x : J.carrier) : Plane :=
  standardTriangleCircle.sphereStraightening.symm
    (J.carrierHomeomorph.symm x)

theorem boundaryPoint_mem (J : JordanCircle) (x : J.carrier) :
    boundaryPoint J x ∈ standardTriangleCircle.carrier := by
  let y : sphere (0 : Plane) 1 := J.carrierHomeomorph.symm x
  have hy : (y : Plane) ∈
      standardTriangleCircle.sphereStraightening ''
        standardTriangleCircle.carrier := by
    rw [standardTriangleCircle.sphereStraightening_image_carrier]
    exact y.2
  obtain ⟨p, hp, hpy⟩ := hy
  have hpEq : p = standardTriangleCircle.sphereStraightening.symm y := by
    apply standardTriangleCircle.sphereStraightening.injective
    rw [standardTriangleCircle.sphereStraightening.apply_symm_apply]
    exact hpy
  change standardTriangleCircle.sphereStraightening.symm (y : Plane) ∈ _
  rw [← hpEq]
  exact hp

theorem boundaryPoint_injective (J : JordanCircle) :
    Injective (boundaryPoint J) := by
  intro x y hxy
  apply J.carrierHomeomorph.symm.injective
  apply Subtype.ext
  apply standardTriangleCircle.sphereStraightening.symm.injective
  exact hxy

/-- The prescribed boundary correspondence as a homeomorphism of carrier
subtypes. -/
def boundaryCarrierHomeomorph (J : JordanCircle) :
    J.carrier ≃ₜ standardTriangleCircle.carrier :=
  J.carrierHomeomorph.symm.trans <|
    standardTriangleCircle.toJordanCircle.carrierHomeomorph.trans
      (Homeomorph.setCongr standardTriangleCircle.carrier_toJordanCircle)

@[simp] theorem boundaryCarrierHomeomorph_apply
    (J : JordanCircle) (x : J.carrier) :
    (boundaryCarrierHomeomorph J x : Plane) = boundaryPoint J x := by
  rfl

/-- Homothety identifies the standard triangle boundary with the boundary
of target disk `n`. -/
def diskBoundaryHomeomorph (n : ℕ) :
    standardTriangleCircle.carrier ≃ₜ (disk n).carrier :=
  ((homothetyHomeomorph (radius n) (radius_pos n).ne').image
      standardTriangleCircle.carrier).trans
    (Homeomorph.setCongr (disk_carrier n).symm)

@[simp] theorem diskBoundaryHomeomorph_apply
    (n : ℕ) (x : standardTriangleCircle.carrier) :
    (diskBoundaryHomeomorph n x : Plane) =
      homothetyPoint (radius n) x := by
  rfl

/-- Direct carrier homeomorphism from the original Jordan curve to target
disk `n`, with the required boundary parametrization and radial scale. -/
def jordanToDiskBoundaryHomeomorph (J : JordanCircle) (n : ℕ) :
    J.carrier ≃ₜ (disk n).toJordanCircle.carrier :=
  (boundaryCarrierHomeomorph J).trans <|
    (diskBoundaryHomeomorph n).trans
      (Homeomorph.setCongr (disk n).carrier_toJordanCircle.symm)

@[simp] theorem jordanToDiskBoundaryHomeomorph_apply
    (J : JordanCircle) (n : ℕ) (x : J.carrier) :
    (jordanToDiskBoundaryHomeomorph J n x : Plane) =
      homothetyPoint (radius n) (boundaryPoint J x) := by
  rfl

private theorem homothetyPoint_mem_openSegment
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {p : Plane} (hp : p ∈ standardTriangleCircle.carrier) :
    homothetyPoint r p ∈ openSegment ℝ center p := by
  have hhom : homothetyPoint r p = AffineMap.lineMap center p r := by
    simp only [homothetyPoint, AffineMap.lineMap_apply_module]
    module
  rw [hhom]
  exact lineMap_mem_openSegment ℝ center p ⟨hr, hr1⟩

private theorem segment_homothetyPoint_subset_openSegment
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs1 : s < 1)
    {p : Plane} (hp : p ∈ standardTriangleCircle.carrier) :
    segment ℝ (homothetyPoint s p) (homothetyPoint r p) ⊆
      openSegment ℝ center p := by
  apply (convex_openSegment center p).segment_subset
  · exact homothetyPoint_mem_openSegment (hr.trans_le hrs) hs1 hp
  · exact homothetyPoint_mem_openSegment hr (hrs.trans_lt hs1) hp

private theorem boundary_eq_of_mem_radial_segments
    {p q z : Plane}
    (hp : p ∈ standardTriangleCircle.carrier)
    (hq : q ∈ standardTriangleCircle.carrier)
    (hzp : z ∈ segment ℝ center p)
    (hzq : z ∈ segment ℝ center q)
    (hzc : z ≠ center) : p = q := by
  apply eq_of_mem_segment_interior_frontier triangleBody_isConvex
    center_mem_triangleInterior
  · change p ∈ frontier (convexHull ℝ (Set.range standardTriangleVertex))
    rw [← standardTriangleCircle_carrier]
    exact hp
  · change q ∈ frontier (convexHull ℝ (Set.range standardTriangleVertex))
    rw [← standardTriangleCircle_carrier]
    exact hq
  · exact hzp
  · exact hzq
  · exact hzc

/-- Radial bands based at distinct standard boundary points are disjoint. -/
theorem disjoint_radialBands
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs1 : s < 1)
    {p q : Plane} (hp : p ∈ standardTriangleCircle.carrier)
    (hq : q ∈ standardTriangleCircle.carrier) (hpq : p ≠ q) :
    Disjoint
      (segment ℝ (homothetyPoint s p) (homothetyPoint r p))
      (segment ℝ (homothetyPoint s q) (homothetyPoint r q)) := by
  rw [Set.disjoint_left]
  intro z hzp hzq
  have hzpOpen := segment_homothetyPoint_subset_openSegment
    hr hrs hs1 hp hzp
  have hzqOpen := segment_homothetyPoint_subset_openSegment
    hr hrs hs1 hq hzq
  apply hpq
  apply boundary_eq_of_mem_radial_segments hp hq
  · exact openSegment_subset_segment ℝ _ _ hzpOpen
  · exact openSegment_subset_segment ℝ _ _ hzqOpen
  · intro hzc
    rw [hzc] at hzpOpen
    have hcp : center ≠ p := by
      intro h
      have hpFrontier : p ∈ frontier triangleBody := by
        change p ∈ frontier (convexHull ℝ (Set.range standardTriangleVertex))
        rw [← standardTriangleCircle_carrier]
        exact hp
      exact (disjoint_interior_frontier (s := triangleBody)).le_bot
        ⟨h ▸ center_mem_triangleInterior, hpFrontier⟩
    exact hcp ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hzpOpen)

theorem disk_closedRegion_isConvex (n : ℕ) :
    Convex ℝ (disk n).closedRegion := by
  rw [disk_closedRegion, standardTriangle_closedRegion]
  simpa only [homothetyHomeomorph_apply, homothetyAffineMap_apply] using
    Convex.affine_image (homothetyAffineMap (radius n))
      triangleBody_isConvex

theorem disk_interiorRegion_isConvex (n : ℕ) :
    Convex ℝ (disk n).interiorRegion := by
  rw [← (disk n).interior_closedRegion]
  exact (disk_closedRegion_isConvex n).interior

theorem center_mem_disk_interiorRegion (n : ℕ) :
    center ∈ (disk n).interiorRegion := by
  rw [disk_interiorRegion]
  refine ⟨center, center_mem_standardInterior, ?_⟩
  simp [homothetyPoint]

/-- The radial closed band between consecutive target boundaries. -/
def radialBand (n : ℕ) (p : Plane) : Set Plane :=
  segment ℝ (homothetyPoint (radius (n + 1)) p)
    (homothetyPoint (radius n) p)

theorem radialBand_subset_openSegment (n : ℕ) {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    radialBand n p ⊆ openSegment ℝ center p := by
  exact segment_homothetyPoint_subset_openSegment (radius_pos n)
    (radius_lt_succ n).le (radius_lt_one (n + 1)) hp

private theorem center_ne_boundaryPoint {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) : center ≠ p := by
  intro h
  have hpFrontier : p ∈ frontier triangleBody := by
    change p ∈ frontier (convexHull ℝ (Set.range standardTriangleVertex))
    rw [← standardTriangleCircle_carrier]
    exact hp
  exact (disjoint_interior_frontier (s := triangleBody)).le_bot
    ⟨h ▸ center_mem_triangleInterior, hpFrontier⟩

theorem radialBand_inter_outerCarrier (n : ℕ) {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    radialBand n p ∩ (disk (n + 1)).carrier =
      {homothetyPoint (radius (n + 1)) p} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzBand, hzCarrier⟩
    have hzpOpen := radialBand_subset_openSegment n hp hzBand
    rw [disk_carrier] at hzCarrier
    obtain ⟨q, hq, hqz⟩ := hzCarrier
    have hqz' : homothetyPoint (radius (n + 1)) q = z := by
      simpa only [homothetyHomeomorph_apply] using hqz
    have hzqOpen : z ∈ openSegment ℝ center q := by
      rw [← hqz']
      exact homothetyPoint_mem_openSegment (radius_pos (n + 1))
        (radius_lt_one (n + 1)) hq
    have hpq : p = q := boundary_eq_of_mem_radial_segments hp hq
      (openSegment_subset_segment ℝ _ _ hzpOpen)
      (openSegment_subset_segment ℝ _ _ hzqOpen) (by
        intro hzc
        rw [hzc] at hzpOpen
        exact center_ne_boundaryPoint hp
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hzpOpen))
    rw [Set.mem_singleton_iff, hpq]
    exact hqz'.symm
  · intro z hz
    have hzEq := Set.mem_singleton_iff.mp hz
    subst z
    constructor
    · exact left_mem_segment ℝ _ _
    · rw [disk_carrier]
      exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩

theorem radialBand_inter_innerCarrier (n : ℕ) {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    radialBand n p ∩ (disk n).carrier =
      {homothetyPoint (radius n) p} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzBand, hzCarrier⟩
    have hzpOpen := radialBand_subset_openSegment n hp hzBand
    rw [disk_carrier] at hzCarrier
    obtain ⟨q, hq, hqz⟩ := hzCarrier
    have hqz' : homothetyPoint (radius n) q = z := by
      simpa only [homothetyHomeomorph_apply] using hqz
    have hzqOpen : z ∈ openSegment ℝ center q := by
      rw [← hqz']
      exact homothetyPoint_mem_openSegment (radius_pos n)
        (radius_lt_one n) hq
    have hpq : p = q := boundary_eq_of_mem_radial_segments hp hq
      (openSegment_subset_segment ℝ _ _ hzpOpen)
      (openSegment_subset_segment ℝ _ _ hzqOpen) (by
        intro hzc
        rw [hzc] at hzpOpen
        exact center_ne_boundaryPoint hp
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hzpOpen))
    rw [Set.mem_singleton_iff, hpq]
    exact hqz'.symm
  · intro z hz
    have hzEq := Set.mem_singleton_iff.mp hz
    subst z
    constructor
    · exact right_mem_segment ℝ _ _
    · rw [disk_carrier]
      exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩

private theorem innerHomothety_mem_segment_center_of_mem_radialBand
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    {p z : Plane}
    (hz : z ∈ segment ℝ (homothetyPoint s p) (homothetyPoint r p)) :
    homothetyPoint r p ∈ segment ℝ center z := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  let t : ℝ := (1 - u) * s + u * r
  have ht : 0 < t := by
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hs : 0 < s := hr.trans_le hrs
    dsimp [t]
    by_cases huEq : u = 1
    · rw [huEq]
      simpa using hr
    · have h1u : 0 < 1 - u := sub_pos.mpr (hu1.lt_of_ne huEq)
      exact add_pos_of_pos_of_nonneg (mul_pos h1u hs) (mul_nonneg hu0 hr.le)
  have hrt : r ≤ t := by
    dsimp [t]
    nlinarith [hu.1, hu.2]
  rw [segment_eq_image_lineMap]
  refine ⟨r / t, ⟨(div_nonneg hr.le ht.le), (div_le_one ht).mpr hrt⟩, ?_⟩
  have hband :
      AffineMap.lineMap (homothetyPoint s p) (homothetyPoint r p) u =
        homothetyPoint t p := by
    simp only [homothetyPoint, AffineMap.lineMap_apply_module, t]
    module
  rw [hband]
  have hhom (v : ℝ) :
      homothetyPoint v p = AffineMap.lineMap center p v := by
    simp only [homothetyPoint, AffineMap.lineMap_apply_module]
    module
  have hcompose :
      AffineMap.lineMap center (homothetyPoint t p) (r / t) =
        AffineMap.lineMap center p ((r / t) * t) := by
    rw [hhom]
    simp only [AffineMap.lineMap_apply_module]
    module
  calc
    AffineMap.lineMap center (homothetyPoint t p) (r / t) =
        AffineMap.lineMap center p ((r / t) * t) := hcompose
    _ = AffineMap.lineMap center p r := by
      congr 1
      field_simp [ht.ne']
    _ = homothetyPoint r p := (hhom r).symm

/-- Every radial band is contained in the exact closed polygonal shell. -/
theorem radialBand_subset_closedShell (n : ℕ) {p : Plane}
    (hp : p ∈ standardTriangleCircle.carrier) :
    radialBand n p ⊆ PolygonalCircle.closedShell (disk n) (disk (n + 1)) := by
  intro z hz
  constructor
  · have houter : homothetyPoint (radius (n + 1)) p ∈
        (disk (n + 1)).closedRegion := by
      rw [(disk (n + 1)).closedRegion_eq_union]
      right
      rw [disk_carrier]
      exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩
    have hinner : homothetyPoint (radius n) p ∈
        (disk (n + 1)).closedRegion := by
      rw [(disk (n + 1)).closedRegion_eq_union]
      left
      apply disk_strictlyNested n
      rw [(disk n).closedRegion_eq_union]
      right
      rw [disk_carrier]
      exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩
    exact (disk_closedRegion_isConvex (n + 1)).segment_subset
      houter hinner hz
  · intro hzInner
    have hinnerSegment : homothetyPoint (radius n) p ∈ segment ℝ center z :=
      innerHomothety_mem_segment_center_of_mem_radialBand
        (radius_pos n) (radius_lt_succ n).le hz
    have hinnerInterior : homothetyPoint (radius n) p ∈
        (disk n).interiorRegion :=
      (disk_interiorRegion_isConvex n).segment_subset
        (center_mem_disk_interiorRegion n) hzInner hinnerSegment
    have hinnerCarrier : homothetyPoint (radius n) p ∈
        (disk n).carrier := by
      rw [disk_carrier]
      exact ⟨p, hp, by simp only [homothetyHomeomorph_apply]⟩
    exact Set.disjoint_left.mp
      (Schoenflies.PolygonalCircle.carrier_disjoint_interiorRegion (disk n))
      hinnerCarrier hinnerInterior

end StandardPolygonalCollars

namespace JordanCircle.InitialAngularArcs

open StandardPolygonalCollars

variable {J : JordanCircle} (I : J.InitialAngularArcs)

/-- The standard-triangle boundary point corresponding to the left endpoint
of a complete-level Jordan arc. -/
def levelTargetBoundaryPoint {k : ℕ} (a : LevelAddress k) : Plane :=
  boundaryPoint J (J.curvePoint (I.levelArc a).left)

theorem levelTargetBoundaryPoint_mem {k : ℕ} (a : LevelAddress k) :
    I.levelTargetBoundaryPoint a ∈ standardTriangleCircle.carrier :=
  boundaryPoint_mem J _

theorem levelTargetBoundaryPoint_injective (k : ℕ) :
    Injective (fun a : LevelAddress k => I.levelTargetBoundaryPoint a) := by
  intro a b hab
  apply I.levelLeftPoint_injective
  exact congrArg Subtype.val (boundaryPoint_injective J hab)

/-- The inner endpoint of the target radial cut for source shell level `k`. -/
def levelTargetInnerMark (k : ℕ) (a : LevelAddress k) : Plane :=
  homothetyPoint (radius (k + 1)) (I.levelTargetBoundaryPoint a)

/-- The outer endpoint of the target radial cut for source shell level `k`. -/
def levelTargetOuterMark (k : ℕ) (a : LevelAddress k) : Plane :=
  homothetyPoint (radius (k + 2)) (I.levelTargetBoundaryPoint a)

theorem levelTargetInnerMark_mem (k : ℕ) (a : LevelAddress k) :
    I.levelTargetInnerMark k a ∈ (disk (k + 1)).carrier := by
  rw [disk_carrier]
  exact ⟨I.levelTargetBoundaryPoint a,
    I.levelTargetBoundaryPoint_mem a, by
      simp only [homothetyHomeomorph_apply, levelTargetInnerMark]⟩

theorem levelTargetOuterMark_mem (k : ℕ) (a : LevelAddress k) :
    I.levelTargetOuterMark k a ∈ (disk (k + 2)).carrier := by
  rw [disk_carrier]
  exact ⟨I.levelTargetBoundaryPoint a,
    I.levelTargetBoundaryPoint_mem a, by
      simp only [homothetyHomeomorph_apply, levelTargetOuterMark]⟩

theorem levelTargetOuterMark_ne_innerMark (k : ℕ)
    (a : LevelAddress k) :
    I.levelTargetOuterMark k a ≠ I.levelTargetInnerMark k a := by
  intro h
  have hinnerClosed : I.levelTargetInnerMark k a ∈
      (disk (k + 1)).closedRegion := by
    rw [(disk (k + 1)).closedRegion_eq_union]
    exact Or.inr (I.levelTargetInnerMark_mem k a)
  have hinnerOuterInterior : I.levelTargetInnerMark k a ∈
      (disk (k + 2)).interiorRegion :=
    disk_strictlyNested (k + 1) hinnerClosed
  exact Set.disjoint_left.mp
    (Schoenflies.PolygonalCircle.carrier_disjoint_interiorRegion
      (disk (k + 2)))
    (h ▸ I.levelTargetOuterMark_mem k a) hinnerOuterInterior

/-- The straight radial crosscut in the standard target shell. -/
def levelTargetAnnularCrosscut (k : ℕ) (a : LevelAddress k) :
    PolygonalCircle.AnnularCrosscut (disk (k + 1)) (disk (k + 2)) where
  outerPoint := I.levelTargetOuterMark k a
  innerPoint := I.levelTargetInnerMark k a
  path := Path.segment (I.levelTargetOuterMark k a)
    (I.levelTargetInnerMark k a)
  path_injective := Path.segment_injective_of_ne
    (I.levelTargetOuterMark_ne_innerMark k a)
  outerPoint_mem := I.levelTargetOuterMark_mem k a
  innerPoint_mem := I.levelTargetInnerMark_mem k a
  range_inter_outer := by
    rw [Path.range_segment]
    exact radialBand_inter_outerCarrier (k + 1)
      (I.levelTargetBoundaryPoint_mem a)
  range_inter_inner := by
    rw [Path.range_segment]
    exact radialBand_inter_innerCarrier (k + 1)
      (I.levelTargetBoundaryPoint_mem a)
  range_subset_closedShell := by
    rw [Path.range_segment]
    exact radialBand_subset_closedShell (k + 1)
      (I.levelTargetBoundaryPoint_mem a)

theorem range_levelTargetAnnularCrosscut (k : ℕ)
    (a : LevelAddress k) :
    range (I.levelTargetAnnularCrosscut k a).path =
      radialBand (k + 1) (I.levelTargetBoundaryPoint a) := by
  exact Path.range_segment _ _

theorem pairwise_disjoint_levelTargetAnnularCrosscut (k : ℕ) :
    Pairwise fun a b : LevelAddress k =>
      Disjoint (range (I.levelTargetAnnularCrosscut k a).path)
        (range (I.levelTargetAnnularCrosscut k b).path) := by
  intro a b hab
  rw [I.range_levelTargetAnnularCrosscut,
    I.range_levelTargetAnnularCrosscut]
  apply disjoint_radialBands (radius_pos (k + 1))
    (radius_lt_succ (k + 1)).le (radius_lt_one (k + 2))
    (I.levelTargetBoundaryPoint_mem a)
    (I.levelTargetBoundaryPoint_mem b)
  exact fun h => hab (I.levelTargetBoundaryPoint_injective k h)

/-- A compatible separator choice for two distinct target radial cuts. -/
def levelTargetSeparatorPair (k : ℕ) {a b : LevelAddress k}
    (hab : a ≠ b) :
    PolygonalCircle.AnnularCrosscut.SeparatorPair
      (I.levelTargetAnnularCrosscut k a)
      (I.levelTargetAnnularCrosscut k b) :=
  Classical.choice <|
    PolygonalCircle.AnnularCrosscut.exists_separatorPair
      (I.levelTargetAnnularCrosscut k a)
      (I.levelTargetAnnularCrosscut k b)
      (by
        intro h
        apply hab
        apply I.levelTargetBoundaryPoint_injective k
        apply (homothetyHomeomorph (radius (k + 2))
          (radius_pos (k + 2)).ne').injective
        simpa only [homothetyHomeomorph_apply,
          levelTargetAnnularCrosscut, levelTargetOuterMark] using h)
      (by
        intro h
        apply hab
        apply I.levelTargetBoundaryPoint_injective k
        apply (homothetyHomeomorph (radius (k + 1))
          (radius_pos (k + 1)).ne').injective
        simpa only [homothetyHomeomorph_apply,
          levelTargetAnnularCrosscut, levelTargetInnerMark] using h)

/-- The target radial cuts packaged for the polygonal two-cell filling
interface. -/
def levelTargetAnnularCellDecomposition (k : ℕ)
    {a b : LevelAddress k} (hab : a ≠ b) :
    Schoenflies.PolygonalCircle.AnnularCellDecomposition
      (disk (k + 1)) (disk (k + 2)) where
  first := I.levelTargetAnnularCrosscut k a
  second := I.levelTargetAnnularCrosscut k b
  separator := I.levelTargetSeparatorPair k hab
  nested := disk_strictlyNested (k + 1)
  disjoint := I.pairwise_disjoint_levelTargetAnnularCrosscut k hab
  outerPoints_ne := by
    intro h
    apply hab
    apply I.levelTargetBoundaryPoint_injective k
    apply (homothetyHomeomorph (radius (k + 2))
      (radius_pos (k + 2)).ne').injective
    simpa only [homothetyHomeomorph_apply,
      levelTargetAnnularCrosscut, levelTargetOuterMark] using h
  innerPoints_ne := by
    intro h
    apply hab
    apply I.levelTargetBoundaryPoint_injective k
    apply (homothetyHomeomorph (radius (k + 1))
      (radius_pos (k + 1)).ne').injective
    simpa only [homothetyHomeomorph_apply,
      levelTargetAnnularCrosscut, levelTargetInnerMark] using h
  first_segment := by
    change range (Path.segment
      (I.levelTargetOuterMark k a) (I.levelTargetInnerMark k a)) = _
    exact Path.range_segment _ _
  second_segment := by
    change range (Path.segment
      (I.levelTargetOuterMark k b) (I.levelTargetInnerMark k b)) = _
    exact Path.range_segment _ _

end JordanCircle.InitialAngularArcs

end

end Schoenflies
