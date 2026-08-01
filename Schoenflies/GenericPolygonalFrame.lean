import Schoenflies.PolygonalTransport
import Schoenflies.PolygonalPaths

/-!
# Generic perturbations of polygonal separator frames

Before applying the finite separator lemma, the polygonal frame may be moved
by an arbitrarily small translation.  The preliminary result below chooses a
translation direction transverse to every edge of a fixed simple broken line.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The standard alternating form on the coordinate plane. -/
def planeDet (u v : Plane) : ℝ :=
  u 0 * v 1 - u 1 * v 0

@[simp] theorem planeDet_vector (m : ℝ) (v : Plane) :
    planeDet !₂[1, m] v = v 1 - m * v 0 := by
  simp [planeDet]

theorem planeDet_sub_add_smul (b p w d : Plane) (r : ℝ) :
    planeDet (b - (p + r • w)) d =
      planeDet (b - p) d - r * planeDet w d := by
  simp [planeDet]
  ring

/-- Every point of the affine line through `a,b` has zero determinant with
the line direction. -/
theorem planeDet_eq_zero_of_mem_affineSpan_pair
    {a b x : Plane} (hx : x ∈ affineSpan ℝ ({a, b} : Set Plane)) :
    planeDet (a - x) (b - a) = 0 := by
  obtain ⟨r, rfl⟩ :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  simp [planeDet, AffineMap.lineMap_apply_module]
  ring

/-- A segment lies in the affine line through its endpoints. -/
theorem mem_affineSpan_pair_of_mem_segment
    {a b x : Plane} (hx : x ∈ segment ℝ a b) :
    x ∈ affineSpan ℝ ({a, b} : Set Plane) := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r, _hr, rfl⟩ := hx
  exact AffineMap.lineMap_mem_affineSpan_pair r a b

/-- If the first segment's initial point is not on the second segment's
supporting line, the two segments meet in at most one point. -/
theorem subsingleton_inter_segment_of_left_not_mem_affineSpan
    {p₀ p₁ q₀ q₁ : Plane}
    (hp : p₀ ∉ affineSpan ℝ ({q₀, q₁} : Set Plane)) :
    (segment ℝ p₀ p₁ ∩ segment ℝ q₀ q₁).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hxP := mem_affineSpan_pair_of_mem_segment hx.1
  have hyP := mem_affineSpan_pair_of_mem_segment hy.1
  have hxQ := mem_affineSpan_pair_of_mem_segment hx.2
  have hyQ := mem_affineSpan_pair_of_mem_segment hy.2
  have hPline : affineSpan ℝ ({x, y} : Set Plane) =
      affineSpan ℝ ({p₀, p₁} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hxP hyP hxy
  have hQline : affineSpan ℝ ({x, y} : Set Plane) =
      affineSpan ℝ ({q₀, q₁} : Set Plane) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hxQ hyQ hxy
  apply hp
  rw [← hQline, hPline]
  exact left_mem_affineSpan_pair ℝ p₀ p₁

namespace JordanCircle.SimpleBrokenLine

variable {U : Set Plane} {a b : Plane}

/-- A finite simple broken line admits one vector transverse to every listed
edge direction.  This reduces the later generic-translation choice to
avoiding finitely many scalar parameters. -/
theorem exists_transverseVector (B : SimpleBrokenLine U a b) :
    ∃ w : Plane, ∀ i : Fin B.data.n,
      planeDet w
        (B.data.vertex i.succ - B.data.vertex i.castSucc) ≠ 0 := by
  let slope : Fin B.data.n → ℝ := fun i =>
    let d := B.data.vertex i.succ - B.data.vertex i.castSucc
    if d 0 = 0 then 0 else d 1 / d 0
  let forbidden : Finset ℝ := Finset.univ.image slope
  obtain ⟨m, _hmIoo, hm⟩ :=
    (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).exists_notMem_finset
      forbidden
  refine ⟨!₂[1, m], ?_⟩
  intro i
  let d : Plane :=
    B.data.vertex i.succ - B.data.vertex i.castSucc
  have hiNe : i.succ ≠ i.castSucc := by
    intro hi
    have hiVal := congrArg Fin.val hi
    simp at hiVal
  have hdNe : d ≠ 0 := by
    intro hd
    apply hiNe
    apply B.vertex_injective
    exact sub_eq_zero.mp hd
  have hmSlope : m ≠ slope i := by
    intro hmi
    apply hm
    rw [hmi]
    exact Finset.mem_image_of_mem slope (Finset.mem_univ i)
  by_cases hd0 : d 0 = 0
  · have hd1 : d 1 ≠ 0 := by
      intro hd1
      apply hdNe
      ext j
      fin_cases j <;> simp [hd0, hd1]
    simpa [planeDet_vector, d, hd0] using hd1
  · intro hdet
    have heq : m = d 1 / d 0 := by
      rw [planeDet_vector] at hdet
      field_simp
      nlinarith
    apply hmSlope
    change m = (if d 0 = 0 then 0 else d 1 / d 0)
    rw [if_neg hd0]
    exact heq

/-- One direction can simultaneously be chosen transverse to every edge of
the broken line and every edge of a polygonal frame. -/
theorem exists_commonTransverseVector
    (B : SimpleBrokenLine U a b) (P : PolygonalCircle) :
    ∃ w : Plane,
      (∀ j : Fin B.data.n,
        planeDet w
          (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0) ∧
      ∀ i : ZMod P.n,
        planeDet w (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
  let direction : Fin B.data.n ⊕ ZMod P.n → Plane
    | Sum.inl j => B.data.vertex j.succ - B.data.vertex j.castSucc
    | Sum.inr i => P.vertex (i + 1) - P.vertex i
  have hdirection : ∀ k, direction k ≠ 0 := by
    intro k
    rcases k with j | i
    · intro hzero
      have := B.vertex_injective (sub_eq_zero.mp hzero)
      have hval := congrArg Fin.val this
      simp at hval
    · exact sub_ne_zero.mpr (P.adjacent_ne i).symm
  let slope : Fin B.data.n ⊕ ZMod P.n → ℝ := fun k =>
    if (direction k) 0 = 0 then 0 else (direction k) 1 / (direction k) 0
  let forbidden : Finset ℝ := Finset.univ.image slope
  obtain ⟨m, _hmIoo, hm⟩ :=
    (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).exists_notMem_finset
      forbidden
  have htransverse : ∀ k,
      planeDet !₂[1, m] (direction k) ≠ 0 := by
    intro k
    let d := direction k
    have hdNe : d ≠ 0 := hdirection k
    have hmSlope : m ≠ slope k := by
      intro hmi
      apply hm
      rw [hmi]
      exact Finset.mem_image_of_mem slope (Finset.mem_univ k)
    by_cases hd0 : d 0 = 0
    · have hd1 : d 1 ≠ 0 := by
        intro hd1
        apply hdNe
        ext q
        fin_cases q <;> simp [hd0, hd1]
      simpa [planeDet_vector, d, hd0] using hd1
    · intro hdet
      have heq : m = d 1 / d 0 := by
        rw [planeDet_vector] at hdet
        field_simp
        nlinarith
      apply hmSlope
      change m = (if d 0 = 0 then 0 else d 1 / d 0)
      rw [if_neg hd0]
      exact heq
  refine ⟨!₂[1, m], ?_, ?_⟩
  · intro j
    exact htransverse (Sum.inl j)
  · intro i
    exact htransverse (Sum.inr i)

/-- There is an arbitrarily small translation for which no translated frame
vertex lies on a supporting line of the fixed broken line.  Consequently no
translated frame edge can overlap a nontrivial subsegment of a broken-line
edge. -/
theorem exists_small_translation_no_vertex_on_edgeLine
    (B : SimpleBrokenLine U a b) (P : PolygonalCircle)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ v : Plane, ‖v‖ < epsilon ∧
      (∀ (i : ZMod P.n) (j : Fin B.data.n),
        planeDet
          (B.data.vertex j.castSucc -
            ((Homeomorph.addLeft v : Plane ≃ₜ Plane) (P.vertex i)))
          (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0) ∧
      ∀ (i : ZMod P.n) (j : Fin (B.data.n + 1)),
        planeDet
          (B.data.vertex j -
            ((Homeomorph.addLeft v : Plane ≃ₜ Plane) (P.vertex i)))
          (P.vertex (i + 1) - P.vertex i) ≠ 0 := by
  obtain ⟨w, hwB, hwP⟩ := B.exists_commonTransverseVector P
  let badB : ZMod P.n × Fin B.data.n → ℝ := fun ij =>
    planeDet
        (B.data.vertex ij.2.castSucc - P.vertex ij.1)
        (B.data.vertex ij.2.succ - B.data.vertex ij.2.castSucc) /
      planeDet w
        (B.data.vertex ij.2.succ - B.data.vertex ij.2.castSucc)
  let badP : ZMod P.n × Fin (B.data.n + 1) → ℝ := fun ij =>
    planeDet
        (B.data.vertex ij.2 - P.vertex ij.1)
        (P.vertex (ij.1 + 1) - P.vertex ij.1) /
      planeDet w (P.vertex (ij.1 + 1) - P.vertex ij.1)
  let forbidden : Finset ℝ :=
    Finset.univ.image badB ∪ Finset.univ.image badP
  let R : ℝ := ‖w‖ + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hquotient : 0 < epsilon / R := div_pos hepsilon hR
  obtain ⟨r, hr, hrForbidden⟩ :=
    (Set.Ioo_infinite hquotient).exists_notMem_finset forbidden
  let v : Plane := r • w
  have hvNorm : ‖v‖ < epsilon := by
    have hwLtR : ‖w‖ < R := by
      dsimp [R]
      linarith
    have hrNonneg : 0 ≤ r := hr.1.le
    have hmul : r * ‖w‖ < (epsilon / R) * R := by
      calc
        r * ‖w‖ ≤ r * R := mul_le_mul_of_nonneg_left hwLtR.le hrNonneg
        _ < (epsilon / R) * R :=
          mul_lt_mul_of_pos_right hr.2 hR
    rw [div_mul_cancel₀ epsilon hR.ne'] at hmul
    simpa [v, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1] using hmul
  refine ⟨v, hvNorm, ?_, ?_⟩
  · intro i j
    have hdet : planeDet w
        (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0 := hwB j
    have hrBad : r ≠ badB (i, j) := by
      intro hrEq
      apply hrForbidden
      apply Finset.mem_union_left
      rw [hrEq]
      exact Finset.mem_image_of_mem badB (Finset.mem_univ (i, j))
    intro hline
    have hformula := planeDet_sub_add_smul
      (B.data.vertex j.castSucc) (P.vertex i) w
      (B.data.vertex j.succ - B.data.vertex j.castSucc) r
    have hzero :
        planeDet
            (B.data.vertex j.castSucc - P.vertex i)
            (B.data.vertex j.succ - B.data.vertex j.castSucc) -
          r * planeDet w
            (B.data.vertex j.succ - B.data.vertex j.castSucc) = 0 := by
      rw [← hformula]
      simpa [v, add_comm] using hline
    apply hrBad
    dsimp [badB]
    apply (eq_div_iff hdet).2
    nlinarith
  · intro i j
    have hdet :
        planeDet w (P.vertex (i + 1) - P.vertex i) ≠ 0 := hwP i
    have hrBad : r ≠ badP (i, j) := by
      intro hrEq
      apply hrForbidden
      apply Finset.mem_union_right
      rw [hrEq]
      exact Finset.mem_image_of_mem badP (Finset.mem_univ (i, j))
    intro hline
    have hformula := planeDet_sub_add_smul
      (B.data.vertex j) (P.vertex i) w
      (P.vertex (i + 1) - P.vertex i) r
    have hzero :
        planeDet (B.data.vertex j - P.vertex i)
            (P.vertex (i + 1) - P.vertex i) -
          r * planeDet w (P.vertex (i + 1) - P.vertex i) = 0 := by
      rw [← hformula]
      simpa [v, add_comm] using hline
    apply hrBad
    dsimp [badP]
    apply (eq_div_iff hdet).2
    nlinarith

/-- Under the preceding genericity condition, the translated polygon carrier
has only finitely many intersections with the broken-line carrier. -/
theorem finite_translatedCarrier_inter_segmentCarrier
    (B : SimpleBrokenLine U a b) (P : PolygonalCircle) (v : Plane)
    (hgeneric : ∀ (i : ZMod P.n) (j : Fin B.data.n),
      planeDet
          (B.data.vertex j.castSucc -
            ((Homeomorph.addLeft v : Plane ≃ₜ Plane) (P.vertex i)))
          (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0) :
    (((Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.carrier) ∩
      B.data.segmentCarrier).Finite := by
  let pEdge : ZMod P.n → Set Plane := fun i =>
    segment ℝ (v + P.vertex i) (v + P.vertex (i + 1))
  let bEdge : Fin B.data.n → Set Plane := fun j =>
    segment ℝ (B.data.vertex j.castSucc) (B.data.vertex j.succ)
  have hpCarrier :
      (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.carrier =
        ⋃ i, pEdge i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [PolygonalCircle.carrier] at hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      apply Set.mem_iUnion_of_mem i
      change v + y ∈ segment ℝ (v + P.vertex i) (v + P.vertex (i + 1))
      rw [← segment_translate_image]
      exact ⟨y, hi, rfl⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      change x ∈ segment ℝ (v + P.vertex i) (v + P.vertex (i + 1)) at hi
      rw [← segment_translate_image] at hi
      obtain ⟨y, hy, rfl⟩ := hi
      refine ⟨y, ?_, rfl⟩
      rw [PolygonalCircle.carrier]
      exact Set.mem_iUnion_of_mem i hy
  have hbCarrier : B.data.segmentCarrier = ⋃ j, bEdge j := by
    rfl
  rw [hpCarrier, hbCarrier]
  have hdistrib :
      (⋃ i, pEdge i) ∩ (⋃ j, bEdge j) =
        ⋃ i, ⋃ j, pEdge i ∩ bEdge j := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    aesop
  rw [hdistrib]
  apply Set.finite_iUnion
  intro i
  apply Set.finite_iUnion
  intro j
  apply Set.Subsingleton.finite
  apply subsingleton_inter_segment_of_left_not_mem_affineSpan
  intro hpLine
  have hzero := planeDet_eq_zero_of_mem_affineSpan_pair hpLine
  apply hgeneric i j
  simpa [pEdge, bEdge, add_comm] using hzero

/-- A separator frame can be moved into finite-intersection position while
preserving prescribed compact sets on its two sides. -/
theorem exists_generic_translation
    (B : SimpleBrokenLine U a b) (P : PolygonalCircle)
    {C D : Set Plane}
    (hCcompact : IsCompact C) (hDcompact : IsCompact D)
    (hC : C ⊆ P.interiorRegion) (hD : D ⊆ P.exteriorRegion)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (v : Plane) (Q : PolygonalCircle),
      ‖v‖ < epsilon ∧
      Q.carrier = (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.carrier ∧
      C ⊆ Q.interiorRegion ∧ D ⊆ Q.exteriorRegion ∧
      (Q.carrier ∩ B.data.segmentCarrier).Finite ∧
      (∀ (i : ZMod Q.n) (j : Fin B.data.n),
        planeDet
          (B.data.vertex j.castSucc - Q.vertex i)
          (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0) ∧
      ∀ (i : ZMod Q.n) (j : Fin (B.data.n + 1)),
        planeDet
          (B.data.vertex j - Q.vertex i)
          (Q.vertex (i + 1) - Q.vertex i) ≠ 0 := by
  obtain ⟨eta, heta, hstable⟩ :=
    PolygonalTransport.exists_translation_stabilityRadius
      P hCcompact hDcompact hC hD
  let delta : ℝ := min epsilon eta
  have hdelta : 0 < delta := lt_min hepsilon heta
  obtain ⟨v, hv, hgeneric, hgenericVertices⟩ :=
    B.exists_small_translation_no_vertex_on_edgeLine P hdelta
  let h : Plane ≃ₜ Plane := Homeomorph.addLeft v
  have hedge : ∀ i : ZMod P.n,
      h '' P.edgeSegment i =
        segment ℝ (h (P.vertex i)) (h (P.vertex (i + 1))) := by
    intro i
    rw [PolygonalCircle.edgeSegment]
    exact segment_translate_image ℝ v (P.vertex i) (P.vertex (i + 1))
  let Q : PolygonalCircle := P.mapHomeomorph h hedge
  have hQcarrier :
      Q.carrier = (Homeomorph.addLeft v : Plane ≃ₜ Plane) '' P.carrier := by
    exact P.mapHomeomorph_carrier h hedge
  have hvEpsilon : ‖v‖ < epsilon := hv.trans_le (min_le_left _ _)
  have hvEta : ‖v‖ < eta := hv.trans_le (min_le_right _ _)
  obtain ⟨hCQ, hDQ⟩ := hstable v Q hvEta hQcarrier
  have hfinite : (Q.carrier ∩ B.data.segmentCarrier).Finite := by
    rw [hQcarrier]
    exact B.finite_translatedCarrier_inter_segmentCarrier P v hgeneric
  have hgenericQ : ∀ (i : ZMod Q.n) (j : Fin B.data.n),
      planeDet
        (B.data.vertex j.castSucc - Q.vertex i)
        (B.data.vertex j.succ - B.data.vertex j.castSucc) ≠ 0 := by
    intro i j
    exact hgeneric i j
  have hgenericVerticesQ :
      ∀ (i : ZMod Q.n) (j : Fin (B.data.n + 1)),
        planeDet
          (B.data.vertex j - Q.vertex i)
          (Q.vertex (i + 1) - Q.vertex i) ≠ 0 := by
    simp only [Q, PolygonalCircle.mapHomeomorph_n,
      PolygonalCircle.mapHomeomorph_vertex, h, Homeomorph.coe_addLeft,
      add_sub_add_left_eq_sub]
    exact hgenericVertices
  exact ⟨v, Q, hvEpsilon, hQcarrier, hCQ, hDQ, hfinite,
    hgenericQ, hgenericVerticesQ⟩

end JordanCircle.SimpleBrokenLine

end Schoenflies
