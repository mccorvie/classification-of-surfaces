import Schoenflies.PolyhedralDiskNeighborhoods

/-!
# Nested polygonal disk exhaustions of a Jordan domain

Finite polyhedral neighborhoods give a direct way to choose the correct side
of every approximating polygon.  At successor stage `k`, the connected core
contains both the preceding closed polygonal disk and every point of the
Jordan inside outside the `1/(k+1)` boundary neighborhood.  Its
exterior-facing polygonal boundary therefore gives all three properties
needed later:

* strict nesting of closed disks;
* exhaustion of the open bounded component;
* convergence of the polygonal carriers to the Jordan carrier.

This construction is independent of the synchronized collar sequence.  The
latter remains useful for boundary markings; the disks here remove its
previously unresolved bounded-side choice.
-/

namespace Schoenflies

open Metric Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle

/-- The compact part of the closed Jordan disk which stays outside the open
`delta`-neighborhood of the boundary. -/
def deepInsideCore (J : JordanCircle) (delta : ℝ) : Set Plane :=
  closure J.inside \ thickening delta J.carrier

theorem isCompact_closure_inside (J : JordanCircle) :
    IsCompact (closure J.inside) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    J.inside_bounded.closure

theorem isCompact_deepInsideCore (J : JordanCircle) (delta : ℝ) :
    IsCompact (J.deepInsideCore delta) :=
  J.isCompact_closure_inside.diff isOpen_thickening

theorem deepInsideCore_subset_inside (J : JordanCircle)
    {delta : ℝ} (hdelta : 0 < delta) :
    J.deepInsideCore delta ⊆ J.inside := by
  rintro x ⟨hxClosure, hxNotNear⟩
  rw [J.closure_inside] at hxClosure
  rcases hxClosure with hxInside | hxCarrier
  · exact hxInside
  · exact False.elim <| hxNotNear
      (Metric.self_subset_thickening hdelta J.carrier hxCarrier)

/-- The core used to select a successor disk: the preceding disk together
with the prescribed compact-depth part of the Jordan inside. -/
def polygonalSuccessorCore (J : JordanCircle) (P : PolygonalCircle)
    (delta : ℝ) : Set Plane :=
  P.closedRegion ∪ J.deepInsideCore delta

theorem isCompact_polygonalSuccessorCore (J : JordanCircle)
    (P : PolygonalCircle) (delta : ℝ) :
    IsCompact (J.polygonalSuccessorCore P delta) :=
  P.isCompact_closedRegion.union (J.isCompact_deepInsideCore delta)

theorem polygonalSuccessorCore_nonempty (J : JordanCircle)
    (P : PolygonalCircle) (delta : ℝ) :
    (J.polygonalSuccessorCore P delta).Nonempty := by
  refine ⟨P.vertex 0, Or.inl ?_⟩
  rw [P.closedRegion_eq_union]
  exact Or.inr (P.vertex_mem_carrier 0)

theorem polygonalSuccessorCore_subset_inside (J : JordanCircle)
    (P : PolygonalCircle) (hPinside : P.closedRegion ⊆ J.inside)
    {delta : ℝ} (hdelta : 0 < delta) :
    J.polygonalSuccessorCore P delta ⊆ J.inside :=
  Set.union_subset hPinside (J.deepInsideCore_subset_inside hdelta)

/-- One automatically nested polygonal successor.  In contrast with a raw
synchronized collar, the preceding disk is on the bounded side by
construction. -/
theorem exists_nestedPolygonalDisk_near
    (J : JordanCircle) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Q : PolygonalCircle,
      P.closedRegion ⊆ Q.interiorRegion ∧
        J.deepInsideCore delta ⊆ Q.interiorRegion ∧
        Q.closedRegion ⊆ J.inside ∧
        Q.carrier ⊆ thickening delta J.carrier := by
  let K := J.polygonalSuccessorCore P delta
  obtain ⟨C, hKC, hCcompact, hCconnected, hCinside⟩ :=
    J.exists_compactConnected_superset_inside
      (J.isCompact_polygonalSuccessorCore P delta)
      (J.polygonalSuccessorCore_nonempty P delta)
      (J.polygonalSuccessorCore_subset_inside P hPinside hdelta)
  obtain ⟨Q, hCInterior, hQinside, hQdisjoint⟩ :=
    J.exists_polygonalDiskNeighborhood_with_boundary_avoidance
      hCcompact hCconnected hCinside
  have hPInterior : P.closedRegion ⊆ Q.interiorRegion := by
    exact (fun x hx => hCInterior (hKC (Or.inl hx)))
  have hdeepInterior : J.deepInsideCore delta ⊆ Q.interiorRegion := by
    exact (fun x hx => hCInterior (hKC (Or.inr hx)))
  have hQnear : Q.carrier ⊆ thickening delta J.carrier := by
    intro x hxCarrier
    by_contra hxNear
    have hxClosed : x ∈ Q.closedRegion := by
      rw [Q.closedRegion_eq_union]
      exact Or.inr hxCarrier
    have hxInside : x ∈ J.inside := hQinside hxClosed
    have hxDeep : x ∈ J.deepInsideCore delta :=
      ⟨subset_closure hxInside, hxNear⟩
    have hxC : x ∈ C := hKC (Or.inr hxDeep)
    exact Set.disjoint_left.mp hQdisjoint hxCarrier hxC
  exact ⟨Q, hPInterior, hdeepInterior, hQinside, hQnear⟩

/-- A nested successor may additionally be required to contain any prescribed
compact subset of the Jordan inside.  This is the marked version used later:
at stage `n`, the extra compact set will be the finite set of tips of the
level-`n` retained access hairs. -/
theorem exists_nestedPolygonalDisk_near_containing_compact
    (J : JordanCircle) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside)
    {K : Set Plane} (hKcompact : IsCompact K) (hKinside : K ⊆ J.inside)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Q : PolygonalCircle,
      P.closedRegion ⊆ Q.interiorRegion ∧
        J.deepInsideCore delta ⊆ Q.interiorRegion ∧
        K ⊆ Q.interiorRegion ∧
        Q.closedRegion ⊆ J.inside ∧
        Q.carrier ⊆ thickening delta J.carrier := by
  let K₀ := (P.closedRegion ∪ J.deepInsideCore delta) ∪ K
  have hK₀compact : IsCompact K₀ :=
    (P.isCompact_closedRegion.union
      (J.isCompact_deepInsideCore delta)).union hKcompact
  have hK₀nonempty : K₀.Nonempty := by
    refine ⟨P.vertex 0, Or.inl (Or.inl ?_)⟩
    rw [P.closedRegion_eq_union]
    exact Or.inr (P.vertex_mem_carrier 0)
  have hK₀inside : K₀ ⊆ J.inside := by
    exact Set.union_subset
      (Set.union_subset hPinside
        (J.deepInsideCore_subset_inside hdelta)) hKinside
  obtain ⟨C, hK₀C, hCcompact, hCconnected, hCinside⟩ :=
    J.exists_compactConnected_superset_inside
      hK₀compact hK₀nonempty hK₀inside
  obtain ⟨Q, hCInterior, hQinside, hQdisjoint⟩ :=
    J.exists_polygonalDiskNeighborhood_with_boundary_avoidance
      hCcompact hCconnected hCinside
  have hPInterior : P.closedRegion ⊆ Q.interiorRegion := by
    exact fun x hx => hCInterior (hK₀C (Or.inl (Or.inl hx)))
  have hdeepInterior : J.deepInsideCore delta ⊆ Q.interiorRegion := by
    exact fun x hx => hCInterior (hK₀C (Or.inl (Or.inr hx)))
  have hKInterior : K ⊆ Q.interiorRegion := by
    exact fun x hx => hCInterior (hK₀C (Or.inr hx))
  have hQnear : Q.carrier ⊆ thickening delta J.carrier := by
    intro x hxCarrier
    by_contra hxNear
    have hxClosed : x ∈ Q.closedRegion := by
      rw [Q.closedRegion_eq_union]
      exact Or.inr hxCarrier
    have hxInside : x ∈ J.inside := hQinside hxClosed
    have hxDeep : x ∈ J.deepInsideCore delta :=
      ⟨subset_closure hxInside, hxNear⟩
    have hxC : x ∈ C := hK₀C (Or.inl (Or.inr hxDeep))
    exact Set.disjoint_left.mp hQdisjoint hxCarrier hxC
  exact ⟨Q, hPInterior, hdeepInterior, hKInterior,
    hQinside, hQnear⟩

/-- The target boundary scale at successor number `k+1`. -/
def polygonalDiskBoundaryScale (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ)⁻¹

theorem polygonalDiskBoundaryScale_pos (k : ℕ) :
    0 < polygonalDiskBoundaryScale k := by
  unfold polygonalDiskBoundaryScale
  positivity

/-- An initial polygonal disk around the selected inside point. -/
noncomputable def initialPolygonalDisk (J : JordanCircle) : PolygonalCircle :=
  Classical.choose <| J.exists_polygonalDiskNeighborhood
    (C := {J.insidePoint}) isCompact_singleton isConnected_singleton
    (Set.singleton_subset_iff.mpr J.insidePoint_mem_inside)

theorem initialPolygonalDisk_closedRegion_subset_inside (J : JordanCircle) :
    J.initialPolygonalDisk.closedRegion ⊆ J.inside :=
  (Classical.choose_spec <| J.exists_polygonalDiskNeighborhood
    (C := {J.insidePoint}) isCompact_singleton isConnected_singleton
    (Set.singleton_subset_iff.mpr J.insidePoint_mem_inside)).2

/-- Choose the next nested disk with the prescribed boundary scale. -/
noncomputable def nextPolygonalDisk (J : JordanCircle) (k : ℕ)
    (P : PolygonalCircle) (hPinside : P.closedRegion ⊆ J.inside) :
    PolygonalCircle :=
  Classical.choose <| J.exists_nestedPolygonalDisk_near P hPinside
    (polygonalDiskBoundaryScale_pos k)

theorem closedRegion_subset_interior_nextPolygonalDisk
    (J : JordanCircle) (k : ℕ) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    P.closedRegion ⊆
      (J.nextPolygonalDisk k P hPinside).interiorRegion :=
  (Classical.choose_spec <| J.exists_nestedPolygonalDisk_near P hPinside
    (polygonalDiskBoundaryScale_pos k)).1

theorem deepInsideCore_subset_interior_nextPolygonalDisk
    (J : JordanCircle) (k : ℕ) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    J.deepInsideCore (polygonalDiskBoundaryScale k) ⊆
      (J.nextPolygonalDisk k P hPinside).interiorRegion :=
  (Classical.choose_spec <| J.exists_nestedPolygonalDisk_near P hPinside
    (polygonalDiskBoundaryScale_pos k)).2.1

theorem nextPolygonalDisk_closedRegion_subset_inside
    (J : JordanCircle) (k : ℕ) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    (J.nextPolygonalDisk k P hPinside).closedRegion ⊆ J.inside :=
  (Classical.choose_spec <| J.exists_nestedPolygonalDisk_near P hPinside
    (polygonalDiskBoundaryScale_pos k)).2.2.1

theorem nextPolygonalDisk_carrier_subset_thickening
    (J : JordanCircle) (k : ℕ) (P : PolygonalCircle)
    (hPinside : P.closedRegion ⊆ J.inside) :
    (J.nextPolygonalDisk k P hPinside).carrier ⊆
      thickening (polygonalDiskBoundaryScale k) J.carrier :=
  (Classical.choose_spec <| J.exists_nestedPolygonalDisk_near P hPinside
    (polygonalDiskBoundaryScale_pos k)).2.2.2

/-- A polygonal disk together with the invariant that its closed region is in
the Jordan inside.  Recursing on this subtype avoids a separate dependent
well-founded proof. -/
abbrev InsidePolygonalDisk (J : JordanCircle) :=
  {P : PolygonalCircle // P.closedRegion ⊆ J.inside}

/-- The recursive nested exhaustion, with its inside invariant packaged in
the codomain. -/
noncomputable def polygonalDiskExhaustionStage
    (J : JordanCircle) : ℕ → J.InsidePolygonalDisk
  | 0 => ⟨J.initialPolygonalDisk,
      J.initialPolygonalDisk_closedRegion_subset_inside⟩
  | k + 1 =>
      let P := J.polygonalDiskExhaustionStage k
      ⟨J.nextPolygonalDisk k P P.2,
        J.nextPolygonalDisk_closedRegion_subset_inside k P P.2⟩

/-- The polygonal circle underlying exhaustion stage `k`. -/
noncomputable def polygonalDiskExhaustion
    (J : JordanCircle) (k : ℕ) : PolygonalCircle :=
  (J.polygonalDiskExhaustionStage k).1

theorem polygonalDiskExhaustion_closedRegion_subset_inside
    (J : JordanCircle) (k : ℕ) :
    (J.polygonalDiskExhaustion k).closedRegion ⊆ J.inside :=
  (J.polygonalDiskExhaustionStage k).2

@[simp] theorem polygonalDiskExhaustion_zero (J : JordanCircle) :
    J.polygonalDiskExhaustion 0 = J.initialPolygonalDisk := rfl

@[simp] theorem polygonalDiskExhaustion_succ (J : JordanCircle) (k : ℕ) :
    J.polygonalDiskExhaustion (k + 1) =
      J.nextPolygonalDisk k (J.polygonalDiskExhaustion k)
        (J.polygonalDiskExhaustion_closedRegion_subset_inside k) := rfl

/-- Strict nesting at every successor stage. -/
theorem polygonalDiskExhaustion_strictly_nested
    (J : JordanCircle) (k : ℕ) :
    (J.polygonalDiskExhaustion k).closedRegion ⊆
      (J.polygonalDiskExhaustion (k + 1)).interiorRegion := by
  rw [J.polygonalDiskExhaustion_succ k]
  exact J.closedRegion_subset_interior_nextPolygonalDisk k _ _

/-- Every compact-depth core occurs inside the corresponding successor. -/
theorem deepInsideCore_subset_polygonalDiskExhaustion_succ
    (J : JordanCircle) (k : ℕ) :
    J.deepInsideCore (polygonalDiskBoundaryScale k) ⊆
      (J.polygonalDiskExhaustion (k + 1)).interiorRegion := by
  rw [J.polygonalDiskExhaustion_succ k]
  exact J.deepInsideCore_subset_interior_nextPolygonalDisk k _ _

/-- Successor boundaries lie in the prescribed shrinking neighborhoods of
the Jordan carrier. -/
theorem polygonalDiskExhaustion_succ_carrier_subset_thickening
    (J : JordanCircle) (k : ℕ) :
    (J.polygonalDiskExhaustion (k + 1)).carrier ⊆
      thickening (polygonalDiskBoundaryScale k) J.carrier := by
  rw [J.polygonalDiskExhaustion_succ k]
  exact J.nextPolygonalDisk_carrier_subset_thickening k _ _

/-- Every point of the Jordan inside belongs to all sufficiently deep open
polygonal disks. -/
theorem eventually_mem_polygonalDiskExhaustion_interior
    (J : JordanCircle) {x : Plane} (hx : x ∈ J.inside) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      x ∈ (J.polygonalDiskExhaustion (k + 1)).interiorRegion := by
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    (Metric.isOpen_iff.mp J.inside_isOpen) x hx
  have hxNotNear : x ∉ thickening (epsilon / 2) J.carrier := by
    intro hxNear
    rw [Metric.mem_thickening_iff] at hxNear
    obtain ⟨q, hqCarrier, hxq⟩ := hxNear
    have hqBall : q ∈ ball x epsilon := by
      rw [Metric.mem_ball, dist_comm]
      nlinarith
    exact J.inside_subset_compl (hball hqBall) hqCarrier
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hepsilon)
  refine ⟨N, ?_⟩
  intro k hk
  have hscale : polygonalDiskBoundaryScale k ≤ epsilon / 2 := by
    have hmono : polygonalDiskBoundaryScale k ≤
        polygonalDiskBoundaryScale N := by
      unfold polygonalDiskBoundaryScale
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      exact_mod_cast Nat.add_le_add_right hk 1
    have hsmall : polygonalDiskBoundaryScale N < epsilon / 2 := by
      simpa [polygonalDiskBoundaryScale, one_div] using hN
    exact hmono.trans hsmall.le
  have hxNotScale : x ∉
      thickening (polygonalDiskBoundaryScale k) J.carrier := by
    intro hxScale
    exact hxNotNear
      (thickening_mono hscale J.carrier hxScale)
  have hxDeep : x ∈ J.deepInsideCore (polygonalDiskBoundaryScale k) :=
    ⟨subset_closure hx, hxNotScale⟩
  exact J.deepInsideCore_subset_polygonalDiskExhaustion_succ k hxDeep

/-- The successor carriers eventually lie in every positive neighborhood of
the Jordan carrier. -/
theorem eventually_polygonalDiskExhaustion_carrier_subset_thickening
    (J : JordanCircle) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (J.polygonalDiskExhaustion (k + 1)).carrier ⊆
        thickening delta J.carrier := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hdelta
  refine ⟨N, ?_⟩
  intro k hk
  have hmono : polygonalDiskBoundaryScale k ≤
      polygonalDiskBoundaryScale N := by
    unfold polygonalDiskBoundaryScale
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.add_le_add_right hk 1
  have hsmall : polygonalDiskBoundaryScale N < delta := by
    simpa [polygonalDiskBoundaryScale, one_div] using hN
  exact (J.polygonalDiskExhaustion_succ_carrier_subset_thickening k).trans
    (thickening_mono (hmono.trans hsmall.le) J.carrier)

end JordanCircle

end

end Schoenflies
