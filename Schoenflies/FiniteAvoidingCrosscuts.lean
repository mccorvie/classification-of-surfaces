import Schoenflies.AvoidingControlledCrosscuts

/-!
# Greedy finite families of disjoint inside crosscuts

The arbitrary-open form of Moise 9.5 supports a direct finite induction.
At each step the forbidden set is enlarged by the compact carrier of the
new line.  Because all earlier lines lie in the Jordan inside, this enlarged
closed set remains disjoint from every remaining boundary arc.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

namespace JordanCircle

variable {J : JordanCircle}

/-- Pairwise-disjoint finite inside joins for a listed family of boundary
arcs, additionally avoiding one fixed closed set. -/
structure FiniteAvoidingJoinFamily (N : ℕ)
    (A : Fin N → J.AccessibleAngularArc)
    (HL : ∀ i, J.InsideAccessHair (J.curvePoint (A i).left))
    (HR : ∀ i, J.InsideAccessHair (J.curvePoint (A i).right))
    (V : Fin N → Set Plane)
    (K : Set Plane) where
  rightPoint : Fin N → Plane
  leftPoint : Fin N → Plane
  rightPoint_mem : ∀ i, rightPoint i ∈ (HR i).carrier
  leftPoint_mem : ∀ i, leftPoint i ∈ (HL i).carrier
  rightPoint_inside : ∀ i, rightPoint i ∈ J.inside
  leftPoint_inside : ∀ i, leftPoint i ∈ J.inside
  endpoint_ne : ∀ i, rightPoint i ≠ leftPoint i
  /-- The open set in which the original line for index `i` was selected.
  Retaining this set lets later trimming reuse that very line rather than
  recomputing a canonical path in a larger ambient set. -/
  sourceAmbient : Fin N → Set Plane
  sourceLine : ∀ i,
    SimpleBrokenLine (sourceAmbient i) (rightPoint i) (leftPoint i)
  path : ∀ i, Path (rightPoint i) (leftPoint i)
  path_eq_sourceLine : ∀ i, path i = (sourceLine i).toPath (endpoint_ne i)
  path_injective : ∀ i, Injective (path i)
  sourceAmbient_subset : ∀ i, sourceAmbient i ⊆ J.inside ∩ V i
  carrierLine : ∀ i,
    SimpleBrokenLine J.inside (rightPoint i) (leftPoint i)
  segmentCarrier_carrierLine_eq_range : ∀ i,
    (carrierLine i).data.segmentCarrier = range (path i)
  controlled : ∀ i, range (path i) ⊆ V i
  avoids : ∀ i, Disjoint (range (path i)) K
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint (range (path i)) (range (path j))

/-- Greedily choose all finite joins, each in the complement of the carriers
chosen before it. -/
theorem nonempty_finiteAvoidingJoinFamily :
    ∀ (N : ℕ)
      (A : Fin N → J.AccessibleAngularArc)
      (HL : ∀ i, J.InsideAccessHair (J.curvePoint (A i).left))
      (HR : ∀ i, J.InsideAccessHair (J.curvePoint (A i).right))
      (hHairs : ∀ i, Disjoint (HL i).carrier (HR i).carrier)
      (V : Fin N → Set Plane) (hVopen : ∀ i, IsOpen (V i))
      (hArcV : ∀ i, (A i).curveArcPlane ⊆ V i)
      (K : Set Plane) (hKclosed : IsClosed K)
      (hKarc : ∀ i, Disjoint K (A i).curveArcPlane),
      Nonempty (J.FiniteAvoidingJoinFamily N A HL HR V K) := by
  intro N
  induction N with
  | zero =>
      intro A HL HR _hHairs V _hVopen _hArcV K _hKclosed _hKarc
      exact ⟨{
        rightPoint := fun i => Fin.elim0 i
        leftPoint := fun i => Fin.elim0 i
        rightPoint_mem := fun i => Fin.elim0 i
        leftPoint_mem := fun i => Fin.elim0 i
        rightPoint_inside := fun i => Fin.elim0 i
        leftPoint_inside := fun i => Fin.elim0 i
        endpoint_ne := fun i => Fin.elim0 i
        sourceAmbient := fun i => Fin.elim0 i
        sourceLine := fun i => Fin.elim0 i
        path := fun i => Fin.elim0 i
        path_eq_sourceLine := fun i => Fin.elim0 i
        path_injective := fun i => Fin.elim0 i
        sourceAmbient_subset := fun i => Fin.elim0 i
        carrierLine := fun i => Fin.elim0 i
        segmentCarrier_carrierLine_eq_range := fun i => Fin.elim0 i
        controlled := fun i => Fin.elim0 i
        avoids := fun i => Fin.elim0 i
        pairwise_disjoint := fun i => Fin.elim0 i }⟩
  | succ N ih =>
      intro A HL HR hHairs V hVopen hArcV K hKclosed hKarc
      obtain ⟨p, q, B0, hp, hq, hpInside, hqInside, _hBavoid⟩ :=
        (A 0).exists_simple_inside_join_in_open_avoiding_closed
          (HL 0) (HR 0) (hHairs 0) (V 0) (hVopen 0) (hArcV 0)
          K hKclosed (hKarc 0)
      have hpq : p ≠ q := by
        intro hpq
        exact Set.disjoint_left.mp (hHairs 0) hq (hpq ▸ hp)
      let gamma : Path p q := B0.toPath hpq
      have hgammaInjective : Injective gamma := B0.toPath_injective hpq
      let B : SimpleBrokenLine J.inside p q :=
        (B0.carrierBrokenLine hpq).mono fun _ hx => hx.1
      have hBcarrier : B.data.segmentCarrier = range gamma := by
        exact B0.segmentCarrier_carrierBrokenLine hpq
      have hgammaControlled : range gamma ⊆ V 0 := by
        intro x hx
        exact (B0.range_toPath_subset hpq hx).2.1
      have hgammaAvoid : Disjoint (range gamma) K := by
        rw [Set.disjoint_left]
        intro x hxGamma hxK
        exact (B0.range_toPath_subset hpq hxGamma).2.2 hxK
      let K' : Set Plane := K ∪ range gamma
      have hK'closed : IsClosed K' :=
        hKclosed.union (isCompact_range gamma.continuous).isClosed
      have hK'arc : ∀ i : Fin N,
          Disjoint K' (A i.succ).curveArcPlane := by
        intro i
        rw [Set.disjoint_left]
        intro x hxK' hxArc
        rcases hxK' with hxK | hxB
        · exact Set.disjoint_left.mp (hKarc i.succ) hxK hxArc
        · exact (J.inside_subset_compl
            (B0.range_toPath_subset hpq hxB).1)
            ((A i.succ).curveArcPlane_subset_carrier J hxArc)
      obtain ⟨R⟩ := ih (fun i => A i.succ) (fun i => HL i.succ)
        (fun i => HR i.succ) (fun i => hHairs i.succ)
        (fun i => V i.succ) (fun i => hVopen i.succ)
        (fun i => hArcV i.succ)
        K' hK'closed hK'arc
      let rightPoint : Fin (N + 1) → Plane :=
        Fin.cases p R.rightPoint
      let leftPoint : Fin (N + 1) → Plane :=
        Fin.cases q R.leftPoint
      let endpoint_ne : ∀ i, rightPoint i ≠ leftPoint i :=
        Fin.cases hpq R.endpoint_ne
      let sourceAmbient : Fin (N + 1) → Set Plane :=
        Fin.cases (J.inside ∩ (V 0 ∩ Kᶜ)) R.sourceAmbient
      let sourceLine : ∀ i, SimpleBrokenLine (sourceAmbient i)
          (rightPoint i) (leftPoint i) :=
        Fin.cases B0 R.sourceLine
      let path : ∀ i, Path (rightPoint i) (leftPoint i) :=
        Fin.cases gamma R.path
      let carrierLine : ∀ i, SimpleBrokenLine J.inside
          (rightPoint i) (leftPoint i) :=
        Fin.cases B R.carrierLine
      refine ⟨{
        rightPoint := rightPoint
        leftPoint := leftPoint
        rightPoint_mem := ?_
        leftPoint_mem := ?_
        rightPoint_inside := ?_
        leftPoint_inside := ?_
        endpoint_ne := endpoint_ne
        sourceAmbient := sourceAmbient
        sourceLine := sourceLine
        path := path
        path_eq_sourceLine := ?_
        path_injective := ?_
        sourceAmbient_subset := ?_
        carrierLine := carrierLine
        segmentCarrier_carrierLine_eq_range := ?_
        controlled := ?_
        avoids := ?_
        pairwise_disjoint := ?_ }⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hp
        · exact R.rightPoint_mem j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hq
        · exact R.leftPoint_mem j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hpInside
        · exact R.rightPoint_inside j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hqInside
        · exact R.leftPoint_inside j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact R.path_eq_sourceLine j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hgammaInjective
        · exact R.path_injective j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro x hx
          exact ⟨hx.1, hx.2.1⟩
        · intro x hx
          exact R.sourceAmbient_subset _ hx
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hBcarrier
        · exact R.segmentCarrier_carrierLine_eq_range j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hgammaControlled
        · exact R.controlled j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hgammaAvoid
        · exact (R.avoids j).mono_right subset_union_left
      · intro i j hij
        by_cases hi : i = 0
        · subst i
          have hj : j ≠ 0 := fun hj => hij hj.symm
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj
          exact ((R.avoids j').mono_right subset_union_right).symm
        · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero hi
          by_cases hj : j = 0
          · subst j
            exact (R.avoids i').mono_right subset_union_right
          · obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj
            apply R.pairwise_disjoint
            intro hij'
            apply hij
            exact congrArg Fin.succ hij'

end JordanCircle

end Schoenflies
