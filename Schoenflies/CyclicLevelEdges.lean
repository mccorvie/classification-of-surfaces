import Schoenflies.SynchronizedLevelReturns
import Schoenflies.ResolvedPolygonalArcs
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.NodupEquivFin

/-!
# The ordered finite edge set of a synchronized collar

Each synchronized crosscut is resolved into finitely many straight edges.
This file orders all those edges first along a crosscut and then around the
complete boundary level.  The result is the indexing object from which the
inner `PolygonalCircle` is constructed.
-/

namespace Schoenflies

open Set Function

namespace JordanCircle
namespace InitialAngularArcs
namespace LevelAvoidingJoinFamily

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  (F : I.LevelAvoidingJoinFamily n epsilon)

/-- Resolve once more so that the listed segment carrier is literally the
range of the synchronized crosscut path. -/
noncomputable def synchronizedCrosscutCarrierLine (a : LevelAddress n) :
    SimpleBrokenLine (F.synchronizedCrosscutSet a)
      (F.leftSynchronizedPoint a) (F.rightSynchronizedPoint a) :=
  (F.synchronizedCrosscutLine a).carrierBrokenLine
    (F.leftSynchronizedPoint_ne_rightSynchronizedPoint a)

theorem synchronizedCrosscutCarrierLine_edgeCount_pos
    (a : LevelAddress n) :
    0 < (F.synchronizedCrosscutCarrierLine a).data.n := by
  apply JordanCircle.BrokenLineData.n_pos_of_start_ne_finish
  intro h
  exact F.leftSynchronizedPoint_ne_rightSynchronizedPoint a
    ((F.synchronizedCrosscutCarrierLine a).start_eq.symm.trans
      (h.trans (F.synchronizedCrosscutCarrierLine a).finish_eq))

/-- An edge is addressed by its boundary arc and its linear edge number
inside that resolved crosscut. -/
abbrev LevelEdgeAddress :=
  Σ a : LevelAddress n,
    Fin (F.synchronizedCrosscutCarrierLine a).data.n

noncomputable def edgeStart (e : F.LevelEdgeAddress) : Plane :=
  (F.synchronizedCrosscutCarrierLine e.1).data.vertex e.2.castSucc

noncomputable def edgeFinish (e : F.LevelEdgeAddress) : Plane :=
  (F.synchronizedCrosscutCarrierLine e.1).data.vertex e.2.succ

noncomputable def edgeSegment (e : F.LevelEdgeAddress) : Set Plane :=
  segment ℝ (F.edgeStart e) (F.edgeFinish e)

def EdgeAdjacent (e f : F.LevelEdgeAddress) : Prop :=
  F.edgeFinish e = F.edgeStart f

/-- The edges of one crosscut in their linear order. -/
noncomputable def edgeBlock (a : LevelAddress n) :
    List F.LevelEdgeAddress :=
  List.ofFn fun i => ⟨a, i⟩

theorem edgeBlock_nonempty (a : LevelAddress n) :
    F.edgeBlock a ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, edgeBlock, List.length_ofFn]
  exact F.synchronizedCrosscutCarrierLine_edgeCount_pos a

theorem edgeBlock_nodup (a : LevelAddress n) :
    (F.edgeBlock a).Nodup := by
  rw [edgeBlock, List.nodup_ofFn]
  intro i j h
  cases h
  rfl

theorem edgeBlock_isChain (a : LevelAddress n) :
    (F.edgeBlock a).IsChain F.EdgeAdjacent := by
  rw [edgeBlock, List.isChain_ofFn]
  intro i hi
  apply congrArg (F.synchronizedCrosscutCarrierLine a).data.vertex
  apply Fin.ext
  rfl

/-- The first edge index in a nonempty crosscut block. -/
noncomputable def firstEdgeIndex (a : LevelAddress n) :
    Fin (F.synchronizedCrosscutCarrierLine a).data.n :=
  ⟨0, F.synchronizedCrosscutCarrierLine_edgeCount_pos a⟩

/-- The last edge index in a nonempty crosscut block. -/
noncomputable def lastEdgeIndex (a : LevelAddress n) :
    Fin (F.synchronizedCrosscutCarrierLine a).data.n :=
  ⟨(F.synchronizedCrosscutCarrierLine a).data.n - 1,
    Nat.sub_lt (F.synchronizedCrosscutCarrierLine_edgeCount_pos a)
      (by omega)⟩

theorem edgeStart_first (a : LevelAddress n) :
    F.edgeStart ⟨a, F.firstEdgeIndex a⟩ =
      F.leftSynchronizedPoint a := by
  change (F.synchronizedCrosscutCarrierLine a).data.vertex
      (F.firstEdgeIndex a).castSucc = _
  calc
    _ = (F.synchronizedCrosscutCarrierLine a).data.start := by
      apply congrArg (F.synchronizedCrosscutCarrierLine a).data.vertex
      apply Fin.ext
      rfl
    _ = F.leftSynchronizedPoint a :=
      (F.synchronizedCrosscutCarrierLine a).start_eq

theorem edgeFinish_last (a : LevelAddress n) :
    F.edgeFinish ⟨a, F.lastEdgeIndex a⟩ =
      F.rightSynchronizedPoint a := by
  change (F.synchronizedCrosscutCarrierLine a).data.vertex
      (F.lastEdgeIndex a).succ = _
  calc
    _ = (F.synchronizedCrosscutCarrierLine a).data.finish := by
      apply congrArg (F.synchronizedCrosscutCarrierLine a).data.vertex
      apply Fin.ext
      simp [lastEdgeIndex]
      exact Nat.sub_add_cancel
        (F.synchronizedCrosscutCarrierLine_edgeCount_pos a)
    _ = F.rightSynchronizedPoint a :=
      (F.synchronizedCrosscutCarrierLine a).finish_eq

theorem edgeBlock_bridge {a b : LevelAddress n}
    (hab : I.LevelAdjacent a b) :
    F.EdgeAdjacent ⟨a, F.lastEdgeIndex a⟩
      ⟨b, F.firstEdgeIndex b⟩ := by
  have hb : b = nextLevelAddress n a :=
    (I.levelRightPoint_eq_levelLeftPoint_iff a b).mp hab
  subst b
  rw [EdgeAdjacent, F.edgeFinish_last, F.edgeStart_first]
  exact F.rightSynchronizedPoint_next_eq_leftSynchronizedPoint a

/-- All resolved edges at the level, in positive cyclic order. -/
noncomputable def orderedLevelEdges : List F.LevelEdgeAddress :=
  (orderedLevelAddresses n).flatMap F.edgeBlock

theorem mem_orderedLevelEdges (e : F.LevelEdgeAddress) :
    e ∈ F.orderedLevelEdges := by
  rw [orderedLevelEdges, List.mem_flatMap]
  refine ⟨e.1, mem_orderedLevelAddresses n e.1, ?_⟩
  simp [edgeBlock]

theorem orderedLevelEdges_nodup : F.orderedLevelEdges.Nodup := by
  rw [orderedLevelEdges, List.nodup_flatMap]
  constructor
  · intro a _ha
    exact F.edgeBlock_nodup a
  · apply (orderedLevelAddresses_nodup n).imp
    intro a b hab
    change List.Disjoint (F.edgeBlock a) (F.edgeBlock b)
    rw [List.disjoint_iff_ne]
    intro x hx y hy hxy
    rw [edgeBlock, List.mem_ofFn'] at hx hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    exact hab (congrArg Sigma.fst hxy)

theorem length_le_length_flatMap_edgeBlock
    (l : List (LevelAddress n)) :
    l.length ≤ (l.flatMap F.edgeBlock).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.flatMap_cons, List.length_cons, List.length_append]
      have hpos : 0 < (F.edgeBlock a).length := by
        rw [List.length_pos_iff_ne_nil]
        exact F.edgeBlock_nonempty a
      omega

theorem orderedLevelEdges_three_le (hn : 1 ≤ n) :
    3 ≤ F.orderedLevelEdges.length := by
  have hle := F.length_le_length_flatMap_edgeBlock
    (orderedLevelAddresses n)
  rw [← orderedLevelEdges, orderedLevelAddresses_length] at hle
  have hpow : 4 ≤ 2 ^ (n + 1) := by
    calc
      4 = 2 ^ (1 + 1) := by norm_num
      _ ≤ 2 ^ (n + 1) :=
        pow_le_pow_right' (by norm_num) (by omega)
  omega

end LevelAvoidingJoinFamily
end InitialAngularArcs
end JordanCircle

end Schoenflies
