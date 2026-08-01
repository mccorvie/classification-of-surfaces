import Schoenflies.HierarchicalCollarStages
import Schoenflies.SegmentChainWalk

/-!
# The ordered segments of one recursive collar band

For one parent crosscut, the Chapter 9 band route runs backwards along the
parent, out along its retained left hair to the later collar, forwards over
all descendant crosscuts, and back along the retained right hair.  This file
packages those straight segments as a finite labelled family in the order
needed by the common-arrangement cycle extraction.
-/

namespace Schoenflies

open Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}

namespace RecursiveInsideCollarStep.Later

variable (L : RecursiveInsideCollarStep.Later F hn)

/-- All descendants of `a` at the selected later collar level, transported
across the stored arithmetic equality of levels. -/
noncomputable def addresses (a : LevelAddress n) :
    List (LevelAddress L.next.level) :=
  (descendantAddresses a L.depth).map fun b =>
    _root_.cast (congrArg LevelAddress L.parentLevel_add_depth) b

theorem addresses_nonempty (a : LevelAddress n) :
    L.addresses a ≠ [] := by
  intro h
  apply descendantAddresses_nonempty a L.depth
  exact List.map_eq_nil_iff.mp h

theorem addresses_nodup (a : LevelAddress n) :
    (L.addresses a).Nodup := by
  unfold addresses
  apply (descendantAddresses_nodup a L.depth).map
  exact (Equiv.cast
    (congrArg LevelAddress L.parentLevel_add_depth)).injective

theorem addresses_isChain (a : LevelAddress n) :
    (L.addresses a).IsChain I.LevelAdjacent := by
  rw [addresses, List.isChain_map]
  apply (descendantAddresses_isChain I a L.depth).imp
  intro b c hbc
  unfold InitialAngularArcs.LevelAdjacent at hbc ⊢
  rw [I.levelArc_cast L.parentLevel_add_depth,
    I.levelArc_cast L.parentLevel_add_depth]
  exact hbc

@[simp] theorem addresses_head (a : LevelAddress n) :
    (L.addresses a).head (L.addresses_nonempty a) =
      L.leftmostAddress a := by
  unfold addresses leftmostAddress
  simp only [List.head_map, descendantAddresses_head]

@[simp] theorem addresses_getLast (a : LevelAddress n) :
    (L.addresses a).getLast (L.addresses_nonempty a) =
      L.rightmostAddress a := by
  unfold addresses rightmostAddress
  simp only [List.getLast_map, descendantAddresses_getLast]

/-- Labels for all source segments used by a single collar band. -/
abbrev BandSegmentAddress :=
  F.LevelEdgeAddress ⊕
    (Unit ⊕
      (L.next.family.forgetObstacle.LevelEdgeAddress ⊕ Unit))

namespace BandSegmentAddress

variable (a : LevelAddress n)

def parent (e : F.LevelEdgeAddress) : L.BandSegmentAddress :=
  Sum.inl e

def leftSide : L.BandSegmentAddress :=
  Sum.inr (Sum.inl ())

def child (e : L.next.family.forgetObstacle.LevelEdgeAddress) :
    L.BandSegmentAddress :=
  Sum.inr (Sum.inr (Sum.inl e))

def rightSide : L.BandSegmentAddress :=
  Sum.inr (Sum.inr (Sum.inr ()))

/-- Initial endpoint of an oriented band segment. -/
noncomputable def left : L.BandSegmentAddress → Plane
  | .inl e => F.edgeFinish e
  | .inr (.inl ()) => F.leftSynchronizedPoint a
  | .inr (.inr (.inl e)) => L.next.family.forgetObstacle.edgeStart e
  | .inr (.inr (.inr ())) =>
      L.next.family.forgetObstacle.rightSynchronizedPoint
        (L.rightmostAddress a)

/-- Final endpoint of an oriented band segment. -/
noncomputable def right : L.BandSegmentAddress → Plane
  | .inl e => F.edgeStart e
  | .inr (.inl ()) =>
      L.next.family.forgetObstacle.leftSynchronizedPoint
        (L.leftmostAddress a)
  | .inr (.inr (.inl e)) => L.next.family.forgetObstacle.edgeFinish e
  | .inr (.inr (.inr ())) => F.rightSynchronizedPoint a

def Adjacent (x y : L.BandSegmentAddress) : Prop :=
  right L a x = left L a y

end BandSegmentAddress

/-- Parent crosscut edges, with both list order and edge orientation
reversed. -/
noncomputable def parentSegments (a : LevelAddress n) :
    List L.BandSegmentAddress :=
  (F.edgeBlock a).reverse.map (BandSegmentAddress.parent L)

/-- All later descendant crosscut edges in forward boundary order. -/
noncomputable def childSegments (a : LevelAddress n) :
    List L.BandSegmentAddress :=
  ((L.addresses a).flatMap
    L.next.family.forgetObstacle.edgeBlock).map
      (BandSegmentAddress.child L)

/-- The complete closed band route. -/
noncomputable def bandSegments (a : LevelAddress n) :
    List L.BandSegmentAddress :=
  L.parentSegments a ++
    [BandSegmentAddress.leftSide L] ++
    L.childSegments a ++
    [BandSegmentAddress.rightSide L]

theorem parentSegments_nonempty (a : LevelAddress n) :
    L.parentSegments a ≠ [] := by
  intro h
  have hrev : (F.edgeBlock a).reverse = [] :=
    List.map_eq_nil_iff.mp h
  exact F.edgeBlock_nonempty a (List.reverse_eq_nil_iff.mp hrev)

theorem childSegments_nonempty (a : LevelAddress n) :
    L.childSegments a ≠ [] := by
  intro hmap
  have hflat : (L.addresses a).flatMap
      L.next.family.forgetObstacle.edgeBlock = [] :=
    List.map_eq_nil_iff.mp hmap
  cases haddr : L.addresses a with
  | nil => exact (L.addresses_nonempty a haddr).elim
  | cons b l =>
      exact L.next.family.forgetObstacle.flatMap_edgeBlock_cons_nonempty b l
        (by simpa [haddr] using hflat)

theorem bandSegments_nonempty (a : LevelAddress n) :
    L.bandSegments a ≠ [] := by
  rw [bandSegments]
  intro h
  have h₁ := (List.append_eq_nil_iff.mp h).1
  have h₂ := (List.append_eq_nil_iff.mp h₁).1
  have h₃ := (List.append_eq_nil_iff.mp h₂).1
  exact L.parentSegments_nonempty a h₃

theorem right_parent_first (a : LevelAddress n) :
    BandSegmentAddress.right L a
      (BandSegmentAddress.parent L ⟨a, F.firstEdgeIndex a⟩) =
        F.leftSynchronizedPoint a :=
  F.edgeStart_first a

theorem left_parent_last (a : LevelAddress n) :
    BandSegmentAddress.left L a
      (BandSegmentAddress.parent L ⟨a, F.lastEdgeIndex a⟩) =
        F.rightSynchronizedPoint a :=
  F.edgeFinish_last a

theorem childSegments_start (a : LevelAddress n) :
    BandSegmentAddress.left L a
      (BandSegmentAddress.child L ⟨L.leftmostAddress a,
        L.next.family.forgetObstacle.firstEdgeIndex
          (L.leftmostAddress a)⟩) =
      L.next.family.forgetObstacle.leftSynchronizedPoint
        (L.leftmostAddress a) :=
  L.next.family.forgetObstacle.edgeStart_first _

theorem childSegments_finish (a : LevelAddress n) :
    BandSegmentAddress.right L a
      (BandSegmentAddress.child L ⟨L.rightmostAddress a,
        L.next.family.forgetObstacle.lastEdgeIndex
          (L.rightmostAddress a)⟩) =
      L.next.family.forgetObstacle.rightSynchronizedPoint
        (L.rightmostAddress a) :=
  L.next.family.forgetObstacle.edgeFinish_last _

theorem parentSegments_isChain (a : LevelAddress n) :
    (L.parentSegments a).IsChain
      (BandSegmentAddress.Adjacent L a) := by
  rw [parentSegments, List.isChain_map, List.isChain_reverse]
  exact (F.edgeBlock_isChain a).imp fun _ _ h => h.symm

theorem childSegments_isChain (a : LevelAddress n) :
    (L.childSegments a).IsChain
      (BandSegmentAddress.Adjacent L a) := by
  rw [childSegments, List.isChain_map]
  exact (L.next.family.forgetObstacle.flatMap_edgeBlock_isChain
    (L.addresses a) (L.addresses_isChain a)).imp fun _ _ h => h

theorem head_parentSegments (a : LevelAddress n) :
    (L.parentSegments a).head (L.parentSegments_nonempty a) =
      BandSegmentAddress.parent L
        ⟨a, F.lastEdgeIndex a⟩ := by
  unfold parentSegments
  rw [List.head_map, List.head_reverse, F.getLast_edgeBlock]

theorem getLast_parentSegments (a : LevelAddress n) :
    (L.parentSegments a).getLast (L.parentSegments_nonempty a) =
      BandSegmentAddress.parent L
        ⟨a, F.firstEdgeIndex a⟩ := by
  unfold parentSegments
  rw [List.getLast_map, List.getLast_reverse, F.head_edgeBlock]

theorem head_childSegments (a : LevelAddress n) :
    (L.childSegments a).head (L.childSegments_nonempty a) =
      BandSegmentAddress.child L
        ⟨L.leftmostAddress a,
          L.next.family.forgetObstacle.firstEdgeIndex
            (L.leftmostAddress a)⟩ := by
  apply Option.some.inj
  rw [← List.head?_eq_some_head (L.childSegments_nonempty a)]
  unfold childSegments
  rw [List.head?_map,
    L.next.family.forgetObstacle.head?_flatMap_edgeBlock_of_nonempty
      (L.addresses a) (L.addresses_nonempty a)]
  exact congrArg (fun b => some (BandSegmentAddress.child L
    ⟨b, L.next.family.forgetObstacle.firstEdgeIndex b⟩))
      (L.addresses_head a)

theorem getLast_childSegments (a : LevelAddress n) :
    (L.childSegments a).getLast (L.childSegments_nonempty a) =
      BandSegmentAddress.child L
        ⟨L.rightmostAddress a,
          L.next.family.forgetObstacle.lastEdgeIndex
            (L.rightmostAddress a)⟩ := by
  apply Option.some.inj
  rw [← List.getLast?_eq_getLast_of_ne_nil (L.childSegments_nonempty a)]
  unfold childSegments
  rw [List.getLast?_map,
    L.next.family.forgetObstacle.getLast?_flatMap_edgeBlock_of_nonempty
      (L.addresses a) (L.addresses_nonempty a)]
  exact congrArg (fun b => some (BandSegmentAddress.child L
    ⟨b, L.next.family.forgetObstacle.lastEdgeIndex b⟩))
      (L.addresses_getLast a)

theorem parentSegments_nodup (a : LevelAddress n) :
    (L.parentSegments a).Nodup := by
  unfold parentSegments
  have hrev : (F.edgeBlock a).reverse.Nodup :=
    List.nodup_reverse.mpr (F.edgeBlock_nodup a)
  exact hrev.map fun _ _ h => Sum.inl.inj h

theorem childSegments_nodup (a : LevelAddress n) :
    (L.childSegments a).Nodup := by
  unfold childSegments
  have hflat : ((L.addresses a).flatMap
      L.next.family.forgetObstacle.edgeBlock).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro b _hb
      exact L.next.family.forgetObstacle.edgeBlock_nodup b
    · apply (L.addresses_nodup a).imp
      intro b c hbc
      change List.Disjoint
        (L.next.family.forgetObstacle.edgeBlock b)
        (L.next.family.forgetObstacle.edgeBlock c)
      rw [List.disjoint_iff_ne]
      intro x hx y hy hxy
      rw [LevelAvoidingJoinFamily.edgeBlock, List.mem_ofFn'] at hx hy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      exact hbc (congrArg Sigma.fst hxy)
  exact hflat.map fun _ _ h =>
    Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))

theorem exists_parent_of_mem_parentSegments {a : LevelAddress n}
    {x : L.BandSegmentAddress} (hx : x ∈ L.parentSegments a) :
    ∃ e : F.LevelEdgeAddress,
      x = BandSegmentAddress.parent L e := by
  rw [parentSegments, List.mem_map] at hx
  rcases hx with ⟨e, _he, rfl⟩
  exact ⟨e, rfl⟩

theorem exists_child_of_mem_childSegments {a : LevelAddress n}
    {x : L.BandSegmentAddress} (hx : x ∈ L.childSegments a) :
    ∃ e : L.next.family.forgetObstacle.LevelEdgeAddress,
      x = BandSegmentAddress.child L e := by
  rw [childSegments, List.mem_map] at hx
  rcases hx with ⟨e, _he, rfl⟩
  exact ⟨e, rfl⟩

theorem bandSegments_nodup (a : LevelAddress n) :
    (L.bandSegments a).Nodup := by
  classical
  rw [bandSegments]
  have hparentLeft : (L.parentSegments a ++
      [BandSegmentAddress.leftSide L]).Nodup :=
    (L.parentSegments_nodup a).append (List.nodup_singleton _) (by
      rw [List.disjoint_iff_ne]
      intro x hx y hy hxy
      obtain ⟨e, rfl⟩ := L.exists_parent_of_mem_parentSegments hx
      have hy' : y = BandSegmentAddress.leftSide L := by
        simpa only [List.mem_singleton] using hy
      rw [hy'] at hxy
      cases hxy)
  have hparentLeftChild : (L.parentSegments a ++
      [BandSegmentAddress.leftSide L] ++ L.childSegments a).Nodup :=
    hparentLeft.append (L.childSegments_nodup a) (by
      rw [List.disjoint_iff_ne]
      intro x hx y hy hxy
      obtain ⟨e, rfl⟩ := L.exists_child_of_mem_childSegments hy
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨f, rfl⟩ := L.exists_parent_of_mem_parentSegments hx
        cases hxy
      · have hx' : x = BandSegmentAddress.leftSide L := by
          simpa only [List.mem_singleton] using hx
        rw [hx'] at hxy
        cases hxy)
  exact hparentLeftChild.append (List.nodup_singleton _) (by
    rw [List.disjoint_iff_ne]
    intro x hx y hy hxy
    have hy' : y = BandSegmentAddress.rightSide L := by
      simpa only [List.mem_singleton] using hy
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨e, rfl⟩ := L.exists_parent_of_mem_parentSegments hx
        rw [hy'] at hxy
        cases hxy
      · have hx' : x = BandSegmentAddress.leftSide L := by
          simpa only [List.mem_singleton] using hx
        rw [hx', hy'] at hxy
        cases hxy
    · obtain ⟨e, rfl⟩ := L.exists_child_of_mem_childSegments hx
      rw [hy'] at hxy
      cases hxy)

theorem parentSegments_append_leftSide_isChain
    (a : LevelAddress n) :
    (L.parentSegments a ++ [BandSegmentAddress.leftSide L]).IsChain
      (BandSegmentAddress.Adjacent L a) := by
  apply (L.parentSegments_isChain a).append (by simp)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  rw [L.getLast_parentSegments a] at hx'
  have hy' := List.head_of_mem_head? hy
  change BandSegmentAddress.leftSide L = y at hy'
  subst x
  subst y
  exact L.right_parent_first a

theorem parentLeftChild_isChain (a : LevelAddress n) :
    (L.parentSegments a ++ [BandSegmentAddress.leftSide L] ++
      L.childSegments a).IsChain
        (BandSegmentAddress.Adjacent L a) := by
  apply (L.parentSegments_append_leftSide_isChain a).append
    (L.childSegments_isChain a)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  have hxlast : (L.parentSegments a ++
      [BandSegmentAddress.leftSide L]).getLast (by simp) =
        BandSegmentAddress.leftSide L := by simp
  rw [hxlast] at hx'
  have hy' := List.head_of_mem_head? hy
  rw [L.head_childSegments a] at hy'
  subst x
  subst y
  exact (L.childSegments_start a).symm

theorem bandSegments_isChain (a : LevelAddress n) :
    (L.bandSegments a).IsChain
      (BandSegmentAddress.Adjacent L a) := by
  rw [bandSegments]
  apply (L.parentLeftChild_isChain a).append (by simp)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  have hxlast : (L.parentSegments a ++
      [BandSegmentAddress.leftSide L] ++
      L.childSegments a).getLast (by simp) =
          (L.childSegments a).getLast
            (L.childSegments_nonempty a) := by
    simp [L.childSegments_nonempty a]
  rw [hxlast, L.getLast_childSegments a] at hx'
  have hy' := List.head_of_mem_head? hy
  change BandSegmentAddress.rightSide L = y at hy'
  subst x
  subst y
  exact L.childSegments_finish a

theorem bandSegments_closes (a : LevelAddress n) :
    BandSegmentAddress.Adjacent L a
      ((L.bandSegments a).getLast (L.bandSegments_nonempty a))
      ((L.bandSegments a).head (L.bandSegments_nonempty a)) := by
  have hlast : (L.bandSegments a).getLast
      (L.bandSegments_nonempty a) =
        BandSegmentAddress.rightSide L := by
    simp [bandSegments]
  have hhead : (L.bandSegments a).head
      (L.bandSegments_nonempty a) =
        BandSegmentAddress.parent L
          ⟨a, F.lastEdgeIndex a⟩ := by
    apply Option.some.inj
    rw [← List.head?_eq_some_head (L.bandSegments_nonempty a)]
    calc
      (L.bandSegments a).head? = (L.parentSegments a).head? := by
        unfold bandSegments
        rw [List.head?_append_of_ne_nil _ (by
              simp [L.parentSegments_nonempty a]),
          List.head?_append_of_ne_nil _ (by
              simp [L.parentSegments_nonempty a]),
          List.head?_append_of_ne_nil _
            (L.parentSegments_nonempty a)]
      _ = some (BandSegmentAddress.parent L
          ⟨a, F.lastEdgeIndex a⟩) := by
        rw [List.head?_eq_some_head (L.parentSegments_nonempty a),
          L.head_parentSegments a]
  rw [hlast, hhead]
  exact (L.left_parent_last a).symm

/-- Canonical first label of the nonempty band route. -/
noncomputable def bandFirst (a : LevelAddress n) :
    L.BandSegmentAddress :=
  (L.bandSegments a).head (L.bandSegments_nonempty a)

/-- Remaining labels of the canonical band route. -/
noncomputable def bandTail (a : LevelAddress n) :
    List L.BandSegmentAddress :=
  (L.bandSegments a).tail

theorem bandFirst_cons_bandTail (a : LevelAddress n) :
    L.bandFirst a :: L.bandTail a = L.bandSegments a := by
  exact List.cons_head_tail (L.bandSegments_nonempty a)

theorem bandRoute_isChain (a : LevelAddress n) :
    (L.bandFirst a :: L.bandTail a).IsChain
      (BandSegmentAddress.Adjacent L a) := by
  rw [L.bandFirst_cons_bandTail a]
  exact L.bandSegments_isChain a

theorem bandRoute_nodup (a : LevelAddress n) :
    (L.bandFirst a :: L.bandTail a).Nodup := by
  rw [L.bandFirst_cons_bandTail a]
  exact L.bandSegments_nodup a

theorem bandRoute_closes (a : LevelAddress n) :
    BandSegmentAddress.right L a
        ((L.bandFirst a :: L.bandTail a).getLast (by simp)) =
      BandSegmentAddress.left L a (L.bandFirst a) := by
  have hlist := L.bandFirst_cons_bandTail a
  have hlast : (L.bandFirst a :: L.bandTail a).getLast (by simp) =
      (L.bandSegments a).getLast (L.bandSegments_nonempty a) := by
    apply List.getLast_congr
    exact hlist
  rw [hlast]
  change BandSegmentAddress.right L a
      ((L.bandSegments a).getLast (L.bandSegments_nonempty a)) =
    BandSegmentAddress.left L a (L.bandFirst a)
  change _ = BandSegmentAddress.left L a
    ((L.bandSegments a).head (L.bandSegments_nonempty a))
  exact L.bandSegments_closes a

/-- The closed common-arrangement walk carried by one collar band. -/
noncomputable def bandClosedWalk (a : LevelAddress n) :=
  BrokenLineData.segmentFamilyClosedWalk
    (BandSegmentAddress.left L a)
    (BandSegmentAddress.right L a)
    (L.bandFirst a) (L.bandTail a)
    (L.bandRoute_isChain a) (L.bandRoute_closes a)

end RecursiveInsideCollarStep.Later

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
