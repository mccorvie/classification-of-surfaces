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

/-- Different parent cells use disjoint transported descendant blocks. -/
theorem addresses_disjoint_of_ne {a b : LevelAddress n} (hab : a ≠ b) :
    List.Disjoint (L.addresses a) (L.addresses b) := by
  rw [List.disjoint_left]
  intro c hca hcb
  rw [addresses, List.mem_map] at hca hcb
  obtain ⟨ca, hcaMem, hcaEq⟩ := hca
  obtain ⟨cb, hcbMem, hcbEq⟩ := hcb
  have hcast :
      (_root_.cast (congrArg LevelAddress L.parentLevel_add_depth) ca :
          LevelAddress L.next.level) =
        _root_.cast (congrArg LevelAddress L.parentLevel_add_depth) cb := by
    exact hcaEq.trans hcbEq.symm
  have hcab : ca = cb :=
    (Equiv.cast
      (congrArg LevelAddress L.parentLevel_add_depth)).injective hcast
  subst cb
  exact List.disjoint_left.mp
    (descendantAddresses_disjoint_of_ne hab) hcaMem hcbMem

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

theorem leftmostAddress_mem_addresses (a : LevelAddress n) :
    L.leftmostAddress a ∈ L.addresses a := by
  have h := List.head_mem (L.addresses_nonempty a)
  rwa [L.addresses_head a] at h

theorem rightmostAddress_mem_addresses (a : LevelAddress n) :
    L.rightmostAddress a ∈ L.addresses a := by
  have h := List.getLast_mem (L.addresses_nonempty a)
  rwa [L.addresses_getLast a] at h

/-- The last descendant of one parent block is followed cyclically by the
first descendant of the next parent block. -/
theorem nextLevelAddress_rightmostAddress (a : LevelAddress n) :
    nextLevelAddress L.next.level (L.rightmostAddress a) =
      L.leftmostAddress (nextLevelAddress n a) := by
  symm
  apply (I.levelRightPoint_eq_levelLeftPoint_iff
    (L.rightmostAddress a)
    (L.leftmostAddress (nextLevelAddress n a))).mp
  calc
    (J.curvePoint (I.levelArc (L.rightmostAddress a)).right : Plane) =
        (J.curvePoint (I.levelArc a).right : Plane) := by
      rw [L.levelArc_rightmostAddress_right a]
    _ = (J.curvePoint
          (I.levelArc (nextLevelAddress n a)).left : Plane) :=
      I.levelAdjacent_nextLevelAddress n a
    _ = (J.curvePoint
          (I.levelArc (L.leftmostAddress
            (nextLevelAddress n a))).left : Plane) := by
      rw [L.levelArc_leftmostAddress_left]

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

theorem parentEdge_inter_parentEdge_subsingleton
    (hlevel : 1 ≤ n) (e f : F.LevelEdgeAddress) (hef : e ≠ f) :
    (F.edgeSegment e ∩ F.edgeSegment f).Subsingleton := by
  by_cases hfnext : f = F.nextLevelEdge e
  · rw [hfnext, F.edgeSegment_inter_next hlevel e]
    exact Set.subsingleton_singleton
  by_cases henext : e = F.nextLevelEdge f
  · rw [Set.inter_comm, henext, F.edgeSegment_inter_next hlevel f]
    exact Set.subsingleton_singleton
  have hdis := F.disjoint_edgeSegment_of_nonadjacent hlevel e f
    hef henext hfnext
  rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
  exact Set.subsingleton_empty

theorem parentEdge_disjoint_childEdge
    (e : F.LevelEdgeAddress)
    (f : L.next.family.forgetObstacle.LevelEdgeAddress) :
    Disjoint (F.edgeSegment e)
      (L.next.family.forgetObstacle.edgeSegment f) := by
  apply L.next.carrier_disjoint.mono
  · intro x hx
    rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
    apply Or.inr
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr
      ⟨e.1, F.edgeSegment_subset_crosscutRange e hx⟩
  · rw [L.next.family.forgetObstacle.carrier_synchronizedPolygonalCircle
      L.next.one_le_level]
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨f.1, L.next.family.forgetObstacle.edgeSegment_subset_crosscutRange f hx⟩

theorem leftSide_subset_parentBaseSegment (a : LevelAddress n) :
    segment ℝ (F.leftSynchronizedPoint a)
        (L.next.family.forgetObstacle.leftSynchronizedPoint
          (L.leftmostAddress a)) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
        (F.leftSynchronizedPoint a) := by
  let H := I.levelLeftHair a
  let child : H.carrier :=
    ⟨L.next.family.forgetObstacle.leftSynchronizedPoint
        (L.leftmostAddress a), by
      rw [← L.leftmostAddress_leftHair_carrier a]
      exact L.next.family.forgetObstacle
        |>.leftSynchronizedPoint_mem_leftHair _⟩
  let parent : H.carrier :=
    ⟨F.leftSynchronizedPoint a,
      F.leftSynchronizedPoint_mem_leftHair a⟩
  have hparameter : H.carrierParameter child ≤
      H.carrierParameter parent :=
    (L.leftmost_carrierParameter_lt_parent a).le
  have hbase : segment ℝ
      (J.curvePoint (I.levelArc a).left : Plane) (child : Plane) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
        (parent : Plane) :=
    H.baseSegment_subset_of_parameter_le child parent hparameter
  have hchild : (child : Plane) ∈
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
        (parent : Plane) :=
    hbase (right_mem_segment ℝ _ _)
  have hsegment : segment ℝ (parent : Plane) (child : Plane) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
        (parent : Plane) :=
    (convex_segment _ _).segment_subset
      (right_mem_segment ℝ _ _) hchild
  simpa [H, child, parent] using hsegment

theorem rightSide_subset_parentBaseSegment (a : LevelAddress n) :
    segment ℝ
        (L.next.family.forgetObstacle.rightSynchronizedPoint
          (L.rightmostAddress a))
        (F.rightSynchronizedPoint a) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a) := by
  let H := I.levelRightHair a
  let child : H.carrier :=
    ⟨L.next.family.forgetObstacle.rightSynchronizedPoint
        (L.rightmostAddress a), by
      rw [← L.rightmostAddress_rightHair_carrier a]
      exact L.next.family.forgetObstacle
        |>.rightSynchronizedPoint_mem_rightHair _⟩
  let parent : H.carrier :=
    ⟨F.rightSynchronizedPoint a,
      F.rightSynchronizedPoint_mem_rightHair a⟩
  have hparameter : H.carrierParameter child ≤
      H.carrierParameter parent :=
    (L.rightmost_carrierParameter_lt_parent a).le
  have hbase : segment ℝ
      (J.curvePoint (I.levelArc a).right : Plane) (child : Plane) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
        (parent : Plane) :=
    H.baseSegment_subset_of_parameter_le child parent hparameter
  have hchild : (child : Plane) ∈
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
        (parent : Plane) :=
    hbase (right_mem_segment ℝ _ _)
  have hsegment : segment ℝ (child : Plane) (parent : Plane) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
        (parent : Plane) :=
    (convex_segment _ _).segment_subset hchild
      (right_mem_segment ℝ _ _)
  simpa [H, child, parent] using hsegment

theorem parentEdge_inter_leftSide_subsingleton
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    (F.edgeSegment ⟨a, i⟩ ∩
      segment ℝ (F.leftSynchronizedPoint a)
        (L.next.family.forgetObstacle.leftSynchronizedPoint
          (L.leftmostAddress a))).Subsingleton := by
  intro x hx y hy
  have hx' : x ∈
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
          (F.leftSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.leftSide_subset_parentBaseSegment a hx.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hx.1⟩
  have hy' : y ∈
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
          (F.leftSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.leftSide_subset_parentBaseSegment a hy.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hy.1⟩
  rw [F.leftBaseSegment_inter_range_synchronizedCrosscutPath a] at hx' hy'
  exact (mem_singleton_iff.mp hx').trans
    (mem_singleton_iff.mp hy').symm

theorem parentEdge_inter_rightSide_subsingleton
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    (F.edgeSegment ⟨a, i⟩ ∩
      segment ℝ
        (L.next.family.forgetObstacle.rightSynchronizedPoint
          (L.rightmostAddress a))
        (F.rightSynchronizedPoint a)).Subsingleton := by
  intro x hx y hy
  have hx' : x ∈
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
          (F.rightSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rightSide_subset_parentBaseSegment a hx.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hx.1⟩
  have hy' : y ∈
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
          (F.rightSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rightSide_subset_parentBaseSegment a hy.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hy.1⟩
  rw [F.rightBaseSegment_inter_range_synchronizedCrosscutPath a] at hx' hy'
  exact (mem_singleton_iff.mp hx').trans
    (mem_singleton_iff.mp hy').symm

theorem parentSegment_inter_bandSegment_subsingleton
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n)
    (j : L.BandSegmentAddress)
    (hji : j ≠ BandSegmentAddress.parent L ⟨a, i⟩) :
    (segment ℝ
        (BandSegmentAddress.left L a
          (BandSegmentAddress.parent L ⟨a, i⟩))
        (BandSegmentAddress.right L a
          (BandSegmentAddress.parent L ⟨a, i⟩)) ∩
      segment ℝ (BandSegmentAddress.left L a j)
        (BandSegmentAddress.right L a j)).Subsingleton := by
  rcases j with f | j
  · have hef : (⟨a, i⟩ : F.LevelEdgeAddress) ≠ f := by
      intro h
      apply hji
      subst f
      rfl
    simpa [BandSegmentAddress.parent, BandSegmentAddress.left,
      BandSegmentAddress.right,
      LevelAvoidingJoinFamily.edgeSegment, segment_symm] using
        parentEdge_inter_parentEdge_subsingleton hn
          (⟨a, i⟩ : F.LevelEdgeAddress) f hef
  · rcases j with _ | j
    · simpa [BandSegmentAddress.parent, BandSegmentAddress.leftSide,
        BandSegmentAddress.left, BandSegmentAddress.right,
        LevelAvoidingJoinFamily.edgeSegment, segment_symm] using
          L.parentEdge_inter_leftSide_subsingleton a i
    · rcases j with f | _
      · have hdis := L.parentEdge_disjoint_childEdge
          (⟨a, i⟩ : F.LevelEdgeAddress) f
        have hsub : (F.edgeSegment ⟨a, i⟩ ∩
            L.next.family.forgetObstacle.edgeSegment f).Subsingleton := by
          rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
          exact Set.subsingleton_empty
        simpa [BandSegmentAddress.parent, BandSegmentAddress.child,
          BandSegmentAddress.left, BandSegmentAddress.right,
          LevelAvoidingJoinFamily.edgeSegment, segment_symm] using hsub
      · simpa [BandSegmentAddress.parent, BandSegmentAddress.rightSide,
          BandSegmentAddress.left, BandSegmentAddress.right,
          LevelAvoidingJoinFamily.edgeSegment, segment_symm] using
            L.parentEdge_inter_rightSide_subsingleton a i

theorem edgeStart_ne_edgeFinish (e : F.LevelEdgeAddress) :
    F.edgeStart e ≠ F.edgeFinish e := by
  intro h
  have hv := (F.synchronizedCrosscutCarrierLine e.1).vertex_injective h
  have hval := congrArg Fin.val hv
  simp at hval

/-- Every source segment in a collar-band family is nondegenerate.  For the
two retained-hair sides this is exactly the strict shallowness built into a
recursive collar step. -/
theorem bandSegment_left_ne_right (a : LevelAddress n)
    (j : L.BandSegmentAddress) :
    BandSegmentAddress.left L a j ≠
      BandSegmentAddress.right L a j := by
  rcases j with e | j
  · simpa [BandSegmentAddress.left, BandSegmentAddress.right] using
      (edgeStart_ne_edgeFinish (F := F) e).symm
  · rcases j with u | j
    · cases u
      have hlt := L.next.dist_child_left_lt_parent_left F hn a
        (L.leftmostAddress a) (by
          simp [L.levelArc_leftmostAddress_left a])
      intro h
      change F.leftSynchronizedPoint a =
        L.next.family.forgetObstacle.leftSynchronizedPoint
          (L.leftmostAddress a) at h
      rw [← h] at hlt
      exact (lt_irrefl _ hlt)
    · rcases j with e | u
      · simpa [BandSegmentAddress.left, BandSegmentAddress.right] using
          (edgeStart_ne_edgeFinish
            (F := L.next.family.forgetObstacle) e)
      · cases u
        have hlt := L.next.dist_child_right_lt_parent_right F hn a
          (L.rightmostAddress a) (by
            simp [L.levelArc_rightmostAddress_right a])
        intro h
        change L.next.family.forgetObstacle.rightSynchronizedPoint
            (L.rightmostAddress a) = F.rightSynchronizedPoint a at h
        rw [h] at hlt
        exact (lt_irrefl _ hlt)

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

/-- A fixed old-collar edge whose odd occurrence certifies that the band
route does not cancel completely. -/
noncomputable def selectedParentEdge (a : LevelAddress n) :
    F.LevelEdgeAddress :=
  ⟨a, F.firstEdgeIndex a⟩

noncomputable def selectedParentSegment (a : LevelAddress n) :
    L.BandSegmentAddress :=
  BandSegmentAddress.parent L (selectedParentEdge (F := F) a)

theorem selectedParentSegment_mem_bandSegments (a : LevelAddress n) :
    L.selectedParentSegment a ∈ L.bandSegments a := by
  rw [bandSegments]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  unfold selectedParentSegment selectedParentEdge parentSegments
  rw [List.mem_map]
  refine ⟨(⟨a, F.firstEdgeIndex a⟩ : F.LevelEdgeAddress), ?_, rfl⟩
  rw [List.mem_reverse, LevelAvoidingJoinFamily.edgeBlock,
    List.mem_ofFn']
  exact ⟨F.firstEdgeIndex a, rfl⟩

theorem selectedParentSegment_mem_bandRoute (a : LevelAddress n) :
    L.selectedParentSegment a ∈ L.bandFirst a :: L.bandTail a := by
  rw [L.bandFirst_cons_bandTail a]
  exact L.selectedParentSegment_mem_bandSegments a

theorem selectedParentSegment_left_ne_right (a : LevelAddress n) :
    BandSegmentAddress.left L a (L.selectedParentSegment a) ≠
      BandSegmentAddress.right L a (L.selectedParentSegment a) := by
  simpa [selectedParentSegment, selectedParentEdge,
    BandSegmentAddress.parent, BandSegmentAddress.left,
    BandSegmentAddress.right] using
      (edgeStart_ne_edgeFinish (F := F)
        (selectedParentEdge (F := F) a)).symm

/-- The selected parent segment contributes an arrangement edge that is
absent from every other member of the collar-band route. -/
theorem exists_private_selectedParentSegmentEdge (a : LevelAddress n) :
    ∃ e : Sym2 (BrokenLineData.segmentFamilyComplex
        (BandSegmentAddress.left L a)
        (BandSegmentAddress.right L a)).Vertex,
      e ∈ (BrokenLineData.segmentFamilyPath
        (BandSegmentAddress.left L a)
        (BandSegmentAddress.right L a)
        (L.selectedParentSegment a) :
          (BrokenLineData.segmentFamilyComplex
            (BandSegmentAddress.left L a)
            (BandSegmentAddress.right L a)).vertexGraph.Walk
              (BrokenLineData.segmentFamilyLeftVertex
                (BandSegmentAddress.left L a)
                (BandSegmentAddress.right L a)
                (L.selectedParentSegment a))
              (BrokenLineData.segmentFamilyRightVertex
                (BandSegmentAddress.left L a)
                (BandSegmentAddress.right L a)
                (L.selectedParentSegment a))).edges ∧
      ∀ j ∈ L.bandFirst a :: L.bandTail a,
        j ≠ L.selectedParentSegment a →
        e ∉ (BrokenLineData.segmentFamilyPath
          (BandSegmentAddress.left L a)
          (BandSegmentAddress.right L a) j :
            (BrokenLineData.segmentFamilyComplex
              (BandSegmentAddress.left L a)
              (BandSegmentAddress.right L a)).vertexGraph.Walk
                (BrokenLineData.segmentFamilyLeftVertex
                  (BandSegmentAddress.left L a)
                  (BandSegmentAddress.right L a) j)
                (BrokenLineData.segmentFamilyRightVertex
                  (BandSegmentAddress.left L a)
                  (BandSegmentAddress.right L a) j)).edges := by
  let left := BandSegmentAddress.left L a
  let right := BandSegmentAddress.right L a
  let s := L.selectedParentSegment a
  let K := BrokenLineData.segmentFamilyComplex left right
  let p : K.vertexGraph.Walk
      (BrokenLineData.segmentFamilyLeftVertex left right s)
      (BrokenLineData.segmentFamilyRightVertex left right s) :=
    BrokenLineData.segmentFamilyPath left right s
  have hvne : BrokenLineData.segmentFamilyLeftVertex left right s ≠
      BrokenLineData.segmentFamilyRightVertex left right s := by
    intro h
    apply L.selectedParentSegment_left_ne_right a
    calc
      BandSegmentAddress.left L a (L.selectedParentSegment a) =
          K.position
            (BrokenLineData.segmentFamilyLeftVertex left right s) := by
        exact (BrokenLineData.segmentFamilyLeftVertex_position
          left right s).symm
      _ = K.position
          (BrokenLineData.segmentFamilyRightVertex left right s) :=
        congrArg K.position h
      _ = BandSegmentAddress.right L a
          (L.selectedParentSegment a) := by
        exact BrokenLineData.segmentFamilyRightVertex_position
          left right s
  have hnotnil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hvne
  have hedges : p.edges ≠ [] :=
    SimpleGraph.Walk.edges_eq_nil.not.mpr hnotnil
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hedges
  refine ⟨e, he, ?_⟩
  intro j _hj hjs
  apply BrokenLineData.segmentFamilyPath_edge_not_mem_of_inter_subsingleton
    left right s j ?_ e he
  change (segment ℝ
      (BandSegmentAddress.left L a (L.selectedParentSegment a))
      (BandSegmentAddress.right L a (L.selectedParentSegment a)) ∩
    segment ℝ (BandSegmentAddress.left L a j)
      (BandSegmentAddress.right L a j)).Subsingleton
  simpa [selectedParentSegment, selectedParentEdge] using
    L.parentSegment_inter_bandSegment_subsingleton a
      (F.firstEdgeIndex a) j hjs

/-- Every collar band contains a simple cycle in its common segment
arrangement.  This is the precise finite-graph form of Moise's phrase
"contains a polygonal cell." -/
theorem exists_bandCycle (a : LevelAddress n) :
    ∃ (z : (BrokenLineData.segmentFamilyComplex
          (BandSegmentAddress.left L a)
          (BandSegmentAddress.right L a)).Vertex)
        (c : (BrokenLineData.segmentFamilyComplex
          (BandSegmentAddress.left L a)
          (BandSegmentAddress.right L a)).vertexGraph.Walk z z),
      c.IsCycle ∧
        ∃ e, e ∈ c.edges ∧
          c.edges.toFinset ⊆
            (L.bandClosedWalk a).edges.toFinset := by
  obtain ⟨e, he, hprivate⟩ :=
    L.exists_private_selectedParentSegmentEdge a
  obtain ⟨z, c, hc, hec, hsubset⟩ :=
    BrokenLineData.exists_isCycle_containing_of_private_segmentEdge
      (BandSegmentAddress.left L a)
      (BandSegmentAddress.right L a)
      (L.bandFirst a) (L.bandTail a)
      (L.bandRoute_isChain a) (L.bandRoute_closes a)
      (L.bandRoute_nodup a)
      (L.selectedParentSegment a)
      (L.selectedParentSegment_mem_bandRoute a)
      e he hprivate
  exact ⟨z, c, hc, e, hec, hsubset⟩

/-- Point-set union of the straight segments in one collar-band route. -/
noncomputable def bandCarrier (a : LevelAddress n) : Set Plane :=
  ⋃ j ∈ L.bandSegments a,
    segment ℝ (BandSegmentAddress.left L a j)
      (BandSegmentAddress.right L a j)

/-- The canonical closed walk traces the complete collar-band route.  This
upgrades the earlier edge-bookkeeping statement to an exact point-set
identity; the remaining local task is to prove that this walk is simple. -/
theorem range_bandClosedWalk (a : LevelAddress n) :
    range ((BrokenLineData.segmentFamilyComplex
        (BandSegmentAddress.left L a)
        (BandSegmentAddress.right L a)).walkGeometricPath
      (L.bandClosedWalk a)) = L.bandCarrier a := by
  have h := BrokenLineData.range_segmentFamilyClosedWalk
    (BandSegmentAddress.left L a)
    (BandSegmentAddress.right L a)
    (L.bandFirst a) (L.bandTail a)
    (L.bandRoute_isChain a) (L.bandRoute_closes a)
    (fun i _hi => L.bandSegment_left_ne_right a i)
  rw [L.bandFirst_cons_bandTail a] at h
  exact h

/-- The common-arrangement cycle gives an honest polygonal circle carried
by the parent crosscut, its retained side hairs, and the child crosscuts. -/
theorem exists_bandPolygonalCircle (a : LevelAddress n) :
    ∃ P : PolygonalCircle, P.carrier ⊆ L.bandCarrier a := by
  obtain ⟨z, c, hc, _e, _hec, hcycleSubset⟩ := L.exists_bandCycle a
  let left := BandSegmentAddress.left L a
  let right := BandSegmentAddress.right L a
  let K := BrokenLineData.segmentFamilyComplex left right
  have hedgeSource : ∀ v w,
      s(v, w) ∈ c.edges →
      segment ℝ (K.position v) (K.position w) ⊆ L.bandCarrier a := by
    intro v w he
    have heClosedFin : s(v, w) ∈ (L.bandClosedWalk a).edges.toFinset :=
      hcycleSubset (List.mem_toFinset.mpr he)
    have heClosed : s(v, w) ∈ (L.bandClosedWalk a).edges :=
      List.mem_toFinset.mp heClosedFin
    obtain ⟨j, hjRoute, hej⟩ :=
      BrokenLineData.segmentFamilyClosedWalk_edges_covered
        left right (L.bandFirst a) (L.bandTail a)
        (L.bandRoute_isChain a) (L.bandRoute_closes a)
        s(v, w) heClosed
    have hjBand : j ∈ L.bandSegments a := by
      rw [← L.bandFirst_cons_bandTail a]
      exact hjRoute
    let pj : K.vertexGraph.Walk
        (BrokenLineData.segmentFamilyLeftVertex left right j)
        (BrokenLineData.segmentFamilyRightVertex left right j) :=
      BrokenLineData.segmentFamilyPath left right j
    have hej' : s(v, w) ∈ pj.edges := hej
    have hsegmentRange : segment ℝ (K.position v) (K.position w) ⊆
        range (K.walkGeometricPath pj) :=
      Schoenflies.TriangleMesh.PlaneComplex.segment_subset_range_walkGeometricPath_of_mem_edges
        K pj hej'
    have hrangeSource :=
      BrokenLineData.range_walkGeometricPath_segmentFamilyPath_subset
        left right j
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨hjBand, ?_⟩⟩
    apply hrangeSource
    unfold pj at hsegmentRange
    exact hsegmentRange hx
  have hnotnil : ¬c.Nil := hc.not_nil
  obtain ⟨w, hw, q, hcEq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnotnil
  have hstart : K.position z ∈ L.bandCarrier a := by
    apply hedgeSource z w
      (by rw [hcEq]; simp)
    exact left_mem_segment ℝ _ _
  have hrange : range (K.walkGeometricPath c) ⊆ L.bandCarrier a :=
    BrokenLineData.range_walkGeometricPath_subset_of_start_of_edges
      K c hstart hedgeSource
  refine ⟨K.polygonalCircleOfCycle c hc, ?_⟩
  rw [K.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath c hc]
  exact hrange

/-- Every transported descendant arc is contained in its parent boundary
arc.  This is the source half of the coarse-window nesting used by the
boundary-continuity drift estimate. -/
theorem levelArc_curveArcPlane_subset_of_mem_addresses
    {c : LevelAddress L.next.level} {a : LevelAddress n}
    (hc : c ∈ L.addresses a) :
    (I.levelArc c).curveArcPlane ⊆ (I.levelArc a).curveArcPlane := by
  rw [addresses, List.mem_map] at hc
  obtain ⟨b, hbMem, rfl⟩ := hc
  rw [I.levelArc_cast L.parentLevel_add_depth]
  exact I.levelArc_curveArcPlane_subset_of_mem_descendantAddresses a b hbMem

end RecursiveInsideCollarStep.Later

end InitialAngularArcs
end JordanCircle

end

end Schoenflies
