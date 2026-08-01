import Schoenflies.CollarBandSegments
import Schoenflies.TrimmedLevelEdges

/-!
# The non-retracing polygonal cells in a recursive Moise band

The synchronized crosscuts form each complete collar level, but an individual
Chapter 9 cell uses the original trimmed crosscuts.  At an interior child
junction the two trimmed endpoints are joined along their common retained
hair.  At the two extremes they are joined directly to the parent collar.
This omits the synchronization extensions that would otherwise be traversed
twice along the extreme hairs.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle
namespace InitialAngularArcs

variable {J : JordanCircle} {I : J.InitialAngularArcs}
  {n : ℕ} {epsilon : ℝ}
  {F : I.LevelAvoidingJoinFamily n epsilon} {hn : 1 ≤ n}

namespace RecursiveInsideCollarStep.Later

variable (L : RecursiveInsideCollarStep.Later F hn)

private noncomputable abbrev childIndex
    (b : LevelAddress L.next.level) :
    Fin (levelAddressCount L.next.level) :=
  levelIndexOf L.next.level b

/-- Labels for the non-retracing source segments of one Moise band cell. -/
abbrev MoiseBandSegmentAddress :=
  F.LevelEdgeAddress ⊕
    (Unit ⊕
      (L.next.family.forgetObstacle.TrimmedEdgeAddress ⊕
        ((LevelAddress L.next.level × LevelAddress L.next.level) ⊕ Unit)))

namespace MoiseBandSegmentAddress

def parent (e : F.LevelEdgeAddress) : L.MoiseBandSegmentAddress :=
  Sum.inl e

def leftSide : L.MoiseBandSegmentAddress :=
  Sum.inr (Sum.inl ())

def child
    (e : L.next.family.forgetObstacle.TrimmedEdgeAddress) :
    L.MoiseBandSegmentAddress :=
  Sum.inr (Sum.inr (Sum.inl e))

def junction (b c : LevelAddress L.next.level) :
    L.MoiseBandSegmentAddress :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (b, c))))

def rightSide : L.MoiseBandSegmentAddress :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

variable (a : LevelAddress n)

/-- Initial endpoint in the positive orientation around the band cell. -/
noncomputable def left : L.MoiseBandSegmentAddress → Plane
  | .inl e => F.edgeFinish e
  | .inr (.inl ()) => F.leftSynchronizedPoint a
  | .inr (.inr (.inl e)) =>
      L.next.family.forgetObstacle.trimmedEdgeFinish e
  | .inr (.inr (.inr (.inl (b, _c)))) =>
      L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b)
  | .inr (.inr (.inr (.inr ()))) =>
      L.next.family.forgetObstacle.trimmedRightPoint
        (L.childIndex (L.rightmostAddress a))

/-- Final endpoint in the positive orientation around the band cell. -/
noncomputable def right : L.MoiseBandSegmentAddress → Plane
  | .inl e => F.edgeStart e
  | .inr (.inl ()) =>
      L.next.family.forgetObstacle.trimmedLeftPoint
        (L.childIndex (L.leftmostAddress a))
  | .inr (.inr (.inl e)) =>
      L.next.family.forgetObstacle.trimmedEdgeStart e
  | .inr (.inr (.inr (.inl (_b, c)))) =>
      L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex c)
  | .inr (.inr (.inr (.inr ()))) => F.rightSynchronizedPoint a

def Adjacent (x y : L.MoiseBandSegmentAddress) : Prop :=
  right L a x = left L a y

end MoiseBandSegmentAddress

/-- One child raw crosscut, traversed from its left endpoint to its right
endpoint. -/
noncomputable def reversedTrimmedBlock
    (b : LevelAddress L.next.level) :
    List L.MoiseBandSegmentAddress :=
  (L.next.family.forgetObstacle.trimmedEdgeBlock b).reverse.map
    (MoiseBandSegmentAddress.child L)

theorem reversedTrimmedBlock_nonempty
    (b : LevelAddress L.next.level) :
    L.reversedTrimmedBlock b ≠ [] := by
  intro h
  have hrev :
      (L.next.family.forgetObstacle.trimmedEdgeBlock b).reverse = [] :=
    List.map_eq_nil_iff.mp h
  exact L.next.family.forgetObstacle.trimmedEdgeBlock_nonempty b
    (List.reverse_eq_nil_iff.mp hrev)

theorem reversedTrimmedBlock_isChain (a : LevelAddress n)
    (b : LevelAddress L.next.level) :
    (L.reversedTrimmedBlock b).IsChain
      (MoiseBandSegmentAddress.Adjacent L a) := by
  rw [reversedTrimmedBlock, List.isChain_map, List.isChain_reverse]
  exact (L.next.family.forgetObstacle.trimmedEdgeBlock_isChain b).imp
    fun _ _ h => h.symm

theorem head_reversedTrimmedBlock
    (b : LevelAddress L.next.level) :
    (L.reversedTrimmedBlock b).head
        (L.reversedTrimmedBlock_nonempty b) =
      MoiseBandSegmentAddress.child L
        ⟨b, L.next.family.forgetObstacle.lastTrimmedEdgeIndex b⟩ := by
  unfold reversedTrimmedBlock
  rw [List.head_map, List.head_reverse,
    L.next.family.forgetObstacle.getLast_trimmedEdgeBlock]

theorem getLast_reversedTrimmedBlock
    (b : LevelAddress L.next.level) :
    (L.reversedTrimmedBlock b).getLast
        (L.reversedTrimmedBlock_nonempty b) =
      MoiseBandSegmentAddress.child L
        ⟨b, L.next.family.forgetObstacle.firstTrimmedEdgeIndex b⟩ := by
  unfold reversedTrimmedBlock
  rw [List.getLast_map, List.getLast_reverse,
    L.next.family.forgetObstacle.head_trimmedEdgeBlock]

theorem left_head_reversedTrimmedBlock (a : LevelAddress n)
    (b : LevelAddress L.next.level) :
    MoiseBandSegmentAddress.left L a
        ((L.reversedTrimmedBlock b).head
          (L.reversedTrimmedBlock_nonempty b)) =
      L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex b) := by
  rw [L.head_reversedTrimmedBlock b]
  exact L.next.family.forgetObstacle.trimmedEdgeFinish_last b

theorem right_getLast_reversedTrimmedBlock (a : LevelAddress n)
    (b : LevelAddress L.next.level) :
    MoiseBandSegmentAddress.right L a
        ((L.reversedTrimmedBlock b).getLast
          (L.reversedTrimmedBlock_nonempty b)) =
      L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b) := by
  rw [L.getLast_reversedTrimmedBlock b]
  exact L.next.family.forgetObstacle.trimmedEdgeStart_first b

/-- The raw child crosscuts joined successively along their common retained
hairs. -/
noncomputable def childMoiseSegments
    (step : RecursiveInsideCollarStep.Later F hn) :
    List (LevelAddress step.next.level) →
      List step.MoiseBandSegmentAddress
  | [] => []
  | [b] => step.reversedTrimmedBlock b
  | b :: c :: tail =>
      step.reversedTrimmedBlock b ++
        [MoiseBandSegmentAddress.junction step b c] ++
        childMoiseSegments step (c :: tail)

theorem childMoiseSegments_nonempty
    {l : List (LevelAddress L.next.level)} (hl : l ≠ []) :
    L.childMoiseSegments l ≠ [] := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b tail =>
      cases tail with
      | nil => exact L.reversedTrimmedBlock_nonempty b
      | cons c tail =>
          simp only [childMoiseSegments]
          intro h
          have hleft := (List.append_eq_nil_iff.mp
            (List.append_eq_nil_iff.mp h).1).1
          exact L.reversedTrimmedBlock_nonempty b hleft

theorem head_childMoiseSegments
    {l : List (LevelAddress L.next.level)} (hl : l ≠ [])
    (a : LevelAddress n) :
    MoiseBandSegmentAddress.left L a
        ((L.childMoiseSegments l).head
          (L.childMoiseSegments_nonempty hl)) =
      L.next.family.forgetObstacle.trimmedLeftPoint
        (L.childIndex (l.head hl)) := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b tail =>
      cases tail with
      | nil =>
          change MoiseBandSegmentAddress.left L a
              ((L.reversedTrimmedBlock b).head _) = _
          simpa using L.left_head_reversedTrimmedBlock a b
      | cons c tail =>
          change MoiseBandSegmentAddress.left L a
              (((L.reversedTrimmedBlock b ++
                [MoiseBandSegmentAddress.junction L b c]) ++
                L.childMoiseSegments (c :: tail)).head _) = _
          rw [List.head_append_of_ne_nil (by
                simp [L.reversedTrimmedBlock_nonempty b]),
            List.head_append_of_ne_nil
              (L.reversedTrimmedBlock_nonempty b)]
          simpa using L.left_head_reversedTrimmedBlock a b

theorem getLast_childMoiseSegments
    {l : List (LevelAddress L.next.level)} (hl : l ≠ [])
    (a : LevelAddress n) :
    MoiseBandSegmentAddress.right L a
        ((L.childMoiseSegments l).getLast
          (L.childMoiseSegments_nonempty hl)) =
      L.next.family.forgetObstacle.trimmedRightPoint
        (L.childIndex (l.getLast hl)) := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons b tail ih =>
      cases tail with
      | nil =>
          change MoiseBandSegmentAddress.right L a
              ((L.reversedTrimmedBlock b).getLast _) = _
          simpa using L.right_getLast_reversedTrimmedBlock a b
      | cons c tail =>
          have htail : (c :: tail) ≠ [] := by simp
          change MoiseBandSegmentAddress.right L a
              (((L.reversedTrimmedBlock b ++
                [MoiseBandSegmentAddress.junction L b c]) ++
                L.childMoiseSegments (c :: tail)).getLast _) = _
          rw [List.getLast_append_of_right_ne_nil _ _
            (L.childMoiseSegments_nonempty htail)]
          simpa using ih htail

theorem reversedTrimmedBlock_append_junction_isChain
    (a : LevelAddress n) {b c : LevelAddress L.next.level}
    (_hbc : I.LevelAdjacent b c) :
    (L.reversedTrimmedBlock b ++
      [MoiseBandSegmentAddress.junction L b c]).IsChain
        (MoiseBandSegmentAddress.Adjacent L a) := by
  apply (L.reversedTrimmedBlock_isChain a b).append (by simp)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  rw [L.getLast_reversedTrimmedBlock b] at hx'
  have hy' := List.head_of_mem_head? hy
  change MoiseBandSegmentAddress.junction L b c = y at hy'
  subst x
  subst y
  change L.next.family.forgetObstacle.trimmedEdgeStart
      ⟨b, L.next.family.forgetObstacle.firstTrimmedEdgeIndex b⟩ =
    L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b)
  exact L.next.family.forgetObstacle.trimmedEdgeStart_first b

theorem childMoiseSegments_isChain
    (a : LevelAddress n) (l : List (LevelAddress L.next.level))
    (hl : l.IsChain I.LevelAdjacent) :
    (L.childMoiseSegments l).IsChain
      (MoiseBandSegmentAddress.Adjacent L a) := by
  induction l with
  | nil => simp [childMoiseSegments]
  | cons b tail ih =>
      cases tail with
      | nil => exact L.reversedTrimmedBlock_isChain a b
      | cons c tail =>
          have htail : (c :: tail) ≠ [] := by simp
          change ((L.reversedTrimmedBlock b ++
              [MoiseBandSegmentAddress.junction L b c]) ++
            L.childMoiseSegments (c :: tail)).IsChain _
          apply (L.reversedTrimmedBlock_append_junction_isChain a
            hl.rel).append (ih hl.tail)
          intro x hx y hy
          have hx' := List.getLast_of_mem_getLast? hx
          have hxlast : (L.reversedTrimmedBlock b ++
              [MoiseBandSegmentAddress.junction L b c]).getLast (by
                simp) = MoiseBandSegmentAddress.junction L b c := by simp
          rw [hxlast] at hx'
          have hy' := List.head_of_mem_head? hy
          have hhead := L.head_childMoiseSegments htail a
          subst x
          change MoiseBandSegmentAddress.right L a
              (MoiseBandSegmentAddress.junction L b c) =
            MoiseBandSegmentAddress.left L a y
          rw [← hy', hhead]
          rfl

/-- Parent crosscut edges in reverse list order and reverse orientation. -/
noncomputable def parentMoiseSegments (a : LevelAddress n) :
    List L.MoiseBandSegmentAddress :=
  (F.edgeBlock a).reverse.map (MoiseBandSegmentAddress.parent L)

/-- The complete non-retracing boundary route of the Moise cell associated
to the parent level arc `a`. -/
noncomputable def moiseBandSegments (a : LevelAddress n) :
    List L.MoiseBandSegmentAddress :=
  L.parentMoiseSegments a ++
    [MoiseBandSegmentAddress.leftSide L] ++
    L.childMoiseSegments (L.addresses a) ++
    [MoiseBandSegmentAddress.rightSide L]

theorem parentMoiseSegments_nonempty (a : LevelAddress n) :
    L.parentMoiseSegments a ≠ [] := by
  intro h
  have hrev : (F.edgeBlock a).reverse = [] := List.map_eq_nil_iff.mp h
  exact F.edgeBlock_nonempty a (List.reverse_eq_nil_iff.mp hrev)

theorem parentMoiseSegments_isChain (a : LevelAddress n) :
    (L.parentMoiseSegments a).IsChain
      (MoiseBandSegmentAddress.Adjacent L a) := by
  rw [parentMoiseSegments, List.isChain_map, List.isChain_reverse]
  exact (F.edgeBlock_isChain a).imp fun _ _ h => h.symm

theorem head_parentMoiseSegments (a : LevelAddress n) :
    (L.parentMoiseSegments a).head (L.parentMoiseSegments_nonempty a) =
      MoiseBandSegmentAddress.parent L
        ⟨a, F.lastEdgeIndex a⟩ := by
  unfold parentMoiseSegments
  rw [List.head_map, List.head_reverse, F.getLast_edgeBlock]

theorem getLast_parentMoiseSegments (a : LevelAddress n) :
    (L.parentMoiseSegments a).getLast
        (L.parentMoiseSegments_nonempty a) =
      MoiseBandSegmentAddress.parent L
        ⟨a, F.firstEdgeIndex a⟩ := by
  unfold parentMoiseSegments
  rw [List.getLast_map, List.getLast_reverse, F.head_edgeBlock]

theorem childMoiseSegments_addresses_nonempty (a : LevelAddress n) :
    L.childMoiseSegments (L.addresses a) ≠ [] :=
  L.childMoiseSegments_nonempty (L.addresses_nonempty a)

theorem left_head_childMoiseSegments_addresses (a : LevelAddress n) :
    MoiseBandSegmentAddress.left L a
        ((L.childMoiseSegments (L.addresses a)).head
          (L.childMoiseSegments_addresses_nonempty a)) =
      L.next.family.forgetObstacle.trimmedLeftPoint
        (L.childIndex (L.leftmostAddress a)) := by
  rw [L.head_childMoiseSegments (L.addresses_nonempty a) a,
    L.addresses_head a]

theorem right_getLast_childMoiseSegments_addresses (a : LevelAddress n) :
    MoiseBandSegmentAddress.right L a
        ((L.childMoiseSegments (L.addresses a)).getLast
          (L.childMoiseSegments_addresses_nonempty a)) =
      L.next.family.forgetObstacle.trimmedRightPoint
        (L.childIndex (L.rightmostAddress a)) := by
  rw [L.getLast_childMoiseSegments (L.addresses_nonempty a) a,
    L.addresses_getLast a]

theorem parentMoiseSegments_append_leftSide_isChain
    (a : LevelAddress n) :
    (L.parentMoiseSegments a ++
      [MoiseBandSegmentAddress.leftSide L]).IsChain
        (MoiseBandSegmentAddress.Adjacent L a) := by
  apply (L.parentMoiseSegments_isChain a).append (by simp)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  rw [L.getLast_parentMoiseSegments a] at hx'
  have hy' := List.head_of_mem_head? hy
  change MoiseBandSegmentAddress.leftSide L = y at hy'
  subst x
  subst y
  exact F.edgeStart_first a

theorem parentLeftChildMoise_isChain (a : LevelAddress n) :
    (L.parentMoiseSegments a ++
      [MoiseBandSegmentAddress.leftSide L] ++
      L.childMoiseSegments (L.addresses a)).IsChain
        (MoiseBandSegmentAddress.Adjacent L a) := by
  apply (L.parentMoiseSegments_append_leftSide_isChain a).append
    (L.childMoiseSegments_isChain a (L.addresses a)
      (L.addresses_isChain a))
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  have hxlast : (L.parentMoiseSegments a ++
      [MoiseBandSegmentAddress.leftSide L]).getLast (by simp) =
        MoiseBandSegmentAddress.leftSide L := by simp
  rw [hxlast] at hx'
  have hy' := List.head_of_mem_head? hy
  have hhead := L.left_head_childMoiseSegments_addresses a
  subst x
  change MoiseBandSegmentAddress.right L a
      (MoiseBandSegmentAddress.leftSide L) =
    MoiseBandSegmentAddress.left L a y
  rw [← hy', hhead]
  rfl

theorem moiseBandSegments_isChain (a : LevelAddress n) :
    (L.moiseBandSegments a).IsChain
      (MoiseBandSegmentAddress.Adjacent L a) := by
  rw [moiseBandSegments]
  apply (L.parentLeftChildMoise_isChain a).append (by simp)
  intro x hx y hy
  have hx' := List.getLast_of_mem_getLast? hx
  have hxlast : (L.parentMoiseSegments a ++
      [MoiseBandSegmentAddress.leftSide L] ++
      L.childMoiseSegments (L.addresses a)).getLast (by simp) =
      (L.childMoiseSegments (L.addresses a)).getLast
        (L.childMoiseSegments_addresses_nonempty a) := by
    exact List.getLast_append_of_right_ne_nil _ _
      (L.childMoiseSegments_addresses_nonempty a)
  rw [hxlast] at hx'
  have hy' := List.head_of_mem_head? hy
  change MoiseBandSegmentAddress.rightSide L = y at hy'
  have hlast := L.right_getLast_childMoiseSegments_addresses a
  subst x
  subst y
  exact hlast

theorem moiseBandSegments_nonempty (a : LevelAddress n) :
    L.moiseBandSegments a ≠ [] := by
  rw [moiseBandSegments]
  intro h
  have h₁ := (List.append_eq_nil_iff.mp h).1
  have h₂ := (List.append_eq_nil_iff.mp h₁).1
  have h₃ := (List.append_eq_nil_iff.mp h₂).1
  exact L.parentMoiseSegments_nonempty a h₃

theorem moiseBandSegments_closes (a : LevelAddress n) :
    MoiseBandSegmentAddress.Adjacent L a
      ((L.moiseBandSegments a).getLast (L.moiseBandSegments_nonempty a))
      ((L.moiseBandSegments a).head (L.moiseBandSegments_nonempty a)) := by
  have hlast : (L.moiseBandSegments a).getLast
      (L.moiseBandSegments_nonempty a) =
        MoiseBandSegmentAddress.rightSide L := by
    simp [moiseBandSegments]
  have hhead : (L.moiseBandSegments a).head
      (L.moiseBandSegments_nonempty a) =
        MoiseBandSegmentAddress.parent L
          ⟨a, F.lastEdgeIndex a⟩ := by
    apply Option.some.inj
    rw [← List.head?_eq_some_head (L.moiseBandSegments_nonempty a)]
    calc
      (L.moiseBandSegments a).head? =
          (L.parentMoiseSegments a).head? := by
        unfold moiseBandSegments
        rw [List.head?_append_of_ne_nil _ (by
              simp [L.parentMoiseSegments_nonempty a]),
          List.head?_append_of_ne_nil _ (by
              simp [L.parentMoiseSegments_nonempty a]),
          List.head?_append_of_ne_nil _
            (L.parentMoiseSegments_nonempty a)]
      _ = some (MoiseBandSegmentAddress.parent L
          ⟨a, F.lastEdgeIndex a⟩) := by
        rw [List.head?_eq_some_head (L.parentMoiseSegments_nonempty a),
          L.head_parentMoiseSegments a]
  rw [hlast, hhead]
  exact (F.edgeFinish_last a).symm

theorem levelAdjacent_ne {b c : LevelAddress L.next.level}
    (hbc : I.LevelAdjacent b c) : b ≠ c := by
  have hc : c = nextLevelAddress L.next.level b :=
    (I.levelRightPoint_eq_levelLeftPoint_iff b c).mp hbc
  rw [hc]
  exact (nextLevelAddress_ne L.next.level b).symm

/-- Adjacent raw trimmed paths have distinct endpoints on their common
retained hair. -/
theorem trimmedRightPoint_ne_trimmedLeftPoint_of_levelAdjacent
    {b c : LevelAddress L.next.level} (hbc : I.LevelAdjacent b c) :
    L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b) ≠
      L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex c) := by
  let G := L.next.family.forgetObstacle
  have hbcNe : b ≠ c := L.levelAdjacent_ne hbc
  have hindex : L.childIndex b ≠ L.childIndex c := by
    intro h
    exact hbcNe (levelIndexOf_injective L.next.level h)
  have hdis := G.pairwise_disjoint_trimmedPath hindex
  intro hpoints
  exact Set.disjoint_left.mp hdis
    (Path.source_mem_range (G.trimmedPath (L.childIndex b)))
    (by
      rw [hpoints]
      exact Path.target_mem_range (G.trimmedPath (L.childIndex c)))

theorem child_or_junction_of_mem_childMoiseSegments
    {l : List (LevelAddress L.next.level)}
    (hl : l.IsChain I.LevelAdjacent)
    {j : L.MoiseBandSegmentAddress}
    (hj : j ∈ L.childMoiseSegments l) :
    (∃ e : L.next.family.forgetObstacle.TrimmedEdgeAddress,
        j = MoiseBandSegmentAddress.child L e) ∨
      ∃ b c : LevelAddress L.next.level,
        I.LevelAdjacent b c ∧
          j = MoiseBandSegmentAddress.junction L b c := by
  induction l with
  | nil => simp [childMoiseSegments] at hj
  | cons b tail ih =>
      cases tail with
      | nil =>
          left
          rw [childMoiseSegments, reversedTrimmedBlock,
            List.mem_map] at hj
          obtain ⟨e, _he, rfl⟩ := hj
          exact ⟨e, rfl⟩
      | cons c tail =>
          rw [childMoiseSegments, List.mem_append] at hj
          rcases hj with hj | hj
          · rw [List.mem_append] at hj
            rcases hj with hj | hj
            · left
              rw [reversedTrimmedBlock, List.mem_map] at hj
              obtain ⟨e, _he, rfl⟩ := hj
              exact ⟨e, rfl⟩
            · right
              have hj' : j = MoiseBandSegmentAddress.junction L b c := by
                simpa only [List.mem_singleton] using hj
              exact ⟨b, c, hl.rel, hj'⟩
          · exact ih hl.tail hj

theorem parent_of_mem_parentMoiseSegments
    {a : LevelAddress n} {j : L.MoiseBandSegmentAddress}
    (hj : j ∈ L.parentMoiseSegments a) :
    ∃ e : F.LevelEdgeAddress,
      j = MoiseBandSegmentAddress.parent L e := by
  rw [parentMoiseSegments, List.mem_map] at hj
  obtain ⟨e, _he, rfl⟩ := hj
  exact ⟨e, rfl⟩

/-- Every raw trimmed edge is nondegenerate. -/
theorem childSegment_left_ne_right
    (a : LevelAddress n)
    (e : L.next.family.forgetObstacle.TrimmedEdgeAddress) :
    MoiseBandSegmentAddress.left L a
        (MoiseBandSegmentAddress.child L e) ≠
      MoiseBandSegmentAddress.right L a
        (MoiseBandSegmentAddress.child L e) := by
  change L.next.family.forgetObstacle.trimmedEdgeFinish e ≠
    L.next.family.forgetObstacle.trimmedEdgeStart e
  exact (L.next.family.forgetObstacle.trimmedEdgeStart_ne_finish e).symm

/-- Both extreme retained-hair sides are nondegenerate. -/
theorem leftSide_left_ne_right (a : LevelAddress n) :
    MoiseBandSegmentAddress.left L a
        (MoiseBandSegmentAddress.leftSide L) ≠
      MoiseBandSegmentAddress.right L a
        (MoiseBandSegmentAddress.leftSide L) := by
  have hlt := L.next.dist_child_trimmedLeft_lt_parent_left F hn a
    (L.leftmostAddress a)
    (by simp [L.levelArc_leftmostAddress_left a])
  intro h
  change F.leftSynchronizedPoint a =
    L.next.family.forgetObstacle.trimmedLeftPoint
      (L.childIndex (L.leftmostAddress a)) at h
  rw [← h] at hlt
  exact (lt_irrefl _ hlt)

theorem rightSide_left_ne_right (a : LevelAddress n) :
    MoiseBandSegmentAddress.left L a
        (MoiseBandSegmentAddress.rightSide L) ≠
      MoiseBandSegmentAddress.right L a
        (MoiseBandSegmentAddress.rightSide L) := by
  have hlt := L.next.dist_child_trimmedRight_lt_parent_right F hn a
    (L.rightmostAddress a)
    (by simp [L.levelArc_rightmostAddress_right a])
  intro h
  change L.next.family.forgetObstacle.trimmedRightPoint
      (L.childIndex (L.rightmostAddress a)) =
        F.rightSynchronizedPoint a at h
  rw [h] at hlt
  exact (lt_irrefl _ hlt)

/-- The corrected extreme left side, ending at the raw trimmed endpoint,
lies in the old retained-hair base segment. -/
theorem rawLeftSide_subset_parentBaseSegment (a : LevelAddress n) :
    segment ℝ (F.leftSynchronizedPoint a)
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (L.leftmostAddress a))) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
        (F.leftSynchronizedPoint a) := by
  let H := I.levelLeftHair a
  let child : H.carrier :=
    ⟨L.next.family.forgetObstacle.trimmedLeftPoint
        (L.childIndex (L.leftmostAddress a)), by
      rw [← L.leftmostAddress_leftHair_carrier a]
      exact (L.next.family.forgetObstacle.leftHairPoint
        (L.leftmostAddress a)).2⟩
  let parent : H.carrier :=
    ⟨F.leftSynchronizedPoint a,
      F.leftSynchronizedPoint_mem_leftHair a⟩
  have hparameter : H.carrierParameter child ≤
      H.carrierParameter parent :=
    (L.leftmost_trimmed_carrierParameter_lt_parent a).le
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

/-- The corrected raw right side has the analogous containment. -/
theorem rawRightSide_subset_parentBaseSegment (a : LevelAddress n) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint
          (L.childIndex (L.rightmostAddress a)))
        (F.rightSynchronizedPoint a) ⊆
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
        (F.rightSynchronizedPoint a) := by
  let H := I.levelRightHair a
  let child : H.carrier :=
    ⟨L.next.family.forgetObstacle.trimmedRightPoint
        (L.childIndex (L.rightmostAddress a)), by
      rw [← L.rightmostAddress_rightHair_carrier a]
      exact (L.next.family.forgetObstacle.rightHairPoint
        (L.rightmostAddress a)).2⟩
  let parent : H.carrier :=
    ⟨F.rightSynchronizedPoint a,
      F.rightSynchronizedPoint_mem_rightHair a⟩
  have hparameter : H.carrierParameter child ≤
      H.carrierParameter parent :=
    (L.rightmost_trimmed_carrierParameter_lt_parent a).le
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

/-- An old parent edge and a raw child-crosscut edge are disjoint. -/
theorem parentEdge_disjoint_rawChildEdge
    (e : F.LevelEdgeAddress)
    (f : L.next.family.forgetObstacle.TrimmedEdgeAddress) :
    Disjoint (F.edgeSegment e)
      (L.next.family.forgetObstacle.trimmedEdgeSegment f) := by
  apply (L.next.trimmed_path_disjoint (L.childIndex f.1)).symm.mono
  · intro x hx
    rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
    apply Or.inr
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr
      ⟨e.1, F.edgeSegment_subset_crosscutRange e hx⟩
  · exact L.next.family.forgetObstacle
      |>.trimmedEdgeSegment_subset_trimmedPathRange f

/-- Every internal raw-hair junction remains in the separating neighborhood
of the original Jordan curve. -/
theorem junctionSegment_subset_thickening
    {b c : LevelAddress L.next.level} (hbc : I.LevelAdjacent b c) :
    segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex c)) ⊆
      thickening L.next.buffer J.carrier := by
  let G := L.next.family.forgetObstacle
  let q : Plane := J.curvePoint (I.levelArc c).left
  have hqCarrier : q ∈ J.carrier :=
    (J.curvePoint (I.levelArc c).left).2
  have hrightReturn : G.trimmedRightPoint (L.childIndex b) ∈
      G.synchronizedReturnSet b := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    exact Or.inr (Path.source_mem_range
      (G.trimmedPath (L.childIndex b)))
  have hleftReturn : G.trimmedLeftPoint (L.childIndex c) ∈
      G.synchronizedReturnSet c := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    exact Or.inr (Path.target_mem_range
      (G.trimmedPath (L.childIndex c)))
  have hrightNearLeft := L.next.return_near b hrightReturn
  have hleftNear : G.trimmedLeftPoint (L.childIndex c) ∈
      ball q (L.next.buffer / 4) := by
    simpa [q] using L.next.return_near c hleftReturn
  have hboundary := L.next.rightBoundaryPoint_mem_cellClosedBall b
  have hboundary' : dist
      (J.curvePoint (I.levelArc b).left : Plane)
      (J.curvePoint (I.levelArc b).right : Plane) ≤
        L.next.buffer / 4 := by
    simpa [mem_closedBall, dist_comm] using hboundary
  have hrightNear : G.trimmedRightPoint (L.childIndex b) ∈
      ball q (L.next.buffer / 2) := by
    rw [mem_ball] at hrightNearLeft ⊢
    have hq : q = (J.curvePoint (I.levelArc b).right : Plane) :=
      hbc.symm
    rw [hq]
    calc
      dist (G.trimmedRightPoint (L.childIndex b))
          (J.curvePoint (I.levelArc b).right : Plane) ≤
          dist (G.trimmedRightPoint (L.childIndex b))
              (J.curvePoint (I.levelArc b).left : Plane) +
            dist (J.curvePoint (I.levelArc b).left : Plane)
              (J.curvePoint (I.levelArc b).right : Plane) :=
        dist_triangle _ _ _
      _ < L.next.buffer / 2 := by
        nlinarith [L.next.buffer_pos, hboundary']
  have hleftNearHalf : G.trimmedLeftPoint (L.childIndex c) ∈
      ball q (L.next.buffer / 2) := by
    exact (Metric.ball_subset_ball (by linarith [L.next.buffer_pos] :
      L.next.buffer / 4 ≤ L.next.buffer / 2)) hleftNear
  have hsegment : segment ℝ
      (G.trimmedRightPoint (L.childIndex b))
      (G.trimmedLeftPoint (L.childIndex c)) ⊆
      ball q (L.next.buffer / 2) :=
    (convex_ball q (L.next.buffer / 2)).segment_subset
      hrightNear hleftNearHalf
  exact hsegment.trans <|
    (Metric.ball_subset_ball (by linarith [L.next.buffer_pos] :
      L.next.buffer / 2 ≤ L.next.buffer)).trans
        (ball_subset_thickening hqCarrier L.next.buffer)

/-- An old parent edge is disjoint from every internal raw-hair junction. -/
theorem parentEdge_disjoint_junction
    (e : F.LevelEdgeAddress)
    {b c : LevelAddress L.next.level} (hbc : I.LevelAdjacent b c) :
    Disjoint (F.edgeSegment e)
      (segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint (L.childIndex b))
        (L.next.family.forgetObstacle.trimmedLeftPoint (L.childIndex c))) := by
  apply L.next.buffer_separation.mono
  · intro x hx
    rw [(F.synchronizedPolygonalCircle hn).closedRegion_eq_union]
    apply Or.inr
    rw [F.carrier_synchronizedPolygonalCircle hn]
    exact Set.mem_iUnion.mpr
      ⟨e.1, F.edgeSegment_subset_crosscutRange e hx⟩
  · exact L.junctionSegment_subset_thickening hbc

/-- An old parent edge meets the corrected left side in at most its old
left endpoint. -/
theorem parentEdge_inter_rawLeftSide_subsingleton
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    (F.edgeSegment ⟨a, i⟩ ∩
      segment ℝ (F.leftSynchronizedPoint a)
        (L.next.family.forgetObstacle.trimmedLeftPoint
          (L.childIndex (L.leftmostAddress a)))).Subsingleton := by
  intro x hx y hy
  have hx' : x ∈
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
          (F.leftSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rawLeftSide_subset_parentBaseSegment a hx.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hx.1⟩
  have hy' : y ∈
      segment ℝ (J.curvePoint (I.levelArc a).left : Plane)
          (F.leftSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rawLeftSide_subset_parentBaseSegment a hy.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hy.1⟩
  rw [F.leftBaseSegment_inter_range_synchronizedCrosscutPath a] at hx' hy'
  exact (mem_singleton_iff.mp hx').trans
    (mem_singleton_iff.mp hy').symm

/-- An old parent edge meets the corrected right side in at most its old
right endpoint. -/
theorem parentEdge_inter_rawRightSide_subsingleton
    (a : LevelAddress n)
    (i : Fin (F.synchronizedCrosscutCarrierLine a).data.n) :
    (F.edgeSegment ⟨a, i⟩ ∩
      segment ℝ
        (L.next.family.forgetObstacle.trimmedRightPoint
          (L.childIndex (L.rightmostAddress a)))
        (F.rightSynchronizedPoint a)).Subsingleton := by
  intro x hx y hy
  have hx' : x ∈
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
          (F.rightSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rawRightSide_subset_parentBaseSegment a hx.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hx.1⟩
  have hy' : y ∈
      segment ℝ (J.curvePoint (I.levelArc a).right : Plane)
          (F.rightSynchronizedPoint a) ∩
        range (F.synchronizedCrosscutPath a) :=
    ⟨L.rawRightSide_subset_parentBaseSegment a hy.2,
      F.edgeSegment_subset_crosscutRange ⟨a, i⟩ hy.1⟩
  rw [F.rightBaseSegment_inter_range_synchronizedCrosscutPath a] at hx' hy'
  exact (mem_singleton_iff.mp hx').trans
    (mem_singleton_iff.mp hy').symm

/-- Every segment which actually occurs in the corrected Moise route is
nondegenerate. -/
theorem moiseBandSegment_left_ne_right_of_mem
    (a : LevelAddress n) {j : L.MoiseBandSegmentAddress}
    (hj : j ∈ L.moiseBandSegments a) :
    MoiseBandSegmentAddress.left L a j ≠
      MoiseBandSegmentAddress.right L a j := by
  rw [moiseBandSegments, List.mem_append] at hj
  rcases hj with hj | hj
  · rw [List.mem_append] at hj
    rcases hj with hj | hj
    · rw [List.mem_append] at hj
      rcases hj with hj | hj
      · obtain ⟨e, rfl⟩ := L.parent_of_mem_parentMoiseSegments hj
        change F.edgeFinish e ≠ F.edgeStart e
        exact (edgeStart_ne_edgeFinish (F := F) e).symm
      · have hj' : j = MoiseBandSegmentAddress.leftSide L := by
          simpa only [List.mem_singleton] using hj
        subst j
        exact L.leftSide_left_ne_right a
    · rcases L.child_or_junction_of_mem_childMoiseSegments
          (L.addresses_isChain a) hj with hchild | hjunction
      · obtain ⟨e, rfl⟩ := hchild
        exact L.childSegment_left_ne_right a e
      · obtain ⟨b, c, hbc, rfl⟩ := hjunction
        exact L.trimmedRightPoint_ne_trimmedLeftPoint_of_levelAdjacent hbc
  · have hj' : j = MoiseBandSegmentAddress.rightSide L := by
      simpa only [List.mem_singleton] using hj
    subst j
    exact L.rightSide_left_ne_right a

/-- Canonical first label and remaining labels of the corrected route. -/
noncomputable def moiseBandFirst (a : LevelAddress n) :
    L.MoiseBandSegmentAddress :=
  (L.moiseBandSegments a).head (L.moiseBandSegments_nonempty a)

noncomputable def moiseBandTail (a : LevelAddress n) :
    List L.MoiseBandSegmentAddress :=
  (L.moiseBandSegments a).tail

theorem moiseBandFirst_cons_tail (a : LevelAddress n) :
    L.moiseBandFirst a :: L.moiseBandTail a =
      L.moiseBandSegments a :=
  List.cons_head_tail (L.moiseBandSegments_nonempty a)

theorem moiseBandRoute_isChain (a : LevelAddress n) :
    (L.moiseBandFirst a :: L.moiseBandTail a).IsChain
      (MoiseBandSegmentAddress.Adjacent L a) := by
  rw [L.moiseBandFirst_cons_tail a]
  exact L.moiseBandSegments_isChain a

theorem moiseBandRoute_closes (a : LevelAddress n) :
    MoiseBandSegmentAddress.right L a
        ((L.moiseBandFirst a :: L.moiseBandTail a).getLast (by simp)) =
      MoiseBandSegmentAddress.left L a (L.moiseBandFirst a) := by
  have hlist := L.moiseBandFirst_cons_tail a
  have hlast : (L.moiseBandFirst a :: L.moiseBandTail a).getLast
      (by simp) =
      (L.moiseBandSegments a).getLast
        (L.moiseBandSegments_nonempty a) := by
    apply List.getLast_congr
    exact hlist
  rw [hlast]
  change MoiseBandSegmentAddress.right L a
      ((L.moiseBandSegments a).getLast
        (L.moiseBandSegments_nonempty a)) =
    MoiseBandSegmentAddress.left L a
      ((L.moiseBandSegments a).head
        (L.moiseBandSegments_nonempty a))
  exact L.moiseBandSegments_closes a

/-- The common-arrangement closed walk of the corrected Moise boundary. -/
noncomputable def moiseBandClosedWalk (a : LevelAddress n) :=
  BrokenLineData.segmentFamilyClosedWalk
    (MoiseBandSegmentAddress.left L a)
    (MoiseBandSegmentAddress.right L a)
    (L.moiseBandFirst a) (L.moiseBandTail a)
    (L.moiseBandRoute_isChain a) (L.moiseBandRoute_closes a)

/-- Point-set union of the non-retracing source segments. -/
noncomputable def moiseBandCarrier (a : LevelAddress n) : Set Plane :=
  ⋃ j ∈ L.moiseBandSegments a,
    segment ℝ (MoiseBandSegmentAddress.left L a j)
      (MoiseBandSegmentAddress.right L a j)

/-- The canonical common-arrangement walk traces exactly the corrected
Moise cell boundary. -/
theorem range_moiseBandClosedWalk (a : LevelAddress n) :
    range ((BrokenLineData.segmentFamilyComplex
        (MoiseBandSegmentAddress.left L a)
        (MoiseBandSegmentAddress.right L a)).walkGeometricPath
      (L.moiseBandClosedWalk a)) = L.moiseBandCarrier a := by
  have h := BrokenLineData.range_segmentFamilyClosedWalk
    (MoiseBandSegmentAddress.left L a)
    (MoiseBandSegmentAddress.right L a)
    (L.moiseBandFirst a) (L.moiseBandTail a)
    (L.moiseBandRoute_isChain a) (L.moiseBandRoute_closes a)
    (fun j hj => L.moiseBandSegment_left_ne_right_of_mem a (by
      rw [← L.moiseBandFirst_cons_tail a]
      exact hj))
  rw [L.moiseBandFirst_cons_tail a] at h
  exact h

end RecursiveInsideCollarStep.Later
end InitialAngularArcs
end JordanCircle

end

end Schoenflies
