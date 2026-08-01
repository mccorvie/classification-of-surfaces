import Schoenflies.CommonSegmentArrangement

/-!
# Concatenating an ordered segment family

An ordered list of labelled segments whose consecutive geometric endpoints
agree gives a graph walk in their common line arrangement.  The walk retains
exact edge-coverage information in both directions.  This is the abstract
concatenation layer used for the parent/children boundary route of a Chapter
9 collar band.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData

namespace BrokenLineData

/-- The common plane complex of a labelled finite segment family. -/
noncomputable abbrev segmentFamilyComplex
    {I : Type*} [Fintype I] (left right : I → Plane) : PlaneComplex :=
  (segmentFamilyChain left right).arrangementMesh.toPlaneComplex

/-- A concatenated walk together with exact bookkeeping of which labelled
segment paths supply its edges. -/
structure SegmentFamilyChainWalkData
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I) where
  walk : (segmentFamilyComplex left right).vertexGraph.Walk
    (segmentFamilyLeftVertex left right a)
    (segmentFamilyRightVertex left right
      ((a :: tail).getLast (by simp)))
  segmentEdges_subset : ∀ i, i ∈ a :: tail → ∀ e,
    e ∈ (segmentFamilyPath left right i :
      (segmentFamilyComplex left right).vertexGraph.Walk
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i)).edges →
    e ∈ walk.edges
  edges_covered : ∀ e, e ∈ walk.edges →
    ∃ i ∈ a :: tail,
      e ∈ (segmentFamilyPath left right i :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right i)
          (segmentFamilyRightVertex left right i)).edges
  edgeCount_eq_sum : ∀ e, walk.edges.count e =
    ((a :: tail).map fun i =>
      (segmentFamilyPath left right i :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right i)
          (segmentFamilyRightVertex left right i)).edges.count e).sum

/-- Consecutive endpoint equalities suffice to concatenate every canonical
segment path in the specified order. -/
theorem nonempty_segmentFamilyChainWalkData
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j) :
    Nonempty (SegmentFamilyChainWalkData left right a tail) := by
  classical
  induction tail generalizing a with
  | nil =>
      let p : (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right a)
          (segmentFamilyRightVertex left right a) :=
        segmentFamilyPath left right a
      refine ⟨{
        walk := p
        segmentEdges_subset := ?_
        edges_covered := ?_
        edgeCount_eq_sum := ?_ }⟩
      · intro i hi e he
        simp only [List.mem_singleton] at hi
        subst i
        exact he
      · intro e he
        exact ⟨a, by simp, he⟩
      · intro e
        rfl
  | cons b tail ih =>
      obtain ⟨Q⟩ := ih b hchain.tail
      let p : (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right a)
          (segmentFamilyRightVertex left right a) :=
        segmentFamilyPath left right a
      have hab : segmentFamilyRightVertex left right a =
          segmentFamilyLeftVertex left right b :=
        segmentFamilyRightVertex_eq_leftVertex_of_eq
          left right hchain.rel
      let q : (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyRightVertex left right a)
          (segmentFamilyRightVertex left right
            ((b :: tail).getLast (by simp))) :=
        Q.walk.copy hab.symm rfl
      let w := p.append q
      have hlast :
          (a :: b :: tail).getLast (by simp) =
            (b :: tail).getLast (by simp) := by
        simp
      let w' : (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right a)
          (segmentFamilyRightVertex left right
            ((a :: b :: tail).getLast (by simp))) :=
        w.copy rfl (congrArg (segmentFamilyRightVertex left right) hlast.symm)
      have hqEdges : q.edges = Q.walk.edges := by
        simp [q, SimpleGraph.Walk.edges_copy]
      refine ⟨{
        walk := w'
        segmentEdges_subset := ?_
        edges_covered := ?_
        edgeCount_eq_sum := ?_ }⟩
      · intro i hi e he
        rw [show w'.edges = p.edges ++ q.edges by
          simp [w', w, SimpleGraph.Walk.edges_append]]
        rw [List.mem_append]
        simp only [List.mem_cons] at hi
        rcases hi with hi | hi
        · subst i
          exact Or.inl he
        · exact Or.inr <| hqEdges.symm ▸ Q.segmentEdges_subset i
            (by simpa only [List.mem_cons] using hi) e he
      · intro e he
        have he' : e ∈ p.edges ++ q.edges := by
          simpa [w', w, SimpleGraph.Walk.edges_copy,
            SimpleGraph.Walk.edges_append] using he
        rw [List.mem_append] at he'
        rcases he' with hep | heq
        · exact ⟨a, by simp, hep⟩
        · obtain ⟨i, hi, hei⟩ := Q.edges_covered e (hqEdges ▸ heq)
          exact ⟨i, by simp [hi], hei⟩
      · intro e
        rw [show w'.edges = p.edges ++ q.edges by
          simp [w', w, SimpleGraph.Walk.edges_append],
          List.count_append, hqEdges, Q.edgeCount_eq_sum]
        rfl

/-- A canonical concatenated walk for a chained segment list. -/
noncomputable def segmentFamilyChainWalkData
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j) :
    SegmentFamilyChainWalkData left right a tail :=
  Classical.choice
    (nonempty_segmentFamilyChainWalkData left right a tail hchain)

/-- If the final endpoint also equals the initial endpoint, the chained walk
closes in the common arrangement. -/
noncomputable def segmentFamilyClosedWalk
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a) :
    (segmentFamilyComplex left right).vertexGraph.Walk
      (segmentFamilyLeftVertex left right a)
      (segmentFamilyLeftVertex left right a) :=
  let D := segmentFamilyChainWalkData left right a tail hchain
  let hv := segmentFamilyRightVertex_eq_leftVertex_of_eq
    left right hclose
  D.walk.copy rfl hv

theorem segmentEdges_subset_segmentFamilyClosedWalk
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a)
    (i : I) (hi : i ∈ a :: tail) (e : Sym2
      (segmentFamilyComplex left right).Vertex)
    (he : e ∈ (segmentFamilyPath left right i :
      (segmentFamilyComplex left right).vertexGraph.Walk
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i)).edges) :
    e ∈ (segmentFamilyClosedWalk left right a tail hchain hclose).edges := by
  let D := segmentFamilyChainWalkData left right a tail hchain
  simpa [segmentFamilyClosedWalk, SimpleGraph.Walk.edges_copy] using
    D.segmentEdges_subset i hi e he

theorem segmentFamilyClosedWalk_edges_covered
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a)
    (e : Sym2 (segmentFamilyComplex left right).Vertex)
    (he : e ∈
      (segmentFamilyClosedWalk left right a tail hchain hclose).edges) :
    ∃ i ∈ a :: tail,
      e ∈ (segmentFamilyPath left right i :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right i)
          (segmentFamilyRightVertex left right i)).edges := by
  let D := segmentFamilyChainWalkData left right a tail hchain
  apply D.edges_covered e
  simpa [segmentFamilyClosedWalk, SimpleGraph.Walk.edges_copy] using he

theorem segmentFamilyClosedWalk_edgeCount_eq_sum
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a)
    (e : Sym2 (segmentFamilyComplex left right).Vertex) :
    (segmentFamilyClosedWalk left right a tail hchain hclose).edges.count e =
      ((a :: tail).map fun i =>
        (segmentFamilyPath left right i :
          (segmentFamilyComplex left right).vertexGraph.Walk
            (segmentFamilyLeftVertex left right i)
            (segmentFamilyRightVertex left right i)).edges.count e).sum := by
  let D := segmentFamilyChainWalkData left right a tail hchain
  simpa [segmentFamilyClosedWalk, SimpleGraph.Walk.edges_copy] using
    D.edgeCount_eq_sum e

/-- A private edge of one segment path is traversed exactly once by a closed
chained walk whose label list has no repetitions. -/
theorem segmentFamilyClosedWalk_count_eq_one_of_private
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a)
    (hnodup : (a :: tail).Nodup)
    (i : I) (hi : i ∈ a :: tail)
    (e : Sym2 (segmentFamilyComplex left right).Vertex)
    (he : e ∈ (segmentFamilyPath left right i :
      (segmentFamilyComplex left right).vertexGraph.Walk
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i)).edges)
    (hprivate : ∀ j ∈ a :: tail, j ≠ i →
      e ∉ (segmentFamilyPath left right j :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right j)
          (segmentFamilyRightVertex left right j)).edges) :
    (segmentFamilyClosedWalk left right a tail hchain hclose).edges.count e = 1 := by
  classical
  rw [segmentFamilyClosedWalk_edgeCount_eq_sum]
  let f : I → ℕ := fun j =>
    (segmentFamilyPath left right j :
      (segmentFamilyComplex left right).vertexGraph.Walk
        (segmentFamilyLeftVertex left right j)
        (segmentFamilyRightVertex left right j)).edges.count e
  have hf (j : I) (hj : j ∈ a :: tail) :
      f j = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      exact SimpleGraph.Path.count_edges_eq_one
        (p := segmentFamilyPath left right i) e he
    · rw [if_neg hji]
      exact List.count_eq_zero_of_not_mem (hprivate j hj hji)
  have hmap : (a :: tail).map f =
      (a :: tail).map (fun j => if j = i then 1 else 0) := by
    apply List.map_congr_left
    intro j hj
    exact hf j hj
  rw [show ((a :: tail).map fun j =>
      (segmentFamilyPath left right j :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right j)
          (segmentFamilyRightVertex left right j)).edges.count e).sum =
      ((a :: tail).map f).sum by rfl,
    hmap]
  have hcountAux (l : List I) :
      (l.map (fun j => if j = i then 1 else 0)).sum = l.count i := by
    induction l with
    | nil => rfl
    | cons j l ih =>
        simp only [List.map_cons, List.sum_cons, List.count_cons, beq_iff_eq]
        by_cases hji : j = i
        · subst j
          rw [ih]
          omega
        · rw [ih]
          rw [if_neg hji]
          omega
  rw [hcountAux]
  exact List.count_eq_one_of_mem hnodup hi

/-- A private arrangement edge in one member of a closed segment chain lies
on a simple cycle made only from edges of that chain. -/
theorem exists_isCycle_containing_of_private_segmentEdge
    {I : Type*} [Fintype I] (left right : I → Plane)
    (a : I) (tail : List I)
    (hchain : (a :: tail).IsChain fun i j => right i = left j)
    (hclose : right ((a :: tail).getLast (by simp)) = left a)
    (hnodup : (a :: tail).Nodup)
    (i : I) (hi : i ∈ a :: tail)
    (e : Sym2 (segmentFamilyComplex left right).Vertex)
    (he : e ∈ (segmentFamilyPath left right i :
      (segmentFamilyComplex left right).vertexGraph.Walk
        (segmentFamilyLeftVertex left right i)
        (segmentFamilyRightVertex left right i)).edges)
    (hprivate : ∀ j ∈ a :: tail, j ≠ i →
      e ∉ (segmentFamilyPath left right j :
        (segmentFamilyComplex left right).vertexGraph.Walk
          (segmentFamilyLeftVertex left right j)
          (segmentFamilyRightVertex left right j)).edges) :
    ∃ (z : (segmentFamilyComplex left right).Vertex)
        (c : (segmentFamilyComplex left right).vertexGraph.Walk z z),
      c.IsCycle ∧ e ∈ c.edges ∧
        c.edges.toFinset ⊆
          (segmentFamilyClosedWalk left right a tail hchain hclose).edges.toFinset := by
  classical
  induction e using Sym2.ind with
  | _ v w =>
      have hcount := segmentFamilyClosedWalk_count_eq_one_of_private
        left right a tail hchain hclose hnodup i hi s(v, w) he hprivate
      have hodd : Odd
          ((segmentFamilyClosedWalk left right a tail hchain hclose).edges.count
            s(v, w)) := by
        rw [hcount]
        exact odd_one
      exact exists_isCycle_containing_of_odd_count
        (segmentFamilyClosedWalk left right a tail hchain hclose) hodd

end BrokenLineData

end Schoenflies
