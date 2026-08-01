import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Ring.Nat
import ClassificationOfSurfaces.Moise.PLMoves
import ClassificationOfSurfaces.Moise.PolygonalArc
import ClassificationOfSurfaces.Moise.PlaneCycle

/-!
# A finite even graph contains a cycle

The boundary edges of a finite planar triangle mesh have even valence at
every vertex.  This small graph-theoretic lemma is the abstract part of
extracting a polygonal frame from that boundary.
-/

namespace Schoenflies

open SimpleGraph

/-- A finite graph with an edge and even degree at every vertex contains a
simple cycle.  The proof uses the leaf theorem for finite trees on the
connected component containing the given edge. -/
theorem SimpleGraph.exists_isCycle_of_even_degree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    {v w : V} (hvw : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle := by
  classical
  by_contra hcycle
  push Not at hcycle
  have hacyclic : G.IsAcyclic := by
    intro u p hp
    exact hcycle u p hp
  let c : G.ConnectedComponent := G.connectedComponentMk v
  have hv : v ∈ c.supp := by
    exact ConnectedComponent.connectedComponentMk_mem
  have hw : w ∈ c.supp := c.mem_supp_of_adj_mem_supp hv hvw
  let vc : c := ⟨v, hv⟩
  let wc : c := ⟨w, hw⟩
  have hvcwc : vc ≠ wc := by
    intro h
    exact hvw.ne (congrArg Subtype.val h)
  letI : Fintype c := Subtype.fintype (fun x : V => x ∈ c.supp)
  letI : Nontrivial c := ⟨⟨vc, wc, hvcwc⟩⟩
  letI : DecidableRel c.toSimpleGraph.Adj :=
    SimpleGraph.instDecidableComapAdj (fun x : c => (x : V)) G
  have htree : c.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent c
  obtain ⟨u, hu⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hneighbors : G.neighborSet (u : V) ⊆ c.supp := by
    intro z hz
    exact c.mem_supp_of_adj_mem_supp u.2 hz
  have hdegree : c.toSimpleGraph.degree u = G.degree (u : V) := by
    exact @SimpleGraph.degree_induce_of_neighborSet_subset
      V c.supp _ _ G _ u hneighbors
  have huone : G.degree (u : V) = 1 := by
    rw [← hdegree]
    exact hu
  obtain ⟨k, hk⟩ := heven (u : V)
  rw [huone] at hk
  omega

/-- Every specified edge of a finite even-degree graph belongs to a simple
cycle.  This strengthens `exists_isCycle_of_even_degree_of_adj` in the form
needed to cover every edge of a mesh boundary by polygonal cycles. -/
theorem SimpleGraph.exists_isCycle_containing_of_even_degree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    {v w : V} (hvw : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  apply SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
  refine ⟨hvw, ?_⟩
  let H := G.deleteEdges {s(v, w)}
  by_contra hnreach
  let S : Set V := {x | H.Reachable v x}
  have hvS : v ∈ S := by
    change H.Reachable v v
    exact @SimpleGraph.Reachable.refl V H v
  have hwS : w ∉ S := hnreach
  let I : SimpleGraph S := G.induce S
  let vv : S := ⟨v, hvS⟩
  have neighbor_subset_S_of_ne_v (x : S) (hxv : (x : V) ≠ v) :
      G.neighborSet (x : V) ⊆ S := by
    intro z hxz
    have hedgeNe : s((x : V), z) ≠ s(v, w) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hxv', -⟩ | ⟨hxw, hzv⟩
      · exact hxv hxv'
      · apply hwS
        rw [← hxw]
        exact x.2
    exact x.2.trans <| (SimpleGraph.deleteEdges_adj.mpr
      ⟨hxz, by simpa using hedgeNe⟩).reachable
  have hdegree_ne (x : S) (hxv : x ≠ vv) : I.degree x = G.degree (x : V) := by
    apply G.degree_induce_of_neighborSet_subset
    exact neighbor_subset_S_of_ne_v x (fun h => hxv (Subtype.ext h))
  have hneighbor_v : G.neighborFinset v ∩ S.toFinset =
      G.neighborFinset v \ {w} := by
    ext z
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Set.mem_toFinset, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hvz, hzS⟩
      exact ⟨hvz, fun hzw => hwS (hzw ▸ hzS)⟩
    · rintro ⟨hvz, hzw⟩
      refine ⟨hvz, ?_⟩
      exact hvS.trans <| (SimpleGraph.deleteEdges_adj.mpr
        ⟨hvz, by simp [Sym2.eq_iff, hzw, hvw.ne]⟩).reachable
  have hdegree_v : I.degree vv + 1 = G.degree v := by
    have hwmem : w ∈ G.neighborFinset v := by
      simpa only [SimpleGraph.mem_neighborFinset] using hvw
    have hcardPos : 0 < (G.neighborFinset v).card :=
      Finset.card_pos.mpr ⟨w, hwmem⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := Function.Embedding.subtype fun x : V => x ∈ S),
      G.map_neighborFinset_induce vv, hneighbor_v]
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hwmem]
    omega
  have hoddv : Odd (I.degree vv) := by
    obtain ⟨k, hk⟩ := heven v
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨x, hxne, hxodd⟩ := I.exists_ne_odd_degree_of_exists_odd_degree vv hoddv
  have hxEven : Even (I.degree x) := by
    rw [hdegree_ne x hxne]
    exact heven x
  obtain ⟨a, ha⟩ := hxEven
  obtain ⟨b, hb⟩ := hxodd
  omega

open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- If a horizontal line first meets a polygon at `q`, and `x` lies just to
the right with no other polygon point strictly between them, then the crossing
index at `x` is one.  The height-avoidance hypothesis excludes polygon
vertices, so the unique crossing is through the relative interior of one
edge. -/
theorem PolygonalCircle.index_eq_one_of_unique_left_crossing
    (P : PolygonalCircle) {q x : Plane}
    (hq : q ∈ P.carrier)
    (hheight : ∀ i : ZMod P.n, q 1 ≠ (P.vertex i) 1)
    (hxheight : x 1 = q 1) (hqx : q 0 < x 0)
    (hbetween : ∀ z : Plane, z ∈ P.carrier → z 1 = q 1 →
      z 0 < x 0 → z = q) :
    P.index x = 1 := by
  classical
  obtain ⟨i₀, hqi₀⟩ := Set.mem_iUnion.mp hq
  have hband := P.strict_height_band_of_mem_edgeSegment hqi₀ hheight
  have hnonhorizontal :
      (P.vertex i₀) 1 ≠ (P.vertex (i₀ + 1)) 1 := by
    rcases hband with hband | hband <;> linarith
  have hcrossq :
      PolygonalCircle.crossingX
        (P.vertex i₀) (P.vertex (i₀ + 1)) (q 1) = q 0 :=
    P.crossingX_eq_of_mem_edgeSegment hnonhorizontal hqi₀
  have hi₀crossed : P.EdgeCrossed i₀ x := by
    refine ⟨?_, ?_⟩
    · rcases hband with hband | hband
      · exact Or.inl ⟨hband.1.le.trans_eq hxheight.symm,
          hxheight.trans_lt hband.2⟩
      · exact Or.inr ⟨hband.1.le.trans_eq hxheight.symm,
          hxheight.trans_lt hband.2⟩
    · rw [hxheight, hcrossq]
      exact hqx
  have hfilter :
      (Finset.univ.filter fun i : ZMod P.n => P.EdgeCrossed i x) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      let z : Plane := planePoint
        (PolygonalCircle.crossingX
          (P.vertex i) (P.vertex (i + 1)) (x 1)) (x 1)
      have hzi : z ∈ P.edgeSegment i := by
        apply P.mem_edgeSegment_of_crossing (P := z) i
        · simpa [z] using hi.1
        · rfl
      have hzcarrier : z ∈ P.carrier := P.edgeSegment_subset_carrier i hzi
      have hzheight : z 1 = q 1 := by simpa [z] using hxheight
      have hzleft : z 0 < x 0 := by simpa [z] using hi.2
      have hzq : z = q := hbetween z hzcarrier hzheight hzleft
      have hqi : q ∈ P.edgeSegment i := hzq ▸ hzi
      by_contra hii₀
      have hends := P.edgeSegment_inter_subset_endpoints
        (i := i₀) (j := i) (Ne.symm hii₀) ⟨hqi₀, hqi⟩
      rcases hends with hqv | hqv
      · exact hheight i₀ (congrArg (fun z : Plane => z 1) hqv)
      · exact hheight (i₀ + 1) (congrArg (fun z : Plane => z 1) hqv)
    · rintro rfl
      exact hi₀crossed
  unfold PolygonalCircle.index
  rw [hfilter]
  simp

namespace TriangleMesh

open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- A geometric edge named in a one-skeleton walk is contained in the range
of that walk's piecewise-linear path. -/
theorem PlaneComplex.segment_subset_range_walkGeometricPath_of_mem_edges
    (K : PlaneComplex) {a b u z : K.Vertex}
    (p : K.vertexGraph.Walk u z) (hab : s(a, b) ∈ p.edges) :
    segment ℝ (K.position a) (K.position b) ⊆
      Set.range (K.walkGeometricPath p) := by
  induction p with
  | nil => simp at hab
  | @cons u v z huv p ih =>
      rw [SimpleGraph.Walk.edges_cons] at hab
      simp only [List.mem_cons] at hab
      rw [K.walkGeometricPath_cons, Path.trans_range]
      rcases hab with hab | hab
      · apply Set.subset_union_of_subset_left
        rw [Path.range_segment]
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
        · subst a; subst b; exact subset_rfl
        · subst a; subst b; rw [segment_symm]
      · exact Set.subset_union_of_subset_right (ih hab) _

/-- Double-counting triangle--vertex incidences around one mesh vertex.
Every triangle containing `v` contributes its other two vertices. -/
theorem sum_incidentTriangles_pair_eq_two_mul
    (M : TriangleMesh) (v : M.Vertex) :
    ∑ w ∈ (Finset.univ.erase v),
        (M.incidentTriangles ({v, w} : Finset M.Vertex)).card =
      2 * (M.triangles.filter fun t => v ∈ t).card := by
  classical
  calc
    ∑ w ∈ (Finset.univ.erase v),
        (M.incidentTriangles ({v, w} : Finset M.Vertex)).card =
        ∑ w ∈ (Finset.univ.erase v),
          ∑ t ∈ M.triangles, if ({v, w} : Finset M.Vertex) ⊆ t then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [TriangleMesh.incidentTriangles]
            exact (Finset.sum_boole
              (fun t => ({v, w} : Finset M.Vertex) ⊆ t) M.triangles).symm
    _ = ∑ t ∈ M.triangles,
          ∑ w ∈ (Finset.univ.erase v),
            if ({v, w} : Finset M.Vertex) ⊆ t then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ t ∈ M.triangles, if v ∈ t then 2 else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases hvt : v ∈ t
          · rw [if_pos hvt]
            have hfilter :
                ((Finset.univ.erase v).filter fun w =>
                    ({v, w} : Finset M.Vertex) ⊆ t) = t.erase v := by
              ext w
              simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
                Finset.insert_subset_iff, Finset.singleton_subset_iff]
              constructor
              · rintro ⟨hwv, ⟨-, hwt⟩⟩
                exact ⟨hwv.1, hwt⟩
              · rintro ⟨hwv, hwt⟩
                exact ⟨⟨hwv, trivial⟩, ⟨hvt, hwt⟩⟩
            rw [← Finset.card_filter, hfilter,
              Finset.card_erase_of_mem hvt, M.card_triangle t ht]
          · rw [if_neg hvt]
            apply Finset.sum_eq_zero
            intro w hw
            rw [if_neg]
            intro hvw
            exact hvt (Finset.insert_subset_iff.mp hvw).1
    _ = 2 * (M.triangles.filter fun t => v ∈ t).card := by
          rw [Finset.sum_ite]
          simp [Nat.mul_comm]

theorem odd_card_incidentTriangles_pair_iff_boundaryEdge
    (M : TriangleMesh) {v w : M.Vertex} (hvw : v ≠ w) :
    Odd (M.incidentTriangles ({v, w} : Finset M.Vertex)).card ↔
      M.IsBoundaryEdge ({v, w} : Finset M.Vertex) := by
  classical
  let e : Finset M.Vertex := {v, w}
  have hecard : e.card = 2 := Finset.card_pair hvw
  constructor
  · intro hodd
    have hle : (M.incidentTriangles e).card ≤ 2 :=
      M.card_incidentTriangles_le_two hecard
    have hpos : 0 < (M.incidentTriangles e).card := hodd.pos
    change Odd (M.incidentTriangles e).card at hodd
    obtain ⟨k, hk⟩ := hodd
    have hone : (M.incidentTriangles e).card = 1 := by omega
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
    have htdata := M.mem_incidentTriangles_iff.mp ht
    refine ⟨?_, hone⟩
    exact Finset.mem_biUnion.mpr
      ⟨t, htdata.1, Finset.mem_powersetCard.mpr ⟨htdata.2, hecard⟩⟩
  · intro he
    rw [he.2]
    exact odd_one

/-- The abstract graph whose edges are exactly the incidence-one edges of
the triangle mesh.  It is kept on `M.Vertex` (rather than on the opaque
vertex type of `M.boundaryComplex`) so that it composes directly with the
full one-skeleton. -/
def boundaryGraph (M : TriangleMesh) : SimpleGraph M.Vertex where
  Adj v w := M.IsBoundaryEdge ({v, w} : Finset M.Vertex)
  symm := ⟨by
    intro v w h
    simpa [Finset.pair_comm] using h⟩
  loopless := ⟨by
    intro v h
    have hcard := M.card_of_mem_edges h.1
    simpa using hcard⟩

theorem boundaryGraph_adj_iff (M : TriangleMesh) {v w : M.Vertex} :
    (boundaryGraph M).Adj v w ↔
      M.IsBoundaryEdge ({v, w} : Finset M.Vertex) := Iff.rfl

/-- Every vertex has even degree in the boundary-edge graph of a finite
triangle mesh.  This is the simplicial identity `∂² = 0` over `𝔽₂`,
proved here by an explicit finite double count. -/
theorem even_degree_boundaryGraph
    (M : TriangleMesh) [DecidableRel (boundaryGraph M).Adj]
    (v : M.Vertex) :
    Even ((boundaryGraph M).degree v) := by
  classical
  let W : Finset M.Vertex := Finset.univ.erase v
  let f : M.Vertex → ℕ := fun w =>
    (M.incidentTriangles ({v, w} : Finset M.Vertex)).card
  have hsum : Even (∑ w ∈ W, f w) := by
    rw [show (∑ w ∈ W, f w) =
      2 * (M.triangles.filter fun t => v ∈ t).card by
        exact sum_incidentTriangles_pair_eq_two_mul M v]
    exact ⟨(M.triangles.filter fun t => v ∈ t).card, by omega⟩
  have hfilter :
      (W.filter fun w => Odd (f w)) =
        (boundaryGraph M).neighborFinset v := by
    ext w
    simp only [W, f, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      true_and, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hwv, hodd⟩
      rw [boundaryGraph_adj_iff M]
      exact (odd_card_incidentTriangles_pair_iff_boundaryEdge M hwv.1.symm).mp hodd
    · intro hadj
      have hwv : w ≠ v := hadj.ne.symm
      refine ⟨⟨hwv, trivial⟩, ?_⟩
      apply (odd_card_incidentTriangles_pair_iff_boundaryEdge M hwv.symm).mpr
      rw [← boundaryGraph_adj_iff M]
      exact hadj
  have hcardEven : Even (W.filter fun w => Odd (f w)).card :=
    (Finset.even_sum_iff_even_card_odd f).mp hsum
  rw [hfilter] at hcardEven
  exact hcardEven

theorem exists_boundaryGraph_adj (M : TriangleMesh)
    (hne : M.triangles.Nonempty) :
    ∃ v w : M.Vertex, (boundaryGraph M).Adj v w := by
  classical
  obtain ⟨t, htfree⟩ := M.exists_free_triangle_of_triangles_nonempty hne
  obtain ⟨e, he⟩ := M.boundaryEdges_nonempty_of_isFreeTriangle htfree
  have hedata := M.mem_boundaryEdges_iff.mp he
  obtain ⟨v, w, hvw, heq⟩ := Finset.card_eq_two.mp hedata.2.1
  refine ⟨v, w, ?_⟩
  rw [boundaryGraph_adj_iff, ← heq]
  exact hedata.2.2

/-- Every boundary edge is an edge of the full mesh one-skeleton. -/
theorem boundaryGraph_le_vertexGraph (M : TriangleMesh) :
    boundaryGraph M ≤ M.toPlaneComplex.vertexGraph := by
  intro v w hvw
  have he := (boundaryGraph_adj_iff M).mp hvw
  have hecard : ({v, w} : Finset M.Vertex).card = 2 :=
    M.card_of_mem_edges he.1
  have hvwne : v ≠ w := by
    intro h
    subst w
    simp at hecard
  change v ≠ w ∧ ({v, w} : Finset M.Vertex) ∈ M.faces
  refine ⟨hvwne, ?_⟩
  obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.mp he.1
  exact M.mem_faces_iff.mpr
    ⟨by simp, t, ht, (Finset.mem_powersetCard.mp het).1⟩

/-- Every nonempty finite planar triangle mesh has at least one polygonal
boundary cycle.  No manifold or disk assumption is needed; at a pinched
boundary vertex the graph may have degree four, but its even-degree
component still contains a simple cycle. -/
theorem exists_boundary_polygonalCircle (M : TriangleMesh)
    (hne : M.triangles.Nonempty) :
    ∃ (v : M.Vertex) (p : M.toPlaneComplex.vertexGraph.Walk v v),
      p.IsCycle := by
  classical
  obtain ⟨v, w, hvw⟩ := exists_boundaryGraph_adj M hne
  obtain ⟨u, p, hp⟩ :=
    SimpleGraph.exists_isCycle_of_even_degree_of_adj
      (boundaryGraph M) (even_degree_boundaryGraph M) hvw
  let q := p.mapLe (boundaryGraph_le_vertexGraph M)
  exact ⟨u, q, hp.mapLe (boundaryGraph_le_vertexGraph M)⟩

/-- Edgewise form of boundary-cycle extraction: every incidence-one mesh edge
lies on a simple cycle in the geometric one-skeleton. -/
theorem exists_boundary_polygonalCycle_containing
    (M : TriangleMesh) {v w : M.Vertex}
    (hvw : (boundaryGraph M).Adj v w) :
    ∃ (u : M.Vertex) (p : M.toPlaneComplex.vertexGraph.Walk u u),
      p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  obtain ⟨u, p, hpcycle, hpedge⟩ :=
    SimpleGraph.exists_isCycle_containing_of_even_degree_of_adj
      (boundaryGraph M) (even_degree_boundaryGraph M) hvw
  let hle := boundaryGraph_le_vertexGraph M
  let q := p.mapLe hle
  refine ⟨u, q, hpcycle.mapLe hle, ?_⟩
  change s(v, w) ∈ (p.mapLe hle).edges
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hpedge

/-- Turn a simple boundary-graph cycle into its geometric polygonal circle. -/
noncomputable def polygonalCircleOfBoundaryCycle
    (M : TriangleMesh) {u : M.Vertex}
    (p : (boundaryGraph M).Walk u u) (hp : p.IsCycle) : PolygonalCircle :=
  let hle := boundaryGraph_le_vertexGraph M
  let q := p.mapLe hle
  M.toPlaneComplex.polygonalCircleOfCycle q (hp.mapLe hle)

theorem polygonalCircleOfBoundaryCycle_carrier_subset_boundaryCarrier
    (M : TriangleMesh) {u : M.Vertex}
    (p : (boundaryGraph M).Walk u u) (hp : p.IsCycle) :
    (polygonalCircleOfBoundaryCycle M p hp).carrier ⊆ M.boundaryCarrier := by
  classical
  let hle := boundaryGraph_le_vertexGraph M
  let q := p.mapLe hle
  have hq : q.IsCycle := hp.mapLe hle
  intro x hx
  have hxrange : x ∈ Set.range (M.toPlaneComplex.walkGeometricPath q) := by
    rw [← M.toPlaneComplex.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath q hq]
    exact hx
  have hqpos : 0 < q.length := lt_of_lt_of_le (by omega) hq.three_le_length
  obtain ⟨i, hi⟩ :=
    M.toPlaneComplex.exists_walkSegment_of_mem_range q hqpos hxrange
  have hlen : p.length = q.length := by
    exact (SimpleGraph.Walk.length_map (SimpleGraph.Hom.ofLE hle) p).symm
  have hij : i.val < p.length := by
    rw [hlen]
    exact i.isLt
  let j : Fin p.length := ⟨i.val, hij⟩
  have hpedge : (boundaryGraph M).Adj
      (p.getVert j.val) (p.getVert (j.val + 1)) :=
    p.adj_getVert_succ j.isLt
  have hboundary : M.IsBoundaryEdge
      ({p.getVert j.val, p.getVert (j.val + 1)} : Finset M.Vertex) :=
    (boundaryGraph_adj_iff M).mp hpedge
  have hi' : x ∈ segment ℝ
      (M.position (p.getVert j.val))
      (M.position (p.getVert (j.val + 1))) := by
    have hpos : M.toPlaneComplex.position = M.position := by rfl
    have hget (n : ℕ) : q.getVert n = p.getVert n := by
      calc
        q.getVert n = (SimpleGraph.Hom.ofLE hle) (p.getVert n) := by
          exact SimpleGraph.Walk.getVert_map (SimpleGraph.Hom.ofLE hle) p n
        _ = p.getVert n := rfl
    rw [hpos] at hi
    have hget0 := congrArg M.position (hget i.val)
    have hget1 := congrArg M.position (hget (i.val + 1))
    have hseg : segment ℝ (M.position (q.getVert i.val))
        (M.position (q.getVert (i.val + 1))) =
        segment ℝ (M.position (p.getVert i.val))
          (M.position (p.getVert (i.val + 1))) :=
      congrArg₂ (segment ℝ) hget0 hget1
    have hiP : x ∈ segment ℝ (M.position (p.getVert i.val))
        (M.position (p.getVert (i.val + 1))) := hseg ▸ hi
    simpa only [j] using hiP
  rw [TriangleMesh.boundaryCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨{p.getVert j.val, p.getVert (j.val + 1)}, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨M.mem_allBoundaryEdges_iff.mpr hboundary, ?_⟩
  have himage : M.position ''
      (({p.getVert j.val, p.getVert (j.val + 1)} : Finset M.Vertex) : Set M.Vertex) =
      {M.position (p.getVert j.val), M.position (p.getVert (j.val + 1))} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact hi'

/-- Every particular incidence-one edge is carried by a polygonal boundary
circle whose polygon vertices are vertices of the mesh.  Retaining the latter
fact is useful for generic horizontal slices: avoiding the finitely many mesh
vertex heights then avoids all vertices of the extracted polygon as well. -/
theorem exists_polygonalCircle_containing_boundaryEdge_with_vertices
    (M : TriangleMesh) {v w : M.Vertex}
    (hvw : (boundaryGraph M).Adj v w) :
    ∃ P : PolygonalCircle,
      segment ℝ (M.position v) (M.position w) ⊆ P.carrier ∧
        P.carrier ⊆ M.boundaryCarrier ∧
          ∀ i : ZMod P.n, P.vertex i ∈ Set.range M.position := by
  classical
  obtain ⟨u, p, hpcycle, hpedge⟩ :=
    SimpleGraph.exists_isCycle_containing_of_even_degree_of_adj
      (boundaryGraph M) (even_degree_boundaryGraph M) hvw
  let hle := boundaryGraph_le_vertexGraph M
  let q := p.mapLe hle
  have hq : q.IsCycle := hpcycle.mapLe hle
  let P := polygonalCircleOfBoundaryCycle M p hpcycle
  refine ⟨P, ?_, polygonalCircleOfBoundaryCycle_carrier_subset_boundaryCarrier M p hpcycle,
    ?_⟩
  have hpedgeq : s(v, w) ∈ q.edges := by
    change s(v, w) ∈ (p.mapLe hle).edges
    rwa [SimpleGraph.Walk.edges_mapLe_eq_edges]
  have hsegment :=
    Schoenflies.TriangleMesh.PlaneComplex.segment_subset_range_walkGeometricPath_of_mem_edges
      M.toPlaneComplex q hpedgeq
  rw [← M.toPlaneComplex.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath q hq]
    at hsegment
  change segment ℝ (M.position v) (M.position w) ⊆
    (M.toPlaneComplex.polygonalCircleOfCycle q hq).carrier
  exact hsegment
  · intro i
    refine ⟨q.getVert i.val, ?_⟩
    rfl

/-- Every particular incidence-one edge is carried by a polygonal boundary
circle, not merely some circle in the same boundary component. -/
theorem exists_polygonalCircle_containing_boundaryEdge
    (M : TriangleMesh) {v w : M.Vertex}
    (hvw : (boundaryGraph M).Adj v w) :
    ∃ P : PolygonalCircle,
      segment ℝ (M.position v) (M.position w) ⊆ P.carrier ∧
        P.carrier ⊆ M.boundaryCarrier := by
  obtain ⟨P, hedge, hboundary, -⟩ :=
    exists_polygonalCircle_containing_boundaryEdge_with_vertices M hvw
  exact ⟨P, hedge, hboundary⟩

/-- The entire mesh boundary is pointwise covered by polygonal circles carried
by that boundary.  This is the finite cycle-decomposition fact needed before
one uses Jordan separation to identify the exterior-facing member. -/
theorem exists_polygonalCircle_of_mem_boundaryCarrier
    (M : TriangleMesh) {x : Plane} (hx : x ∈ M.boundaryCarrier) :
    ∃ P : PolygonalCircle, x ∈ P.carrier ∧
      P.carrier ⊆ M.boundaryCarrier := by
  classical
  rw [TriangleMesh.boundaryCarrier] at hx
  obtain ⟨e, heall, hxe⟩ := Set.mem_iUnion₂.mp hx
  have he : M.IsBoundaryEdge e := M.mem_allBoundaryEdges_iff.mp heall
  have hecard : e.card = 2 := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  have hadj : (boundaryGraph M).Adj v w := by
    rw [boundaryGraph_adj_iff]
    exact he
  obtain ⟨P, hedgeP, hPboundary⟩ :=
    Schoenflies.TriangleMesh.exists_polygonalCircle_containing_boundaryEdge M hadj
  refine ⟨P, hedgeP ?_, hPboundary⟩
  have himage : M.position ''
      (({v, w} : Finset M.Vertex) : Set M.Vertex) =
      {M.position v, M.position w} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair] at hxe
  exact hxe

/-- A nonempty mesh therefore has an honest polygonal circle carried by
its incidence-one boundary edges. -/
theorem exists_polygonalCircle_carrier_subset_boundaryCarrier
    (M : TriangleMesh) (hne : M.triangles.Nonempty) :
    ∃ P : PolygonalCircle, P.carrier ⊆ M.boundaryCarrier := by
  classical
  obtain ⟨v, w, hvw⟩ := exists_boundaryGraph_adj M hne
  obtain ⟨u, p, hp⟩ :=
    SimpleGraph.exists_isCycle_of_even_degree_of_adj
      (boundaryGraph M) (even_degree_boundaryGraph M) hvw
  let hle := boundaryGraph_le_vertexGraph M
  let q := p.mapLe hle
  have hq : q.IsCycle := hp.mapLe hle
  let P : PolygonalCircle := M.toPlaneComplex.polygonalCircleOfCycle q hq
  refine ⟨P, ?_⟩
  intro x hx
  have hxrange : x ∈ Set.range (M.toPlaneComplex.walkGeometricPath q) := by
    rw [← M.toPlaneComplex.polygonalCircleOfCycle_carrier_eq_range_walkGeometricPath q hq]
    exact hx
  have hqpos : 0 < q.length := lt_of_lt_of_le (by omega) hq.three_le_length
  obtain ⟨i, hi⟩ :=
    M.toPlaneComplex.exists_walkSegment_of_mem_range q hqpos hxrange
  have hlen : p.length = q.length := by
    exact (SimpleGraph.Walk.length_map (SimpleGraph.Hom.ofLE hle) p).symm
  have hij : i.val < p.length := by
    rw [hlen]
    exact i.isLt
  let j : Fin p.length := ⟨i.val, hij⟩
  have hpedge : (boundaryGraph M).Adj
      (p.getVert j.val) (p.getVert (j.val + 1)) :=
    p.adj_getVert_succ j.isLt
  have hboundary : M.IsBoundaryEdge
      ({p.getVert j.val, p.getVert (j.val + 1)} : Finset M.Vertex) :=
    (boundaryGraph_adj_iff M).mp hpedge
  have hi' : x ∈ segment ℝ
      (M.position (p.getVert j.val))
      (M.position (p.getVert (j.val + 1))) := by
    have hpos : M.toPlaneComplex.position = M.position := by rfl
    have hget (n : ℕ) : q.getVert n = p.getVert n := by
      calc
        q.getVert n = (SimpleGraph.Hom.ofLE hle) (p.getVert n) := by
          exact SimpleGraph.Walk.getVert_map (SimpleGraph.Hom.ofLE hle) p n
        _ = p.getVert n := rfl
    rw [hpos] at hi
    have hget0 := congrArg M.position (hget i.val)
    have hget1 := congrArg M.position (hget (i.val + 1))
    have hseg : segment ℝ (M.position (q.getVert i.val))
        (M.position (q.getVert (i.val + 1))) =
        segment ℝ (M.position (p.getVert i.val))
          (M.position (p.getVert (i.val + 1))) :=
      congrArg₂ (segment ℝ) hget0 hget1
    have hiP : x ∈ segment ℝ (M.position (p.getVert i.val))
        (M.position (p.getVert (i.val + 1))) := hseg ▸ hi
    simpa only [j] using hiP
  rw [TriangleMesh.boundaryCarrier]
  apply Set.mem_iUnion.mpr
  refine ⟨{p.getVert j.val, p.getVert (j.val + 1)}, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨M.mem_allBoundaryEdges_iff.mpr hboundary, ?_⟩
  have himage : M.position ''
      (({p.getVert j.val, p.getVert (j.val + 1)} : Finset M.Vertex) : Set M.Vertex) =
      {M.position (p.getVert j.val), M.position (p.getVert (j.val + 1))} := by
    ext y
    simp [eq_comm]
  rw [himage, convexHull_pair]
  exact hi'

/-- A nonempty finite triangle mesh has a horizontal slice, avoiding every
mesh vertex height, whose leftmost support point lies on the frontier.  The
generic height is obtained from any polygonal boundary cycle; compactness of
the mesh then supplies the leftmost point. -/
theorem exists_leftmost_frontier_at_generic_height
    (M : TriangleMesh) (hne : M.triangles.Nonempty) :
    ∃ (y : ℝ) (q : Plane),
      q ∈ frontier M.toPlaneComplex.support ∧
        (∀ v : M.Vertex, y ≠ (M.position v) 1) ∧ q 1 = y ∧
          ∀ z ∈ M.toPlaneComplex.support, z 1 = y → q 0 ≤ z 0 := by
  classical
  obtain ⟨P₀, hP₀boundary⟩ :=
    exists_polygonalCircle_carrier_subset_boundaryCarrier M hne
  obtain ⟨i₀, hi₀⟩ := P₀.exists_nonhorizontal_edge
  let vertexHeights : Finset ℝ :=
    Finset.univ.image fun v : M.Vertex => (M.position v) 1
  have hinterval :
      min ((P₀.vertex i₀) 1) ((P₀.vertex (i₀ + 1)) 1) <
        max ((P₀.vertex i₀) 1) ((P₀.vertex (i₀ + 1)) 1) :=
    min_lt_max.mpr hi₀
  obtain ⟨y, hy, hynot⟩ :=
    (Set.Ioo_infinite hinterval).exists_notMem_finset vertexHeights
  have hyne : ∀ v : M.Vertex, y ≠ (M.position v) 1 := by
    intro v heq
    apply hynot
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, heq.symm⟩
  have hyband :
      ((P₀.vertex i₀) 1 < y ∧ y < (P₀.vertex (i₀ + 1)) 1) ∨
        ((P₀.vertex (i₀ + 1)) 1 < y ∧ y < (P₀.vertex i₀) 1) := by
    rcases lt_or_gt_of_ne hi₀ with hlt | hgt
    · left
      simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hy
    · right
      simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hy
  let q₀ : Plane := planePoint
    (PolygonalCircle.crossingX
      (P₀.vertex i₀) (P₀.vertex (i₀ + 1)) y) y
  have hq₀edge : q₀ ∈ P₀.edgeSegment i₀ := by
    apply P₀.mem_edgeSegment_of_crossing (P := q₀) i₀
    · rcases hyband with hyband | hyband
      · exact Or.inl ⟨hyband.1.le, hyband.2⟩
      · exact Or.inr ⟨hyband.1.le, hyband.2⟩
    · rfl
  have hq₀boundary : q₀ ∈ M.boundaryCarrier :=
    hP₀boundary (P₀.edgeSegment_subset_carrier i₀ hq₀edge)
  have hq₀support : q₀ ∈ M.toPlaneComplex.support :=
    M.toPlaneComplex.isCompact_support.isClosed.frontier_subset
      (M.boundaryCarrier_subset_frontier hq₀boundary)
  let slice : Set Plane :=
    M.toPlaneComplex.support ∩ {p : Plane | p 1 = y}
  have hlevelClosed : IsClosed {p : Plane | p 1 = y} :=
    isClosed_eq (PolygonalCircle.continuous_coord 1) continuous_const
  have hsliceCompact : IsCompact slice :=
    M.toPlaneComplex.isCompact_support.inter_right hlevelClosed
  have hq₀slice : q₀ ∈ slice := ⟨hq₀support, rfl⟩
  obtain ⟨q, hqslice, hqmin⟩ :=
    hsliceCompact.exists_isMinOn ⟨q₀, hq₀slice⟩
      (PolygonalCircle.continuous_coord 0).continuousOn
  have hqSupport : q ∈ M.toPlaneComplex.support := hqslice.1
  have hqHeight : q 1 = y := hqslice.2
  have hqFrontier : q ∈ frontier M.toPlaneComplex.support := by
    apply (mem_frontier_iff_notMem_interior hqSupport).mpr
    intro hqInterior
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hqInterior)
    let q' : Plane := planePoint (q 0 - r / 2) y
    have hq'ball : q' ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q' - q = planePoint (-r / 2) 0 by
        apply plane_ext <;> simp [q', hqHeight] <;> ring]
      simp [planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two]
      rw [Real.sqrt_sq_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hr) (by norm_num))]
      linarith
    have hq'Support : q' ∈ M.toPlaneComplex.support := hball hq'ball
    have hq'Slice : q' ∈ slice := ⟨hq'Support, rfl⟩
    have hmin := hqmin hq'Slice
    change q 0 ≤ q' 0 at hmin
    dsimp [q'] at hmin
    linarith
  exact ⟨y, q, hqFrontier, hyne, hqHeight, fun z hz hzy =>
    hqmin ⟨hz, hzy⟩⟩

/-- At the generic leftmost frontier point, the unique incident triangle
opens to the right.  Hence a point of the mesh interior occurs at the same
height immediately to the right, and the open segment from the frontier point
to that interior point stays in the mesh interior. -/
theorem exists_interior_point_to_right_of_leftmost_frontier
    (M : TriangleMesh) {y : ℝ} {q : Plane}
    (hqFrontier : q ∈ frontier M.toPlaneComplex.support)
    (hyne : ∀ v : M.Vertex, y ≠ (M.position v) 1)
    (hqHeight : q 1 = y)
    (hqmin : ∀ z ∈ M.toPlaneComplex.support, z 1 = y → q 0 ≤ z 0) :
    ∃ x : Plane, x ∈ interior M.toPlaneComplex.support ∧
      x 1 = y ∧ q 0 < x 0 ∧
        openSegment ℝ q x ⊆ interior M.toPlaneComplex.support := by
  classical
  have hqv : ∀ v : M.Vertex, q ≠ M.position v := by
    intro v hqv
    apply hyne v
    rw [← hqHeight, hqv]
  obtain ⟨e, he, hqe⟩ :=
    (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hqv).mp hqFrontier
  have hecard : e.card = 2 := M.card_of_mem_edges he.1
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hecard
  obtain ⟨t, ht, hetPower⟩ := Finset.mem_biUnion.mp he.1
  have hetData := Finset.mem_powersetCard.mp hetPower
  let T : M.Triangle := ⟨t, ht⟩
  obtain ⟨k, hedge⟩ := M.exists_oppositeEdgePoints_eq T hetData.1 hetData.2
  let pa : Plane := M.position a
  let pb : Plane := M.position b
  have hedge' : M.oppositeEdgePoints T k = {pa, pb} := by
    simpa [pa, pb] using hedge
  have hqEdge : q ∈ convexHull ℝ
      ((M.oppositeEdgePoints T k : Finset Plane) : Set Plane) := by
    rw [hedge, Finset.coe_image]
    exact hqe
  have hpaEdge : pa ∈ M.oppositeEdgePoints T k := by
    rw [hedge']
    simp
  have hpbEdge : pb ∈ M.oppositeEdgePoints T k := by
    rw [hedge']
    simp
  have hpaCoord : M.oppositeCoord T k pa = 0 :=
    M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k
      (subset_convexHull ℝ _ hpaEdge)
  have hpbCoord : M.oppositeCoord T k pb = 0 :=
    M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k
      (subset_convexHull ℝ _ hpbEdge)
  have hqCoord : M.oppositeCoord T k q = 0 :=
    M.oppositeCoord_eq_zero_of_mem_oppositeEdge T k hqEdge
  have hqTriangle : q ∈ M.triangleCarrier T.1 :=
    convexHull_mono (Set.image_mono hetData.1) hqe
  have hpabHeight : pa 1 ≠ pb 1 := by
    intro heq
    have himage : M.position ''
        (({a, b} : Finset M.Vertex) : Set M.Vertex) = {pa, pb} := by
      ext w
      simp [pa, pb, eq_comm]
    have hqe' : q ∈ segment ℝ pa pb := by
      rw [← convexHull_pair, ← himage]
      exact hqe
    rcases hqe' with ⟨c, d, hc, hd, hcd, hqeq⟩
    have hqy : q 1 = pa 1 := by
      calc
        q 1 = (c • pa + d • pb) 1 := congrArg (fun w : Plane => w 1) hqeq.symm
        _ = c * pa 1 + d * pb 1 := by
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        _ = (c + d) * pb 1 := by rw [heq]; ring
        _ = pa 1 := by rw [hcd, one_mul, heq]
    exact hyne a (hqHeight.symm.trans hqy)
  have hqN : q ∈ M.nonOppositeCoordNeighborhood T k := by
    apply M.mem_nonOppositeCoordNeighborhood_of_mem_edge T k hqEdge
    intro i
    exact hqv (M.orderedVertex T i)
  let u : Plane := M.position (M.orderedVertex T k)
  let lam : ℝ := (q 1 - u 1) / (pb 1 - pa 1)
  let z : Plane := lam • (pb - pa) + u
  have hzHeight : z 1 = q 1 := by
    dsimp [z, lam]
    field_simp [sub_ne_zero.mpr hpabHeight.symm]
    ring
  have huCoord : M.oppositeCoord T k u = 1 := by
    change M.oppositeCoord T k (M.position (M.orderedVertex T k)) = 1
    rw [M.oppositeCoord_vertex]
    simp
  have hzCoord : M.oppositeCoord T k z = 1 := by
    change M.oppositeCoord T k (lam • (pb - pa) +ᵥ u) = 1
    rw [(M.oppositeCoord T k).map_vadd, map_smul,
      show pb - pa = pb -ᵥ pa by rfl,
      (M.oppositeCoord T k).linearMap_vsub, hpbCoord, hpaCoord,
      vsub_self, smul_zero, zero_vadd, huCoord]
  let γ : ℝ → Plane := fun s => AffineMap.lineMap q z s
  have hγcont : Continuous γ := by fun_prop
  have hopen : IsOpen (γ ⁻¹' M.nonOppositeCoordNeighborhood T k) :=
    (M.isOpen_nonOppositeCoordNeighborhood T k).preimage hγcont
  have hzero : (0 : ℝ) ∈ γ ⁻¹' M.nonOppositeCoordNeighborhood T k := by
    simpa [γ] using hqN
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  let s : ℝ := min (ε / 2) (1 / 2)
  have hspos : 0 < s := by
    apply lt_min
    · linarith
    · norm_num
  have hslt : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hsle : s ≤ ε / 2 := min_le_left _ _
    rw [sub_zero, abs_of_pos hspos]
    linarith
  let x : Plane := γ s
  have hxN : x ∈ M.nonOppositeCoordNeighborhood T k := hball hsball
  have hxHeight : x 1 = y := by
    dsimp [x, γ]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
    rw [hzHeight, hqHeight]
    ring
  have hxCoord : M.oppositeCoord T k x = s := by
    dsimp [x, γ]
    rw [(M.oppositeCoord T k).apply_lineMap, hqCoord, hzCoord,
      AffineMap.lineMap_apply_module]
    ring
  have hxTriangleInterior : x ∈ interior (M.triangleCarrier T.1) := by
    rw [M.interior_triangleCarrier T]
    intro i
    by_cases hik : i = k
    · subst i
      rw [hxCoord]
      exact hspos
    · exact hxN i hik
  have htriangleSupport : M.triangleCarrier T.1 ⊆
      M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hxInterior : x ∈ interior M.toPlaneComplex.support :=
    interior_mono htriangleSupport hxTriangleInterior
  have hxSupport : x ∈ M.toPlaneComplex.support := interior_subset hxInterior
  have hqxle : q 0 ≤ x 0 := hqmin x hxSupport hxHeight
  have hqxne : q 0 ≠ x 0 := by
    intro hcoord
    have hqx : q = x := plane_ext hcoord (hqHeight.trans hxHeight.symm)
    exact Set.disjoint_left.mp disjoint_interior_frontier hxInterior
      (hqx ▸ hqFrontier)
  have hqx : q 0 < x 0 := lt_of_le_of_ne hqxle hqxne
  have hopenSegment : openSegment ℝ q x ⊆
      interior M.toPlaneComplex.support :=
    ((convex_convexHull ℝ _).openSegment_self_interior_subset_interior
      hqTriangle hxTriangleInterior).trans (interior_mono htriangleSupport)
  exact ⟨x, hxInterior, hxHeight, hqx, hopenSegment⟩

/-- Some polygonal boundary cycle of a nonempty finite mesh has its bounded
side meeting the mesh interior.  This is the exterior-facing cycle: the proof
takes the cycle through the leftmost edge of a generic horizontal slice and
computes index one immediately on the mesh side of that edge. -/
theorem exists_boundaryPolygonalCircle_meeting_interiorRegion
    (M : TriangleMesh) (hne : M.triangles.Nonempty) :
    ∃ P : PolygonalCircle, P.carrier ⊆ M.boundaryCarrier ∧
      (P.interiorRegion ∩ interior M.toPlaneComplex.support).Nonempty := by
  classical
  obtain ⟨y, q, hqFrontier, hyne, hqHeight, hqmin⟩ :=
    exists_leftmost_frontier_at_generic_height M hne
  obtain ⟨x, hxInterior, hxHeight, hqx, hopenSegment⟩ :=
    exists_interior_point_to_right_of_leftmost_frontier M
      hqFrontier hyne hqHeight hqmin
  have hqv : ∀ v : M.Vertex, q ≠ M.position v := by
    intro v hqv
    apply hyne v
    rw [← hqHeight, hqv]
  obtain ⟨e, he, hqe⟩ :=
    (M.mem_frontier_iff_exists_boundaryEdge_of_nonvertex hqv).mp hqFrontier
  have hecard : e.card = 2 := M.card_of_mem_edges he.1
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hecard
  have hadj : (boundaryGraph M).Adj v w :=
    (boundaryGraph_adj_iff M).mpr he
  obtain ⟨P, hedgeP, hPboundary, hPvertices⟩ :=
    exists_polygonalCircle_containing_boundaryEdge_with_vertices M hadj
  have himage : M.position ''
      (({v, w} : Finset M.Vertex) : Set M.Vertex) =
        {M.position v, M.position w} := by
    ext z
    simp [eq_comm]
  have hqP : q ∈ P.carrier := by
    apply hedgeP
    rw [← convexHull_pair, ← himage]
    exact hqe
  have hheight : ∀ i : ZMod P.n, q 1 ≠ (P.vertex i) 1 := by
    intro i hqi
    obtain ⟨v, hv⟩ := hPvertices i
    apply hyne v
    calc
      y = q 1 := hqHeight.symm
      _ = (P.vertex i) 1 := hqi
      _ = (M.position v) 1 := congrArg (fun z : Plane => z 1) hv.symm
  have hxNotCarrier : x ∉ P.carrier := by
    intro hxP
    have hxFrontier : x ∈ frontier M.toPlaneComplex.support :=
      M.boundaryCarrier_subset_frontier (hPboundary hxP)
    exact Set.disjoint_left.mp disjoint_interior_frontier hxInterior hxFrontier
  have hbetween : ∀ z : Plane, z ∈ P.carrier → z 1 = q 1 →
      z 0 < x 0 → z = q := by
    intro z hzP hzHeight hzLeft
    have hzFrontier : z ∈ frontier M.toPlaneComplex.support :=
      M.boundaryCarrier_subset_frontier (hPboundary hzP)
    have hzSupport : z ∈ M.toPlaneComplex.support :=
      M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hzFrontier
    have hzY : z 1 = y := hzHeight.trans hqHeight
    have hqzle : q 0 ≤ z 0 := hqmin z hzSupport hzY
    rcases eq_or_lt_of_le hqzle with hqz | hqz
    · exact plane_ext hqz.symm hzHeight
    · have hzSegment : z ∈ segment ℝ q x :=
        PolygonalCircle.mem_segment_of_horizontal
          (P := z) hzHeight.symm (hxHeight.trans hzY.symm) hqz.le hzLeft.le
      have hzOpen : z ∈ openSegment ℝ q x := by
        have hsbtw : Sbtw ℝ q z x :=
          ⟨mem_segment_iff_wbtw.mp hzSegment,
            fun hzq => hqz.ne (congrArg (fun p : Plane => p 0) hzq).symm,
            fun hzx => hzLeft.ne (congrArg (fun p : Plane => p 0) hzx)⟩
        rw [openSegment_eq_image_lineMap]
        exact hsbtw.mem_image_Ioo
      have hzInterior : z ∈ interior M.toPlaneComplex.support :=
        hopenSegment hzOpen
      exact (Set.disjoint_left.mp disjoint_interior_frontier
        hzInterior hzFrontier).elim
  have hxIndex : P.index x = 1 :=
    Schoenflies.PolygonalCircle.index_eq_one_of_unique_left_crossing P hqP hheight
      (hxHeight.trans hqHeight.symm) hqx hbetween
  have hxInside : x ∈ P.interiorRegion := by
    rw [P.interiorRegion_eq_indexRegion_one]
    exact ⟨hxNotCarrier, hxIndex⟩
  exact ⟨P, hPboundary, x, hxInside, hxInterior⟩

end TriangleMesh

end Schoenflies
