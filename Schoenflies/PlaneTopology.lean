import Schoenflies.JordanRegions
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Small planar connectivity lemmas

Local separation arguments for finite polygonal boundaries repeatedly use
that deleting the centre from a plane ball does not disconnect it.
-/

namespace Schoenflies

open Metric Set

/-- A convenient homeomorphism from the plane onto an arbitrary nonempty
open ball, normalized to send the origin to the centre. -/
noncomputable def planeHomeomorphBall (p : Plane) (r : ℝ) (hr : 0 < r) :
    Plane ≃ₜ ball p r := by
  let b := OpenPartialHomeomorph.univBall p r
  exact (Homeomorph.Set.univ _).symm |>.trans
    ((Homeomorph.setCongr
        (OpenPartialHomeomorph.univBall_source p r).symm).trans
      (b.toHomeomorphSourceTarget.trans
        (Homeomorph.setCongr
          (OpenPartialHomeomorph.univBall_target p hr))))

@[simp] theorem planeHomeomorphBall_zero (p : Plane) (r : ℝ) (hr : 0 < r) :
    ((planeHomeomorphBall p r hr 0 : ball p r) : Plane) = p := by
  change OpenPartialHomeomorph.univBall p r 0 = p
  exact OpenPartialHomeomorph.univBall_apply_zero p r

/-- A punctured open ball in the plane is connected. -/
theorem isConnected_ball_diff_singleton (p : Plane) {r : ℝ} (hr : 0 < r) :
    IsConnected (ball p r \ {p}) := by
  let e := planeHomeomorphBall p r hr
  have he0 : ((e 0 : ball p r) : Plane) = p :=
    planeHomeomorphBall_zero p r hr
  have himage : e '' ({0}ᶜ : Set Plane) =
      {q : ball p r | (q : Plane) ≠ p} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro heq
      apply hx
      apply e.injective
      apply Subtype.ext
      exact heq.trans he0.symm
    · intro hq
      let x := e.symm q
      have hxe := e.apply_symm_apply q
      refine ⟨x, ?_, hxe⟩
      intro hx
      apply hq
      rw [← hxe]
      change ((e x : ball p r) : Plane) = p
      have hx0 : x = 0 := by simpa using hx
      rw [hx0]
      exact he0
  have hsource : IsConnected ({0}ᶜ : Set Plane) :=
    (isPathConnected_compl_singleton_of_one_lt_rank (by
      apply Module.one_lt_rank_of_one_lt_finrank
      simp [Plane]) 0).isConnected
  have hsub : IsConnected {q : ball p r | (q : Plane) ≠ p} := by
    rw [← himage]
    exact (e.isConnected_image).2 hsource
  have hval := hsub.image ((↑) : ball p r → Plane)
    continuous_subtype_val.continuousOn
  have hvalImage : ((↑) : ball p r → Plane) ''
      {q : ball p r | (q : Plane) ≠ p} = ball p r \ {p} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, by simpa using hq⟩
    · rintro ⟨hxball, hxne⟩
      exact ⟨⟨x, hxball⟩, by simpa using hxne, rfl⟩
  rwa [hvalImage] at hval

/-- The frontier of a regular closed planar set has no finite collection of
locally isolated points.  Equivalently, deleting any finite set from the
frontier leaves a dense subset of the frontier. -/
theorem frontier_subset_closure_sdiff_finite_of_regularClosed
    {S F : Set Plane} (hSclosed : IsClosed S)
    (hregular : closure (interior S) = S) (hF : F.Finite) :
    frontier S ⊆ closure (frontier S \ F) := by
  intro x hxFrontier
  rw [_root_.mem_closure_iff]
  intro O hOopen hxO
  let F' : Set Plane := F \ {x}
  have hF'finite : F'.Finite := hF.sdiff
  have hF'closed : IsClosed F' := hF'finite.isClosed
  have hxF' : x ∉ F' := by simp [F']
  let V : Set Plane := O ∩ F'ᶜ
  have hVopen : IsOpen V := hOopen.inter hF'closed.isOpen_compl
  have hxV : x ∈ V := ⟨hxO, hxF'⟩
  obtain ⟨ε, hε, hballV⟩ := (Metric.isOpen_iff.mp hVopen) x hxV
  have hballO : ball x ε ⊆ O := hballV.trans inter_subset_left
  have hballAvoid : ball x ε ∩ F ⊆ {x} := by
    rintro y ⟨hyBall, hyF⟩
    by_contra hyx
    have hyF' : y ∈ F' := ⟨hyF, by simpa [Set.mem_singleton_iff] using hyx⟩
    exact (hballV hyBall).2 hyF'
  by_contra hmeet
  have hpuncturedAvoid : ball x ε \ {x} ⊆ (frontier S)ᶜ := by
    rintro y ⟨hyBall, hyx⟩ hyFrontier
    have hyNotF : y ∉ F := by
      intro hyF
      have hySingleton := hballAvoid ⟨hyBall, hyF⟩
      exact hyx hySingleton
    exact hmeet ⟨y, hballO hyBall, hyFrontier, hyNotF⟩
  have hxS : x ∈ S := hSclosed.frontier_subset hxFrontier
  have hxClosureInterior : x ∈ closure (interior S) := by
    rw [hregular]
    exact hxS
  obtain ⟨a, haBall, haInterior⟩ :=
    (_root_.mem_closure_iff.mp hxClosureInterior) (ball x ε)
      isOpen_ball (mem_ball_self hε)
  have hax : a ≠ x := by
    intro hax
    subst a
    exact Set.disjoint_left.mp disjoint_interior_frontier haInterior hxFrontier
  have haPunctured : a ∈ ball x ε \ {x} :=
    ⟨haBall, by simpa [Set.mem_singleton_iff] using hax⟩
  have hxClosureCompl : x ∈ closure Sᶜ := by
    rw [frontier_eq_closure_inter_closure] at hxFrontier
    exact hxFrontier.2
  obtain ⟨b, hbBall, hbCompl⟩ :=
    (_root_.mem_closure_iff.mp hxClosureCompl) (ball x ε)
      isOpen_ball (mem_ball_self hε)
  have hbx : b ≠ x := by
    intro hbx
    subst b
    exact hbCompl hxS
  have hbPunctured : b ∈ ball x ε \ {x} :=
    ⟨hbBall, by simpa [Set.mem_singleton_iff] using hbx⟩
  have hbInteriorCompl : b ∈ interior Sᶜ := by
    rwa [hSclosed.isOpen_compl.interior_eq]
  have hcover : ball x ε \ {x} ⊆ interior S ∪ interior Sᶜ := by
    intro y hy
    rw [← compl_frontier_eq_union_interior]
    exact hpuncturedAvoid hy
  have hdisjoint : Disjoint (interior S) (interior Sᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  have hallInterior : ball x ε \ {x} ⊆ interior S :=
    (isConnected_ball_diff_singleton x hε).isPreconnected
      |>.subset_left_of_subset_union isOpen_interior isOpen_interior
        hdisjoint hcover ⟨a, haPunctured, haInterior⟩
  exact Set.disjoint_left.mp hdisjoint (hallInterior hbPunctured) hbInteriorCompl

end Schoenflies
