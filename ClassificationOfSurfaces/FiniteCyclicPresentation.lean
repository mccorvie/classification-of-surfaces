/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.SignedPresentation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Count

/-!
# Finite cyclic surface presentations

This file packages the purely combinatorial data used by polygon-word moves. Edge names and faces
are finite by construction, and a face boundary is a cyclic list of signed edge names. Unlike
`SurfaceCellComplex`, this presentation has no arbitrary vertex labels or placeholder realization.

`EdgeRelabeling` records an equivalence of edge names together with an independent orientation
reversal for each source edge. `SignedPresentationIso` combines such a relabeling with an
equivalence of faces and a rotation witness for every renamed face boundary. The original
orientation-preserving `PresentationIso` remains available as a compatible special case.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open scoped BigOperators

/-- A finite list of cyclic signed boundary words with edge names in `Fin edgeCount`. -/
structure FiniteCyclicPresentation where
  edgeCount : ℕ
  faces : List (List (SurfaceCellComplex.SignedDart (Fin edgeCount)))

namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- The finite type of unoriented edge names. -/
abbrev Edge (P : FiniteCyclicPresentation) :=
  Fin P.edgeCount

/-- Signed occurrences of unoriented edge names. -/
abbrev Dart (P : FiniteCyclicPresentation) :=
  SignedDart P.Edge

/-- Faces are positions in the stored list of boundary words. -/
abbrev Face (P : FiniteCyclicPresentation) :=
  Fin P.faces.length

/-- The stored cyclic boundary word of a face. -/
def boundary (P : FiniteCyclicPresentation) (f : P.Face) : List P.Dart :=
  P.faces.get f

/-- Forget the orientation of a signed edge occurrence. -/
def edgeOfDart {α : Type*} : SignedDart α → α
  | .pos e => e
  | .neg e => e

/-- A relabeling of unoriented edges with an independent orientation reversal for each source
edge. -/
structure EdgeRelabeling (α β : Type*) where
  edgeEquiv : α ≃ β
  reverse : α → Bool

namespace EdgeRelabeling

/-- Apply an edge relabeling to a signed dart. -/
def mapDart {α β : Type*} (e : EdgeRelabeling α β) : SignedDart α → SignedDart β
  | .pos a =>
      if e.reverse a then
        .neg (e.edgeEquiv a)
      else
        .pos (e.edgeEquiv a)
  | .neg a =>
      if e.reverse a then
        .pos (e.edgeEquiv a)
      else
        .neg (e.edgeEquiv a)

/-- The identity signed-edge relabeling. -/
def refl (α : Type*) : EdgeRelabeling α α where
  edgeEquiv := Equiv.refl α
  reverse := fun _ ↦ false

/-- Reverse a signed-edge relabeling. -/
def symm {α β : Type*} (e : EdgeRelabeling α β) : EdgeRelabeling β α where
  edgeEquiv := e.edgeEquiv.symm
  reverse := fun b ↦ e.reverse (e.edgeEquiv.symm b)

/-- Compose signed-edge relabelings. Reversing twice cancels, so the reversal bits compose by
exclusive-or. -/
def trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) : EdgeRelabeling α γ where
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  reverse := fun a ↦ Bool.xor (e.reverse a) (f.reverse (e.edgeEquiv a))

/-- An ordinary edge equivalence, viewed as a relabeling that preserves every chosen
orientation. -/
def ofEquiv {α β : Type*} (e : α ≃ β) : EdgeRelabeling α β where
  edgeEquiv := e
  reverse := fun _ ↦ false

@[simp]
theorem mapDart_refl {α : Type*} (d : SignedDart α) :
    (refl α).mapDart d = d := by
  cases d <;> rfl

@[simp]
theorem mapDart_symm_apply {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.symm.mapDart (e.mapDart d) = d := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, symm, h]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, symm, h]

@[simp]
theorem mapDart_apply_symm {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart β) :
    e.mapDart (e.symm.mapDart d) = d := by
  cases d with
  | pos b =>
      cases h : e.reverse (e.edgeEquiv.symm b) <;>
        simp [mapDart, symm, h]
  | neg b =>
      cases h : e.reverse (e.edgeEquiv.symm b) <;>
        simp [mapDart, symm, h]

/-- A signed-edge relabeling is an equivalence on darts. -/
def dartEquiv {α β : Type*} (e : EdgeRelabeling α β) :
    SignedDart α ≃ SignedDart β where
  toFun := e.mapDart
  invFun := e.symm.mapDart
  left_inv := e.mapDart_symm_apply
  right_inv := e.mapDart_apply_symm

@[simp]
theorem dartEquiv_apply {α β : Type*} (e : EdgeRelabeling α β) (d : SignedDart α) :
    e.dartEquiv d = e.mapDart d :=
  rfl

@[simp]
theorem edgeOfDart_mapDart {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    edgeOfDart (e.mapDart d) = e.edgeEquiv (edgeOfDart d) := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, h, edgeOfDart]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, h, edgeOfDart]

@[simp]
theorem edgeOfDart_dartEquiv {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    edgeOfDart (e.dartEquiv d) = e.edgeEquiv (edgeOfDart d) :=
  e.edgeOfDart_mapDart d

@[simp]
theorem mapDart_flip {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.mapDart d.flip = (e.mapDart d).flip := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, SignedDart.flip, h]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, SignedDart.flip, h]

@[simp]
theorem dartEquiv_flip {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.dartEquiv d.flip = (e.dartEquiv d).flip :=
  e.mapDart_flip d

@[simp]
theorem mapDart_trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) (d : SignedDart α) :
    (e.trans f).mapDart d = f.mapDart (e.mapDart d) := by
  cases d with
  | pos a =>
      cases h₁ : e.reverse a <;>
        cases h₂ : f.reverse (e.edgeEquiv a) <;>
          simp [mapDart, trans, h₁, h₂]
  | neg a =>
      cases h₁ : e.reverse a <;>
        cases h₂ : f.reverse (e.edgeEquiv a) <;>
          simp [mapDart, trans, h₁, h₂]

@[simp]
theorem mapDart_ofEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    (ofEquiv e).mapDart d = SignedDart.mapEquiv e d := by
  cases d <;> rfl

@[simp]
theorem map_mapDart_ofEquiv {α β : Type*} (e : α ≃ β) (l : List (SignedDart α)) :
    l.map (ofEquiv e).mapDart = l.map (SignedDart.mapEquiv e) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_ofEquiv, ih]

@[simp]
theorem map_mapDart_refl {α : Type*} (l : List (SignedDart α)) :
    l.map (refl α).mapDart = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_refl, ih]

@[simp]
theorem map_mapDart_symm {α β : Type*}
    (e : EdgeRelabeling α β) (l : List (SignedDart α)) :
    (l.map e.mapDart).map e.symm.mapDart = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_symm_apply, ih]

theorem map_mapDart_trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) (l : List (SignedDart α)) :
    l.map (e.trans f).mapDart = (l.map e.mapDart).map f.mapDart := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_trans, ih]

end EdgeRelabeling

@[simp]
theorem edgeOfDart_mapEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    edgeOfDart (SignedDart.mapEquiv e d) = e (edgeOfDart d) := by
  cases d <;> rfl

@[simp]
theorem mapEquiv_refl {α : Type*} (d : SignedDart α) :
    SignedDart.mapEquiv (Equiv.refl α) d = d := by
  cases d <;> rfl

@[simp]
theorem mapEquiv_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (d : SignedDart α) :
    SignedDart.mapEquiv (e.trans f) d =
      SignedDart.mapEquiv f (SignedDart.mapEquiv e d) := by
  cases d <;> rfl

@[simp]
theorem mapEquiv_symm_apply {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    SignedDart.mapEquiv e.symm (SignedDart.mapEquiv e d) = d := by
  cases d <;> simp [SignedDart.mapEquiv]

@[simp]
theorem map_mapEquiv_refl {α : Type*} (l : List (SignedDart α)) :
    l.map (SignedDart.mapEquiv (Equiv.refl α)) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_refl, ih]

@[simp]
theorem map_mapEquiv_symm {α β : Type*} (e : α ≃ β) (l : List (SignedDart α)) :
    (l.map (SignedDart.mapEquiv e)).map (SignedDart.mapEquiv e.symm) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_symm_apply, ih]

theorem map_mapEquiv_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (l : List (SignedDart α)) :
    l.map (SignedDart.mapEquiv (e.trans f)) =
      (l.map (SignedDart.mapEquiv e)).map (SignedDart.mapEquiv f) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_trans, ih]

/-- Multiplicity of an edge in one face boundary. -/
def faceEdgeMultiplicity (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) : ℕ :=
  ((P.boundary f).map edgeOfDart).count e

/-- Total number of boundary occurrences of an unoriented edge. -/
def edgeMultiplicity (P : FiniteCyclicPresentation) (e : P.Edge) : ℕ :=
  ∑ f : P.Face, P.faceEdgeMultiplicity f e

/-- An edge is a boundary edge when it occurs in exactly one face boundary position. -/
def IsBoundaryEdge (P : FiniteCyclicPresentation) (e : P.Edge) : Prop :=
  P.edgeMultiplicity e = 1

/-- Incidence validity for a finite cyclic presentation.

There is at least one face, every face has a nonempty boundary, different faces have different
cyclic boundary words, and every edge occurs either once or twice. -/
def IsSurfaceValid (P : FiniteCyclicPresentation) : Prop :=
  Nonempty P.Face ∧
    (∀ f, P.boundary f ≠ []) ∧
    (∀ f g, (P.boundary f).IsRotated (P.boundary g) → f = g) ∧
    ∀ e, P.edgeMultiplicity e = 1 ∨ P.edgeMultiplicity e = 2

/-- Two faces are adjacent when their boundary words contain a common unoriented edge. -/
def FaceAdjacent (P : FiniteCyclicPresentation) (f g : P.Face) : Prop :=
  ∃ e : P.Edge,
    e ∈ (P.boundary f).map edgeOfDart ∧ e ∈ (P.boundary g).map edgeOfDart

/-- Connectivity of the face-edge incidence graph. -/
def IsConnected (P : FiniteCyclicPresentation) : Prop :=
  Nonempty P.Face ∧ ∀ f g, Relation.ReflTransGen P.FaceAdjacent f g

/-- An orientation-preserving isomorphism of finite cyclic presentations, allowing a cyclic
rotation of each face. The sign of every dart is retained under `edgeEquiv`. -/
structure PresentationIso (P Q : FiniteCyclicPresentation) where
  edgeEquiv : P.Edge ≃ Q.Edge
  faceEquiv : P.Face ≃ Q.Face
  boundary_rotated :
    ∀ f, ((P.boundary f).map (SignedDart.mapEquiv edgeEquiv)).IsRotated
      (Q.boundary (faceEquiv f))

namespace PresentationIso

/-- The identity isomorphism of a finite cyclic presentation. -/
def refl (P : FiniteCyclicPresentation) : PresentationIso P P where
  edgeEquiv := Equiv.refl P.Edge
  faceEquiv := Equiv.refl P.Face
  boundary_rotated := by
    intro f
    rw [map_mapEquiv_refl]
    exact List.IsRotated.refl (P.boundary f)

/-- Reverse an isomorphism of finite cyclic presentations. -/
def symm {P Q : FiniteCyclicPresentation} (e : PresentationIso P Q) :
    PresentationIso Q P where
  edgeEquiv := e.edgeEquiv.symm
  faceEquiv := e.faceEquiv.symm
  boundary_rotated := by
    intro f
    have h := (e.boundary_rotated (e.faceEquiv.symm f)).symm.map
      (SignedDart.mapEquiv e.edgeEquiv.symm)
    rw [map_mapEquiv_symm] at h
    simpa only [e.faceEquiv.apply_symm_apply] using h

/-- Compose isomorphisms of finite cyclic presentations. -/
def trans {P Q R : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : PresentationIso Q R) :
    PresentationIso P R where
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  boundary_rotated := by
    intro p
    have h₁ := (e.boundary_rotated p).map (SignedDart.mapEquiv f.edgeEquiv)
    have h₂ := f.boundary_rotated (e.faceEquiv p)
    rw [map_mapEquiv_trans]
    exact h₁.trans h₂

/-- A presentation isomorphism preserves the multiplicity of an edge in each corresponding
face. -/
theorem faceEdgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) =
        ((Q.boundary (e.faceEquiv f)).map edgeOfDart).count (e.edgeEquiv a) := by
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) := by
          symm
          exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- A presentation isomorphism preserves total edge multiplicities. -/
theorem edgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

/-- Corresponding face boundaries have the same length. -/
theorem boundary_length_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  simpa using (e.boundary_rotated f).perm.length_eq

/-- Cyclic equivalence of face boundaries is preserved by a presentation isomorphism. -/
theorem map_isRotated {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) {f g : P.Face}
    (h : (P.boundary f).IsRotated (P.boundary g)) :
    (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  exact (e.boundary_rotated f).symm.trans
    ((h.map (SignedDart.mapEquiv e.edgeEquiv)).trans (e.boundary_rotated g))

/-- Two source boundaries are cyclically equivalent exactly when the corresponding target
boundaries are. -/
theorem isRotated_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f g : P.Face) :
    (P.boundary f).IsRotated (P.boundary g) ↔
      (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  constructor
  · exact e.map_isRotated
  · intro h
    simpa [PresentationIso.symm] using e.symm.map_isRotated h

/-- Face adjacency is preserved by a presentation isomorphism. -/
theorem map_faceAdjacent {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply ((e.boundary_rotated f).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hfa, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary f).map edgeOfDart).map e.edgeEquiv)
  · apply ((e.boundary_rotated g).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hga, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary g).map edgeOfDart).map e.edgeEquiv)

/-- Face adjacency corresponds exactly under a presentation isomorphism. -/
theorem faceAdjacent_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f g : P.Face) :
    P.FaceAdjacent f g ↔ Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  constructor
  · exact e.map_faceAdjacent
  · intro h
    simpa [PresentationIso.symm] using e.symm.map_faceAdjacent h

/-- Boundary-edge status is preserved by a presentation isomorphism. -/
theorem isBoundaryEdge_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Incidence validity is preserved by a presentation isomorphism. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (h : P.IsSurfaceValid) : Q.IsSurfaceValid := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := e.faceEquiv.symm q
    have hlength := e.boundary_length_eq f
    rw [e.faceEquiv.apply_symm_apply] at hlength
    have hzero : (P.boundary f).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact h.2.1 f (List.length_eq_zero_iff.mp hzero)
  · intro q r hqr
    let f := e.faceEquiv.symm q
    let g := e.faceEquiv.symm r
    have htarget :
        (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
      dsimp [f, g]
      simpa only [e.faceEquiv.apply_symm_apply] using hqr
    have hsource := (e.isRotated_iff f g).mpr htarget
    exact e.faceEquiv.symm.injective (h.2.2.1 f g hsource)
  · intro b
    let a := e.edgeEquiv.symm b
    have hmultiplicity := h.2.2.2 a
    rw [e.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [e.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- Incidence validity corresponds exactly under a presentation isomorphism. -/
theorem isSurfaceValid_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) : P.IsSurfaceValid ↔ Q.IsSurfaceValid :=
  ⟨e.isSurfaceValid, e.symm.isSurfaceValid⟩

/-- Face-incidence connectivity is preserved by a presentation isomorphism. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped := hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q)) (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Face-incidence connectivity corresponds exactly under a presentation isomorphism. -/
theorem isConnected_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) : P.IsConnected ↔ Q.IsConnected :=
  ⟨e.isConnected, e.symm.isConnected⟩

end PresentationIso

/-- A signed isomorphism of finite cyclic presentations. Each edge may be independently
reoriented while it is renamed; face boundary order is preserved up to cyclic rotation. -/
structure SignedPresentationIso (P Q : FiniteCyclicPresentation) where
  edgeRelabeling : EdgeRelabeling P.Edge Q.Edge
  faceEquiv : P.Face ≃ Q.Face
  boundary_rotated :
    ∀ f, ((P.boundary f).map edgeRelabeling.mapDart).IsRotated
      (Q.boundary (faceEquiv f))

namespace SignedPresentationIso

/-- The underlying equivalence of unoriented edge names. -/
abbrev edgeEquiv {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    P.Edge ≃ Q.Edge :=
  e.edgeRelabeling.edgeEquiv

/-- The orientation-reversal bit attached to a source edge. -/
abbrev reverse {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    P.Edge → Bool :=
  e.edgeRelabeling.reverse

/-- Regard an orientation-preserving presentation isomorphism as a general signed
isomorphism. -/
def ofPresentationIso {P Q : FiniteCyclicPresentation} (e : PresentationIso P Q) :
    SignedPresentationIso P Q where
  edgeRelabeling := EdgeRelabeling.ofEquiv e.edgeEquiv
  faceEquiv := e.faceEquiv
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    exact e.boundary_rotated f

/-- The identity signed isomorphism of a finite cyclic presentation. -/
def refl (P : FiniteCyclicPresentation) : SignedPresentationIso P P where
  edgeRelabeling := EdgeRelabeling.refl P.Edge
  faceEquiv := Equiv.refl P.Face
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl]
    exact List.IsRotated.refl (P.boundary f)

/-- Reverse a signed isomorphism of finite cyclic presentations. -/
def symm {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    SignedPresentationIso Q P where
  edgeRelabeling := e.edgeRelabeling.symm
  faceEquiv := e.faceEquiv.symm
  boundary_rotated := by
    intro f
    have h := (e.boundary_rotated (e.faceEquiv.symm f)).symm.map
      e.edgeRelabeling.symm.mapDart
    rw [EdgeRelabeling.map_mapDart_symm] at h
    simpa only [e.faceEquiv.apply_symm_apply] using h

/-- Compose signed isomorphisms of finite cyclic presentations. -/
def trans {P Q R : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : SignedPresentationIso Q R) :
    SignedPresentationIso P R where
  edgeRelabeling := e.edgeRelabeling.trans f.edgeRelabeling
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  boundary_rotated := by
    intro p
    have h₁ := (e.boundary_rotated p).map f.edgeRelabeling.mapDart
    have h₂ := f.boundary_rotated (e.faceEquiv p)
    rw [EdgeRelabeling.map_mapDart_trans]
    exact h₁.trans h₂

/-- A signed presentation isomorphism preserves edge multiplicity in each corresponding
face. -/
theorem faceEdgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) =
        ((Q.boundary (e.faceEquiv f)).map edgeOfDart).count (e.edgeEquiv a) := by
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) := by
          symm
          exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- A signed presentation isomorphism preserves total edge multiplicities. -/
theorem edgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

/-- Corresponding face boundaries have the same length under a signed isomorphism. -/
theorem boundary_length_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  simpa using (e.boundary_rotated f).perm.length_eq

/-- Cyclic equivalence of face boundaries is preserved by a signed presentation isomorphism. -/
theorem map_isRotated {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) {f g : P.Face}
    (h : (P.boundary f).IsRotated (P.boundary g)) :
    (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  exact (e.boundary_rotated f).symm.trans
    ((h.map e.edgeRelabeling.mapDart).trans (e.boundary_rotated g))

/-- Two source boundaries are cyclically equivalent exactly when the corresponding target
boundaries are. -/
theorem isRotated_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f g : P.Face) :
    (P.boundary f).IsRotated (P.boundary g) ↔
      (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  constructor
  · exact e.map_isRotated
  · intro h
    simpa [SignedPresentationIso.symm] using e.symm.map_isRotated h

/-- Face adjacency is preserved by a signed presentation isomorphism. -/
theorem map_faceAdjacent {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply ((e.boundary_rotated f).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hfa, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary f).map edgeOfDart).map e.edgeEquiv)
  · apply ((e.boundary_rotated g).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hga, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary g).map edgeOfDart).map e.edgeEquiv)

/-- Face adjacency corresponds exactly under a signed presentation isomorphism. -/
theorem faceAdjacent_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f g : P.Face) :
    P.FaceAdjacent f g ↔ Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  constructor
  · exact e.map_faceAdjacent
  · intro h
    simpa [SignedPresentationIso.symm] using e.symm.map_faceAdjacent h

/-- Boundary-edge status is preserved by a signed presentation isomorphism. -/
theorem isBoundaryEdge_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Incidence validity is preserved by a signed presentation isomorphism. -/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsSurfaceValid) : Q.IsSurfaceValid := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := e.faceEquiv.symm q
    have hlength := e.boundary_length_eq f
    rw [e.faceEquiv.apply_symm_apply] at hlength
    have hzero : (P.boundary f).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact h.2.1 f (List.length_eq_zero_iff.mp hzero)
  · intro q r hqr
    let f := e.faceEquiv.symm q
    let g := e.faceEquiv.symm r
    have htarget :
        (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
      dsimp [f, g]
      simpa only [e.faceEquiv.apply_symm_apply] using hqr
    have hsource := (e.isRotated_iff f g).mpr htarget
    exact e.faceEquiv.symm.injective (h.2.2.1 f g hsource)
  · intro b
    let a := e.edgeEquiv.symm b
    have hmultiplicity := h.2.2.2 a
    rw [e.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [e.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- Incidence validity corresponds exactly under a signed presentation isomorphism. -/
theorem isSurfaceValid_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : P.IsSurfaceValid ↔ Q.IsSurfaceValid :=
  ⟨e.isSurfaceValid, e.symm.isSurfaceValid⟩

/-- Face-incidence connectivity is preserved by a signed presentation isomorphism. -/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped := hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q)) (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Face-incidence connectivity corresponds exactly under a signed presentation isomorphism. -/
theorem isConnected_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : P.IsConnected ↔ Q.IsConnected :=
  ⟨e.isConnected, e.symm.isConnected⟩

end SignedPresentationIso

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
