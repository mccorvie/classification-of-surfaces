/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.CellComplex
import ClassificationOfSurfaces.PolygonalQuotient

/-!
# Polygonal realization of surface cell-complex data

This file connects face-boundary *occurrences* in `SurfaceCellComplex` to the generic quotient
construction in `PolygonalQuotient.lean`. The distinction between occurrences and dart values is
essential: a word such as `a a` has two different sides carrying the same oriented dart.

An internal pair carrying the same dart uses the identity interval parameter; a pair carrying
inverse darts uses parameter reversal. `OccurrencePairingValid` states the nonemptiness and
occurrence-count conditions under which every internal side has exactly one unoriented partner.
The public polygonal gluing relation requires a witness of this predicate.

The definitions here are additive. `SurfaceCellComplex.Realization` still denotes the stored
placeholder realization until the triangulation bridge can be cut over atomically.
`SurfaceCellComplex.sphere` uses the explicit two-monogon presentation needed by this polygonal
realization, and the standard one-face examples have occurrence-validity witnesses. Before the
cutover, this adapter must be reconciled with the incidence-derived validity API and connected
through a certified triangulation-to-quotient homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace SurfaceCellComplex

/-- A position in the boundary word of a face. -/
abbrev BoundaryOccurrence (K : SurfaceCellComplex) : Type :=
  Σ f : K.Face, Fin (K.faceBoundaryLength f)

/-- The oriented dart carried by a boundary occurrence. -/
def occurrenceDart (K : SurfaceCellComplex) (o : K.BoundaryOccurrence) : K.Dart :=
  (K.boundary o.1).get (by simpa only [faceBoundaryLength] using o.2)

/-- The polygon side indexed by a boundary occurrence. -/
def occurrenceSide (K : SurfaceCellComplex) (o : K.BoundaryOccurrence) :
    PolygonGluing.Side K.Face K.faceBoundaryLength :=
  ⟨o.1, o.2⟩

/-- A compatible gluing instruction between two boundary occurrences.

Equal oriented darts use the same interval direction. Inverse darts use the opposite direction.
Boundary darts are excluded from both ends of a gluing instruction. -/
structure BoundaryPairing (K : SurfaceCellComplex) where
  source : K.BoundaryOccurrence
  target : K.BoundaryOccurrence
  source_ne_target : source ≠ target
  source_not_boundary : ¬K.isBoundaryDart (K.occurrenceDart source)
  target_not_boundary : ¬K.isBoundaryDart (K.occurrenceDart target)
  direction : PolygonGluing.ParameterDirection
  compatible :
    match direction with
    | .same => K.occurrenceDart target = K.occurrenceDart source
    | .opposite => K.occurrenceDart target = K.inv (K.occurrenceDart source)

/-- The occurrence conditions needed for the pairing relation to glue every internal side once.

This is not a full surface-validity predicate: it does not include connectedness, boundary-contour
counts, or the condition that each vertex link is a circle or interval. In particular, it does not
certify that the current example named `annulusCellComplex` has annulus topology. -/
structure OccurrencePairingValid (K : SurfaceCellComplex) : Prop where
  face_nonempty : Nonempty K.Face
  face_boundary_nonempty : ∀ f, 0 < K.faceBoundaryLength f
  inv_ne : ∀ d, K.inv d ≠ d
  boundary_inv : ∀ d, K.isBoundaryDart (K.inv d) ↔ K.isBoundaryDart d
  boundary_occurs_once :
    ∀ d, K.isBoundaryDart d →
      ∃! o : K.BoundaryOccurrence,
        K.occurrenceDart o = d ∨ K.occurrenceDart o = K.inv d
  interior_occurs_twice :
    ∀ d, ¬K.isBoundaryDart d →
      ∃ o₁ o₂ : K.BoundaryOccurrence, o₁ ≠ o₂ ∧
        ∀ o : K.BoundaryOccurrence,
          (K.occurrenceDart o = d ∨ K.occurrenceDart o = K.inv d) ↔
            o = o₁ ∨ o = o₂

namespace OccurrencePairingValid

/-- Every internal occurrence has a unique distinct partner in its inverse-dart orbit. -/
theorem exists_unique_partner {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.isBoundaryDart (K.occurrenceDart source)) :
    ∃! target : K.BoundaryOccurrence,
      source ≠ target ∧
        (K.occurrenceDart target = K.occurrenceDart source ∨
          K.occurrenceDart target = K.inv (K.occurrenceDart source)) := by
  obtain ⟨o₁, o₂, hne, hcover⟩ :=
    h.interior_occurs_twice (K.occurrenceDart source) hsource
  rcases (hcover source).mp (Or.inl rfl) with hsource₁ | hsource₂
  · refine ⟨o₂, ⟨hsource₁.trans_ne hne, (hcover o₂).mpr (Or.inr rfl)⟩, ?_⟩
    intro target htarget
    rcases (hcover target).mp htarget.2 with htarget₁ | htarget₂
    · exact False.elim (htarget.1 (hsource₁.trans htarget₁.symm))
    · exact htarget₂
  · refine ⟨o₁, ⟨hsource₂.trans_ne hne.symm, (hcover o₁).mpr (Or.inl rfl)⟩, ?_⟩
    intro target htarget
    rcases (hcover target).mp htarget.2 with htarget₁ | htarget₂
    · exact htarget₁
    · exact False.elim (htarget.1 (hsource₂.trans htarget₂.symm))

/-- Every internal boundary occurrence is the source of a compatible pairing. -/
theorem exists_pairing_source {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.isBoundaryDart (K.occurrenceDart source)) :
    ∃ pairing : K.BoundaryPairing, pairing.source = source := by
  have makePairing (target : K.BoundaryOccurrence) (hne : source ≠ target)
      (htarget : K.occurrenceDart target = K.occurrenceDart source ∨
        K.occurrenceDart target = K.inv (K.occurrenceDart source)) :
      ∃ pairing : K.BoundaryPairing, pairing.source = source := by
    rcases htarget with hsame | hopposite
    · refine ⟨⟨source, target, hne, hsource, ?_, .same, hsame⟩, rfl⟩
      rw [hsame]
      exact hsource
    · refine ⟨⟨source, target, hne, hsource, ?_, .opposite, hopposite⟩, rfl⟩
      rw [hopposite]
      exact fun hboundary ↦ hsource ((h.boundary_inv _).mp hboundary)
  obtain ⟨o₁, o₂, hne, hcover⟩ :=
    h.interior_occurs_twice (K.occurrenceDart source) hsource
  rcases (hcover source).mp (Or.inl rfl) with hsource₁ | hsource₂
  · exact makePairing o₂ (hsource₁.trans_ne hne) ((hcover o₂).mpr (Or.inr rfl))
  · exact makePairing o₁ (hsource₂.trans_ne hne.symm) ((hcover o₁).mpr (Or.inl rfl))

end OccurrencePairingValid

/-! ## One-face presentation criterion -/

namespace SignedDart

/-- The unoriented edge name carried by a signed dart. -/
def edgeName {Edge : Type} : SignedDart Edge → Edge
  | pos e => e
  | neg e => e

@[simp]
theorem edgeName_flip {Edge : Type} (d : SignedDart Edge) :
    edgeName (flip d) = edgeName d := by
  cases d <;> rfl

theorem eq_or_eq_flip_iff_edgeName_eq {Edge : Type} (x d : SignedDart Edge) :
    x = d ∨ x = flip d ↔ edgeName x = edgeName d := by
  cases x <;> cases d <;> simp [edgeName, flip]

end SignedDart

/-- Positions in a boundary word carrying either orientation of `e`. -/
def wordEdgeOccurrences {Edge : Type} [DecidableEq Edge]
    (word : List (SignedDart Edge)) (e : Edge) : Finset (Fin word.length) :=
  Finset.univ.filter fun i ↦ SignedDart.edgeName (word.get i) = e

@[simp]
theorem mem_wordEdgeOccurrences {Edge : Type} [DecidableEq Edge]
    (word : List (SignedDart Edge)) (e : Edge) (i : Fin word.length) :
    i ∈ wordEdgeOccurrences word e ↔ SignedDart.edgeName (word.get i) = e := by
  simp [wordEdgeOccurrences]

/-- A one-face presentation is occurrence-pairing-valid when each boundary edge name occurs once
and each internal edge name occurs twice, with orientation ignored. -/
theorem oneFacePresentation_occurrencePairingValid
    {Edge : Type} [Fintype Edge] [DecidableEq Edge]
    (word : List (SignedDart Edge)) (boundaryEdge : Edge → Prop)
    [DecidablePred boundaryEdge] (hword : word ≠ [])
    (hcard : ∀ e, (wordEdgeOccurrences word e).card = if boundaryEdge e then 1 else 2) :
    (oneFacePresentation Edge word boundaryEdge).OccurrencePairingValid := by
  let K := oneFacePresentation Edge word boundaryEdge
  let occurrence : Fin word.length → K.BoundaryOccurrence := fun i ↦ ⟨PUnit.unit, i⟩
  have occurrence_injective : Function.Injective occurrence := by
    intro i j hij
    have hval : i.val = j.val := congrArg (fun o : K.BoundaryOccurrence ↦ o.2.val) hij
    exact Fin.ext hval
  have occurrence_surjective : Function.Surjective occurrence := by
    rintro ⟨f, i⟩
    cases f
    exact ⟨i, rfl⟩
  have occurrenceDart_occurrence (i : Fin word.length) :
      K.occurrenceDart (occurrence i) = word.get i := by
    rfl
  have orbit_iff (i : Fin word.length) (d : SignedDart Edge) :
      K.occurrenceDart (occurrence i) = d ∨
          K.occurrenceDart (occurrence i) = K.inv d ↔
        i ∈ wordEdgeOccurrences word (SignedDart.edgeName d) := by
    rw [occurrenceDart_occurrence]
    change word.get i = d ∨ word.get i = SignedDart.flip d ↔ _
    rw [SignedDart.eq_or_eq_flip_iff_edgeName_eq]
    exact (mem_wordEdgeOccurrences word (SignedDart.edgeName d) i).symm
  constructor
  · exact ⟨PUnit.unit⟩
  · intro f
    cases f
    exact List.length_pos_of_ne_nil hword
  · intro d
    cases d <;> intro h <;> cases h
  · intro d
    cases d <;> rfl
  · intro d hd
    have hboundary : boundaryEdge (SignedDart.edgeName d) := by
      cases d <;> exact hd
    have hone : (wordEdgeOccurrences word (SignedDart.edgeName d)).card = 1 := by
      simpa [hboundary] using hcard (SignedDart.edgeName d)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    refine ⟨occurrence i, (orbit_iff i d).mpr ?_, ?_⟩
    · simp [hi]
    · intro o ho
      obtain ⟨j, rfl⟩ := occurrence_surjective o
      apply congrArg occurrence
      have hj : j ∈ wordEdgeOccurrences word (SignedDart.edgeName d) :=
        (orbit_iff j d).mp ho
      simpa [hi] using hj
  · intro d hd
    have hinterior : ¬boundaryEdge (SignedDart.edgeName d) := by
      cases d <;> exact hd
    have htwo : (wordEdgeOccurrences word (SignedDart.edgeName d)).card = 2 := by
      simpa [hinterior] using hcard (SignedDart.edgeName d)
    obtain ⟨i, j, hij, hindices⟩ := Finset.card_eq_two.mp htwo
    refine ⟨occurrence i, occurrence j, occurrence_injective.ne hij, ?_⟩
    intro o
    obtain ⟨k, rfl⟩ := occurrence_surjective o
    rw [orbit_iff]
    simp [hindices, occurrence_injective.eq_iff]

namespace BoundaryPairing

/-- The generic polygon-side identification associated to an occurrence pairing. -/
def identification {K : SurfaceCellComplex} (pairing : K.BoundaryPairing) :
    PolygonGluing.Identification K.Face K.faceBoundaryLength where
  source := K.occurrenceSide pairing.source
  target := K.occurrenceSide pairing.target
  direction := pairing.direction

@[simp]
theorem identification_source {K : SurfaceCellComplex} (pairing : K.BoundaryPairing) :
    pairing.identification.source = K.occurrenceSide pairing.source :=
  rfl

@[simp]
theorem identification_target {K : SurfaceCellComplex} (pairing : K.BoundaryPairing) :
    pairing.identification.target = K.occurrenceSide pairing.target :=
  rfl

@[simp]
theorem identification_direction {K : SurfaceCellComplex} (pairing : K.BoundaryPairing) :
    pairing.identification.direction = pairing.direction :=
  rfl

end BoundaryPairing

/-- All side identifications compatible with a pairing-valid complex. -/
def polygonalIdentifications (K : SurfaceCellComplex) (_valid : K.OccurrencePairingValid) :
    Set (PolygonGluing.Identification K.Face K.faceBoundaryLength) :=
  Set.range BoundaryPairing.identification

@[simp]
theorem pairing_identification_mem {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (pairing : K.BoundaryPairing) :
    pairing.identification ∈ K.polygonalIdentifications valid :=
  ⟨pairing, rfl⟩

/-- Under the occurrence-count conditions, every internal side starts an identification. -/
theorem OccurrencePairingValid.exists_identification_source {K : SurfaceCellComplex}
    (h : K.OccurrencePairingValid) (source : K.BoundaryOccurrence)
    (hsource : ¬K.isBoundaryDart (K.occurrenceDart source)) :
    ∃ identification ∈ K.polygonalIdentifications h,
      identification.source = K.occurrenceSide source := by
  obtain ⟨pairing, hp⟩ := h.exists_pairing_source source hsource
  refine ⟨pairing.identification, pairing_identification_mem h pairing, ?_⟩
  rw [BoundaryPairing.identification_source, hp]

/-- The disjoint union of the polygonal cells indexed by the faces of `K`. -/
abbrev PolygonalPreRealization (K : SurfaceCellComplex) : Type :=
  PolygonGluing.PreRealization K.Face K.faceBoundaryLength

/-- The generated gluing relation associated to the boundary occurrences of pairing-valid `K`. -/
abbrev PolygonalGluingRel (K : SurfaceCellComplex) (valid : K.OccurrencePairingValid) :
    Setoid K.PolygonalPreRealization :=
  PolygonGluing.setoid (K.polygonalIdentifications valid)

/-- The quotient of a pairing-valid complex by its compatible internal occurrence pairings. -/
abbrev PolygonalRealization (K : SurfaceCellComplex) (valid : K.OccurrencePairingValid) : Type :=
  PolygonGluing.Realization (K.polygonalIdentifications valid)

/-- The quotient map from the polygonal disjoint union of `K`. -/
def polygonalMk (K : SurfaceCellComplex) (valid : K.OccurrencePairingValid) :
    K.PolygonalPreRealization → K.PolygonalRealization valid :=
  PolygonGluing.mk (K.polygonalIdentifications valid)

theorem continuous_polygonalMk (K : SurfaceCellComplex) (valid : K.OccurrencePairingValid) :
    Continuous (K.polygonalMk valid) :=
  PolygonGluing.continuous_mk (K.polygonalIdentifications valid)

theorem isQuotientMap_polygonalMk (K : SurfaceCellComplex)
    (valid : K.OccurrencePairingValid) :
    _root_.Topology.IsQuotientMap (K.polygonalMk valid) :=
  PolygonGluing.isQuotientMap_mk (K.polygonalIdentifications valid)

/-- A compatible occurrence pairing identifies its side points in the polygonal quotient. -/
theorem polygonalMk_pairing_eq {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (pairing : K.BoundaryPairing) (t : unitInterval) :
    K.polygonalMk valid (pairing.identification.source.point t) =
      K.polygonalMk valid
        (pairing.identification.target.point (pairing.identification.parameter t)) :=
  PolygonGluing.mk_source_eq_mk_target pairing.identification
    (pairing_identification_mem valid pairing) t

/-! ## The two-monogon sphere presentation -/

/-- The positively oriented side in the two-monogon sphere presentation. -/
def spherePositiveOccurrence : sphere.BoundaryOccurrence :=
  ⟨false, ⟨0, by simp [faceBoundaryLength, sphere]⟩⟩

/-- The negatively oriented side in the two-monogon sphere presentation. -/
def sphereNegativeOccurrence : sphere.BoundaryOccurrence :=
  ⟨true, ⟨0, by simp [faceBoundaryLength, sphere]⟩⟩

@[simp]
theorem spherePositiveOccurrence_dart :
    sphere.occurrenceDart spherePositiveOccurrence = SignedDart.pos PUnit.unit := by
  simp [occurrenceDart, spherePositiveOccurrence, sphere, faceBoundaryLength]

@[simp]
theorem sphereNegativeOccurrence_dart :
    sphere.occurrenceDart sphereNegativeOccurrence = SignedDart.neg PUnit.unit := by
  simp [occurrenceDart, sphereNegativeOccurrence, sphere, faceBoundaryLength]

@[simp]
theorem sphere_inv_pos (e : PUnit) :
    sphere.inv (SignedDart.pos e) = SignedDart.neg e :=
  rfl

@[simp]
theorem sphere_inv_neg (e : PUnit) :
    sphere.inv (SignedDart.neg e) = SignedDart.pos e :=
  rfl

/-- The two-monogon sphere satisfies the occurrence-level pairing conditions. -/
theorem sphere_occurrencePairingValid : sphere.OccurrencePairingValid := by
  constructor
  · exact ⟨false⟩
  · intro f
    cases f <;> simp [faceBoundaryLength, sphere]
  · intro d
    cases d <;> simp
  · intro d
    simp [sphere]
  · intro d hd
    simp [sphere] at hd
  · intro d _hd
    refine ⟨spherePositiveOccurrence, sphereNegativeOccurrence, ?_, ?_⟩
    · simp [spherePositiveOccurrence, sphereNegativeOccurrence]
    · rintro ⟨f, i⟩
      cases f
      · change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        cases d <;> rename_i e <;> cases e
        · simp [spherePositiveOccurrence, sphereNegativeOccurrence, sphere,
            occurrenceDart, faceBoundaryLength]
        · simp [spherePositiveOccurrence, sphereNegativeOccurrence, sphere,
            occurrenceDart, faceBoundaryLength]
          rfl
      · change Fin 1 at i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        cases d <;> rename_i e <;> cases e
        · simp [spherePositiveOccurrence, sphereNegativeOccurrence, sphere,
            occurrenceDart, faceBoundaryLength]
          rfl
        · simp [spherePositiveOccurrence, sphereNegativeOccurrence, sphere,
            occurrenceDart, faceBoundaryLength]

/-- The gluing from the positive monogon to the negative monogon. -/
def sphereBoundaryPairing : sphere.BoundaryPairing where
  source := spherePositiveOccurrence
  target := sphereNegativeOccurrence
  source_ne_target := by
    simp [spherePositiveOccurrence, sphereNegativeOccurrence]
  source_not_boundary := by
    simp [sphere]
  target_not_boundary := by
    simp [sphere]
  direction := .opposite
  compatible := by
    simp

@[simp]
theorem sphereBoundaryPairing_mem :
    sphereBoundaryPairing.identification ∈
      sphere.polygonalIdentifications sphere_occurrencePairingValid :=
  pairing_identification_mem sphere_occurrencePairingValid sphereBoundaryPairing

end SurfaceCellComplex
end ClassificationOfSurfaces
end Topology
end LeanEval
