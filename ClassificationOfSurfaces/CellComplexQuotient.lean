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
inverse darts uses parameter reversal. `OccurrencePairingValid` combines the incidence-derived
`IsSurfaceValid` predicate with the nonempty-boundary condition needed by the current polygon
model. The public polygonal gluing relation requires a witness of this predicate.

The definitions here are additive. `SurfaceCellComplex.Realization` still denotes the stored
placeholder realization until the triangulation bridge can be cut over atomically.
`SurfaceCellComplex.sphere` uses the explicit two-monogon presentation needed by this polygonal
realization, and the standard one-face examples have occurrence-validity witnesses. The adapter
now derives its orbit conditions from `IsSurfaceValid`; the remaining cutover dependency is a
certified triangulation-to-quotient homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace SurfaceCellComplex

/-- The oriented dart carried by a boundary occurrence. -/
abbrev occurrenceDart (K : SurfaceCellComplex) (o : K.BoundaryOccurrence) : K.Dart :=
  o.dart

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
  source_not_boundary : ¬K.IsBoundaryDart (K.occurrenceDart source)
  target_not_boundary : ¬K.IsBoundaryDart (K.occurrenceDart target)
  direction : PolygonGluing.ParameterDirection
  compatible :
    match direction with
    | .same => K.occurrenceDart target = K.occurrenceDart source
    | .opposite => K.occurrenceDart target = K.inv (K.occurrenceDart source)

/-- Incidence validity together with nonempty face boundaries for the polygonal realization.

The extra boundary condition excludes the empty-word sphere presentation because `PolygonCell 0`
is a side-free disk, not a sphere. Connectedness and vertex-link conditions remain separate. -/
structure OccurrencePairingValid (K : SurfaceCellComplex) : Prop where
  surface_valid : K.IsSurfaceValid
  face_boundary_nonempty : ∀ f, 0 < K.faceBoundaryLength f

namespace OccurrencePairingValid

/-- A polygonally valid complex has at least one face. -/
theorem face_nonempty {K : SurfaceCellComplex} (h : K.OccurrencePairingValid) :
    Nonempty K.Face :=
  h.surface_valid.1

/-- Inverse darts in a polygonally valid complex are distinct. -/
theorem inv_ne {K : SurfaceCellComplex} (h : K.OccurrencePairingValid) (d : K.Dart) :
    K.inv d ≠ d :=
  h.surface_valid.inv_ne d

/-- A non-boundary edge in a valid incidence system occurs exactly twice. -/
theorem interior_occurs_twice {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (d : K.Dart) (hd : ¬K.IsBoundaryDart d) : K.OccursExactlyTwice d := by
  exact h.surface_valid.occurs_twice_of_not_boundary hd

/-- Every internal occurrence has a unique distinct partner in its inverse-dart orbit. -/
theorem exists_unique_partner {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    ∃! target : K.BoundaryOccurrence,
      source ≠ target ∧
        (K.occurrenceDart target = K.occurrenceDart source ∨
          K.occurrenceDart target = K.inv (K.occurrenceDart source)) := by
  obtain ⟨o₁, o₂, hne, ho₁, ho₂, hcover⟩ :=
    h.interior_occurs_twice (K.occurrenceDart source) hsource
  rcases hcover source (Or.inl rfl) with hsource₁ | hsource₂
  · refine ⟨o₂, ⟨hsource₁.trans_ne hne, ho₂⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact False.elim (htarget.1 (hsource₁.trans htarget₁.symm))
    · exact htarget₂
  · refine ⟨o₁, ⟨hsource₂.trans_ne hne.symm, ho₁⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact htarget₁
    · exact False.elim (htarget.1 (hsource₂.trans htarget₂.symm))

/-- Every internal boundary occurrence is the source of a compatible pairing. -/
theorem exists_pairing_source {K : SurfaceCellComplex} (h : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    ∃ pairing : K.BoundaryPairing, pairing.source = source := by
  obtain ⟨target, ⟨hne, htarget⟩, _hunique⟩ := h.exists_unique_partner source hsource
  rcases htarget with hsame | hopposite
  · refine ⟨⟨source, target, hne, hsource, ?_, .same, hsame⟩, rfl⟩
    rw [hsame]
    exact hsource
  · refine ⟨⟨source, target, hne, hsource, ?_, .opposite, hopposite⟩, rfl⟩
    rw [hopposite]
    exact fun hboundary ↦ hsource ((K.isBoundaryDart_inv_iff _).mp hboundary)

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

/-- A one-face presentation is incidence-valid when every edge name occurs once or twice, with
orientation ignored. Boundary status is then derived from the occurrence count. -/
theorem oneFacePresentation_isSurfaceValid
    {Edge : Type} [Fintype Edge] [DecidableEq Edge]
    (word : List (SignedDart Edge))
    (hcard : ∀ e, (wordEdgeOccurrences word e).card = 1 ∨
      (wordEdgeOccurrences word e).card = 2) :
    (oneFacePresentation Edge word).IsSurfaceValid := by
  let K := oneFacePresentation Edge word
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
  refine ⟨⟨PUnit.unit⟩, ?_, ?_, ?_⟩
  · intro f g _h
    cases f
    cases g
    rfl
  · intro d
    cases d <;> intro hd <;> cases hd
  · intro d
    rcases hcard (SignedDart.edgeName d) with hone | htwo
    · left
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
      refine ⟨occurrence i, (orbit_iff i d).mpr ?_, ?_⟩
      · simp [hi]
      · intro o ho
        obtain ⟨j, rfl⟩ := occurrence_surjective o
        apply congrArg occurrence
        have hj : j ∈ wordEdgeOccurrences word (SignedDart.edgeName d) :=
          (orbit_iff j d).mp ho
        simpa [hi] using hj
    · right
      obtain ⟨i, j, hij, hindices⟩ := Finset.card_eq_two.mp htwo
      refine ⟨occurrence i, occurrence j, occurrence_injective.ne hij, ?_, ?_, ?_⟩
      · apply (orbit_iff i d).mpr
        simp [hindices]
      · apply (orbit_iff j d).mpr
        simp [hindices]
      · intro o ho
        obtain ⟨k, rfl⟩ := occurrence_surjective o
        have hk : k ∈ wordEdgeOccurrences word (SignedDart.edgeName d) :=
          (orbit_iff k d).mp ho
        simpa [hindices, occurrence_injective.eq_iff] using hk

/-- A nonempty, incidence-valid one-face word supplies polygonal pairing data. -/
theorem oneFacePresentation_occurrencePairingValid
    {Edge : Type} [Fintype Edge] [DecidableEq Edge]
    (word : List (SignedDart Edge)) (hword : word ≠ [])
    (hcard : ∀ e, (wordEdgeOccurrences word e).card = 1 ∨
      (wordEdgeOccurrences word e).card = 2) :
    (oneFacePresentation Edge word).OccurrencePairingValid := by
  refine ⟨oneFacePresentation_isSurfaceValid word hcard, ?_⟩
  intro f
  cases f
  exact List.length_pos_of_ne_nil hword

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
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
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
  ⟨false, ⟨0, by simp [sphere]⟩⟩

/-- The negatively oriented side in the two-monogon sphere presentation. -/
def sphereNegativeOccurrence : sphere.BoundaryOccurrence :=
  ⟨true, ⟨0, by simp [sphere]⟩⟩

@[simp]
theorem spherePositiveOccurrence_dart :
    sphere.occurrenceDart spherePositiveOccurrence = SignedDart.pos PUnit.unit := by
  simp [occurrenceDart, BoundaryOccurrence.dart, spherePositiveOccurrence, sphere]

@[simp]
theorem sphereNegativeOccurrence_dart :
    sphere.occurrenceDart sphereNegativeOccurrence = SignedDart.neg PUnit.unit := by
  simp [occurrenceDart, BoundaryOccurrence.dart, sphereNegativeOccurrence, sphere]

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
  refine ⟨sphere_isSurfaceValid, ?_⟩
  intro f
  cases f <;> simp [faceBoundaryLength, sphere]

/-- Neither oriented representative of the sphere edge is a boundary dart. -/
theorem sphere_not_isBoundaryDart (d : sphere.Dart) : ¬sphere.IsBoundaryDart d := by
  rintro ⟨o, _ho, hunique⟩
  have hpositive : sphere.Occurs d spherePositiveOccurrence := by
    cases d <;> rename_i e <;> cases e
    · exact Or.inl spherePositiveOccurrence_dart
    · exact Or.inr spherePositiveOccurrence_dart
  have hnegative : sphere.Occurs d sphereNegativeOccurrence := by
    cases d <;> rename_i e <;> cases e
    · exact Or.inr sphereNegativeOccurrence_dart
    · exact Or.inl sphereNegativeOccurrence_dart
  have heq := (hunique spherePositiveOccurrence hpositive).trans
    (hunique sphereNegativeOccurrence hnegative).symm
  have hne : spherePositiveOccurrence ≠ sphereNegativeOccurrence := by
    intro h
    have hface := congrArg (fun o : sphere.BoundaryOccurrence ↦ o.1) h
    cases hface
  exact hne heq

/-- The gluing from the positive monogon to the negative monogon. -/
def sphereBoundaryPairing : sphere.BoundaryPairing where
  source := spherePositiveOccurrence
  target := sphereNegativeOccurrence
  source_ne_target := by
    simp [spherePositiveOccurrence, sphereNegativeOccurrence]
  source_not_boundary := sphere_not_isBoundaryDart _
  target_not_boundary := sphere_not_isBoundaryDart _
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
