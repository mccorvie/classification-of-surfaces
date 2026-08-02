import Schoenflies.LocalizedTargetCellCover
import Schoenflies.StandardRadialCollars

/-!
# Compatible localized collar homeomorphisms

The cellwise construction supplies a homeomorphism of each localized shell,
but independently chosen shell homeomorphisms need not agree on their common
boundary.  This file removes that obstruction.  First we package the raw
inner-boundary restriction as a homeomorphism.  We then postcompose the raw
shell map with the radial standard-shell adjustment, making its restriction
equal to any prescribed homeomorphism of the shared boundary.
-/

namespace Schoenflies

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise

noncomputable section

namespace JordanCircle.InitialAngularArcs

variable {J : JordanCircle} (I : J.InitialAngularArcs)

private abbrev sourceInnerDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 1)

private abbrev sourceOuterDisk (k : ℕ) : PolygonalCircle :=
  I.localizedMarkedPolygonalDisk (k + 2)

private abbrev targetInnerDisk (_I : J.InitialAngularArcs) (k : ℕ) :
    PolygonalCircle :=
  StandardPolygonalCollars.disk (k + 1)

private abbrev targetOuterDisk (_I : J.InitialAngularArcs) (k : ℕ) :
    PolygonalCircle :=
  StandardPolygonalCollars.disk (k + 2)

/-- Convert the polygonal carrier subtype to the definitionally equivalent
carrier of its associated Jordan circle. -/
def localizedSourceInnerCarrierToJordanCarrier (k : ℕ) :
    (I.sourceInnerDisk k).carrier →
      (I.sourceInnerDisk k).toJordanCircle.carrier := fun x =>
  ⟨x, by
    simpa only [(I.sourceInnerDisk k).carrier_toJordanCircle] using x.2⟩

theorem continuous_localizedSourceInnerCarrierToJordanCarrier (k : ℕ) :
    Continuous (I.localizedSourceInnerCarrierToJordanCarrier k) := by
  exact continuous_subtype_val.subtype_mk _

/-- The restriction of the raw localized shell map to its inner carrier,
with its codomain tightened to the standard inner carrier. -/
def localizedRawInnerBoundaryMap (k : ℕ) (hk : 1 ≤ k) :
    (I.sourceInnerDisk k).carrier → (I.targetInnerDisk k).carrier := fun x =>
  let xJ := I.localizedSourceInnerCarrierToJordanCarrier k x
  ⟨I.localizedInnerBoundaryEmbedding k hk xJ,
    I.localizedInnerBoundaryEmbedding_mem_targetInnerCarrier k hk xJ⟩

theorem continuous_localizedRawInnerBoundaryMap
    (k : ℕ) (hk : 1 ≤ k) :
    Continuous (I.localizedRawInnerBoundaryMap k hk) := by
  apply continuous_induced_rng.mpr
  exact (I.continuous_localizedInnerBoundaryEmbedding k hk).comp
    (I.continuous_localizedSourceInnerCarrierToJordanCarrier k)

theorem injective_localizedRawInnerBoundaryMap
    (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (I.localizedRawInnerBoundaryMap k hk) := by
  intro x y hxy
  have hembed :
      I.localizedInnerBoundaryEmbedding k hk
          (I.localizedSourceInnerCarrierToJordanCarrier k x) =
        I.localizedInnerBoundaryEmbedding k hk
          (I.localizedSourceInnerCarrierToJordanCarrier k y) :=
    congrArg (fun z : (I.targetInnerDisk k).carrier => (z : Plane)) hxy
  have hcast := I.injective_localizedInnerBoundaryEmbedding k hk hembed
  exact Subtype.ext <|
    congrArg (fun z : (I.sourceInnerDisk k).toJordanCircle.carrier =>
      (z : Plane)) hcast

theorem surjective_localizedRawInnerBoundaryMap
    (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (I.localizedRawInnerBoundaryMap k hk) := by
  intro y
  have hyRange : (y : Plane) ∈
      Set.range (I.localizedInnerBoundaryEmbedding k hk) := by
    rw [I.range_localizedInnerBoundaryEmbedding k hk]
    exact y.2
  obtain ⟨x, hx⟩ := hyRange
  let x' : (I.sourceInnerDisk k).carrier :=
    ⟨x, by
      simpa only [(I.sourceInnerDisk k).carrier_toJordanCircle] using x.2⟩
  refine ⟨x', ?_⟩
  apply Subtype.ext
  change I.localizedInnerBoundaryEmbedding k hk
      (I.localizedSourceInnerCarrierToJordanCarrier k x') = y
  simpa only [x', localizedSourceInnerCarrierToJordanCarrier] using hx

/-- The raw shell map's inner-boundary restriction as an actual
homeomorphism of polygonal carriers. -/
def localizedRawInnerBoundaryHomeomorph
    (k : ℕ) (hk : 1 ≤ k) :
    (I.sourceInnerDisk k).carrier ≃ₜ (I.targetInnerDisk k).carrier := by
  letI : CompactSpace (I.sourceInnerDisk k).carrier :=
    isCompact_iff_compactSpace.mp (I.sourceInnerDisk k).isCompact_carrier
  let e : (I.sourceInnerDisk k).carrier ≃ (I.targetInnerDisk k).carrier :=
    Equiv.ofBijective (I.localizedRawInnerBoundaryMap k hk)
      ⟨I.injective_localizedRawInnerBoundaryMap k hk,
        I.surjective_localizedRawInnerBoundaryMap k hk⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) (I.continuous_localizedRawInnerBoundaryMap k hk)

@[simp] theorem localizedRawInnerBoundaryHomeomorph_apply
    (k : ℕ) (hk : 1 ≤ k) (x : (I.sourceInnerDisk k).carrier) :
    (I.localizedRawInnerBoundaryHomeomorph k hk x : Plane) =
      I.localizedInnerBoundaryEmbedding k hk
        (I.localizedSourceInnerCarrierToJordanCarrier k x) := by
  rfl

/-- Regard the source inner carrier as a subtype of its localized shell. -/
def localizedSourceInnerCarrierInShell (k : ℕ)
    (x : (I.sourceInnerDisk k).carrier) :
    PolygonalCircle.closedShell
      (I.sourceInnerDisk k) (I.sourceOuterDisk k) :=
  ⟨x, PolygonalCircle.innerCarrier_subset_closedShell _ _
    (I.localizedMarkedPolygonalDisk_strictly_nested (k + 1)) x.2⟩

@[simp] theorem localizedSourceInnerCarrierInShell_val
    (k : ℕ) (x : (I.sourceInnerDisk k).carrier) :
    (I.localizedSourceInnerCarrierInShell k x : Plane) = x := by
  rfl

/-- Correct the raw localized shell homeomorphism so that it realizes a
prescribed map on the shared inner boundary. -/
def compatibleLocalizedShellHomeomorph
    (k : ℕ) (hk : 1 ≤ k)
    (b : (I.sourceInnerDisk k).carrier ≃ₜ
      (I.targetInnerDisk k).carrier) :
    PolygonalCircle.closedShell
        (I.sourceInnerDisk k) (I.sourceOuterDisk k) ≃ₜ
      PolygonalCircle.closedShell
        (I.targetInnerDisk k) (I.targetOuterDisk k) :=
  (I.localizedShellHomeomorph k hk).trans <|
    StandardPolygonalCollars.standardShellBoundaryAdjustment (k + 1)
      ((I.localizedRawInnerBoundaryHomeomorph k hk).symm.trans b)

/-- The corrected shell map agrees pointwise with the prescribed map on the
entire shared inner carrier. -/
theorem compatibleLocalizedShellHomeomorph_apply_innerCarrier
    (k : ℕ) (hk : 1 ≤ k)
    (b : (I.sourceInnerDisk k).carrier ≃ₜ
      (I.targetInnerDisk k).carrier)
    (x : (I.sourceInnerDisk k).carrier) :
    (I.compatibleLocalizedShellHomeomorph k hk b
        (I.localizedSourceInnerCarrierInShell k x) : Plane) = b x := by
  rw [compatibleLocalizedShellHomeomorph, Homeomorph.trans_apply]
  have hraw :
      I.localizedShellHomeomorph k hk
          (I.localizedSourceInnerCarrierInShell k x) =
        StandardPolygonalCollars.innerCarrierInClosedShell (k + 1)
          (I.localizedRawInnerBoundaryHomeomorph k hk x) := by
    apply Subtype.ext
    rfl
  rw [hraw,
    StandardPolygonalCollars.standardShellBoundaryAdjustment_apply_innerCarrier]
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]

end JordanCircle.InitialAngularArcs

end


end Schoenflies
