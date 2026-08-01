import Schoenflies.PolygonalSubpathExtraction

/-!
# Controlled prescribed-hair joins in arbitrary neighborhoods

The metric version of Moise 9.5 produces a finite simple join in an
`epsilon`-thickening of a selected boundary arc.  Finite-level collar
assembly needs a slightly more flexible interface: a join inside an arbitrary
open neighborhood of that arc.  Compactness supplies a positive thickening
contained in the prescribed neighborhood, so no new separator argument is
needed.
-/

namespace Schoenflies

open Metric Set Function

namespace JordanCircle
namespace AccessibleAngularArc

variable {J : JordanCircle}

/-- Prescribed disjoint endpoint hairs can be joined through the Jordan
inside in any open neighborhood of the selected boundary arc. -/
theorem exists_simple_inside_join_between_prescribedHairs_in_open
    (A : J.AccessibleAngularArc)
    (HL : J.InsideAccessHair (J.curvePoint A.left))
    (HR : J.InsideAccessHair (J.curvePoint A.right))
    (hdisjoint : Disjoint HL.carrier HR.carrier)
    {V : Set Plane} (hVopen : IsOpen V) (hArcV : A.curveArcPlane ⊆ V) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon)
        (p q : Plane)
        (_B : SimpleBrokenLine (J.inside ∩ V) p q),
      thickening epsilon A.curveArcPlane ⊆ V ∧
        p ∈ (HR.shortenToOpen Metric.isOpen_thickening
          (self_subset_thickening hepsilon _ A.right_mem_curveArcPlane)).carrier ∧
        q ∈ (HL.shortenToOpen Metric.isOpen_thickening
          (self_subset_thickening hepsilon _ A.left_mem_curveArcPlane)).carrier ∧
        p ∈ J.inside ∧ q ∈ J.inside := by
  obtain ⟨epsilon, hepsilon, hthick⟩ :=
    A.curveArcPlane_isCompact.exists_thickening_subset_open hVopen hArcV
  obtain ⟨p, q, B, hp, hq, hpInside, hqInside⟩ :=
    A.exists_simple_controlled_inside_join_between_prescribedHairs
      (HL.shortenToOpen Metric.isOpen_thickening
        (self_subset_thickening hepsilon _ A.left_mem_curveArcPlane))
      (HR.shortenToOpen Metric.isOpen_thickening
        (self_subset_thickening hepsilon _ A.right_mem_curveArcPlane))
      (hdisjoint.mono
        (HL.shortenToOpen_carrier_subset Metric.isOpen_thickening
          (self_subset_thickening hepsilon _ A.left_mem_curveArcPlane))
        (HR.shortenToOpen_carrier_subset Metric.isOpen_thickening
          (self_subset_thickening hepsilon _ A.right_mem_curveArcPlane)))
      hepsilon
  let B' : SimpleBrokenLine (J.inside ∩ V) p q :=
    B.mono fun _ hx => ⟨hx.1, hthick hx.2⟩
  exact ⟨epsilon, hepsilon, p, q, B', hthick,
    hp, hq, hpInside, hqInside⟩

end AccessibleAngularArc
end JordanCircle

end Schoenflies
