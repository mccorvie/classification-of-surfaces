import Schoenflies.MoiseChapter9

/-!
# The final Schoenflies reduction

Once the Chapter 9 construction supplies compatible disk extensions, the
strong ambient Schoenflies theorem follows immediately from the gluing theorem.
-/

namespace Schoenflies

open Metric Set Function

/-- Strong Schoenflies, reduced to the concrete output of Moise Chapter 9. -/
theorem schoenflies_of_diskExtensionData
    (r : sphere (0 : Plane) 1 → Plane) (hcont : Continuous r) (hinj : Injective r)
    (E : DiskExtensionData
      { parametrization := r, continuous := hcont, injective := hinj }) :
    ∃ h : Plane ≃ₜ Plane, h '' Set.range r = sphere (0 : Plane) 1 := by
  let J : JordanCircle :=
    { parametrization := r, continuous := hcont, injective := hinj }
  exact ⟨E.ambientHomeomorph, E.ambientHomeomorph_image_carrier⟩

/-- The exact final hand-off from Moise Chapter 9 to the lean-eval statement. -/
theorem schoenflies_of_moise
    (r : sphere (0 : Plane) 1 → Plane) (hcont : Continuous r) (hinj : Injective r)
    (hmoise : MoiseChapter9.HasMoiseDiskExtensions
      { parametrization := r, continuous := hcont, injective := hinj }) :
    ∃ h : Plane ≃ₜ Plane, h '' Set.range r = sphere (0 : Plane) 1 := by
  exact schoenflies_of_diskExtensionData r hcont hinj hmoise.some.diskExtensionData

/-- The strong planar Schoenflies theorem: every continuous injective
parametrization of the unit circle is carried onto the unit circle by an
ambient homeomorphism of the plane. -/
theorem schoenflies
    (r : sphere (0 : Plane) 1 → Plane) (hcont : Continuous r) (hinj : Injective r) :
    ∃ h : Plane ≃ₜ Plane, h '' Set.range r = sphere (0 : Plane) 1 := by
  exact schoenflies_of_moise r hcont hinj <|
    MoiseChapter9.hasMoiseDiskExtensions
      { parametrization := r, continuous := hcont, injective := hinj }

end Schoenflies
