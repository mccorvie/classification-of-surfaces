import Schoenflies.OrderedPathCrossing

/-!
# Constancy of Jordan side on a crossing-free interval

A connected path segment which avoids a Jordan circle lies in one connected
component of its complement.  This is the global counterpart of the local
ordered-crossing lemma.
-/

namespace Schoenflies

open Metric Set Function

namespace JordanCircle

/-- The endpoints of a continuous, carrier-avoiding interval lie on the same
side of a Jordan circle. -/
theorem interval_image_same_side (J : JordanCircle)
    {f : unitInterval → Plane} (hf : Continuous f)
    {a b : unitInterval} (hab : a ≤ b)
    (havoid : ∀ t ∈ Icc a b, f t ∉ J.carrier) :
    ((f a ∈ J.inside ∧ f b ∈ J.inside) ∨
      (f a ∈ J.outside ∧ f b ∈ J.outside)) := by
  let S : Set Plane := f '' Icc a b
  have hpreconnected : IsPreconnected S :=
    Set.ordConnected_Icc.isPreconnected.image f hf.continuousOn
  have hsubset : S ⊆ J.carrierᶜ := by
    rintro x ⟨t, ht, rfl⟩
    exact havoid t ht
  have haS : f a ∈ S := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hbS : f b ∈ S := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  rcases J.mem_inside_or_outside (hsubset haS) with haInside | haOutside
  · left
    refine ⟨haInside, ?_⟩
    have hcomponent :=
      hpreconnected.subset_connectedComponentIn haS hsubset hbS
    have hcomponentEq :
        connectedComponentIn J.carrierᶜ (f a) = J.inside := by
      change connectedComponentIn J.carrierᶜ (f a) =
        connectedComponentIn J.carrierᶜ J.insidePoint
      exact (connectedComponentIn_eq haInside).symm
    rwa [hcomponentEq] at hcomponent
  · right
    refine ⟨haOutside, ?_⟩
    have hcomponent :=
      hpreconnected.subset_connectedComponentIn haS hsubset hbS
    have hcomponentEq :
        connectedComponentIn J.carrierᶜ (f a) = J.outside := by
      change connectedComponentIn J.carrierᶜ (f a) =
        connectedComponentIn J.carrierᶜ J.outsidePoint
      exact (connectedComponentIn_eq haOutside).symm
    rwa [hcomponentEq] at hcomponent

end JordanCircle

end Schoenflies
