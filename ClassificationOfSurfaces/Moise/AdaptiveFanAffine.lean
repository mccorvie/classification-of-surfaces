/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import ClassificationOfSurfaces.Moise.AdaptiveTriangulation
import ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import ClassificationOfSurfaces.Moise.LocallyFiniteFaceModel

/-!
# Affine standard-coordinate formulas for adaptive fan faces

The adaptive fan realization is assembled through faithful midpoint subdivisions.  Although its
definition is geometric, on each named fan triangle its value in the original intrinsic
barycentric coordinates is one affine function of the standard planar face coordinates.  The
relative Radó weld uses this formula after composing with the inverse-affine pieces of retained
polygonal filling certificates.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (L : LocallyFiniteTriangleComplex S)

/-- Reindex standard coordinates onto the literal three-vertex type of one locally finite
face. -/
noncomputable def faceCoordExtensionAffineLF (f : L.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  AffineMap.pi fun v =>
    (LinearMap.proj ((L.faceVertexEquiv f).symm v)).toAffineMap

@[simp] theorem faceCoordExtensionAffineLF_apply
    (f : L.Face) (z : Fin 3 → ℝ)
    (v : {v // v ∈ L.faceVertices f}) :
    L.faceCoordExtensionAffineLF f z v =
      z ((L.faceVertexEquiv f).symm v) := by
  simp [faceCoordExtensionAffineLF]

/-- The affine inverse-coordinate formula for the standard plane chart of a locally finite
face. -/
noncomputable def facePlaneInverseAffineLF (f : L.Face) :
    Plane →ᵃ[ℝ] ({v // v ∈ L.faceVertices f} → ℝ) :=
  (L.faceCoordExtensionAffineLF f).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

theorem facePlaneHomeomorph_symm_val_LF (f : L.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((L.facePlaneHomeomorph f).symm p).1 =
      L.facePlaneInverseAffineLF f p.1 := by
  let z := (standardTrianglePlaneComplex.realizationHomeomorph
    standardTrianglePlaneComplex_pure).symm p
  have hz : z.1 = standardTrianglePlaneComplex.faceCoords
      standardTriangleMeshFace p.1 := by
    apply standardTrianglePlaneComplex.realizationHomeomorph_symm_val_eq_faceCoords
      standardTrianglePlaneComplex_pure standardTriangleMeshFace p
    change p.1 ∈ standardTrianglePlaneComplex.cellCarrier
      (Finset.univ : Finset (Fin 3))
    rw [standardTriangle_cellCarrier_univ]
    exact p.2
  change
    (L.faceReindexFromStandard f
      (standardRealizationToSimplex z)).1 =
        L.facePlaneInverseAffineLF f p.1
  funext v
  simp only [faceReindexFromStandard, standardRealizationToSimplex,
    facePlaneInverseAffineLF, AffineMap.comp_apply,
    L.faceCoordExtensionAffineLF_apply]
  exact congrFun hz ((L.faceVertexEquiv f).symm v)

end LocallyFiniteTriangleComplex

namespace IntrinsicTwoComplex

variable {K : IntrinsicTwoComplex} {U : Set K.realization}
variable [K.AdaptiveSafety U]
variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Relabeling a global adaptive fan simplex preserves the source-weighted affine sum. -/
theorem adaptiveFanRelabel_source_sum_apply
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU)
    (x : stdSimplex ℝ
      {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f})
    (v : (K.safeSubdivision f.1.1).refined.Vertex) :
    (∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        (K.adaptiveFanRelabelSimplex U hU f x) p *
          (K.adaptiveFanVertexSource U hU f p).1 v) =
      ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
        x ((K.adaptiveFanFaceVertexEquiv U hU f).symm p) *
          (K.adaptiveFanVertexSource U hU f p).1 v := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  let q : {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} :=
    (K.adaptiveFanFaceVertexEquiv U hU f).symm p
  have hweight :=
    K.adaptiveFanRelabel_extended_apply U hU f x q.1
  change
    extendFaceCoordinates (K.adaptiveFanFaceVertices U hU f)
        (K.adaptiveFanRelabelSimplex U hU f x) p.1 =
      extendFaceCoordinates (K.adaptiveGlobalFanFaceVertices U hU f) x q.1
    at hweight
  rw [extendFaceCoordinates_of_mem _ _ p.2,
    extendFaceCoordinates_of_mem _ _ q.2] at hweight
  exact hweight

/- One adaptive global fan face is affine, in original intrinsic barycentric coordinates, as a
function of its standard planar face coordinates.  Elaborating the dependent fan relabeling and
the original affine realization together needs a larger local heartbeat budget. -/
set_option maxHeartbeats 300000 in
-- The relabeling sum is factored out above; the remaining dependent affine assembly needs
-- between 250k and 300k heartbeats.
theorem adaptiveGlobalFanFaceMap_standardAffine
    (hU : IsOpen U) (f : K.AdaptiveFanFace U hU) :
    ∃ a : Plane →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : stdSimplex ℝ
          {v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f},
        (K.adaptiveGlobalFanFaceMap U hU f x).1.1 =
          a ((K.adaptiveLocallyFiniteTriangleComplex U hU).facePlaneHomeomorph f x).1 := by
  classical
  let R := K.adaptiveLocallyFiniteTriangleComplex U hU
  let Q := K.safeSubdivision f.1.1
  obtain ⟨aQ, haQ⟩ := Q.affineOnFace f.1.2.1.1 f.1.2.1.2
  let b :
      ({v // v ∈ K.adaptiveGlobalFanFaceVertices U hU f} → ℝ) →ₗ[ℝ]
        (Q.refined.Vertex → ℝ) :=
    ∑ p : {p // p ∈ K.adaptiveFanFaceVertices U hU f},
      (LinearMap.proj
        ((K.adaptiveFanFaceVertexEquiv U hU f).symm p)).smulRight
          (K.adaptiveFanVertexSource U hU f p).1
  let a : Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
    (aQ.comp b.toAffineMap).comp (R.facePlaneInverseAffineLF f)
  refine ⟨a, ?_⟩
  intro x
  let y := K.adaptiveFanRelabelSimplex U hU f x
  have hyCarrier :
      K.adaptiveFanSourcePoint U hU f y ∈
        Q.refined.faceCarrier f.1.2.1.1 :=
    K.adaptiveFanSourcePoint_mem_carrier U hU f y
  have hxPlane :
      x.1 =
        R.facePlaneInverseAffineLF f (R.facePlaneHomeomorph f x).1 := by
    have h :=
      R.facePlaneHomeomorph_symm_val_LF f (R.facePlaneHomeomorph f x)
    rw [(R.facePlaneHomeomorph f).symm_apply_apply] at h
    exact h
  change
    (Q.homeo (K.adaptiveFanSourcePoint U hU f y)).1 =
      a (R.facePlaneHomeomorph f x).1
  rw [haQ _ hyCarrier]
  change aQ (K.adaptiveFanSourcePoint U hU f y).1 =
    aQ (b (R.facePlaneInverseAffineLF f (R.facePlaneHomeomorph f x).1))
  apply congrArg aQ
  rw [← hxPlane]
  funext v
  change
    (∑ p, y p * (K.adaptiveFanVertexSource U hU f p).1 v) =
      b x.1 v
  simp only [b, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact K.adaptiveFanRelabel_source_sum_apply hU f x v

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
