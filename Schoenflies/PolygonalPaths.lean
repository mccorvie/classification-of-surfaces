import Schoenflies.Crosscuts
import ClassificationOfSurfaces.Moise.LocallyFiniteGraphApproximation

/-!
# Polygonal broken lines as embedded paths

The Chapter 6 loop-erasure API produces a finite graph path.  Its existing
`PLArcParameterization` realizes the resolved carrier as the injective image
of the unit interval.  This file exposes that fact as an ordinary Mathlib
`Path`, which is the convenient input for the auxiliary Jordan curve in
Moise 9.1 and 9.5.
-/

namespace Schoenflies

open Metric Set Function
open LeanEval.Topology.ClassificationOfSurfaces.Moise

private abbrev MoisePLArcParameterization :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.LocallyFiniteTriangleComplex.PlaneGraphRealization.PLArcParameterization

namespace PLArcParameterization

variable {C : Set Plane} {a b : Plane}

/-- The underlying injective unit-interval path of a finite PL arc. -/
def toPath (P : MoisePLArcParameterization C a b) : Path a b where
  toFun := fun t => P.curve t
  continuous_toFun := P.continuousOn.restrict
  source' := P.start_eq
  target' := P.finish_eq

theorem toPath_injective (P : MoisePLArcParameterization C a b) :
    Function.Injective (toPath P) := by
  intro s t hst
  apply Subtype.ext
  exact P.injectiveOn s.2 t.2 hst

theorem range_toPath (P : MoisePLArcParameterization C a b) :
    range (toPath P) = C := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact P.image_eq.le ⟨t, t.2, rfl⟩
  · intro hx
    obtain ⟨t, ht, rfl⟩ := P.image_eq.ge hx
    exact ⟨⟨t, ht⟩, rfl⟩

end PLArcParameterization

namespace JordanCircle

private abbrev MoiseBrokenLineData :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData

namespace BrokenLineData

/-- A nonconstant broken line has at least one listed segment. -/
theorem n_pos_of_start_ne_finish {U : Set Plane} (B : MoiseBrokenLineData U)
    (hne : B.start ≠ B.finish) : 0 < B.n := by
  by_contra hn
  have hnzero : B.n = 0 := Nat.eq_zero_of_not_pos hn
  apply hne
  unfold LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData.start
    LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData.finish
  apply congrArg B.vertex
  exact Fin.ext (by simpa [hnzero])

/-- The initial point of a nonconstant broken line belongs to its permitted
ambient set. -/
theorem start_mem_of_ne {U : Set Plane} (B : MoiseBrokenLineData U)
    (hne : B.start ≠ B.finish) : B.start ∈ U := by
  let i : Fin B.n := ⟨0, n_pos_of_start_ne_finish B hne⟩
  apply B.segment_subset i
  exact left_mem_segment ℝ _ _

end BrokenLineData

namespace SimpleBrokenLine

variable {U : Set Plane} {a b : Plane}

/-- Replace the listed vertices of a simple broken line by the vertices of
its canonical resolved graph path.  This does not change the path ultimately
parameterized by `toPath`, but makes its geometric carrier literally the
`segmentCarrier` of the resulting broken line. -/
noncomputable def carrierBrokenLine (B : SimpleBrokenLine U a b)
    (_hne : a ≠ b) : SimpleBrokenLine U a b where
  data := B.data.resolvedBrokenLine
  start_eq := B.data.resolvedBrokenLine_start.trans B.start_eq
  finish_eq := B.data.resolvedBrokenLine_finish.trans B.finish_eq
  vertex_injective := B.data.resolvedBrokenLine_vertex_injective

/-- The canonical PL parameterization selected from the Chapter 6 resolved
carrier of a simple broken line. -/
noncomputable def parameterization (B : SimpleBrokenLine U a b)
    (hne : a ≠ b) :
    MoisePLArcParameterization B.data.resolvedCarrier B.data.start B.data.finish := by
  have hdata : B.data.start ≠ B.data.finish := by
    intro h
    exact hne (B.start_eq.symm.trans (h.trans B.finish_eq))
  exact Classical.choice
    (LeanEval.Topology.ClassificationOfSurfaces.Moise.LocallyFiniteTriangleComplex.PlaneGraphRealization.BrokenLineData.exists_plArcParameterization
      B.data hdata)

/-- A loop-erased broken line is a genuinely injective path, not merely a
list with pairwise distinct vertices. -/
noncomputable def toPath (B : SimpleBrokenLine U a b) (hne : a ≠ b) :
    Path a b := by
  exact (PLArcParameterization.toPath (B.parameterization hne)).cast
    B.start_eq.symm B.finish_eq.symm

theorem toPath_injective (B : SimpleBrokenLine U a b) (hne : a ≠ b) :
    Function.Injective (B.toPath hne) := by
  let P := B.parameterization hne
  change Function.Injective
    ((PLArcParameterization.toPath P).cast B.start_eq.symm B.finish_eq.symm)
  intro s t hst
  apply PLArcParameterization.toPath_injective P
  simpa only [Path.cast_coe] using hst

theorem range_toPath (B : SimpleBrokenLine U a b) (hne : a ≠ b) :
    range (B.toPath hne) = B.data.resolvedCarrier := by
  let P := B.parameterization hne
  change range ((PLArcParameterization.toPath P).cast
    B.start_eq.symm B.finish_eq.symm) = _
  rw [show ((PLArcParameterization.toPath P).cast
      B.start_eq.symm B.finish_eq.symm : unitInterval → Plane) =
      PLArcParameterization.toPath P from Path.cast_coe _ _ _]
  exact PLArcParameterization.range_toPath P

/-- The carrier of `carrierBrokenLine` is exactly the image of the canonical
path associated to the original broken line. -/
theorem segmentCarrier_carrierBrokenLine
    (B : SimpleBrokenLine U a b) (hne : a ≠ b) :
    (B.carrierBrokenLine hne).data.segmentCarrier = range (B.toPath hne) := by
  rw [B.range_toPath hne]
  have hdata : B.data.start ≠ B.data.finish := by
    intro h
    exact hne (B.start_eq.symm.trans (h.trans B.finish_eq))
  have hresolved :
      B.data.resolvedBrokenLine.start ≠
        B.data.resolvedBrokenLine.finish := by
    rw [B.data.resolvedBrokenLine_start, B.data.resolvedBrokenLine_finish]
    exact hdata
  have hlength : B.data.resolvedWalk.length ≠ 0 :=
    Nat.ne_of_gt
      (BrokenLineData.n_pos_of_start_ne_finish
        B.data.resolvedBrokenLine hresolved)
  unfold carrierBrokenLine
  unfold LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData.segmentCarrier
    LeanEval.Topology.ClassificationOfSurfaces.Moise.BrokenLineData.resolvedCarrier
  simp only [hlength, ↓reduceDIte]
  rfl

theorem range_toPath_subset (B : SimpleBrokenLine U a b) (hne : a ≠ b) :
    range (B.toPath hne) ⊆ U := by
  rw [B.range_toPath hne]
  have hdata : B.data.start ≠ B.data.finish := by
    intro h
    exact hne (B.start_eq.symm.trans (h.trans B.finish_eq))
  exact B.data.resolvedCarrier_subset
    (Schoenflies.JordanCircle.BrokenLineData.start_mem_of_ne B.data hdata)

end SimpleBrokenLine

end JordanCircle

end Schoenflies
