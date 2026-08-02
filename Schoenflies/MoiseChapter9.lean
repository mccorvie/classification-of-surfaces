import Schoenflies.AmbientGluing
import Schoenflies.Accessibility
import Schoenflies.BoundaryPartitions
import Schoenflies.AccessHairs
import Schoenflies.HairOrdering
import Schoenflies.AngularSubdivisions
import Schoenflies.ArcNeighborhoods
import Schoenflies.Crosscuts
import Schoenflies.PolygonalPaths
import Schoenflies.TwoArcJordan
import Schoenflies.AuxiliaryJordan
import Schoenflies.SeparatorFrame
import Schoenflies.PolygonalTransport
import Schoenflies.PolygonalJordanCircle
import Schoenflies.PolygonalJordanNesting
import Schoenflies.PolygonalDiskBoundaryExtension
import Schoenflies.GenericPolygonalFrame
import Schoenflies.LocalStraightCrossing
import Schoenflies.TransverseIntersections
import Schoenflies.AuxiliaryTransverseIntersections
import Schoenflies.FiniteSeparatorSetup
import Schoenflies.ReturnPathCrossings
import Schoenflies.SideConstancy
import Schoenflies.FiniteCrossingParity
import Schoenflies.OddWalkEdgeGraph
import Schoenflies.CommonSegmentArrangement
import Schoenflies.SegmentChainWalk
import Schoenflies.CollarBandSegments
import Schoenflies.MoiseBandCells
import Schoenflies.NestedCollarStages
import Schoenflies.PolyhedralDiskNeighborhoods
import Schoenflies.PolygonalDiskExhaustion
import Schoenflies.MarkedPolygonalDiskExhaustion
import Schoenflies.LocalizedPolygonalDiskExhaustion
import Schoenflies.MarkedHairCrossings
import Schoenflies.LocalizedMarkedHairCrossings
import Schoenflies.PolygonalShells
import Schoenflies.PolygonalShellTriangulation
import Schoenflies.LocalizedShellCrosscuts
import Schoenflies.LocalizedShellCutPaths
import Schoenflies.JordanArcPaths
import Schoenflies.AnnularCrosscutSeparators
import Schoenflies.AnnularSeparatorPairs
import Schoenflies.LocallyStraightSets
import Schoenflies.LocalizedAnnularCrosscuts
import Schoenflies.AnnularSeparatorSides
import Schoenflies.JordanThetaRegions
import Schoenflies.PolygonalAnnularTheta
import Schoenflies.AnnularCrosscutOrder
import Schoenflies.LocalizedAnnularTheta
import Schoenflies.FiniteAnnularCrosscutOrder
import Schoenflies.LocalizedAnnularOrder
import Schoenflies.ReturnPathParity
import Schoenflies.RefinedSeparatorFrame
import Schoenflies.RefinedEdgeSides
import Schoenflies.CyclicCrossingParity
import Schoenflies.RefinedCyclicCuts
import Schoenflies.ControlledTailJoin
import Schoenflies.PrescribedHairCrosscuts
import Schoenflies.ShrinkingCollars
import Schoenflies.TrimmedHairCrosscuts
import Schoenflies.PolygonalSubpathExtraction
import Schoenflies.OpenControlledCrosscuts
import Schoenflies.AvoidingControlledCrosscuts
import Schoenflies.FiniteAvoidingCrosscuts
import Schoenflies.FiniteLevelCrosscuts
import Schoenflies.FiniteLevelHairSynchronization
import Schoenflies.CyclicLevelAddresses
import Schoenflies.HierarchicalLevelHairs
import Schoenflies.LevelArcCover
import Schoenflies.LevelEndpointIncidence
import Schoenflies.SynchronizedLevelReturns
import Schoenflies.ResolvedPolygonalArcs
import Schoenflies.CyclicLevelEdges
import Schoenflies.SynchronizedPolygonalCircle
import Schoenflies.AvoidingLevelCollars
import Schoenflies.SynchronizedCollarCells
import Schoenflies.ExactSynchronizedCollarCells
import Schoenflies.JordanRegionRecognition
import Schoenflies.RecursiveCollarStages
import Schoenflies.HierarchicalCollarStages
import Schoenflies.TrimmedCollarCells
import Schoenflies.LevelHairSynchronization
import Schoenflies.PolygonalSubarcs
import Schoenflies.ControlledCrosscuts
import Schoenflies.HairReturns
import Schoenflies.ReturnArcFrames
import Schoenflies.ReturnArcParity
import Schoenflies.RegionalExtensions
import ClassificationOfSurfaces.Moise.BrokenLine
import ClassificationOfSurfaces.Moise.PolygonalSchoenflies
import ClassificationOfSurfaces.Moise.PLApproximation

/-!
# Moise Chapter 9: the geometric input

This module is the dependency boundary between the new Schoenflies proof and
the existing Moise development.  Imports and theorem applications deliberately
use the declarations in their current `ClassificationOfSurfaces.Moise`
location; no copy of that development is maintained here.

The main remaining construction is to build `DiskExtensionData J`.  Its two
halves are obtained by Moise's accessible-point, nested-crosscut, and shrinking
collar argument.  `Schoenflies.AmbientGluing` proves that this is exactly enough
for the strong ambient statement.
-/

namespace Schoenflies

open Metric Set

namespace MoiseChapter9

/-- Compile-time use of the existing polygonal Schoenflies endpoint.  Besides
being useful in the collar construction, this deliberately records the current
API on which the new branch depends. -/
theorem polygonal_circles_ambient_equivalent
    (P Q : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle) :
    ∃ h : Plane ≃ₜ Plane, h '' P.carrier = Q.carrier :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.polygonal_schoenflies P Q

/-- A boundary point is accessible from a region if a broken line reaches it
while staying in the region except possibly at its endpoint. -/
def IsAccessibleFrom (U : Set Plane) (x : Plane) : Prop :=
  ∃ a ∈ U, LeanEval.Topology.ClassificationOfSurfaces.Moise.JoinedByBrokenLine
    (U ∪ {x}) a x

/-- The elementary Chapter 1 input used throughout Chapter 9: two points of
the inside region can be joined by a broken line in that region. -/
theorem inside_joinedByBrokenLine (J : JordanCircle) {a b : Plane}
    (ha : a ∈ J.inside) (hb : b ∈ J.inside) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.JoinedByBrokenLine J.inside a b :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.IsPreconnected.joinedByBrokenLine
    J.inside_isOpen
    J.inside_isConnected.isPreconnected ha hb

/-- The corresponding broken-line connectivity statement for the outside. -/
theorem outside_joinedByBrokenLine (J : JordanCircle) {a b : Plane}
    (ha : a ∈ J.outside) (hb : b ∈ J.outside) :
    LeanEval.Topology.ClassificationOfSurfaces.Moise.JoinedByBrokenLine J.outside a b :=
  LeanEval.Topology.ClassificationOfSurfaces.Moise.IsPreconnected.joinedByBrokenLine
    J.outside_isOpen
    J.outside_isConnected.isPreconnected ha hb

/-- A finite family of pairwise disjoint access lines to marked points of the
curve.  This is the output shape of Moise 9.2 used at each finite stage of the
nested construction. -/
structure AccessFamily (J : JordanCircle) (ι : Type*) [Fintype ι] where
  anchor : ι → Plane
  anchor_mem : ∀ i, anchor i ∈ J.carrier
  anchor_injective : Function.Injective anchor
  start : ι → Plane
  start_mem_inside : ∀ i, start i ∈ J.inside
  accessible : ∀ i,
    LeanEval.Topology.ClassificationOfSurfaces.Moise.JoinedByBrokenLine
      (J.inside ∪ {anchor i}) (start i) (anchor i)

/-- The final output of the nested-crosscut/collar construction of Moise
9.1--9.6.  The first unresolved geometric input is now stated independently
as `AccessibleAngularArc.HasControlledInsideCrosscut`; the finite polyhedral
neighborhood preceding that separation step is supplied by
`AccessibleAngularArc.exists_openSubmesh_in_thickening`.

The output here consists only of homeomorphisms of the two closed regions.
`RegionalExtensions` handles their irrelevant whole-plane extensions and
ambient pasting.  This is a proposition, not an axiom. -/
def HasMoiseDiskExtensions (J : JordanCircle) : Prop :=
  Nonempty (RegionalExtensionData J)

/-- Moise's first form: the closed bounded complementary region is a disk,
with the parametrized Jordan curve sent to the corresponding point of the
unit circle.  This is the active geometric milestone; the unbounded form is
derived only after this proposition has been constructed. -/
def HasMoiseInsideDiskExtension (J : JordanCircle) : Prop :=
  Nonempty (InsideRegionalExtensionData J)

theorem HasMoiseDiskExtensions.inside {J : JordanCircle}
    (h : HasMoiseDiskExtensions J) : HasMoiseInsideDiskExtension J :=
  ⟨h.some.insideData⟩

end MoiseChapter9

end Schoenflies
