# Schoenflies proof strategy and status

Status date: 2026-08-02

The full strong planar Schoenflies theorem is now proved.  The maintained
endpoint is `Schoenflies.schoenflies` in `Schoenflies/Main.lean`; it has the
exact statement required by the LeanEval challenge.  The proof contains no
`sorry`, `admit`, or project-specific axioms.  Its axiom audit reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## 1. Overall proof strategy

Given a continuous injective parametrization

```lean
r : sphere (0 : Plane) 1 → Plane
```

form the corresponding `JordanCircle` `J`.  The vendored Jordan curve theorem
provides its bounded and unbounded complementary components, together with
their connectedness, frontier, closure, and boundedness properties.

### A. Construct shrinking polygonal collars

Following Moise Chapter 9, repeatedly subdivide the parameter circle, choose
compatible access hairs and polygonal crosscuts, and build nested polygonal
Jordan curves in `J.inside` converging to `J.carrier`.  Cut each successive
collar band into a finite cyclic family of marked disk cells.  The construction
records parent and child boundary arcs, side seams, cyclic incidence, and
quantitative diameter bounds relative to the corresponding carrier arc.

This layer reuses the current declarations under
`ClassificationOfSurfaces.Moise`, notably broken-line connectivity, finite
polygonal complexes, polygonal disk filling, and polygonal Schoenflies.  Those
files are referenced directly and are not duplicated or modified in the
maintained source tree.

### B. Map finite collars to standard radial shells

Decompose each shell between two homothetic standard triangles into matching
cyclic target cells.  Extend the marked boundary map of every source cell over
its disk, prove equality on common seams, and glue the finite cell maps into a
band homeomorphism.  A radial correction makes each new band agree exactly
with the preceding disk stage while retaining quantitative angular and radial
control.

This produces a compatible sequence of homeomorphisms from nested closed
polygonal disks to nested standard triangle disks.

### C. Pass to the limit and add the Jordan boundary

The source disks exhaust `J.inside`, and the target disks exhaust the open
standard triangle.  Compatible finite maps therefore define mutually inverse
continuous direct-limit maps on the open regions.  The source-cell and
target-cell shrinking estimates prove convergence to the prescribed carrier
correspondence from both directions.  Adding those boundary values gives a
homeomorphism

```lean
closure J.inside ≃ₜ closedBall (0 : Plane) 1
```

whose value at every carrier point `x` is exactly
`J.carrierHomeomorph.symm x`.

### D. Recover the unbounded side by Euclidean inversion

Invert the plane about a chosen point of `J.inside`.  Inversion identifies the
original closed outside with the bounded side of the inverted Jordan curve
with the inversion center removed; the filled center represents infinity.
Apply the bounded-side theorem to the inverted curve, use a normalized
closed-ball recentering that sends the missing interior point to zero while
fixing the sphere pointwise, and use Mathlib's Euclidean inversion to identify
the punctured closed ball with the standard closed exterior.

The result is

```lean
closure J.outside ≃ₜ ((ball (0 : Plane) 1)ᶜ : Set Plane)
```

with exactly the same boundary values as the bounded-side map.

### E. Glue the regional maps

Package the two regional homeomorphisms as `RegionalExtensionData J`.
`RegionalExtensions` turns them into the whole-plane maps expected by
`DiskExtensionData`; values away from the relevant closed regions are supplied
by Tietze extension and play no mathematical role.  `AmbientGluing` pastes the
inside and outside maps along their identical carrier values, proves that the
forward and inverse pasted maps are continuous and mutually inverse, and
obtains the ambient plane homeomorphism.  Its carrier image is the unit sphere,
which is the required LeanEval conclusion.

## 2. Progress

The proof is complete end to end.

- `ShrinkingInteriorHomeomorphism.lean` constructs the open direct-limit
  homeomorphism.
- `ShrinkingBoundaryConvergence.lean` proves source and target cell convergence
  and localization at every carrier point.
- `InsideBoundaryExtension.lean` adds the boundary, proves continuity,
  bijectivity, and the exact sphere parametrization, and packages Moise's
  bounded-side theorem.
- `InvertedJordanRegions.lean` proves the needed component identities under
  Euclidean inversion and identifies the punctured regional spaces.
- `BallPunctureExterior.lean` constructs the sphere-fixing recentering and the
  punctured-ball-to-exterior homeomorphism.
- `OutsideBoundaryExtension.lean` constructs the closed outside homeomorphism
  and proves its exact boundary formula.
- `CompleteRegionalExtension.lean` pairs the two maps.
- `MoiseChapter9.hasMoiseDiskExtensions` now discharges the formerly
  conditional Chapter 9 interface for every Jordan circle.
- `Schoenflies.schoenflies` closes the unconditional strong theorem.
- The generated LeanEval payload contains the 219-module transitive closure.
  Its pristine-shaped `lake build Submission Solution` completes successfully,
  including the exact trusted `Solution.lean` statement.

The final work did not require any changes to the existing
`ClassificationOfSurfaces/Moise` sources.  Moving those files into a future
shared module should therefore be an import/name migration, not a duplication
or proof rewrite, provided their public API remains recognizable.

## 3. Known weak areas

There are no known mathematical holes in the compiled theorem.  The remaining
weaknesses are engineering and maintainability concerns.

- The construction is spread across a large dependency graph.  Many files are
  deliberately narrow proof layers, but discovering the controlling invariant
  can still require following several modules.
- The cell-localization part is sensitive to the exact marked-arc and seam APIs.
  Refactors of the collaborator-owned Moise modules may require mechanical
  theorem-name and namespace repairs.
- The outside proof contains a dense chain of subtype homeomorphisms.  It is
  fully checked, but could benefit from a higher-level reusable API for
  compactifying an unbounded complementary component.
- The standalone benchmark sets `autoImplicit = false`.  One older helper had
  relied on an implicit type variable; that binder is now explicit.  Keeping
  the standalone build in CI is important for catching similar portability
  issues.
- The tree still emits pre-existing linter warnings.  They do not affect the
  theorem or its axiom closure.

## 4. Risks and difficulties

- The generated evaluator payload is large: it vendors 219 local modules
  because the proof genuinely reuses JordanCurve, the Schoenflies development,
  and part of `ClassificationOfSurfaces.Moise`.  Fresh standalone builds are
  consequently more expensive than compiling the final wrapper in the root
  project.
- A shared-module reorganization could temporarily break imports or qualified
  theorem names.  Since the proof does not alter the reused Moise sources, the
  repair should be mechanical unless the collaborator changes theorem
  statements rather than locations.
- The most delicate mathematics remains the limiting boundary-control layer:
  compatibility corrections must preserve enough angular localization for
  cell diameters to converge.  This invariant is now proved quantitatively,
  but future simplification of the finite-stage construction must preserve it.
- The inversion proof depends on distinguishing the filled inversion center
  (the point representing infinity) from the punctured regional space.  Any
  future abstraction should retain these types explicitly; treating inversion
  as an ordinary whole-plane homeomorphism would be incorrect.
- The elaboration and exact-statement build have passed.  The external
  comparator/kernel replay is a separate infrastructure check and requires the
  pinned comparator tools in `PATH`.
