# Schoenflies proof strategy and status

Status date: 2026-08-02 (evening update: Risk 1 resolved at design level, see §5)

This document describes the current Schoenflies branch modulo the Jordan
curve theorem (JCT).  It distinguishes Lean theorems that already compile
from intended later steps.  In particular, the final theorem is **not yet
proved unconditionally**: `Schoenflies.schoenflies_of_moise` still assumes
`MoiseChapter9.HasMoiseDiskExtensions J`.

## 1. Overall proof strategy

Given a continuous injective map

```lean
r : sphere (0 : Plane) 1 → Plane
```

form its `JordanCircle` `J`.  The assumed JCT supplies the two complementary
components `J.inside` and `J.outside`, their openness and connectedness, and
the usual closure/frontier identities.

The intended proof then follows Moise Chapter 9 in four layers.

### A. Build shrinking polygonal collars inside the Jordan curve

1. Subdivide the parameter circle into finite cyclic families of angular
   arcs.
2. Construct disjoint access hairs and synchronized polygonal crosscuts near
   those arcs.
3. Recursively choose polygonal Jordan curves contained in `J.inside`, with
   carriers converging to `J.carrier` and, after a finite threshold, strictly
   nested closed regions.
4. Cut every band between consecutive polygonal curves into finitely many
   marked topological cells.  Each cell has:

   - a parent-boundary arc;
   - a child-boundary arc;
   - two side seams;
   - a quantitative bound keeping it close to the corresponding arc of
     `J.carrier`.

The existing Moise and triangulation work is reused here.  In particular,
the proof calls the existing `ClassificationOfSurfaces.Moise` polygonal
Jordan, finite-complex, triangulation, and polygonal Schoenflies APIs without
changing those files.

### B. Map each finite collar band to a standard radial shell

1. Define a matching cyclic cell decomposition of a shell between two
   homothetic standard triangles.
2. Construct a boundary homeomorphism for each source cell, respecting the
   four marked sides.
3. Extend each boundary map across the closed cell by the disk-extension
   theorem.
4. Prove adjacent cell maps agree on their common seam and glue the finite
   family into a homeomorphism of the entire closed band.
5. Restrict the band map to both its inner and outer polygonal boundaries.
6. Correct the band map on the standard shell so that its inner restriction
   agrees exactly with the preceding closed-disk stage.  Retain the induced
   outer-boundary homeomorphism for the next recursion step.

### C. Take the direct limit and add the Jordan boundary

1. Start with an Alexander extension of the first retained boundary map.
2. Recursively extend it across every later collar band.  The resulting
   finite closed-disk homeomorphisms agree exactly on all earlier disks.
3. Prove the shrinking source disks exhaust `J.inside`; the standard target
   disks exhaust the open standard triangle.
4. Use the compatible finite maps to define mutually inverse continuous maps
   on the two open exhaustions.
5. Use the marked-cell diameter estimates to prove that the open map and its
   inverse converge to the prescribed boundary correspondence.  Extend them
   to a homeomorphism

   ```lean
   closure J.inside ≃ₜ closedBall (0 : Plane) 1
   ```

   whose value on `J.carrier` is exactly `J.carrierHomeomorph.symm`.

This is Moise's bounded-side or “first form” of Schoenflies, represented by
`InsideRegionalExtensionData J`.

### D. Treat the outside and paste the two regional maps

Construct the analogous homeomorphism

```lean
closure J.outside ≃ₜ ((ball (0 : Plane) 1)ᶜ : Set Plane)
```

with the same boundary values.  Package the two maps as
`RegionalExtensionData J`.  The existing `RegionalExtensions` code converts
this to `DiskExtensionData J`, and the existing `AmbientGluing` code pastes
the regional maps into an ambient homeomorphism of the plane.  `Main.lean`
then gives the required image equality for `Set.range r`.

## 2. Progress so far

### Completed and compiling

The following parts are implemented without `sorry` or new axioms.

- The JCT-facing Jordan-region API and the Chapter 1--5 polygonal and
  finite-complex infrastructure are available and reused.
- The angular subdivision, access-hair, crosscut, auxiliary-Jordan-curve,
  separator, and nested polygonal-collar constructions are implemented.
- The shrinking recursive collar sequence has quantitative carrier and cell
  bounds.  Its sufficiently late bands are proved to have the required
  outward orientation and strict nesting.
- A source Moise band is proved to be exactly the finite union of its closed
  marked cells.  Adjacent intersections are exactly their shared seams, and
  nonadjacent cells are disjoint.
- The matching standard radial cells are constructed and proved to cover the
  complete target shell.
- Marked source-cell boundary maps are extended across their closed disks,
  proved compatible on seams, and glued into homeomorphisms of whole closed
  bands.
- The raw band homeomorphism has been restricted to genuine homeomorphisms
  on both the parent and child polygonal carriers.  The formerly arbitrary
  complementary cell boundary path is proved to be exactly the child edge;
  this avoids assuming a general boundary-invariance theorem.
- A band can be corrected to realize any prescribed inner-boundary
  homeomorphism, and its exact induced outer-boundary homeomorphism is
  retained.
- The generic operation that glues a compatible closed-disk map to one more
  shell was already implemented in `CompatibleDiskStages.lean`.
- The new shrinking-Moise specialization now constructs a recursive sequence
  of compatible closed-disk homeomorphisms.  It proves forward and inverse
  agreement between arbitrary earlier and later stages.  This work is in
  `CompatibleShrinkingMoiseDiskStages.lean` and compiles independently.
- The final regional-to-ambient pasting layer is implemented.  Given
  `RegionalExtensionData J`, it produces the exact LeanEval Schoenflies
  conclusion.

Recent committed checkpoints are:

```text
c55d03c control both boundaries of recursive Moise bands
a57fd69 glue recursive Moise bands to radial shells
5d59430 prove cyclic Moise cell compatibility
242575f construct seam-compatible Moise cell maps
0d81de5 build canonical radial target cells
e511ed5 identify recursive Moise band shells
d66261e prove eventual strict nesting of Moise collars
```

At this snapshot, `CompatibleShrinkingMoiseDiskStages.lean` and its import in
`MoiseChapter9.lean` are working-tree changes not yet included in one of the
listed commits.

### What “stripped-down end-to-end” currently means

There are two nearby but importantly different results:

1. `CompatibleInteriorHomeomorphism.lean` already gives a complete
   homeomorphism from `J.inside` to the interior of the standard triangle.
   It uses the older localized polygonal exhaustion.  This is an end-to-end
   result only for the **open interior stratum**; it does not extend to
   `J.carrier` and therefore does not prove Schoenflies.
2. The new shrinking-Moise route now reaches compatible homeomorphisms at
   **every finite closed-disk stage**.  It has not yet been taken through its
   own open direct limit, boundary extension, outside construction, and
   ambient pasting.

Thus, the stripped-down full Schoenflies proof is **not finished**.  The
finite combinatorial/topological core is substantially complete, but the
infinite boundary passage remains.

### Tasks remaining for the full theorem

1. **Prove source exhaustion for the shrinking sequence.**  Show every point
   of `J.inside` lies in the interior of some retained source disk.  The
   planned proof uses path connectedness of `J.inside`, convergence of the
   polygonal carriers to `J.carrier`, and eventual strict nesting.
2. **Build the shrinking-sequence open direct limit.**  Reuse the proof shape
   of `CompatibleInteriorHomeomorphism.lean` with the new finite stages and
   prove a homeomorphism from `J.inside` to the open standard triangle.
3. **Prove marked boundary control survives compatibility corrections.**  A
   corrected shell map must still send points in a source cell assigned to a
   level arc into a target sector whose diameter tends to zero at the
   corresponding parameter point.
4. **Extend across `J.carrier`.**  Define the boundary values, prove forward
   and inverse continuity at every boundary point, prove the two maps are
   inverse on the closed regions, and compose the standard triangle
   straightening with the unit disk.
5. **Construct the outside regional homeomorphism.**  Either transport the
   bounded-side theorem through a rigorously implemented inversion/compactified
   argument, or implement the outside collar construction directly.
6. **Assemble `RegionalExtensionData J` and discharge
   `HasMoiseDiskExtensions J`.**  The existing regional extension and ambient
   gluing code should then close the precise LeanEval theorem.
7. **Run the aggregate build and commit the new recursive-stage checkpoint.**

## 3. Known weak areas in the current proof

These are not `sorry`s; they are places where the current proved API is weaker
than the next theorem needs.

### Boundary control after shell correction

The raw marked band map has an exact formula on every cell.  The compatible
band map is obtained by postcomposing it with a radial shell adjustment that
forces agreement with the preceding stage.  The code currently proves exact
inner- and outer-boundary restrictions, but it does **not yet prove** that the
adjustment preserves each marked target sector, or an equivalent shrinking
diameter estimate.

This is the most important weak area.  The recursive maps are topologically
compatible, but topological compatibility alone does not imply continuity at
the limiting Jordan boundary.

The desired strengthening is one of:

- prove inductively that every retained boundary homeomorphism preserves the
  cyclic marked arcs, then show the radial adjustment preserves their
  sectors; or
- prove a direct uniform diameter estimate for each corrected band image.

The first route is preferable because it exposes the combinatorial invariant
that Moise's argument uses.

### Exhaustion of the Jordan inside by the shrinking collars

Carrier convergence and strict nesting are proved, but their combination has
not yet been packaged as an exhaustion theorem.  The claim is mathematically
standard, but its Lean proof must explicitly keep a path from an old interior
point to the requested point away from a sufficiently late polygonal
carrier, then use connectedness to select the bounded side.

This appears to be a contained lemma rather than a conceptual gap, but it is
a prerequisite for the direct limit.

### The older open-interior result is not yet reusable verbatim

The existing `compatibleInsideHomeomorph` is based on
`localizedMarkedPolygonalDisk`, whereas the quantitative shrinking estimates
belong to `shrinkingInsideCollarStage`.  The direct-limit argument can be
reused structurally, but the theorem itself cannot simply be cited for the
new finite maps.

### No closed-boundary extension yet

The repository has the needed source-cell shrink estimates and standard
radial geometry, but it does not yet contain the theorem that combines them
to prove continuity of the limit map at `J.carrier`.  Neither the forward nor
inverse boundary-continuity proof has been completed.

### Outside reduction is specified but not implemented

`RegionalExtensionData` requires both complementary regions.  Only the
inside construction is currently being developed.  The code does not yet
contain a verified inversion or compactification theorem that turns the
inside result into the required unbounded-side homeomorphism.

## 4. Risks and difficulties in the current approach

### Risk 1: the compatibility adjustment may erase localization

This is the main mathematical risk.  An arbitrary homeomorphism of a circle
can move a very small marked arc across a large part of the target boundary.
If the recursively accumulated boundary correction is controlled only as a
homeomorphism, the raw cell-diameter estimates are insufficient for boundary
continuity.  The proof must establish the stronger marked-arc invariant
before relying on those estimates.

If that invariant fails for the current correction, the finite-stage maps
remain valid, but the construction of the compatible maps must be changed.
The likely repair would be to choose boundary parameterizations coherently
from the outset or replace the unrestricted radial adjustment with a
cell-preserving one.

### Risk 2: the last infinite-limit theorem may be comparable in difficulty
to much of the finite construction

The finite cell-gluing results give genuine homeomorphisms at every stage,
but a limit of compatible homeomorphisms need not extend continuously to the
frontier without uniform control.  Proving both forward and inverse
continuity, with the exact prescribed parametrization, is the nonformal heart
of the remaining bounded-side proof.  It should not be treated as a routine
pasting lemma.

### Risk 3: inversion of the outside is subtle in the plane

Euclidean inversion is naturally a homeomorphism of a punctured plane and
exchanges a point with infinity only after one-point compactification.  A
casual “apply the inside theorem after inversion” argument does not directly
produce the exact subtype homeomorphism required by
`RegionalExtensionData`.  This step may require additional compactification
infrastructure or a separate outside exhaustion.

### Risk 4: dependent indexing remains an engineering cost

The shrinking collars package successor stages in dependent `Later` records.
The new wrapper has isolated the current coercions and index equalities, but
future cell-level limit theorems must still relate absolute collar indices,
recursive stage indices, and cyclic `LevelAddress` types.  This is manageable
but can make otherwise simple estimates expensive to express.

### Risk 5: duplicated proof branches can drift

There is an older localized-exhaustion branch with a complete open-interior
homeomorphism and a newer shrinking-Moise branch with the correct metric cell
control.  Reusing theorem patterns is valuable, but mixing the two source
disk sequences would create false compatibility claims.  New direct-limit
and boundary theorems should consistently use the shrinking sequence; the
older branch should serve as a template, not as an interchangeable source of
facts.

### Risk 6: upstream API movement

The new top-level `Schoenflies` files deliberately cite current theorem names
under `ClassificationOfSurfaces.Moise` and do not modify that directory.
When the collaborator moves the Moise material into a shared module, import
paths or namespaces may break.  Because the dependency is through theorem
names rather than copied proofs, this should be a mechanical migration, but
it will still require an aggregate build and likely import/name fixes.

## 5. Resolution of Risk 1 (2026-08-02 design analysis)

A close reading of the actual construction shows the marked-sector question
resolves positively, but with a twist: the limit boundary values are not the
raw prescription; they are the prescription composed with a limit circle
homeomorphism, and the discrepancy is repaired at the very end by one radial
composition.  The facts:

1. **The J-dependence cancels in the master marks.**
   `boundaryPoint J (J.curvePoint t) = sphereStraightening.symm (Arcs.param t)`
   because `curvePoint t = carrierHomeomorph (Arcs.param t)`.  Hence
   `levelTargetBoundaryPoint a` is the standard-triangle boundary point at the
   binary angular parameter of `a`, and the master target arcs are angular
   arcs whose parameter widths decay like `(2/3)^k`
   (`AccessibleAngularArc.descendant_width_le`).  Working in parameter space
   makes the decay exactly geometric with no Lipschitz analysis needed.

2. **The adjustment is angular, not an interpolation.**
   `standardShellBoundaryAdjustment` is the Alexander radial extension
   conjugated by the homogeneous gauge `triangleToBall`; it applies the same
   angular map at every radius (`ambientRadialHomeomorph_smul_ofSphere`), and
   therefore maps each radial sector over an arc `B` exactly onto the sector
   over the image arc.  In gauge coordinates every canonical target cell IS an
   annular sector (both circular sides are homothetic copies of one master
   arc), so sector control is purely an angular statement on the master
   circle.

3. **Stage recursion in angular terms.**  With `q_n` the accumulated inner
   discrepancy at stage `n` (`q_0 = id`), one has
   `q_{n+1} = induced(q_n) ∘ e_{n+1}⁻¹` where
   `e_{n+1} = rawInner_{n+1} ∘ rawOuter_n⁻¹` is the mismatch between the two
   canonical parametrizations of the shared polygon.  Both parametrizations
   send each retained level-`λ(n)` hair mark to the same target mark and each
   level-`λ(n)` sub-arc onto the same target arc, so `e_{n+1}` **fixes the
   coarse marks and preserves each coarse arc exactly**.  (This is the one
   substantial combinatorial lemma still to prove in Lean.)

4. **Summable drift and the limit twist.**  Arc preservation bounds the
   pointwise angular drift of `e_j` by the level-`(j-1)` window size, which is
   geometrically summable by (1).  Hence the accumulated angular maps
   converge uniformly (with uniformly convergent inverses) to a limit circle
   homeomorphism `q_∞`, and for any fixed tail cutoff `k` the stage-`n` cell
   image lies in the sector over `q̂_k(ball(θ_P, tail_k))`, whose diameter is
   controlled by continuity of the FIXED map `q_∞` plus `2·tail_k`.  This
   yields boundary continuity of the limit disk map with boundary values
   `q_∞`-twisted.

5. **Final repair.**  Compose the limit closed-disk homeomorphism with the
   Alexander radial extension of `q_∞⁻¹` (already available:
   `extendSphereHomeomorph` / `ambientRadialHomeomorph`).  This restores the
   exact prescribed boundary values required by `InsideRegionalExtensionData`
   without disturbing interior bijectivity.

Implementation order: (a) `RadialSectorTransport.lean` — polygonal sectors,
sector-transport under `standardShellBoundaryAdjustment`, sector diameter
estimates near the outer radius; (b) the `e_j` arc-preservation lemma from
the marked cell maps; (c) the parameter-space drift/uniform-limit layer;
(d) boundary continuity + final repair.  (a) and (c) are self-contained.

## Bottom line

The work has passed the stage where the principal uncertainty is whether the
finite Moise cells really form compatible annular homeomorphisms: that part is
now proved.  The project has **not** yet passed the principal infinite-limit
uncertainty.  The next go/no-go checkpoint should be a proof that the
recursive boundary corrections preserve marked sectors (or satisfy an
equivalent shrinking estimate).  Once that is established, the inside
exhaustion and open direct limit are mostly reuse; the closed-boundary limit
and outside reduction remain the two substantial end-to-end tasks.
