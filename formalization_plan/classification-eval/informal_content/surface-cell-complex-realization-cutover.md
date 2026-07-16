# SurfaceCellComplex realization cutover

Delete the arbitrary `realization` and `realizationTop` fields from `SurfaceCellComplex`. For a
complex whose boundary occurrences admit the pairing certificate, define its pre-realization as the
disjoint union of one marked polygonal disc per face and define its realization as the quotient by
the generated side identifications.

The cutover must be atomic: constructors, examples, `Equivalent`, and every theorem mentioning
`K.Realization` must move to the new definition together. In particular,
`FiniteSurfaceTriangulation.toCellComplex_realization_homeomorphic` must stop being reflexivity and
become the separate triangulation-to-polygon-quotient theorem.
