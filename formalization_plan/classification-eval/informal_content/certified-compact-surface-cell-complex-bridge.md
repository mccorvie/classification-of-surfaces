# Certified compact-surface cell-complex bridge

For every compact connected Hausdorff topological two-manifold with boundary, produce a
`SurfaceCellComplex K` together with:

```lean
Nonempty (S ≃ₜ K.Realization) ∧ K.IsSurfaceValid ∧ K.IsConnected
```

Obtain the geometric triangulation and its global incidence certificate from the Radó route,
transport the certificate to the finite triangulation, convert its incidence data to the cell
complex, and use the triangulation-to-polygon-quotient homeomorphism for the first conjunct.
