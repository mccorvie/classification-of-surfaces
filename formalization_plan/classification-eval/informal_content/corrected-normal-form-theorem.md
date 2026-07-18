# Corrected surface-cell-complex normal-form theorem

The intended statement is:

```lean
theorem surface_cell_complex_reduces_to_normal_form
    (K : SurfaceCellComplex)
    (hvalid : K.IsSurfaceValid)
    (hconnected : K.IsConnected) :
    ∃ N, N.IsEvalAdmissible ∧ K.HasNormalForm N
```

Reduce to one face and one derived vertex, separate the orientable and nonorientable cases, group
handles or crosscaps, and collect the boundary-component tails. Compose elementary-move soundness
with the canonical-quotient correspondence. The sphere case uses the separate two-monogon
realization theorem.
