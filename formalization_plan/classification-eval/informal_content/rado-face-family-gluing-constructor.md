# Radó face-family gluing constructor

Given an old partial triangulation and a chart patch in the genuine overlap case, construct a final
partial triangulation together with maps from both old face families into the final family. Require:

- preservation of every old and patch face carrier;
- exhaustion of the final face family by the two maps;
- one old/patch pair sharing a two-vertex edge;
- no new edge of valence greater than two;
- an embedded global realization;
- the required support and absorbed-core inclusions.

These data are deliberately stronger than the present existential output of
`moise_induction_step`. They let the already-proved union lemma transport dual connectivity and let
the existing combinatorial-surface proof transport edge valence without guessing how the opaque
final face type was assembled.
