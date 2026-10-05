# Layer Codes: Status and Completion Plan

This note tracks the Lean formalization in `Layer.lean`. The comparison
baseline is branch `add-layer-codes`; the current development branch is
`extend-layer-coding`. The paper is Williamson and Baspin, *Layer Codes*,
arXiv:2309.16503 / Nature Communications 15, 9528 (2024).

The baseline already had the CSS check-row/weight/commutation record, layer
kind and plane tags, finite layer/cell indices, Tanner-incidence types, and a
certificate-style `LayerCode`. The additions below should be read as a delta
from that starting point, not as a claim that the paper lacks those concepts.

## Current Status

Implemented in `Layer.lean`:

- A `CSSLayerInput` contract tying binary X/Z rows to a QECLean `StabilizerCode`
  with matching logical-qubit count and an explicit input-distance lower bound.
- A finite oriented-edge indexing of a cuboid, edge-to-qubit numbering, and
  X/Z Pauli lifts from finite edge supports.
- Candidate four-edge Z plaquettes and interior X stars on xz, xy, and yz
  layers, plus three-edge rough-boundary plaquettes and smooth-boundary stars
  on the orientations specified by the paper. Support cardinalities and Pauli
  weights are proved.
- Separate stabilizer subgroups for the homogeneous bulk Z and X candidate
  families, and separate surface X/Z groups including standard boundaries.
  They are not combined: cross-commutation is not established.
- Even-cardinality proofs and an ordered matching for each X/Z check overlap.
  Matched y-segments, trivial crossing complements, X/Z incidence lines, and
  first/middle/last incidence labels are represented as finite geometry.
- Point-defect locations as intersections of distinct line supports, split
  into bulk and boundary vertices.

Implemented in `../Framework/Core/Logical/Decoder.lean`:

- Exhaustive minimum-weight decoding for any supplied finite `StabilizerCode`,
  plus separate exact X-only and Z-only syndrome decoders.
- A proof that a minimum-weight recovery is logically correct for errors below
  half a supplied distance lower bound, up to stabilizer and global Pauli phase.
  The sector decoders have the same conditional correction guarantee.

Still incomplete:

- `LayerCode.outputCode` is still an input certificate; the CSS input does not
  yet produce the output code.
- Figure-defined line- and point-defect Pauli supports are not encoded. In
  particular, none of the eight line-junction or 22 point-defect check families
  has yet been added to the generated check lists.
- Sector decoders are exhaustive reference algorithms, not efficient
  renormalization-group decoders. The Layer-codes paper does not specify its
  suggested specialized decoders.
- There is no proof that a complete candidate list commutes, has independent
  generators of length `N - k`, excludes `-I`, or has exactly `k` logical
  qubits. No output distance lower-bound theorem has been derived from the
  input hypotheses.
- The current cuboid edge count is an explicit formal model, not yet proved to
  match the paper's exact physical-qubit count or boundary spacing convention.
  For positive dimensions, it is now bounded between three and twelve times
  `n * nX * nZ`, establishing the same asymptotic volume scaling.

The bulk X and Z groups must remain separate until the defect modifications
that repair their cross-commutation are implemented and proved.

## Completion Plan

Work in the QECLean Dev Container with Lean, Lake, and ripgrep (`rg`) available.
Do not validate this Lean development with host tools from the Sustainable
Factory environment. Before starting, check `command -v lean lake rg` and
`lean --version`; the project toolchain is recorded in `lean-toolchain`.

1. **Reconcile the lattice model.** Compare `LayerLatticeEdge`, its exact
   cardinality, axis conventions, and boundary coordinates against the paper's
   lattice model. Record the relationship between the finite edge count and
   the paper's scaling equation before calling this the paper's exact output
   qubit count.
2. **Reconcile surface checks with defects.** Rough/smooth boundary supports
  and their cardinality laws are implemented. Confirm which ordinary surface
  checks must be omitted or replaced where line defects meet those boundaries.
3. **Encode line-defect checks.** Translate all eight line-junction cases from
   the paper (three x-oriented, three z-oriented, and trivial/nontrivial
   y-oriented) into finite edge supports. Use ordered input-check support for
   first/middle/last cases. Add weight and incidence lemmas for every family.
4. **Encode point-defect checks.** Translate the ten bulk and twelve boundary
   point-defect configurations into explicit support constructors. State
   which adjacent line checks are replaced so the final generator list has no
   duplicates or stale bulk checks.
5. **Prove the CSS stabilizer laws.** Assemble one X list and one Z list from
   the surface and defect checks. Prove phase zero, per-generator weight at
   most six, and every X/Z commutation relation. Reuse the existing CSS
   no-`-I` and homogeneous-type lemmas where their hypotheses apply.
6. **Prove code dimension and construct the code.** Prove generator
   independence and `generatorsList.length = outputN - k`. Construct logical X/Z
   representatives from the input code and prove centralizer membership,
   anticommutation, and cross-logical commutation. Only after these obligations
   are discharged should `LayerCode.outputCode` become a definition derived
   from the check list rather than a supplied certificate.
7. **Prove the distance statement at the right strength.** The paper gives
   asymptotic lower bounds for families, not an exact distance for every finite
   input. First derive a lower-bound theorem with explicit hypotheses; reserve
   `HasCodeDistance` for concrete instances where an exact witness and exact
   minimum are proved.
8. **Connect and test decoding.** Keep the exhaustive general and sector
  decoders as correctness references for small finite examples. Select and
  prove an efficient Layer-specific decoder separately; the paper leaves this
  algorithm open. Test the full constructor on the 3-qubit repetition,
  `[[4,2,2]]`, Shor, and Steane examples after their defect supports are
  available.

## Definition of Done

- `LayerCode` is constructed from `CSSLayerInput` and finite defect data; it
  does not accept an arbitrary `StabilizerCode` as its output.
- The physical-qubit index is proved to match the chosen lattice model, and
  all final checks are generated by the constructor.
- The resulting check list is phase zero, weight at most six, pairwise
  commuting, independent, and has exactly `N - k` generators.
- Logical operators and the stated distance lower bound are proved from the
  declared input hypotheses. Exact distance is claimed only for instances
  where it is established.
- Example constructors and the umbrella import build without `sorry`, `admit`,
  or `native_decide`.

## Dev Container Validation

Run one Lake process at a time from the QECLean repository root:

```sh
command -v lean lake rg
lean --version
lake env lean QEC/Stabilizer/Codes/Layer.lean
lake build QEC.Stabilizer.Codes.Layer
lake env lean QEC/Stabilizer/Codes.lean
rg -n 'sorry|admit|native_decide' QEC/Stabilizer/Codes/Layer.lean QEC/Stabilizer/Framework/Core/Logical/Decoder.lean
git diff --check
```

The `rg` command is an audit, not a substitute for Lean's diagnostics. Also
build each focused example module and the `QEC.Stabilizer.Codes` umbrella after
the constructor is integrated.