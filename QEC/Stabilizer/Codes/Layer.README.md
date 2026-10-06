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
- A separate pre-defect `LayerSurfaceEdge` space retains layer ownership of
  each surface edge. Its exact count is
  `6 * n * nX * nZ + 2 * (n * nX + n * nZ + nX * nZ)`.
  Owner and cuboid position jointly identify each edge. Coincident xy/yz
  crossing edges have equal positions but are distinct qubits. Owned xy stars
  and yz plaquettes have weight four, recover the original supports under
  position projection, and commute for arbitrary cross-layer coordinates.
  Generic numbered support lifts preserve support and weight and characterize
  X/Z commutation by even overlap. This space is not yet connected to
  `LayerOutputSize` or defect coupling.
- Candidate four-edge Z plaquettes and interior X stars on xz, xy, and yz
  layers, plus three-edge rough-boundary plaquettes and smooth-boundary stars
  on the orientations specified by the paper. Support cardinalities and Pauli
  weights are proved.
- Separate stabilizer subgroups for the homogeneous bulk Z and X candidate
  families, and separate surface X/Z groups including standard boundaries.
  They are not combined: cross-commutation is not established.
- Even-cardinality proofs and an ordered matching for each X/Z check overlap.
  Matched y-segments, trivial crossing complements, X/Z incidence lines, and
  first/middle/last incidence labels are represented as finite geometry. The
  matched and trivial y-segments are proved disjoint and exhaustive, and both
  kinds now appear in the line index used for point-intersection detection.
- Point-defect locations as intersections of distinct line supports, split
  into bulk and boundary vertices.
- Finite indices for the ten bulk and twelve boundary point-defect case labels
  from the paper, with a theorem that the combined taxonomy has 22 cases. The
  indices classify configurations only; they do not define the diagrammed
  point-check supports. Each bulk label also carries its X/Z incidence
  position (or a trivial crossing) and oriented y-junction pattern. The bulk
  classification counts are proved: one trivial X-crossing case, one trivial
  Z-crossing case, and two nontrivial through-y cases. Boundary
  applicability tags identify the two
  middle-z cases with an extra plaquette and the six x-junction cases with
  modified boundary stars.
- Candidate X-star supports and adjacent-face Z-plaquette supports at x/z
  junctions, with first/middle/last orientation choosing the forward data cell
  except at the last incidence. The candidate Paulis are type-correct and have
  proved weight four. Finite x/z candidate lists now enumerate all indexed
  stars and applicable plaquettes, with exact membership, phase-zero CSS type,
  and weight-four laws. They are not final replacement-aware check lists.
  The extra x-junction Z plaquette is gated
  to first/middle cases, and the extra z-junction Z plaquette to the middle
  case, matching the paper's line-defect descriptions.
- Interior nontrivial-y cell candidates require two consecutive edges in a
  matched segment. Their X/Z lifts are type-correct with weights four and five;
  the same-cell pair has exactly two common edges and provably commutes. A
  reusable theorem identifies X/Z edge-lift commutation with even support
  overlap. Arbitrary-cell and cross-family commutation remain unproved, so
  these candidates remain outside the generated check lists.

Implemented in `../Framework/Core/Logical/Decoder.lean`:

- Exhaustive minimum-weight decoding for any supplied finite `StabilizerCode`,
  plus separate exact X-only and Z-only syndrome decoders.
- A proof that a minimum-weight recovery is logically correct for errors below
  half a supplied distance lower bound, up to stabilizer and global Pauli phase.
  The sector decoders have the same conditional correction guarantee.
- The exhaustive Pauli universe has exactly `4^(n + 1)` elements, and every
  syndrome candidate set is bounded by that count. This makes the reference
  decoder's exponential search explicit; it is not an RG decoder.
- Pauli-product syndromes compose by pointwise Boolean XOR, providing the
  algebraic residual-update law needed by a future multiscale decoder.

Still incomplete:

- `LayerCode.outputCode` is still an input certificate; the CSS input does not
  yet produce the output code.
- The unmodified shared-edge surface lists provably fail cross-commutation:
  `unmodified_surface_candidates_not_cross_commuting` exhibits an xy star and
  yz plaquette with one common edge in a `n = 2, nX = 1, nZ = 2` cuboid.
  Consequently, appending the existing lists unchanged cannot construct a
  stabilizer code. The layer-owned space addresses uncoupled crossing identity
  and the owned xy-star/yz-plaquette commutation obstruction; defect coupling
  and replacement-aware support transport are still
  required before changing the output qubit index.
- The full figure-defined line- and point-defect checks are not encoded. The
  x/z and interior nontrivial-y templates above are only partial candidates;
  y cross-commutation, complete line lists, replacement rules, and all 22
  point-defect support families remain to be added to generated check lists.
- Sector decoders are exhaustive reference algorithms, not efficient
  renormalization-group decoders. The Layer-codes paper does not specify its
  suggested specialized decoders.
- The cited general RG method requires cluster geometry and local
  topological-order and annihilation contracts that the certificate-based
  `LayerCode` does not supply. The syndrome-XOR theorem alone does not
  implement clustering, local recovery, or a multiscale decoder.
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
  qubit count. The shared-edge crossing regression is now proved and the
  pre-defect layer-owned edge space is implemented. Connect that space to
  explicit defect coupling and superlattice spacing rather than identifying
  coincident edges merely because their coordinates agree. The paper's
  physical-qubit scaling discussion uses a spacing constant `c`; neither
  current finite count is an exact paper-output count.
2. **Reconcile surface checks with defects.** Rough/smooth boundary supports
  and their cardinality laws are implemented. Confirm which ordinary surface
  checks must be omitted or replaced where line defects meet those boundaries.
3. **Encode line-defect checks.** Translate all eight line-junction cases from
   the paper (three x-oriented, three z-oriented, and trivial/nontrivial
  y-oriented) into finite edge supports. Initial four-edge x/z star and
  adjacent-face plaquette candidates now have type and weight proofs. Finish
  the complete lists, y-junction checks, applicability conditions, and
  replacement/incidence lemmas for every family.
4. **Encode point-defect checks.** The ten bulk and twelve boundary case labels
  are now indexed, along with boundary tags for the extra-plaquette and
  modified-star families. Translate each into explicit support constructors
  and state which adjacent line checks are replaced so the final generator
  list has no duplicates or stale bulk checks.
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
  algorithm open. For an RG implementation, first supply cluster geometry and
  local topological-order/annihilation contracts, then use the syndrome-XOR law
  to justify staged residual updates. Test the full constructor on the
  3-qubit repetition,
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
lake build QEC.Stabilizer.Framework.Core.Logical.Decoder
lake env lean QEC/Stabilizer/Codes.lean
rg -n 'sorry|admit|native_decide' QEC/Stabilizer/Codes/Layer.lean QEC/Stabilizer/Framework/Core/Logical/Decoder.lean
git diff --check
```

The `rg` command is an audit, not a substitute for Lean's diagnostics. Also
build each focused example module and the `QEC.Stabilizer.Codes` umbrella after
the constructor is integrated.

### Recorded Checkpoint

The previous development loop produced seven focused commits, from `01029ee`
through `3bb1806`. At that checkpoint:

- `lake build QEC.Stabilizer.Codes.Layer` passed at `3,147/3,147` jobs.
- `lake build QEC.Stabilizer.Framework.Core.Logical.Decoder` passed at
  `3,144/3,144` jobs.
- `git diff --check` passed.
- The broader `lake build QEC.Stabilizer.Codes` still had failures in unrelated
  modules.

The full check lists, point-defect supports and replacement rules, output
CSS/dimension/distance laws, and RG decoder remain incomplete. Preserved `.tmp`
paper files and unrelated parent-worktree changes were left untouched.

### Follow-On Implementation Loop

Four tested increments advance the construction work:

- Prove the exact two-edge same-cell nontrivial-y overlap and Pauli commutation.
- Enumerate finite x/z line candidates with exact plaquette applicability,
  membership, phase-zero CSS type, and weight-four laws.
- Prove the shared-edge surface assembly obstruction and introduce layer-owned
  pre-defect edges with cardinality, identity, and coordinate-projection laws.
- Lift owned xy stars and yz plaquettes, preserving their spatial supports and
  weight four while proving arbitrary-coordinate cross-layer commutation.

Each increment passed the focused Lean check and
`lake build QEC.Stabilizer.Codes.Layer` (`3,147` jobs), plus whitespace and
proof-placeholder audits. With explicit user authorization, this loop used the
installed pinned Lean `v4.35.0-rc3` toolchain in the Sustainable Factory
container rather than the otherwise-required standalone QECLean devcontainer.

Final assembly still requires explicit defect coupling and replacement rules
on the layer-owned qubit space. The old shared-edge lists cannot satisfy the
required CSS commutation law unchanged. No output-code constructor,
dimension/distance theorem, or RG decoder is claimed by these increments.