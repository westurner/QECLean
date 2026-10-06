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
  the legacy `LayerOutputSize` or final defect templates.
- The proposed `canonDefectEdge` convention normalizes active X/Z line edges
  to their data-layer owners and matched y-segment edges to xy owners.
  Idempotence, position preservation, active/inactive gates, upper-boundary
  preservation, and an exact fixed-point count are proved. `LayerPhysicalEdge`
  is the fixed-point carrier; `defectGluingSetoid` equates precisely those
  ambient edges with equal canonical representatives. This is not yet a
  validated reconstruction of the paper's coupling and replacement rules.
- `physicalSupport` transports owned supports to physical representatives,
  does not increase cardinality, and is unchanged by prior normalization.
  Physical X/Z Pauli lifts have phase-zero homogeneous type and exact support
  weight; their commutation criterion uses overlap after normalization.
  `normalization_can_change_overlap_parity` proves why pre-gluing evenness
  cannot be assumed to survive gluing.
- Twelve `LayerHalfStarLeg` slots describe the four bulk legs in each of the
  xz, xy, and yz planes at `LayerInteriorStarVertex`. Each four-leg plane
  projection recovers its existing surface-star geometry. `localXStar` has
  phase-zero X type and weight at most six whenever at most six legs are
  selected. No diagram-specific line/point template is inferred from this
  generic combinator; defect-specific boundary and coupling supports remain missing.
- `LayerFaceCell`, `LayerFacePlane`, and `layerFaceEdge` give four owned legs
  for a planar face. Their projections recover all three existing surface
  plaquettes, and the yz-owned support is recovered exactly. The canonical
  projection is injective within each owner layer, so `localZPlaquette`
  preserves the exact number of selected legs and has phase-zero Z type.
  Every such check has weight at most four; a full face has weight exactly
  four. These are planar primitives, not defect replacement/coupling checks.
- Standard rough xz/yz boundaries and smooth xz/xy boundaries now have owned
  three-leg primitives, projection laws, phase-zero physical lifts, and exact
  weight-three laws. Rough plaquettes keep the inward horizontal edge, as in
  the paper's surface-code diagram; the previous outward-edge convention
  anticommutes with a neighboring smooth star. All four two-by-two corner
  overlaps now have cardinality two. Their normalized physical checks commute
  for every supplied input and data-layer owner. Same-owner intersection and
  overlap-cardinality transport are proved; this does not apply unrestrictedly
  to supports on different owners.
- `card_physicalEdge_no_check_layers` proves that the proposed physical
  carrier is empty when `nX = nZ = 0`.
  `no_physical_capacity_without_check_layers` excludes the required
  `k ≤ N` capacity bound for positive `k` in that case. The unrestricted
  `CSSLayerInput` domain therefore cannot have a dimension-preserving
  constructor on this carrier: require a nondegenerate construction domain,
  or specify a different carrier/construction for degenerate inputs.
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
  and validated replacement templates are still required before changing the
  output qubit index. Proposed normalization and physical support transport
  APIs are now available, but are not a commutation proof for final defects.
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

1. **Canonical physical edges.** Use `LayerSurfaceEdge` as the owned ambient
  geometry and cuboid coordinates only for spatial location. The proposed
  `canonDefectEdge` convention sends active xy x-edges and yz z-edges to their
  data-layer copies, and matched yz y-edges to their xy copies. Idempotence,
  position preservation, active/inactive gates, upper-boundary preservation,
  and surjection onto the fixed-point subtype `LayerPhysicalEdge` are proved.
  The exact count is the owned-edge count minus `removedDefectEdges.card`.
  Verify this convention against every paper diagram, including any added
  coupling qubits, truncated layers, and superlattice spacing `c`, before
  replacing `LayerOutputSize`. These normalization laws alone do not prove
  that the convention realizes the paper's code.
  Resolve the proved zero-check capacity obstruction before a total
  constructor is promised: restrict its construction domain or define a
  separate degenerate geometry. Do not silently add count hypotheses to
  `CSSLayerInput` or pretend the existing carrier has capacity for positive
  `k` when both check counts vanish.
2. **Local legs and boundary rules.** Twelve bulk half-star leg slots and their
  three surface-star projection laws are implemented, along with normalized
  X-star type and six-leg weight bounds. Four-leg planar face combinators,
  all three projection laws, owner-fiber injectivity, and exact normalized
  Z-plaquette weights are also implemented. Standard rough/smooth boundary
  legs, their projection and weight-three laws, and normalized corner CSS
  regressions are implemented. Rough plaquettes omit the outer horizontal
  edge. Add defect-specific boundary and coupling plaquette supports. Specify the
  actual terminated direction for first/last incidences from the diagrams;
  do not infer it from the junction's axis name. Handle the existing `single`
  incidence case and degenerate dimensions explicitly. Record which surface
  slots survive at boundaries and defects.
3. **Eight line templates.** Translate all eight paper line cases into local
  owned supports, normalize them onto physical edges, and prove their
  applicability and exact support laws. Reuse existing x/z gates and
  nontrivial-y matching, but do not regard the shared-edge candidate lists as
  final physical checks. Distinguish geometric union of legs from Pauli
  multiplication: coincident factors in a product cancel modulo two.
4. **Point templates and total slots.** Factor the ten bulk and twelve
  boundary cases through the local leg/face combinators. Implement total
  vertex/cell classification and dependent star/plaquette slots so each
  location emits its replacement checks, never both old and new slots.
  Classification is not yet implemented. Prove slot coverage, exclusion of
  stale checks, and support uniqueness separately; pattern matching does not
  automatically prevent different slots from yielding equal supports.
5. **Local CSS verification.** Lift normalized supports to phase-zero X/Z
  checks and prove weight at most six. Prove distant supports disjoint and
  enumerate compatible adjacent vertex/cell neighborhoods. Choose a finite
  local carrier large enough for boundary and coupling qubits; 36 slots is
  not established. Prove each embedding injective on the actual normalized
  support and verify even overlap using kernel `decide`. Gluing can change
  overlap parity, so pre-gluing commutation cannot simply be transported.
  Then derive global cross-commutation and exclusion of `-I`.
6. **Rank, dimension, and logical lifts.** Count physical qubits and emitted
  slots, track local replacement deltas, and prove rank/independence; an Euler
  count of checks alone does not establish encoded dimension. Prove a pivot
  family exists with a consistent triangular orientation, or use the input
  rank and a chain-complex argument where sparse pivots do not exist. Dress
  input logical strings via even crossing pairings and prove centralizer,
  anticommutation, and cross-logical laws. Establish CSS-sector input logical
  representatives rather than assuming arbitrary logical operators are pure
  X or Z. Only then construct `LayerCode.outputCode` from the generated checks.
7. **Slice-based distance.** Define disjoint slice projections, prove their
  stabilizer invariance, and prove that a nontrivial output logical class has
  nontrivial input projections on enough slices. State spacing, boundary,
  nonzero-weight, and slice-multiplicity hypotheses explicitly before deriving
  a finite lower bound. The proposed floor formula with coefficient one does
  not follow from the paper's asymptotic bound without those proofs. Reserve
  `HasCodeDistance` for separately proved exact finite instances.
8. **Examples and decoding.** Validate the complete physical-edge constructor
  first on 3-qubit repetition and `[[4,2,2]]`, then Shor and Steane, and build
  the umbrella import. Retain exhaustive decoders as small-instance references.
  RG remains separate: supply cluster geometry and local topological-order/
  annihilation contracts, then use syndrome XOR for staged residual updates.

Commit each validated increment in this order: canonical normalization;
local templates; total slots; local/global CSS; rank and logical lifts;
slice distance and examples. Keep every checkpoint buildable and mark a step
complete only when its stated obligations are proved, not when a record stores
them as assumptions.

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

### Canonical-Edge Architecture Loop

This loop implements the proposed active-defect normalization and its
fixed-point physical carrier, followed by the gluing equivalence relation,
physical support/Pauli lifts, bulk local-star legs, and planar-face combinators. Regression
theorems cover active and inactive gates, unmatched upper boundaries, all
three star and face plane projections, exact yz-owned face recovery, exact
normalized planar Z-check weights, and loss of overlap parity under gluing.

The standard-boundary increment adds owned rough/smooth legs and exact
physical weights, fixes the inward-edge rough truncation, and verifies all
four two-by-two rough/smooth corners before and after normalization. The
surface-code diagram (`TikzFiguresUnrotated.pdf`, page 10) was inspected; the
source assets were left untouched. A standard boundary primitive is not a
replacement slot: full face slots at truncated boundaries still need to be
suppressed by the total construction. Defect termination, `single` incidence,
coupling supports, and the complete line/point case table remain outstanding.

The subsequent domain regression proves that both zero check counts give an
empty physical carrier and that positive logical capacity then cannot hold.
Choosing a restricted construction domain versus a separate degenerate
carrier remains a required contract decision. The first/middle z-junction
diagrams (pages 33/34 of `TikzFigures.pdf`) were inspected: their displayed
modified stars have five legs, so the existing four-edge candidates must not
be emitted as complete line templates.

Focused Lean checks and the Layer build (`3,147` jobs) pass, with the existing
linter warnings unchanged. The parent documentation build also succeeds with
29 warnings about existing documentation references. The eight-step plan now makes diagram validation,
slot uniqueness, normalized local embeddings, rank, dressed logical operators,
and finite slice-distance constants explicit obligations. None is replaced by
an Euler count, an assumed pivot assignment, or a supplied certificate.