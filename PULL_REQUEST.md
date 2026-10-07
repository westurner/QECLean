# PR: Extend Layer-Coding Formalization

**Base:** `upstream/main`  
**Branch:** `extend-layer-coding`

## Summary

Port QECLean to Lean `v4.35.0-rc3`, add a finite Layer-code geometry and
junction model, and add a generic exhaustive minimum-weight decoder with a
conditional correction theorem. The Layer module remains a certificate/model
boundary: it does not construct the complete output stabilizer code from an
input CSS code.

## Changes

### Lean 4.35 compatibility

- Pin Lean, Mathlib, and LeanArchitect to compatible `v4.35.0-rc3` revisions.
- Update proof elaboration across `Foundations/Basic.lean`, `Foundations/Gates.lean`,
  the Pauli representation and commutation modules, CSS predicates, codespace,
  logical operators/gates, and symplectic independence proofs. These are
  compatibility changes to coercions, projection reduction, finite `Fin 4`
  phase arithmetic, and explicit family arguments; they do not change the
  represented quantum-code semantics.
- Replace old set-builder helpers with the pinned Mathlib `Set.ofPred` API in
  `IndependentEquiv.lean`.

### Layer geometry

- Extend `CSSLayerInput` with an actual input `StabilizerCode`, a generator-list
  correspondence, and a supplied input-distance lower-bound premise.
- Define a finite oriented cuboid edge type, prove its cardinality, and map it
  to QECLean's `Fin`-indexed Pauli qubits.
- Add a separate layer-owned surface-edge space with exact cardinality and
  owner/position injectivity. Coincident uncoupled xy/yz edges remain distinct.
  This is the ambient geometry for proposed normalization, not yet the legacy
  output qubit index or a validated final defect construction.
- Implement the proposed active-defect canonical projection on owned edges.
  Active xy x-edges and yz z-edges normalize to data-layer copies; matched yz
  y-edges normalize to xy copies. Prove idempotence, spatial preservation,
  active/inactive and upper-boundary gates, and a surjection onto fixed-point
  `LayerPhysicalEdge`. Its exact count is the ambient owned-edge count minus
  removed representatives. Paper-diagram correspondence and check replacement
  correctness remain unproved; the existing output index is unchanged.
- Supply the gluing setoid, canonical physical support transport, numbering,
  and phase-zero X/Z Pauli lifts with exact support weights. Commutation is
  characterized by normalized support overlap. A kernel-decided regression
  proves that idempotent normalization can destroy even overlap.
- Add twelve bulk half-star leg slots and prove that each four-leg plane
  projection recovers its original surface star. Selecting at most six legs
  yields a normalized X check of weight at most six. Boundary truncation,
  coupling plaquettes, and the diagram-specific case table remain incomplete.
- Add four-leg owned planar faces in all three orientations, with exact
  surface-plaquette projection laws and yz-owned support recovery. Prove
  canonical representatives remain distinct within an owner layer, yielding
  exact selected-leg weight and phase-zero Z type for normalized planar
  plaquettes. Full faces retain weight four after active-defect normalization;
  no coupling-specific replacement or global CSS law is inferred from this.
- Lift owned xy stars and yz plaquettes to Paulis, prove weight four, and
  prove cross-layer disjointness and commutation for arbitrary coordinates.
  Their coordinate projections recover the original cuboid supports. A
  generic numbered-support lift supplies support, weight, and even-overlap
  commutation laws while preserving the existing cuboid lift APIs.
- Lift finite edge supports to X/Z Paulis and prove support, type, and weight
  properties. Define four-edge surface plaquettes and four-edge interior stars
  on xz, xy, and yz layers, together with three-edge rough-boundary Z
  plaquettes and smooth-boundary X stars in the orientations specified by the
  paper.
- Add owned three-leg rough xz/yz plaquettes and smooth xz/xy stars, their
  spatial projection laws, and phase-zero physical lifts of exact weight
  three. Correct rough plaquettes to retain the inward horizontal edge: the
  former outer-edge convention gave odd overlap at a smooth/rough corner.
  Verify all four two-by-two corners commute, including on normalized
  physical representatives for every input and data-layer owner. Prove
  same-owner overlap transport without assuming it for cross-owner gluing.
- Prove a construction-domain obstruction: with both check counts zero,
  `LayerPhysicalEdge` has cardinality zero, so positive `k` cannot satisfy
  the output capacity bound. A dimension-preserving constructor on this
  carrier needs an explicit domain restriction or a different degenerate
  carrier. The general input interface has not been silently restricted.
- Choose positive X/Z counts through `LayerConstructionDomain` for the future
  paper-style constructor, preserving the unrestricted input interface.
  Inject input qubits into fixed data-layer representatives to derive
  `n ≤ N` and `k ≤ N`; these do not establish stabilizer rank or dimension.
- Implement a reflected five-leg bulk z-line X-star shape with exact spatial
  support, distinct positions, phase-zero X type, and physical weight five.
  Its incidence applicability, coupling plaquettes, point replacements, and
  emitted-slot integration remain separate obligations.
- Prove the compact interior-vertex obstruction for either one-check sector.
  Add explicit padded spacing, real-layer coordinate recovery/separation,
  and an actual-owner `LayerGridSurfaceEdge` with exact count and injective
  ambient embedding. Its one-X/one-Z junction is inhabited.
- Normalize the spaced grid directly from original input rows and scaled
  half-open pairing intervals; prove position preservation, idempotence, and
  active/inactive x/z gates. Number fixed-point `LayerGridPhysicalEdge`, prove
  its count, and derive logical capacity by a data-qubit injection, including
  empty check sectors. Do not inflate generator counts to grid dimensions.
  Template migration and final output assembly remain unfinished.
- Lift spaced actual-owner supports to X/Z Paulis with exact normalized
  weights and an even-overlap commutation criterion. Spatially injective
  local maps remain injective on the fixed-point carrier.
- Migrate the five-leg z-line X-star to original data/Z-check owners, prove
  exact ambient recovery, normalized weight five, and phase-zero X type.
  Dispatch actual ordered incidences with forward first/middle and reflected
  last orientations. Name point intersections and single incidences as
  unresolved states, prove they are exactly the absent-candidate cases, and
  prove every emitted candidate's weight and type. This is not a complete
  termination or replacement rule. The finite endpoint adjacency tests below
  are verified, but general coupling and replacement laws remain incomplete.
- Migrate all three ordinary planar-face orientations to the spaced
  actual-owner carrier. Prove exact ambient recovery, spatial/physical leg
  injectivity, selected-leg weight preservation, phase-zero Z type, the
  weight-four bound, and full-face weight four. These are not defect coupling
  plaquettes and do not establish cross-commutation with the line stars.
- Prove prefix-padding coordinates have no real owner and physical overlap
  cardinalities equal canonical-image overlap cardinalities. Exact absence
  of embedded owners and a prefix-star fixed-point law are also proved.
  Generalize owner absence to the successor of every real-owner coordinate
  using spacing, and prove the corresponding yz z edge stays fixed under
  normalization. Reuse this law in the inward-face fixture.
- Register structural computable equality for spaced owned edges. Resolve
  the earlier failed adjacency probe by explicit per-leg normalization and
  kernel `decide`: the finite forward-star fixture has one shared edge with
  the outward ordinary yz face and two with the inward face. Prove physical
  noncommutation outward and commutation inward. No custom axiom, placeholder,
  native evaluation, or elaboration option is introduced.
- Gate ordinary check-sheet face candidates to the span of active input
  incidences, excluding cells outside the endpoints and prefix padding.
  Singleton supports have no ordinary-face interval. Prove exact candidate
  emission/absence, weight four, and Z type; verify outward suppression and
  inward retention in the fixture. The gate does not remove unused physical
  qubits or define middle coupling, boundary/point replacements, or global CSS.
  The roadmap now requires coupling-qubit identity validation at middle
  junctions before promoting any gluing convention to the final constructor.
- Characterize ordinary check-sheet spans by active extrema and finite-support
  minimum/maximum. Prove the existing rank classifier's first/last/single
  labels imply least/greatest/unique owner semantics. Derive general ordinary
  yz candidate absence before actual first Z junctions, from actual last Z
  junctions onward, and for all singleton Z rows. No general endpoint CSS,
  physical-qubit truncation, or singleton defect replacement is claimed.
- Prove a general physical-support insertion redundancy law when two owned
  edges have the same canonical image. Test an inward yz face augmented by
  its coincident data-owned z edge: its owned support has cardinality five,
  but active gluing makes its physical Z Pauli exactly the ordinary
  weight-four plaquette. This rules out that naive insertion as a distinct
  middle replacement on the current carrier; no paper-support correspondence
  or revised gluing convention is claimed.
- Build separate same-type surface X/Z stabilizer groups that include those
  standard boundary candidates. Cross-sector commutation with line/point defect
  checks remains unproved because those checks are not yet encoded.
- Derive even X/Z overlap from CSS commutation; pair overlap indices in their
  canonical order; define matched y-segments and their trivial remainder; and
  index X/Z line supports and their incidence positions.
- Represent point defects as vertices touched by distinct line supports, and
  partition these vertices into bulk and boundary sets.
- Keep X- and Z-type bulk candidate groups separate. Their cross-commutation is
  not established. `LayerCode.outputCode` remains a supplied certificate with
  a distance lower bound, rather than a constructor derived from the input.

### Generic decoder

`Framework/Core/Logical/Decoder.lean` defines a binary syndrome for a supplied
finite stabilizer code, an exhaustive all-Pauli minimum-weight decoder, and
separate exhaustive X-only and Z-only minimum-weight decoders. Each has a
conditional correction theorem below half a supplied distance lower bound,
up to stabilizers and global Pauli phase. `LayerCode` exposes all three. The
Pauli search universe is now proved to have `4^(n + 1)` elements, bounding each
syndrome candidate set explicitly. These are exact reference decoders, not
efficient renormalization-group decoders. The syndrome of a Pauli product is
also proved to be the pointwise XOR of the factor syndromes, establishing the
algebraic update law needed by a future RG implementation.

## Compatibility notes

### Why `noncomputable`?

`noncomputable` is not a Lean 4.35 feature requirement by itself; it records
that the declaration's implementation may use noncomputable choice or
classical instances. Here the sources differ by definition:

- `layerEdgeEquiv` uses `Fintype.equivFin` to choose a numbering of the finite
  edge type. Candidate-list and ordered-pairing definitions also use finite
  choice/order constructions.
- Stabilizer-group construction depends on QECLean's noncomputable Pauli group
  operations and subgroup closure.
- The decoder uses `Classical.choose` to select a minimum from a nonempty finite
  candidate set; its specification is proved separately.
- The support and weight wrappers currently use a local `classical` context,
  so their definitions are marked noncomputable and that marker propagates to
  group-element support and weight. `PauliOperator` does derive `DecidableEq`,
  so these particular markers may be reducible with a narrower explicit
  decidability implementation. They should not be presented as inherently
  required by Lean 4.35 without that separate check.

These markers mean Lean does not promise executable code for those definitions;
they do not bypass kernel checking. A theorem using classical definitions may
depend on Lean's standard `Classical.choice` axiom, but this patch introduces no
custom axiom.

### Why `Set.mem_ofPred`?

The pinned Mathlib defines `Set.mem_ofPred` and `Set.mem_ofPred_eq` for
predicate-built sets and retains `Set.mem_setOf` and `Set.mem_setOf_eq` only as
deprecated aliases (deprecated since 2026-07-09). The branch uses the `iff`
form where a membership proposition is rewritten and the equality form where
`simp only` expects an equation. This migration is forward-compatible API
cleanup; the deprecated aliases still exist in this revision, so the rename
alone is not required to make the target compile.

## Model comparison and limits

The primary [Layer-codes paper](#williamson-baspin-2024) supports the
high-level arrangement used here:
physical-qubit layers on xz planes, X-check layers on xy planes, Z-check layers
on yz planes, and junctions determined by the input Tanner incidences. It also
states the scaling $N=\Theta(n n_X n_Z)$, $K=k$, and
$D=\Omega(d\min(n_X,n_Z)/w)$, with maximum check weight six.

No source reviewed contradicts that high-level arrangement. The standard
rough/smooth boundary checks are now included. The remaining gap is the paper's
explicit line- and point-defect checks (eight line cases, ten bulk point cases,
and twelve boundary point cases), whose supports are given as lattice diagrams.
Initial four-edge X-star and adjacent-face Z-plaquette candidates now exist at
x/z junctions, with type and weight proofs, but they are not yet organized into
all eight case-specific families or replacement rules. Finite x/z candidate
lists enumerate the existing stars and gated plaquettes; exact membership
laws enforce the incidence gates, and all listed checks have phase-zero CSS
type and weight four. These are not final replacement-aware lists. The y-junction
geometry now proves that matched nontrivial segments and their trivial
complement are disjoint and exhaustive, and the line index includes both for
point-location detection. The modified y-junction Pauli checks and all
point-defect supports are still missing. Interior nontrivial-y X/Z support
candidates now have type and weight proofs, but their cross-sector overlap is
proved to have cardinality two for the same-cell pair, whose Paulis commute.
A reusable edge-lift criterion equates X/Z commutation with even overlap.
Arbitrary-cell and cross-family commutation remain unproved, and the candidates
are not integrated into the check lists. Plaquette
applicability is now gated to first/middle x incidences and middle z incidences.
The ten bulk and twelve boundary point-defect patterns are now indexed as a
22-case taxonomy. Bulk labels carry the X/Z incidence positions and oriented
y-pattern; boundary metadata marks the two extra-plaquette cases and six
modified-star cases. Diagrammed supports and adjacent-check replacements
remain unimplemented. The bulk classification counts are proved: one trivial
X-crossing case, one trivial Z-crossing case, and two nontrivial through-y
cases. These counts classify labels, not generated point-defect supports.
Its exact finite
edge count is a formal indexing choice and has not been proved to match the
paper's boundary-spacing convention or exact physical-qubit count. For positive
dimensions, the formal edge count is now bounded between `3 n n_X n_Z` and
`12 n n_X n_Z`, matching the paper's asymptotic volume scaling. Consequently,
the paper's distance, locality, topology, and scaling results are not theorems
of this Lean module.

A concrete regression theorem now proves that the unmodified shared-edge
surface candidate lists do not cross-commute: for `n = 2, nX = 1, nZ = 2`, an
xy star and yz plaquette share one edge. Therefore these lists cannot simply
be appended into a stabilizer code. `LayerSurfaceEdge` introduces layer-owned
pre-defect qubits, whose count is
`6 * n * nX * nZ + 2 * (n * nX + n * nZ + nX * nZ)`, to distinguish uncoupled
coincident edges. The owned xy-star/yz-plaquette pair is now proved disjoint
and commuting for arbitrary coordinates, with weight four and the same
projected spatial supports. Explicit defect coupling, replacements, and the paper's
superlattice spacing constant `c` still need to be connected to the output
index; neither finite edge count is claimed as the paper's exact output count.

The revised completion plan uses canonical physical edges, local leg/face
templates, total replacement-aware slots, and finite local commutation checks.
Normalization is now implemented, but it is an explicit proposed gluing
convention, not a derivation of all paper checks. Slot classification does not
by itself prove support uniqueness or rank. Quotienting can change overlap
parity, so local embeddings must be injective on the normalized supports.
Euler counts, triangular pivots, CSS logical representatives, and slice
nontriviality each require separate proofs. No exact distance formula or
fixed 36-edge local carrier is claimed without those obligations.

The zero-check domain obstruction is now kernel-checked. Additionally, direct
inspection of the first/middle z-junction diagrams shows five-leg modified
stars; the earlier four-edge candidates are not complete replacements. The
five-leg bulk shape is implemented, but not emitted into the output code.
The chosen positive-count construction domain has derived capacity bounds;
it neither changes the input interface nor claims a degenerate fallback.
The ordinary three-qubit repetition example is outside this positive-count
domain and is deferred; the first planned constructor examples are
`[[4,2,2]]`, Shor, and Steane. Independent generator lists must not be padded
with identity checks to evade the domain condition.

The subsequent spaced-grid model repairs a further compact-geometry issue:
one-check sectors have no compact bulk star vertex. Padded interior coordinates
and actual-owner gluing now resolve that issue and the geometric capacity gap.
They do not establish the final emitted checks, diagram correspondence,
global CSS, rank, encoded dimension, or distance; the output certificate and
legacy qubit index remain unchanged.

The paper explicitly leaves specialized decoding open, while noting that a
general renormalization-group decoder is applicable. The exact X/Z sector
decoders added here are separate exhaustive reference algorithms; they do not
implement that RG method or claim efficiency. The cited general RG method
needs cluster geometry and local topological-order and annihilation contracts
that the certificate-based `LayerCode` does not currently supply. The
syndrome-XOR law is algebraic groundwork only, not an RG implementation. Other
published local-code constructions, including Portnoy's subdivided-manifold
construction [#portnoy-2023] and Lin, Wills, and Hsieh's subdivision approach
[#lin-wills-hsieh-2023], use different construction mechanisms rather than
contradicting this Layer model. They do not validate this particular lattice
indexing.

## Verification

The previous development loop produced seven focused commits, from `01029ee`
through `3bb1806`. This is a partial-completion checkpoint, not completion of
the Layer construction plan. Recorded checks at that checkpoint:

- `lake build QEC.Stabilizer.Codes.Layer` under Lean `v4.35.0-rc3`: passed,
  `3,147/3,147` Lake jobs.
- `lake build QEC.Stabilizer.Framework.Core.Logical.Decoder`: passed,
  `3,144/3,144` Lake jobs.
- `git diff --check`: passed.
- The broader `lake build QEC.Stabilizer.Codes` still fails in unrelated
  modules; focused successes do not imply an umbrella-build success.
- Preserved `.tmp` paper files and unrelated parent-worktree changes were
  left untouched.
- The follow-on implementation loop kernel-checked each of four increments
  (local y commutation, gated x/z lists, owned geometry/crossing regression,
  and owned-check lifting) and rebuilt `QEC.Stabilizer.Codes.Layer` successfully
  at `3,147` jobs each time. Whitespace and proof-placeholder audits passed.
  The installed pinned toolchain in the parent container was used with
  explicit user authorization. Final defect coupling/replacement integration
  and the output CSS/dimension/distance and RG obligations remain unfinished.
- The canonical-edge architecture loop also passes focused Lean checks and
  the `3,147`-job Layer build for normalization, physical support/Pauli lifts,
  bulk-leg/face projection regressions, owner-fiber injectivity, and exact
  planar Z-plaquette weights. The original linter warnings remain;
  no proof placeholders or custom axioms were introduced.
  The parent documentation gate (`make -C docs html`) also succeeds with
  29 warnings about existing documentation references.
- The standard-boundary increment also passes focused Lean and the
  `3,147`-job Layer build, whitespace and proof-placeholder audits, and the
  parent documentation gate. The surface-code boundary diagram was inspected
  directly; source PDFs were preserved. These tests do not establish global
  CSS or boundary replacement-slot completeness.
- The Sustainable Factory root devcontainer installs PyMuPDF in an isolated
  `/opt/pdf-tools` virtual environment for inspecting the paper's PDF check
  diagrams. The root image could not be built here because Docker/Podman/Buildah
  is absent; the standalone QECLean image is unchanged.

## References

<a id="williamson-baspin-2024"></a> Williamson, D. J. and Baspin, N.,
["Layer Codes"](https://doi.org/10.1038/s41467-024-53881-3),
*Nature Communications* 15, 9528 (2024); [arXiv:2309.16503](https://arxiv.org/abs/2309.16503).

<a id="portnoy-2023"></a> Portnoy, E.,
["Local Quantum Codes from Subdivided Manifolds"](https://arxiv.org/abs/2303.06755),
arXiv:2303.06755 (2023).

<a id="lin-wills-hsieh-2023"></a> Lin, T.-C., Wills, A. and Hsieh, M.-H.,
["Geometrically Local Quantum and Classical Codes from Subdivision"](https://arxiv.org/abs/2309.16104),
arXiv:2309.16104 (2023).

Mathlib API source: [`Set.mem_ofPred` and deprecated aliases](https://github.com/leanprover-community/mathlib4/blob/v4.35.0-rc3/Mathlib/Data/Set/Operations.lean#L76-L94).

## Files

- [`QEC/Stabilizer/Codes/Layer.lean`](QEC/Stabilizer/Codes/Layer.lean)
- [`QEC/Stabilizer/Codes/Layer.README.md`](QEC/Stabilizer/Codes/Layer.README.md)
- [`QEC/Stabilizer/Framework/Core/Logical/Decoder.lean`](QEC/Stabilizer/Framework/Core/Logical/Decoder.lean)
- [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), and `lake-manifest.json`
