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
- Lift finite edge supports to X/Z Paulis and prove support, type, and weight
  properties. Define four-edge surface plaquettes and four-edge interior stars
  on xz, xy, and yz layers, together with three-edge rough-boundary Z
  plaquettes and smooth-boundary X stars in the orientations specified by the
  paper.
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
efficient renormalization-group decoders.

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
the eight case-specific families or replacement rules. The y-junction
geometry now proves that matched nontrivial segments and their trivial
complement are disjoint and exhaustive, and the line index includes both for
point-location detection. The modified y-junction Pauli checks and all
point-defect supports are still missing. Interior nontrivial-y X/Z support
candidates now have type and weight proofs, but their cross-sector overlap is
not yet proved even and they are not integrated into the check lists. Plaquette
applicability is now gated to first/middle x incidences and middle z incidences.
The ten bulk and twelve boundary point-defect patterns are now indexed as a 22-case
taxonomy. Boundary metadata marks the two extra-plaquette cases and six
modified-star cases; diagrammed supports and adjacent-check replacements remain
unimplemented. Its exact finite
edge count is a formal indexing choice and has not been proved to match the
paper's boundary-spacing convention or exact physical-qubit count. For positive
dimensions, the formal edge count is now bounded between `3 n n_X n_Z` and
`12 n n_X n_Z`, matching the paper's asymptotic volume scaling. Consequently,
the paper's distance, locality, topology, and scaling results are not theorems
of this Lean module.

The paper explicitly leaves specialized decoding open, while noting that a
general renormalization-group decoder is applicable. The exact X/Z sector
decoders added here are separate exhaustive reference algorithms; they do not
implement that RG method or claim efficiency. Other
published local-code constructions, including Portnoy's subdivided-manifold
construction [#portnoy-2023] and Lin, Wills, and Hsieh's subdivision approach
[#lin-wills-hsieh-2023], use different construction mechanisms rather than
contradicting this Layer model. They do not validate this particular lattice
indexing.

## Verification

- `lake build QEC.Stabilizer.Codes.Layer` under Lean `v4.35.0-rc3`: passed,
  `3,147/3,147` Lake jobs.
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
