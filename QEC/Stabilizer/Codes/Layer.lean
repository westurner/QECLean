import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.Decoder

/-!
# Layer-Code Construction Boundary

Finite indexing and selected checks for a 3D Layer-code construction. This
module records CSS input data and an output-code certificate; it does not yet
construct the paper's complete output stabilizer code or prove its asymptotic
parameter bounds.
-/

namespace Quantum
namespace Stabilizer

open scoped BigOperators

/-! ## Formalization changelog

Compared with branch `add-layer-codes`, this module now adds the following
Lean artifacts around the construction described in Williamson and Baspin:

The baseline branch already contained `checkWeight`, the basic binary CSS
input/weight/commutation record, the three layer kinds and planes, finite layer
and cell indices, Tanner-incidence junction types, and a certificate-based
`LayerCode` wrapper. Those are baseline scaffolding, not additions in this
changelog.

- `CSSLayerInput` ties the binary check rows to an actual QECLean input code,
  including its logical-qubit count and a supplied input-distance lower bound.
- `LayerLatticeEdge` gives a finite oriented-edge indexing of a cuboid, with
  an exact cardinality theorem and a numbering equivalence to QECLean's `Fin`
  qubit indices. This exact finite grid is a Lean modeling choice; its boundary
  conventions and count still need reconciliation with the paper's lattice
  spacing and asymptotic physical-qubit count.
- X/Z edge-support lifts, support/weight lemmas, and candidate four-edge
  plaquettes and interior stars are defined for the three layer orientations.
  Each homogeneous candidate family generates its own stabilizer subgroup;
  these subgroups are not combined because their cross-commutation is not yet
  proved.
- `css_check_overlap_even` derives even overlap from the binary CSS law.
  `orderedPairing` then pairs the overlap in the canonical finite order, and
  the endpoint and y-segment lemmas formalize the matching used at X/Z layer
  intersections. The paper describes this matching; the Lean proofs are new.
- X-, Z-, and Y-oriented line-defect edge sets are indexed from Tanner
  incidences and matched overlaps. X/Z incidences are classified as first,
  middle, last, or single within their ordered check support. Y crossings are
  partitioned into matched nontrivial segments and remaining trivial edges.
- `LayerPointDefect` and the bulk/boundary vertex sets formalize geometric
  intersections of distinct line supports. They do not yet encode the paper's
  individual point-defect check patterns.
- `QEC.Stabilizer.Framework.Core.Logical.Decoder` adds an exhaustive,
  minimum-weight syndrome decoder for any supplied finite stabilizer code,
  with a proof of correction below half a supplied distance lower bound. This
  generic decoder is not part of the paper, which leaves specialized decoding
  for future work; exhaustive search is not intended as an efficient decoder.
- The `LayerCode` output size is tied to `LayerLatticeEdge`, and its distance
  premise is a lower bound rather than an exact-distance claim. However,
  `outputCode` remains an independently supplied `StabilizerCode` certificate.

The paper already describes the three layer orientations, Tanner incidences,
the line/point defects, the check-weight-six bound, and the resulting code
parameter scaling. The Lean additions above formalize selected finite data and
generic consequences; they do not establish a new physical result or yet
reproduce the paper's complete layer-code construction.

References:
* https://errorcorrectionzoo.org/c/surface
* https://errorcorrectionzoo.org/c/layer

```bibtex
@article{williamson2024layercodes,
  author        = {Williamson, Dominic J. and Baspin, Nou{\'e}dyn},
  title         = {{Layer Codes}},
  journal       = {Nature Communications},
  volume        = {15},
  number        = {1},
  pages         = {9528},
  year          = {2024},
  doi           = {10.1038/s41467-024-53881-3},
  eprint        = {2309.16503},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  url           = {https://arxiv.org/abs/2309.16503}
}
```
-/

/-!
The construction boundary below is intentionally finite and certificate-based:
it indexes the input Tanner data and accepts an independently supplied
QECLean output certificate. It does not yet construct the output stabilizers.
-/

/-- The binary support weight of a finite check vector. -/
def checkWeight {n : ℕ} (check : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun q => check q = 1)).card

/-- Lift a binary X-check row to a phase-free Pauli generator. -/
def xCheckPauli {n : ℕ} (check : Fin n → ZMod 2) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.ofOperator
    (fun q => if check q = 1 then PauliOperator.X else PauliOperator.I)

/-- Lift a binary Z-check row to a phase-free Pauli generator. -/
def zCheckPauli {n : ℕ} (check : Fin n → ZMod 2) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.ofOperator
    (fun q => if check q = 1 then PauliOperator.Z else PauliOperator.I)

/-- Finite CSS check data used to index a layer-code construction.

The fields record the binary X/Z check matrices and their CSS commutation law.
`inputCode` and `inputCode_generators_eq` ensure the declared logical-qubit
count is represented by these checks; `inputDistance_lower_bound` records the
input distance hypothesis needed for the layer-code bound. -/
structure CSSLayerInput (n k nX nZ : ℕ) where
  logicalQubits_le_physical : k ≤ n
  xCheck : Fin nX → Fin n → ZMod 2
  zCheck : Fin nZ → Fin n → ZMod 2
  xCheckWeight : Fin nX → ℕ
  zCheckWeight : Fin nZ → ℕ
  xCheckWeight_law : ∀ x,
    xCheckWeight x = checkWeight (xCheck x)
  zCheckWeight_law : ∀ z,
    zCheckWeight z = checkWeight (zCheck z)
  maximumCheckWeight : ℕ
  xCheckWeight_le : ∀ x, xCheckWeight x ≤ maximumCheckWeight
  zCheckWeight_le : ∀ z, zCheckWeight z ≤ maximumCheckWeight
  css_commutation : ∀ x z, ∑ q : Fin n, xCheck x q * zCheck z q = 0
  inputCode : StabilizerGroup.StabilizerCode n k
  inputCode_generators_eq : inputCode.generatorsList =
    (List.ofFn (fun x : Fin nX => xCheckPauli (xCheck x))) ++
      List.ofFn (fun z : Fin nZ => zCheckPauli (zCheck z))
  inputDistance : ℕ
  inputDistance_lower_bound : ∀ g,
    StabilizerGroup.IsNontrivialLogicalOperator g inputCode.toStabilizerGroup →
      0 < NQubitPauliGroupElement.weight g →
        NQubitPauliGroupElement.weight g ≥ inputDistance

/-- A check vector has support weight at most the number of physical qubits. -/
lemma checkWeight_le_physicalQubits {n : ℕ} (check : Fin n → ZMod 2) :
    checkWeight check ≤ n := by
  classical
  unfold checkWeight
  simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun q => check q = 1))

/-- The three kinds of surface-code layers in the construction. -/
inductive LayerKind
  | physicalQubit
  | xCheck
  | zCheck
  deriving DecidableEq, Repr

/-- Plane assignment from the Layer-code construction.

Physical-qubit layers lie on xz planes, X-check layers on xy planes, and
Z-check layers on yz planes. -/
inductive LayerPlane
  | xz
  | xy
  | yz
  deriving DecidableEq, Repr

/-- Assign the surface-code plane associated with each layer kind. -/
def LayerKind.plane : LayerKind → LayerPlane
  | .physicalQubit => .xz
  | .xCheck => .xy
  | .zCheck => .yz

/-- The finite index of one input item that receives a surface-code layer. -/
abbrev LayerIndex (n nX nZ : ℕ) : Type :=
  Fin n ⊕ (Fin nX ⊕ Fin nZ)

/-- The layer kind determined by a finite layer index. -/
def layerKind {n nX nZ : ℕ} : LayerIndex n nX nZ → LayerKind
  | Sum.inl _ => .physicalQubit
  | Sum.inr (Sum.inl _) => .xCheck
  | Sum.inr (Sum.inr _) => .zCheck

/-- The surface-code plane determined by a finite layer index. -/
def layerPlane {n nX nZ : ℕ} (layer : LayerIndex n nX nZ) : LayerPlane :=
  (layerKind layer).plane

/-- A physical-qubit layer lies in an xz plane. -/
@[simp] lemma layerPlane_physical {n nX nZ : ℕ} (q : Fin n) :
    layerPlane (Sum.inl q : LayerIndex n nX nZ) = LayerPlane.xz := rfl

/-- An X-check layer lies in an xy plane. -/
@[simp] lemma layerPlane_xCheck {n nX nZ : ℕ} (x : Fin nX) :
    layerPlane (Sum.inr (Sum.inl x) : LayerIndex n nX nZ) = LayerPlane.xy := rfl

/-- A Z-check layer lies in a yz plane. -/
@[simp] lemma layerPlane_zCheck {n nX nZ : ℕ} (z : Fin nZ) :
    layerPlane (Sum.inr (Sum.inr z) : LayerIndex n nX nZ) = LayerPlane.yz := rfl

/-- A square cell in one of the finite surface-code layers. -/
abbrev LayerCell (n nX nZ side : ℕ) : Type :=
  LayerIndex n nX nZ × Fin side × Fin side

/-- Count the disjoint layer indices for data qubits and both check families. -/
@[simp] lemma card_layerIndex (n nX nZ : ℕ) :
    Fintype.card (LayerIndex n nX nZ) = n + nX + nZ := by
  simp [LayerIndex]
  omega

/-- The number of square cells in the disjoint layer-grid indexing. -/
lemma card_layerCell (n nX nZ side : ℕ) :
    Fintype.card (LayerCell n nX nZ side) =
      (n + nX + nZ) * side * side := by
  simp [LayerCell]
  ring

/-- Oriented edge-qubits of the cuboid underlying a layer-code lattice.

The x, y, and z edge counts are the numbers of Z checks, input physical qubits,
and X checks. Each axis has one extra vertex for its two boundaries. -/
abbrev LayerLatticeEdge (n nX nZ : ℕ) : Type :=
  (Fin nZ × Fin (n + 1) × Fin (nX + 1)) ⊕
    ((Fin (nZ + 1) × Fin n × Fin (nX + 1)) ⊕
      (Fin (nZ + 1) × Fin (n + 1) × Fin nX))

/-- The exact number of edge-qubits in the finite cuboid lattice. -/
lemma card_layerLatticeEdge (n nX nZ : ℕ) :
    Fintype.card (LayerLatticeEdge n nX nZ) =
      nZ * (n + 1) * (nX + 1) +
        (nZ + 1) * n * (nX + 1) + (nZ + 1) * (n + 1) * nX := by
  simp only [LayerLatticeEdge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The finite edge count is at least three times the volume product. -/
lemma card_layerLatticeEdge_lower_bound {n nX nZ : ℕ}
  : 3 * n * nX * nZ ≤ Fintype.card (LayerLatticeEdge n nX nZ) := by
  rw [card_layerLatticeEdge]
  have h₁ : nZ * n * nX ≤ nZ * (n + 1) * (nX + 1) := by gcongr <;> omega
  have h₂ : nZ * n * nX ≤ (nZ + 1) * n * (nX + 1) := by gcongr <;> omega
  have h₃ : nZ * n * nX ≤ (nZ + 1) * (n + 1) * nX := by gcongr <;> omega
  calc
    3 * n * nX * nZ = nZ * n * nX + nZ * n * nX + nZ * n * nX := by ring
    _ ≤ nZ * (n + 1) * (nX + 1) +
        (nZ + 1) * n * (nX + 1) + (nZ + 1) * (n + 1) * nX := by omega

/-- The finite edge count is at most twelve times the volume product. -/
lemma card_layerLatticeEdge_upper_bound {n nX nZ : ℕ}
    (hn : 0 < n) (hnX : 0 < nX) (hnZ : 0 < nZ) :
    Fintype.card (LayerLatticeEdge n nX nZ) ≤ 12 * n * nX * nZ := by
  rw [card_layerLatticeEdge]
  have hn' : n + 1 ≤ 2 * n := by omega
  have hnX' : nX + 1 ≤ 2 * nX := by omega
  have hnZ' : nZ + 1 ≤ 2 * nZ := by omega
  have h₁ : nZ * (n + 1) * (nX + 1) ≤ nZ * (2 * n) * (2 * nX) := by
    gcongr
  have h₂ : (nZ + 1) * n * (nX + 1) ≤ (2 * nZ) * n * (2 * nX) := by
    gcongr
  have h₃ : (nZ + 1) * (n + 1) * nX ≤ (2 * nZ) * (2 * n) * nX := by
    gcongr
  calc
    nZ * (n + 1) * (nX + 1) +
        (nZ + 1) * n * (nX + 1) + (nZ + 1) * (n + 1) * nX ≤
      nZ * (2 * n) * (2 * nX) +
        (2 * nZ) * n * (2 * nX) + (2 * nZ) * (2 * n) * nX := by omega
    _ = 12 * n * nX * nZ := by ring

abbrev LayerSurfaceEdge (n nX nZ : ℕ) : Type :=
  (Fin n × ((Fin nZ × Fin (nX + 1)) ⊕ (Fin (nZ + 1) × Fin nX))) ⊕
    ((Fin nX × ((Fin nZ × Fin (n + 1)) ⊕ (Fin (nZ + 1) × Fin n))) ⊕
      (Fin nZ × ((Fin n × Fin (nX + 1)) ⊕ (Fin (n + 1) × Fin nX))))

lemma card_layerSurfaceEdge (n nX nZ : ℕ) :
    Fintype.card (LayerSurfaceEdge n nX nZ) =
      6 * n * nX * nZ + 2 * (n * nX + n * nZ + nX * nZ) := by
  simp only [LayerSurfaceEdge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

def layerSurfaceEdgeOwner {n nX nZ : ℕ} :
    LayerSurfaceEdge n nX nZ → LayerIndex n nX nZ
  | Sum.inl (qubit, _) => Sum.inl qubit
  | Sum.inr (Sum.inl (check, _)) => Sum.inr (Sum.inl check)
  | Sum.inr (Sum.inr (check, _)) => Sum.inr (Sum.inr check)

def layerSurfaceEdgePosition {n nX nZ : ℕ} :
    LayerSurfaceEdge n nX nZ → LayerLatticeEdge n nX nZ
  | Sum.inl (qubit, Sum.inl (xCoord, zCoord)) =>
      Sum.inl (xCoord, qubit.castSucc, zCoord)
  | Sum.inl (qubit, Sum.inr (xCoord, zCoord)) =>
      Sum.inr (Sum.inr (xCoord, qubit.castSucc, zCoord))
  | Sum.inr (Sum.inl (check, Sum.inl (xCoord, yCoord))) =>
      Sum.inl (xCoord, yCoord, check.castSucc)
  | Sum.inr (Sum.inl (check, Sum.inr (xCoord, yCoord))) =>
      Sum.inr (Sum.inl (xCoord, yCoord, check.castSucc))
  | Sum.inr (Sum.inr (check, Sum.inl (yCoord, zCoord))) =>
      Sum.inr (Sum.inl (check.castSucc, yCoord, zCoord))
  | Sum.inr (Sum.inr (check, Sum.inr (yCoord, zCoord))) =>
      Sum.inr (Sum.inr (check.castSucc, yCoord, zCoord))

def xyLayerYEdge {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ + 1)) (yCoord : Fin n) :
    LayerSurfaceEdge n nX nZ :=
  Sum.inr (Sum.inl (check, Sum.inr (xCoord, yCoord)))

def yzLayerYEdge {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin (nX + 1)) :
    LayerSurfaceEdge n nX nZ :=
  Sum.inr (Sum.inr (check, Sum.inl (yCoord, zCoord)))

lemma crossing_layer_edges_same_position {n nX nZ : ℕ}
    (xCheck : Fin nX) (zCheck : Fin nZ) (yCoord : Fin n) :
    layerSurfaceEdgePosition (xyLayerYEdge xCheck zCheck.castSucc yCoord) =
      layerSurfaceEdgePosition (yzLayerYEdge zCheck yCoord xCheck.castSucc) := rfl

lemma crossing_layer_edges_distinct {n nX nZ : ℕ}
    (xCheck : Fin nX) (zCheck : Fin nZ) (yCoord : Fin n) :
    xyLayerYEdge xCheck zCheck.castSucc yCoord ≠
      yzLayerYEdge zCheck yCoord xCheck.castSucc := by
  simp [xyLayerYEdge, yzLayerYEdge]

lemma layerSurfaceEdgeOwner_position_injective {n nX nZ : ℕ} :
    Function.Injective (fun edge : LayerSurfaceEdge n nX nZ =>
      (layerSurfaceEdgeOwner edge, layerSurfaceEdgePosition edge)) := by
  intro first second heq
  rcases first with ⟨qubit, ⟨xCoord, zCoord⟩ | ⟨xCoord, zCoord⟩⟩ |
    (⟨check, ⟨xCoord, yCoord⟩ | ⟨xCoord, yCoord⟩⟩ |
      ⟨check, ⟨yCoord, zCoord⟩ | ⟨yCoord, zCoord⟩⟩) <;>
    rcases second with ⟨other, ⟨otherX, otherZ⟩ | ⟨otherX, otherZ⟩⟩ |
      (⟨other, ⟨otherX, otherY⟩ | ⟨otherX, otherY⟩⟩ |
        ⟨other, ⟨otherY, otherZ⟩ | ⟨otherY, otherZ⟩⟩) <;>
    simp_all [layerSurfaceEdgeOwner, layerSurfaceEdgePosition]

/-- Output physical-qubit count fixed by the finite cuboid edge lattice. -/
abbrev LayerOutputSize (n nX nZ : ℕ) : ℕ :=
  Fintype.card (LayerLatticeEdge n nX nZ)

/-- Canonically number the cuboid edge-qubits for QECLean's `Fin`-indexed Paulis. -/
noncomputable def layerEdgeEquiv (n nX nZ : ℕ) :
    LayerLatticeEdge n nX nZ ≃ Fin (LayerOutputSize n nX nZ) :=
  Fintype.equivFin _

noncomputable def numberedSupportPauli {Edge : Type*} [DecidableEq Edge]
    {qubits : ℕ} (numbering : Edge ≃ Fin qubits) (operator : PauliOperator)
    (support : Finset Edge) : NQubitPauliGroupElement qubits :=
  NQubitPauliGroupElement.ofOperator (fun qubit =>
    if numbering.symm qubit ∈ support then operator else PauliOperator.I)

lemma support_numberedSupportPauli {Edge : Type*} [DecidableEq Edge]
    {qubits : ℕ} (numbering : Edge ≃ Fin qubits) (operator : PauliOperator)
    (support : Finset Edge) (hne : operator ≠ PauliOperator.I) :
    NQubitPauliGroupElement.support (numberedSupportPauli numbering operator support) =
      support.image numbering := by
  classical
  change NQubitPauliOperator.support
    (numberedSupportPauli numbering operator support).operators = support.image numbering
  ext qubit
  rw [NQubitPauliOperator.mem_support, Finset.mem_image]
  change (if numbering.symm qubit ∈ support then operator else PauliOperator.I) ≠
    PauliOperator.I ↔ ∃ edge ∈ support, numbering edge = qubit
  constructor
  · intro hoperator
    have hmem : numbering.symm qubit ∈ support := by
      by_contra hnot
      simp [hnot] at hoperator
    exact ⟨_, hmem, numbering.apply_symm_apply qubit⟩
  · rintro ⟨edge, hedge, rfl⟩
    simpa [hedge] using hne

lemma weight_numberedSupportPauli {Edge : Type*} [DecidableEq Edge]
    {qubits : ℕ} (numbering : Edge ≃ Fin qubits) (operator : PauliOperator)
    (support : Finset Edge) (hne : operator ≠ PauliOperator.I) :
    NQubitPauliGroupElement.weight (numberedSupportPauli numbering operator support) =
      support.card := by
  change (NQubitPauliGroupElement.support
    (numberedSupportPauli numbering operator support)).card = support.card
  rw [support_numberedSupportPauli numbering operator support hne]
  exact Finset.card_image_of_injective _ numbering.injective

/-- X-type Pauli check supported on a finite set of cuboid edges. -/
noncomputable def layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  numberedSupportPauli (layerEdgeEquiv n nX nZ) PauliOperator.X support

/-- Z-type Pauli check supported on a finite set of cuboid edges. -/
noncomputable def layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  numberedSupportPauli (layerEdgeEquiv n nX nZ) PauliOperator.Z support

/-- The Z-lift's output support is the image of its lattice-edge support. -/
lemma support_layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.support (layerZPauli support) =
      support.image (layerEdgeEquiv n nX nZ) := by
  classical
  change NQubitPauliOperator.support (layerZPauli support).operators =
    support.image (layerEdgeEquiv n nX nZ)
  ext q
  rw [NQubitPauliOperator.mem_support, Finset.mem_image]
  change (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.Z else PauliOperator.I) ≠
      PauliOperator.I ↔ ∃ edge ∈ support, layerEdgeEquiv n nX nZ edge = q
  constructor
  · intro h
    by_cases hmem : (layerEdgeEquiv n nX nZ).symm q ∈ support
    · exact ⟨(layerEdgeEquiv n nX nZ).symm q, hmem, Equiv.apply_symm_apply _ _⟩
    · simp [hmem] at h
  · rintro ⟨edge, hedge, hq⟩
    have heq : edge = (layerEdgeEquiv n nX nZ).symm q := by
      calc
        edge = (layerEdgeEquiv n nX nZ).symm (layerEdgeEquiv n nX nZ edge) :=
          (Equiv.symm_apply_apply _ _).symm
        _ = (layerEdgeEquiv n nX nZ).symm q := by rw [hq]
    have hmem : (layerEdgeEquiv n nX nZ).symm q ∈ support := by
      simpa [heq] using hedge
    simp [hmem]

/-- The Z-lift preserves the cardinality of its lattice-edge support. -/
lemma weight_layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.weight (layerZPauli support) = support.card := by
  have hSupport : NQubitPauliOperator.support (layerZPauli support).operators =
      support.image (layerEdgeEquiv n nX nZ) := by
    simpa [NQubitPauliGroupElement.support, layerZPauli] using support_layerZPauli support
  change (NQubitPauliOperator.support (layerZPauli support).operators).card = support.card
  rw [hSupport]
  exact Finset.card_image_of_injective _ (layerEdgeEquiv n nX nZ).injective

/-- The X-lift's output support is the image of its lattice-edge support. -/
lemma support_layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.support (layerXPauli support) =
      support.image (layerEdgeEquiv n nX nZ) := by
  classical
  change NQubitPauliOperator.support (layerXPauli support).operators =
    support.image (layerEdgeEquiv n nX nZ)
  ext q
  rw [NQubitPauliOperator.mem_support, Finset.mem_image]
  change (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.X else PauliOperator.I) ≠
      PauliOperator.I ↔ ∃ edge ∈ support, layerEdgeEquiv n nX nZ edge = q
  constructor
  · intro h
    by_cases hmem : (layerEdgeEquiv n nX nZ).symm q ∈ support
    · exact ⟨(layerEdgeEquiv n nX nZ).symm q, hmem, Equiv.apply_symm_apply _ _⟩
    · simp [hmem] at h
  · rintro ⟨edge, hedge, hq⟩
    have heq : edge = (layerEdgeEquiv n nX nZ).symm q := by
      calc
        edge = (layerEdgeEquiv n nX nZ).symm (layerEdgeEquiv n nX nZ edge) :=
          (Equiv.symm_apply_apply _ _).symm
        _ = (layerEdgeEquiv n nX nZ).symm q := by rw [hq]
    have hmem : (layerEdgeEquiv n nX nZ).symm q ∈ support := by
      simpa [heq] using hedge
    simp [hmem]

/-- The X-lift preserves the cardinality of its lattice-edge support. -/
lemma weight_layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.weight (layerXPauli support) = support.card := by
  have hSupport : NQubitPauliOperator.support (layerXPauli support).operators =
      support.image (layerEdgeEquiv n nX nZ) := by
    simpa [NQubitPauliGroupElement.support, layerXPauli] using support_layerXPauli support
  change (NQubitPauliOperator.support (layerXPauli support).operators).card = support.card
  rw [hSupport]
  exact Finset.card_image_of_injective _ (layerEdgeEquiv n nX nZ).injective

/-- A Z-lift contains only Z and identity factors. -/
lemma layerZPauli_isZType {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.IsZTypeElement (layerZPauli support) := by
  refine ⟨rfl, ?_⟩
  intro q
  change PauliOperator.IsZType
    (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.Z else PauliOperator.I)
  split_ifs <;> simp [PauliOperator.IsZType]

/-- An X-lift contains only X and identity factors. -/
lemma layerXPauli_isXType {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.IsXTypeElement (layerXPauli support) := by
  refine ⟨rfl, ?_⟩
  intro q
  change PauliOperator.IsXType
    (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.X else PauliOperator.I)
  split_ifs <;> simp [PauliOperator.IsXType]

lemma numberedSupportPauli_commutes_iff {Edge : Type*} [DecidableEq Edge]
    {qubits : ℕ} (numbering : Edge ≃ Fin qubits)
    (xSupport zSupport : Finset Edge) :
    numberedSupportPauli numbering PauliOperator.X xSupport *
        numberedSupportPauli numbering PauliOperator.Z zSupport =
      numberedSupportPauli numbering PauliOperator.Z zSupport *
        numberedSupportPauli numbering PauliOperator.X xSupport ↔
      Even (xSupport ∩ zSupport).card := by
  classical
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes]
  have hset : Finset.univ.filter
      (NQubitPauliGroupElement.anticommutesAt
        (numberedSupportPauli numbering PauliOperator.X xSupport).operators
        (numberedSupportPauli numbering PauliOperator.Z zSupport).operators) =
      (xSupport ∩ zSupport).image numbering := by
    ext qubit
    have hmem : qubit ∈ (xSupport ∩ zSupport).image numbering ↔
        numbering.symm qubit ∈ xSupport ∩ zSupport := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨edge, hedge, rfl⟩
        simpa using hedge
      · intro hedge
        exact ⟨_, hedge, Equiv.apply_symm_apply _ _⟩
    rw [hmem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    unfold NQubitPauliGroupElement.anticommutesAt
    change ((if numbering.symm qubit ∈ xSupport then PauliOperator.X
        else PauliOperator.I).mulOp
        (if numbering.symm qubit ∈ zSupport then PauliOperator.Z
        else PauliOperator.I)).phasePower =
      ((if numbering.symm qubit ∈ zSupport then PauliOperator.Z
        else PauliOperator.I).mulOp
        (if numbering.symm qubit ∈ xSupport then PauliOperator.X
        else PauliOperator.I)).phasePower + 2 ↔ _
    split_ifs <;> simp_all [PauliOperator.mulOp]
  rw [hset, Finset.card_image_of_injective _ numbering.injective]

lemma layerXPauli_commutes_layerZPauli_iff {n nX nZ : ℕ}
    (xSupport zSupport : Finset (LayerLatticeEdge n nX nZ)) :
    layerXPauli xSupport * layerZPauli zSupport =
        layerZPauli zSupport * layerXPauli xSupport ↔
      Even (xSupport ∩ zSupport).card :=
  numberedSupportPauli_commutes_iff (layerEdgeEquiv n nX nZ) xSupport zSupport

/-- An edge along the x-axis, whose layers are indexed by Z checks. -/
def layerXEdge {n nX nZ : ℕ} (x : Fin nZ) (y : Fin (n + 1)) (z : Fin (nX + 1)) :
    LayerLatticeEdge n nX nZ :=
  Sum.inl (x, y, z)

/-- An edge along the y-axis, whose layers are indexed by input qubits. -/
def layerYEdge {n nX nZ : ℕ} (x : Fin (nZ + 1)) (y : Fin n) (z : Fin (nX + 1)) :
    LayerLatticeEdge n nX nZ :=
  Sum.inr (Sum.inl (x, y, z))

/-- An edge along the z-axis, whose layers are indexed by X checks. -/
def layerZEdge {n nX nZ : ℕ} (x : Fin (nZ + 1)) (y : Fin (n + 1)) (z : Fin nX) :
    LayerLatticeEdge n nX nZ :=
  Sum.inr (Sum.inr (x, y, z))

/-- The lower and upper endpoints of a `Fin` interval are distinct. -/
private lemma fin_castSucc_ne_succ {m : ℕ} (i : Fin m) :
    Fin.castSucc i ≠ i.succ := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval

/-- Reverse orientation of `fin_castSucc_ne_succ`. -/
private lemma fin_succ_ne_castSucc {m : ℕ} (i : Fin m) :
    i.succ ≠ Fin.castSucc i :=
  Ne.symm (fin_castSucc_ne_succ i)

/-- The four boundary edges of a square in one physical-qubit xz layer. -/
def xzSurfacePlaquetteEdges {n nX nZ : ℕ} (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x q.castSucc z.castSucc,
    layerZEdge x.succ q.castSucc z,
    layerXEdge x q.castSucc z.succ,
    layerZEdge x.castSucc q.castSucc z}

/-- The four boundary edges of an xz plaquette are distinct. -/
lemma card_xzSurfacePlaquetteEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    (xzSurfacePlaquetteEdges q x z).card = 4 := by
  classical
  simp [xzSurfacePlaquetteEdges, layerXEdge, layerZEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

/-- The four boundary edges of a square in one X-check xy layer. -/
def xySurfacePlaquetteEdges {n nX nZ : ℕ} (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x q.castSucc check.castSucc,
    layerYEdge x.succ q check.castSucc,
    layerXEdge x q.succ check.castSucc,
    layerYEdge x.castSucc q check.castSucc}

/-- The four boundary edges of an xy plaquette are distinct. -/
lemma card_xySurfacePlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    (xySurfacePlaquetteEdges check x q).card = 4 := by
  classical
  simp [xySurfacePlaquetteEdges, layerXEdge, layerYEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

/-- The four boundary edges of a square in one Z-check yz layer. -/
def yzSurfacePlaquetteEdges {n nX nZ : ℕ} (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerYEdge check.castSucc q z.castSucc,
    layerZEdge check.castSucc q.succ z,
    layerYEdge check.castSucc q z.succ,
    layerZEdge check.castSucc q.castSucc z}

/-- The four boundary edges of a yz plaquette are distinct. -/
lemma card_yzSurfacePlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    (yzSurfacePlaquetteEdges check q z).card = 4 := by
  classical
  simp [yzSurfacePlaquetteEdges, layerYEdge, layerZEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

/-- The three edges of a rough-boundary plaquette on an xz layer. -/
def xzRoughBoundaryPlaquetteEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (isUpper : Bool) (hnX : 0 < nX) :
    Finset (LayerLatticeEdge n nX nZ) := by
  let zCell : Fin nX := if isUpper then ⟨nX - 1, by omega⟩ else ⟨0, hnX⟩
  let zVertex : Fin (nX + 1) :=
    if isUpper then ⟨nX, by omega⟩ else ⟨0, by omega⟩
  exact {layerXEdge x q.castSucc zVertex,
    layerZEdge x.castSucc q.castSucc zCell,
    layerZEdge x.succ q.castSucc zCell}

/-- Rough-boundary xz plaquettes have three distinct edges. -/
lemma card_xzRoughBoundaryPlaquetteEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (isUpper : Bool) (hnX : 0 < nX) :
    (xzRoughBoundaryPlaquetteEdges q x isUpper hnX).card = 3 := by
  classical
  simp [xzRoughBoundaryPlaquetteEdges, layerXEdge, layerZEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

/-- The three edges of a rough-boundary plaquette on a yz layer. -/
def yzRoughBoundaryPlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (isUpper : Bool) (hnX : 0 < nX) :
    Finset (LayerLatticeEdge n nX nZ) := by
  let zCell : Fin nX := if isUpper then ⟨nX - 1, by omega⟩ else ⟨0, hnX⟩
  let zVertex : Fin (nX + 1) :=
    if isUpper then ⟨nX, by omega⟩ else ⟨0, by omega⟩
  exact {layerYEdge check.castSucc q zVertex,
    layerZEdge check.castSucc q.castSucc zCell,
    layerZEdge check.castSucc q.succ zCell}

/-- Rough-boundary yz plaquettes have three distinct edges. -/
lemma card_yzRoughBoundaryPlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (isUpper : Bool) (hnX : 0 < nX) :
    (yzRoughBoundaryPlaquetteEdges check q isUpper hnX).card = 3 := by
  classical
  simp [yzRoughBoundaryPlaquetteEdges, layerYEdge, layerZEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

/-- Canonical Z-plaquette generator in a physical-qubit xz layer. -/
noncomputable def xzSurfacePlaquette {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (xzSurfacePlaquetteEdges q x z)

/-- An xz plaquette generator has Pauli weight four. -/
lemma weight_xzSurfacePlaquette {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    NQubitPauliGroupElement.weight (xzSurfacePlaquette q x z) = 4 := by
  rw [xzSurfacePlaquette, weight_layerZPauli, card_xzSurfacePlaquetteEdges]

/-- Canonical Z-plaquette generator in an X-check xy layer. -/
noncomputable def xySurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (xySurfacePlaquetteEdges check x q)

/-- An xy plaquette generator has Pauli weight four. -/
lemma weight_xySurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    NQubitPauliGroupElement.weight (xySurfacePlaquette check x q) = 4 := by
  rw [xySurfacePlaquette, weight_layerZPauli, card_xySurfacePlaquetteEdges]

/-- Canonical Z-plaquette generator in a Z-check yz layer. -/
noncomputable def yzSurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (yzSurfacePlaquetteEdges check q z)

/-- A yz plaquette generator has Pauli weight four. -/
lemma weight_yzSurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    NQubitPauliGroupElement.weight (yzSurfacePlaquette check q z) = 4 := by
  rw [yzSurfacePlaquette, weight_layerZPauli, card_yzSurfacePlaquetteEdges]

/-- Candidate Z plaquettes on all physical-qubit xz layers. -/
noncomputable def xzSurfacePlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin nZ × Fin nX)).toList).map
    (fun face => xzSurfacePlaquette face.1 face.2.1 face.2.2)

/-- Candidate Z plaquettes on all X-check xy layers. -/
noncomputable def xySurfacePlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact ((Finset.univ : Finset (Fin nX × Fin nZ × Fin n)).toList).map
    (fun face => xySurfacePlaquette face.1 face.2.1 face.2.2)

/-- Candidate Z plaquettes on all Z-check yz layers. -/
noncomputable def yzSurfacePlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact ((Finset.univ : Finset (Fin nZ × Fin n × Fin nX)).toList).map
    (fun face => yzSurfacePlaquette face.1 face.2.1 face.2.2)

/-- All unmodified surface-layer Z plaquette candidates, before defect replacements. -/
noncomputable def layerSurfacePlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  xzSurfacePlaquetteCandidates ++
    (xySurfacePlaquetteCandidates ++ yzSurfacePlaquetteCandidates)

/-- Every unmodified surface-layer plaquette candidate has weight four. -/
theorem layerSurfacePlaquetteCandidates_weight {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfacePlaquetteCandidates) :
    NQubitPauliGroupElement.weight g = 4 := by
  classical
  simp only [layerSurfacePlaquetteCandidates, List.mem_append] at hg
  rcases hg with hxz | hrest
  · simp only [xzSurfacePlaquetteCandidates, List.mem_map] at hxz
    rcases hxz with ⟨face, hface, rfl⟩
    exact weight_xzSurfacePlaquette _ _ _
  · rcases hrest with hxy | hyz
    · simp only [xySurfacePlaquetteCandidates, List.mem_map] at hxy
      rcases hxy with ⟨face, hface, rfl⟩
      exact weight_xySurfacePlaquette _ _ _
    · simp only [yzSurfacePlaquetteCandidates, List.mem_map] at hyz
      rcases hyz with ⟨face, hface, rfl⟩
      exact weight_yzSurfacePlaquette _ _ _

/-- Every candidate in the unmodified plaquette list is Z-type. -/
theorem layerSurfacePlaquetteCandidates_zType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfacePlaquetteCandidates) :
    NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  simp only [layerSurfacePlaquetteCandidates, List.mem_append] at hg
  rcases hg with hxz | hrest
  · simp only [xzSurfacePlaquetteCandidates, List.mem_map] at hxz
    rcases hxz with ⟨face, hface, rfl⟩
    exact layerZPauli_isZType _
  · rcases hrest with hxy | hyz
    · simp only [xySurfacePlaquetteCandidates, List.mem_map] at hxy
      rcases hxy with ⟨face, hface, rfl⟩
      exact layerZPauli_isZType _
    · simp only [yzSurfacePlaquetteCandidates, List.mem_map] at hyz
      rcases hyz with ⟨face, hface, rfl⟩
      exact layerZPauli_isZType _

/-- Rough-boundary plaquette checks on xz layers. -/
noncomputable def xzRoughBoundaryPlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact if hnX : 0 < nX then
    ((Finset.univ : Finset (Fin n × Fin nZ × Bool)).toList).map
      (fun p => layerZPauli
        (xzRoughBoundaryPlaquetteEdges p.1 p.2.1 p.2.2 hnX))
  else []

/-- Rough-boundary plaquette checks on yz layers. -/
noncomputable def yzRoughBoundaryPlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact if hnX : 0 < nX then
    ((Finset.univ : Finset (Fin nZ × Fin n × Bool)).toList).map
      (fun p => layerZPauli
        (yzRoughBoundaryPlaquetteEdges p.1 p.2.1 p.2.2 hnX))
  else []

/-- All rough-boundary Z plaquettes on the xz and yz layers. -/
noncomputable def layerRoughBoundaryPlaquetteCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  xzRoughBoundaryPlaquetteCandidates ++ yzRoughBoundaryPlaquetteCandidates

/-- Rough-boundary plaquettes have weight three. -/
theorem layerRoughBoundaryPlaquetteCandidates_weight {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerRoughBoundaryPlaquetteCandidates) :
    NQubitPauliGroupElement.weight g = 3 := by
  classical
  simp only [layerRoughBoundaryPlaquetteCandidates, List.mem_append] at hg
  rcases hg with hxz | hyz
  · by_cases hnX : 0 < nX
    · simp only [xzRoughBoundaryPlaquetteCandidates, dite_eq_left hnX,
        List.mem_map] at hxz
      rcases hxz with ⟨p, hp, rfl⟩
      rw [weight_layerZPauli, card_xzRoughBoundaryPlaquetteEdges]
    · simp [xzRoughBoundaryPlaquetteCandidates, hnX] at hxz
  · by_cases hnX : 0 < nX
    · simp only [yzRoughBoundaryPlaquetteCandidates, dite_eq_left hnX,
        List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      rw [weight_layerZPauli, card_yzRoughBoundaryPlaquetteEdges]
    · simp [yzRoughBoundaryPlaquetteCandidates, hnX] at hyz

/-- Rough-boundary plaquette checks are Z-type. -/
theorem layerRoughBoundaryPlaquetteCandidates_zType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerRoughBoundaryPlaquetteCandidates) :
    NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  simp only [layerRoughBoundaryPlaquetteCandidates, List.mem_append] at hg
  rcases hg with hxz | hyz
  · by_cases hnX : 0 < nX
    · simp only [xzRoughBoundaryPlaquetteCandidates, dite_eq_left hnX,
        List.mem_map] at hxz
      rcases hxz with ⟨p, hp, rfl⟩
      exact layerZPauli_isZType _
    · simp [xzRoughBoundaryPlaquetteCandidates, hnX] at hxz
  · by_cases hnX : 0 < nX
    · simp only [yzRoughBoundaryPlaquetteCandidates, dite_eq_left hnX,
        List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      exact layerZPauli_isZType _
    · simp [yzRoughBoundaryPlaquetteCandidates, hnX] at hyz

/-- Lower interior grid coordinate embedded in `Fin m`. -/
private def interiorCast {m : ℕ} (i : Fin (m - 1)) : Fin m := by
  have hi : i.val < m - 1 := i.isLt
  have hm : 0 < m := by omega
  exact Fin.cast (by omega) i.castSucc

/-- Upper interior grid coordinate embedded in `Fin m`. -/
private def interiorSucc {m : ℕ} (i : Fin (m - 1)) : Fin m :=
  ⟨i.val + 1, by omega⟩

/-- Convert an upper interior grid coordinate to its vertex coordinate. -/
private def interiorSuccVertex {m : ℕ} (i : Fin (m - 1)) : Fin (m + 1) :=
  Fin.castSucc (interiorSucc i)

/-- The lower and upper coordinates around an interior vertex are distinct. -/
private lemma interiorCast_ne_succ {m : ℕ} (i : Fin (m - 1)) :
    interiorCast i ≠ interiorSucc i := by
  intro h
  have hval := congrArg Fin.val h
  simp [interiorCast, interiorSucc] at hval

/-- Reverse orientation of `interiorCast_ne_succ`. -/
private lemma interiorSucc_ne_cast {m : ℕ} (i : Fin (m - 1)) :
    interiorSucc i ≠ interiorCast i :=
  Ne.symm (interiorCast_ne_succ i)

/-- The four in-plane edges incident to an interior vertex of an xz layer. -/
noncomputable def xzSurfaceStarEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact {layerXEdge (interiorCast (m := nZ) x) q.castSucc (interiorSuccVertex (m := nX) z),
    layerXEdge (interiorSucc (m := nZ) x) q.castSucc (interiorSuccVertex (m := nX) z),
    layerZEdge (interiorSuccVertex (m := nZ) x) q.castSucc (interiorCast (m := nX) z),
    layerZEdge (interiorSuccVertex (m := nZ) x) q.castSucc (interiorSucc (m := nX) z)}

/-- The four edges incident to an interior xz vertex are distinct. -/
lemma card_xzSurfaceStarEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    (xzSurfaceStarEdges q x z).card = 4 := by
  classical
  simp [xzSurfaceStarEdges, layerXEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- The three edges in an X-star at a smooth xz-layer boundary. -/
noncomputable def xzSmoothBoundaryStarEdges {n nX nZ : ℕ}
    (q : Fin n) (z : Fin (nX - 1)) (isRight : Bool) (hnZ : 0 < nZ) :
    Finset (LayerLatticeEdge n nX nZ) := by
  let xCell : Fin nZ := if isRight then ⟨nZ - 1, by omega⟩ else ⟨0, hnZ⟩
  let xVertex : Fin (nZ + 1) :=
    if isRight then ⟨nZ, by omega⟩ else ⟨0, by omega⟩
  exact {layerXEdge xCell q.castSucc (interiorSuccVertex (m := nX) z),
    layerZEdge xVertex q.castSucc (interiorCast (m := nX) z),
    layerZEdge xVertex q.castSucc (interiorSucc (m := nX) z)}

/-- Smooth-boundary X-stars have weight three before defect replacement. -/
lemma card_xzSmoothBoundaryStarEdges {n nX nZ : ℕ}
    (q : Fin n) (z : Fin (nX - 1)) (isRight : Bool) (hnZ : 0 < nZ) :
    (xzSmoothBoundaryStarEdges q z isRight hnZ).card = 3 := by
  classical
  simp [xzSmoothBoundaryStarEdges, layerXEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- The three edges in an X-star at a smooth xy-layer boundary. -/
noncomputable def xySmoothBoundaryStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (q : Fin (n - 1)) (isRight : Bool) (hnZ : 0 < nZ) :
    Finset (LayerLatticeEdge n nX nZ) := by
  let xCell : Fin nZ := if isRight then ⟨nZ - 1, by omega⟩ else ⟨0, hnZ⟩
  let xVertex : Fin (nZ + 1) :=
    if isRight then ⟨nZ, by omega⟩ else ⟨0, by omega⟩
  exact {layerXEdge xCell (interiorSuccVertex (m := n) q) check.castSucc,
    layerYEdge xVertex (interiorCast (m := n) q) check.castSucc,
    layerYEdge xVertex (interiorSucc (m := n) q) check.castSucc}

/-- Smooth-boundary xy-layer X-stars have three distinct edges. -/
lemma card_xySmoothBoundaryStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (q : Fin (n - 1)) (isRight : Bool) (hnZ : 0 < nZ) :
    (xySmoothBoundaryStarEdges check q isRight hnZ).card = 3 := by
  classical
  simp [xySmoothBoundaryStarEdges, layerXEdge, layerYEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- The four in-plane edges incident to an interior vertex of an xy layer. -/
noncomputable def xySurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact {layerXEdge (interiorCast (m := nZ) x) (interiorSuccVertex (m := n) q) check.castSucc,
    layerXEdge (interiorSucc (m := nZ) x) (interiorSuccVertex (m := n) q) check.castSucc,
    layerYEdge (interiorSuccVertex (m := nZ) x) (interiorCast (m := n) q) check.castSucc,
    layerYEdge (interiorSuccVertex (m := nZ) x) (interiorSucc (m := n) q) check.castSucc}

noncomputable def xyOwnedStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ - 1)) (yCoord : Fin (n - 1)) :
    Finset (LayerSurfaceEdge n nX nZ) := by
  classical
  exact {Sum.inr (Sum.inl (check, Sum.inl (interiorCast xCoord, interiorSuccVertex yCoord))),
    Sum.inr (Sum.inl (check, Sum.inl (interiorSucc xCoord, interiorSuccVertex yCoord))),
    xyLayerYEdge check (interiorSuccVertex xCoord) (interiorCast yCoord),
    xyLayerYEdge check (interiorSuccVertex xCoord) (interiorSucc yCoord)}

noncomputable def yzOwnedPlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin nX) :
    Finset (LayerSurfaceEdge n nX nZ) := by
  classical
  exact {yzLayerYEdge check yCoord zCoord.castSucc,
    Sum.inr (Sum.inr (check, Sum.inr (yCoord.succ, zCoord))),
    yzLayerYEdge check yCoord zCoord.succ,
    Sum.inr (Sum.inr (check, Sum.inr (yCoord.castSucc, zCoord)))}

lemma xyOwnedStarEdges_position {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ - 1)) (yCoord : Fin (n - 1)) :
    (xyOwnedStarEdges check xCoord yCoord).image layerSurfaceEdgePosition =
      xySurfaceStarEdges check xCoord yCoord := by
  classical
  simp [xyOwnedStarEdges, xySurfaceStarEdges, xyLayerYEdge,
    layerSurfaceEdgePosition, layerXEdge, layerYEdge]

lemma yzOwnedPlaquetteEdges_position {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin nX) :
    (yzOwnedPlaquetteEdges check yCoord zCoord).image layerSurfaceEdgePosition =
      yzSurfacePlaquetteEdges check yCoord zCoord := by
  classical
  simp [yzOwnedPlaquetteEdges, yzSurfacePlaquetteEdges, yzLayerYEdge,
    layerSurfaceEdgePosition, layerYEdge, layerZEdge]

lemma xyOwnedStarEdges_card {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ - 1)) (yCoord : Fin (n - 1)) :
    (xyOwnedStarEdges check xCoord yCoord).card = 4 := by
  classical
  simp [xyOwnedStarEdges, xyLayerYEdge, interiorCast_ne_succ]

lemma yzOwnedPlaquetteEdges_card {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin nX) :
    (yzOwnedPlaquetteEdges check yCoord zCoord).card = 4 := by
  classical
  simp [yzOwnedPlaquetteEdges, yzLayerYEdge,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

lemma owned_crossing_supports_disjoint {n nX nZ : ℕ}
    (xCheck : Fin nX) (starX : Fin (nZ - 1)) (starY : Fin (n - 1))
    (zCheck : Fin nZ) (faceY : Fin n) (faceZ : Fin nX) :
    Disjoint (xyOwnedStarEdges xCheck starX starY)
      (yzOwnedPlaquetteEdges zCheck faceY faceZ) := by
  classical
  simp [xyOwnedStarEdges, yzOwnedPlaquetteEdges, xyLayerYEdge, yzLayerYEdge,
    Finset.disjoint_left]

noncomputable def xyOwnedStar {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ - 1)) (yCoord : Fin (n - 1)) :
    NQubitPauliGroupElement (Fintype.card (LayerSurfaceEdge n nX nZ)) := by
  classical
  exact numberedSupportPauli (Fintype.equivFin _) PauliOperator.X
    (xyOwnedStarEdges check xCoord yCoord)

noncomputable def yzOwnedPlaquette {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin nX) :
    NQubitPauliGroupElement (Fintype.card (LayerSurfaceEdge n nX nZ)) := by
  classical
  exact numberedSupportPauli (Fintype.equivFin _) PauliOperator.Z
    (yzOwnedPlaquetteEdges check yCoord zCoord)

lemma xyOwnedStar_weight {n nX nZ : ℕ}
    (check : Fin nX) (xCoord : Fin (nZ - 1)) (yCoord : Fin (n - 1)) :
    NQubitPauliGroupElement.weight (xyOwnedStar check xCoord yCoord) = 4 := by
  classical
  rw [xyOwnedStar, weight_numberedSupportPauli _ _ _ (by decide), xyOwnedStarEdges_card]

lemma yzOwnedPlaquette_weight {n nX nZ : ℕ}
    (check : Fin nZ) (yCoord : Fin n) (zCoord : Fin nX) :
    NQubitPauliGroupElement.weight (yzOwnedPlaquette check yCoord zCoord) = 4 := by
  classical
  rw [yzOwnedPlaquette, weight_numberedSupportPauli _ _ _ (by decide), yzOwnedPlaquetteEdges_card]

lemma owned_crossing_checks_commute {n nX nZ : ℕ}
    (xCheck : Fin nX) (starX : Fin (nZ - 1)) (starY : Fin (n - 1))
    (zCheck : Fin nZ) (faceY : Fin n) (faceZ : Fin nX) :
    xyOwnedStar xCheck starX starY * yzOwnedPlaquette zCheck faceY faceZ =
      yzOwnedPlaquette zCheck faceY faceZ * xyOwnedStar xCheck starX starY := by
  classical
  rw [xyOwnedStar, yzOwnedPlaquette, numberedSupportPauli_commutes_iff,
    Finset.disjoint_iff_inter_eq_empty.mp
      (owned_crossing_supports_disjoint xCheck starX starY zCheck faceY faceZ)]
  simp

/-- The four edges incident to an interior xy vertex are distinct. -/
lemma card_xySurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    (xySurfaceStarEdges check x q).card = 4 := by
  classical
  simp [xySurfaceStarEdges, layerXEdge, layerYEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- The four in-plane edges incident to an interior vertex of a yz layer. -/
noncomputable def yzSurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact {layerYEdge check.castSucc (interiorCast (m := n) q) (interiorSuccVertex (m := nX) z),
    layerYEdge check.castSucc (interiorSucc (m := n) q) (interiorSuccVertex (m := nX) z),
    layerZEdge check.castSucc (interiorSuccVertex (m := n) q) (interiorCast (m := nX) z),
    layerZEdge check.castSucc (interiorSuccVertex (m := n) q) (interiorSucc (m := nX) z)}

/-- The four edges incident to an interior yz vertex are distinct. -/
lemma card_yzSurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    (yzSurfaceStarEdges check q z).card = 4 := by
  classical
  simp [yzSurfaceStarEdges, layerYEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- Canonical X-star generator at an interior vertex of an xz layer. -/
noncomputable def xzSurfaceStar {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (xzSurfaceStarEdges q x z)

/-- An interior xz star generator has Pauli weight four. -/
lemma weight_xzSurfaceStar {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement.weight (xzSurfaceStar q x z) = 4 := by
  rw [xzSurfaceStar, weight_layerXPauli, card_xzSurfaceStarEdges]

/-- Canonical X-star generator at an interior vertex of an xy layer. -/
noncomputable def xySurfaceStar {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (xySurfaceStarEdges check x q)

/-- An interior xy star generator has Pauli weight four. -/
lemma weight_xySurfaceStar {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    NQubitPauliGroupElement.weight (xySurfaceStar check x q) = 4 := by
  rw [xySurfaceStar, weight_layerXPauli, card_xySurfaceStarEdges]

/-- Canonical X-star generator at an interior vertex of a yz layer. -/
noncomputable def yzSurfaceStar {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (yzSurfaceStarEdges check q z)

/-- An interior yz star generator has Pauli weight four. -/
lemma weight_yzSurfaceStar {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement.weight (yzSurfaceStar check q z) = 4 := by
  rw [yzSurfaceStar, weight_layerXPauli, card_yzSurfaceStarEdges]

/-- Interior X-star candidates on all three kinds of surface-code layers. -/
noncomputable def layerInteriorStarCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  let xz := ((Finset.univ : Finset (Fin n × Fin (nZ - 1) × Fin (nX - 1))).toList).map
    (fun p => xzSurfaceStar p.1 p.2.1 p.2.2)
  let xy := ((Finset.univ : Finset (Fin nX × Fin (nZ - 1) × Fin (n - 1))).toList).map
    (fun p => xySurfaceStar p.1 p.2.1 p.2.2)
  let yz := ((Finset.univ : Finset (Fin nZ × Fin (n - 1) × Fin (nX - 1))).toList).map
    (fun p => yzSurfaceStar p.1 p.2.1 p.2.2)
  exact xz ++ (xy ++ yz)

/-- Every interior surface-layer X-star candidate has weight four. -/
theorem layerInteriorStarCandidates_weight {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerInteriorStarCandidates) :
    NQubitPauliGroupElement.weight g = 4 := by
  classical
  simp only [layerInteriorStarCandidates, List.mem_append] at hg
  rcases hg with hxz | hrest
  · simp only [List.mem_map] at hxz
    rcases hxz with ⟨p, hp, rfl⟩
    exact weight_xzSurfaceStar _ _ _
  · rcases hrest with hxy | hyz
    · simp only [List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      exact weight_xySurfaceStar _ _ _
    · simp only [List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      exact weight_yzSurfaceStar _ _ _

/-- Every candidate in the interior-star list is X-type. -/
theorem layerInteriorStarCandidates_xType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerInteriorStarCandidates) :
    NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  simp only [layerInteriorStarCandidates, List.mem_append] at hg
  rcases hg with hxz | hrest
  · simp only [List.mem_map] at hxz
    rcases hxz with ⟨p, hp, rfl⟩
    exact layerXPauli_isXType _
  · rcases hrest with hxy | hyz
    · simp only [List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _
    · simp only [List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _

/-- Smooth-boundary X stars on physical-qubit xz layers. -/
noncomputable def xzSmoothBoundaryStarCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact if hnZ : 0 < nZ then
    ((Finset.univ : Finset (Fin n × Fin (nX - 1) × Bool)).toList).map
      (fun p => layerXPauli
        (xzSmoothBoundaryStarEdges p.1 p.2.1 p.2.2 hnZ))
  else []

/-- Smooth-boundary X stars on input X-check xy layers. -/
noncomputable def xySmoothBoundaryStarCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact if hnZ : 0 < nZ then
    ((Finset.univ : Finset (Fin nX × Fin (n - 1) × Bool)).toList).map
      (fun p => layerXPauli
        (xySmoothBoundaryStarEdges p.1 p.2.1 p.2.2 hnZ))
  else []

/-- All smooth-boundary X stars on the xz and xy layers. -/
noncomputable def layerSmoothBoundaryStarCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  xzSmoothBoundaryStarCandidates ++ xySmoothBoundaryStarCandidates

/-- Smooth-boundary stars have weight three. -/
theorem layerSmoothBoundaryStarCandidates_weight {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSmoothBoundaryStarCandidates) :
    NQubitPauliGroupElement.weight g = 3 := by
  classical
  simp only [layerSmoothBoundaryStarCandidates, List.mem_append] at hg
  rcases hg with hxz | hxy
  · by_cases hnZ : 0 < nZ
    · simp only [xzSmoothBoundaryStarCandidates, dite_eq_left hnZ,
        List.mem_map] at hxz
      rcases hxz with ⟨p, hp, rfl⟩
      rw [weight_layerXPauli, card_xzSmoothBoundaryStarEdges]
    · simp [xzSmoothBoundaryStarCandidates, hnZ] at hxz
  · by_cases hnZ : 0 < nZ
    · simp only [xySmoothBoundaryStarCandidates, dite_eq_left hnZ,
        List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      rw [weight_layerXPauli, card_xySmoothBoundaryStarEdges]
    · simp [xySmoothBoundaryStarCandidates, hnZ] at hxy

/-- Smooth-boundary star checks are X-type. -/
theorem layerSmoothBoundaryStarCandidates_xType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSmoothBoundaryStarCandidates) :
    NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  simp only [layerSmoothBoundaryStarCandidates, List.mem_append] at hg
  rcases hg with hxz | hxy
  · by_cases hnZ : 0 < nZ
    · simp only [xzSmoothBoundaryStarCandidates, dite_eq_left hnZ,
        List.mem_map] at hxz
      rcases hxz with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _
    · simp [xzSmoothBoundaryStarCandidates, hnZ] at hxz
  · by_cases hnZ : 0 < nZ
    · simp only [xySmoothBoundaryStarCandidates, dite_eq_left hnZ,
        List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _
    · simp [xySmoothBoundaryStarCandidates, hnZ] at hxy

/-- Surface-layer check candidates before line- and point-defect replacement. -/
noncomputable def layerSurfaceCheckCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  layerInteriorStarCandidates ++
    (layerSmoothBoundaryStarCandidates ++
      (layerSurfacePlaquetteCandidates ++ layerRoughBoundaryPlaquetteCandidates))

/-- Every unmodified surface-layer check candidate has weight at most four. -/
theorem layerSurfaceCheckCandidates_weight_le_four {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfaceCheckCandidates) :
    NQubitPauliGroupElement.weight g ≤ 4 := by
  simp only [layerSurfaceCheckCandidates, List.mem_append] at hg
  rcases hg with hstar | hrest
  · rw [layerInteriorStarCandidates_weight g hstar]
  · rcases hrest with hboundaryStar | hrest
    · rw [layerSmoothBoundaryStarCandidates_weight g hboundaryStar]
      omega
    · rcases hrest with hplaquette | hboundaryPlaquette
      · rw [layerSurfacePlaquetteCandidates_weight g hplaquette]
      · rw [layerRoughBoundaryPlaquetteCandidates_weight g hboundaryPlaquette]
        omega

/-- All unmodified surface X stars, including smooth-boundary checks. -/
noncomputable def layerSurfaceXCheckCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  layerInteriorStarCandidates ++ layerSmoothBoundaryStarCandidates

/-- Every unmodified surface X candidate is X-type. -/
theorem layerSurfaceXCheckCandidates_xType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfaceXCheckCandidates) :
    NQubitPauliGroupElement.IsXTypeElement g := by
  simp only [layerSurfaceXCheckCandidates, List.mem_append] at hg
  rcases hg with hinterior | hboundary
  · exact layerInteriorStarCandidates_xType g hinterior
  · exact layerSmoothBoundaryStarCandidates_xType g hboundary

/-- All unmodified surface Z plaquettes, including rough-boundary checks. -/
noncomputable def layerSurfaceZCheckCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  layerSurfacePlaquetteCandidates ++ layerRoughBoundaryPlaquetteCandidates

/-- Every unmodified surface Z candidate is Z-type. -/
theorem layerSurfaceZCheckCandidates_zType {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfaceZCheckCandidates) :
    NQubitPauliGroupElement.IsZTypeElement g := by
  simp only [layerSurfaceZCheckCandidates, List.mem_append] at hg
  rcases hg with hsurface | hboundary
  · exact layerSurfacePlaquetteCandidates_zType g hsurface
  · exact layerRoughBoundaryPlaquetteCandidates_zType g hboundary

lemma unmodified_crossing_overlap_card :
    ((xySurfaceStarEdges (n := 2) (nX := 1) (nZ := 2) 0 0 0) ∩
      yzSurfacePlaquetteEdges (n := 2) (nX := 1) (nZ := 2) 1 0 0).card = 1 := by
  classical
  simp [xySurfaceStarEdges, yzSurfacePlaquetteEdges, layerXEdge, layerYEdge,
    layerZEdge, interiorCast, interiorSucc, interiorSuccVertex]

lemma unmodified_crossing_checks_not_commuting :
    layerXPauli (xySurfaceStarEdges (n := 2) (nX := 1) (nZ := 2) 0 0 0) *
        layerZPauli (yzSurfacePlaquetteEdges (n := 2) (nX := 1) (nZ := 2) 1 0 0) ≠
      layerZPauli (yzSurfacePlaquetteEdges (n := 2) (nX := 1) (nZ := 2) 1 0 0) *
        layerXPauli (xySurfaceStarEdges (n := 2) (nX := 1) (nZ := 2) 0 0 0) := by
  rw [ne_eq, layerXPauli_commutes_layerZPauli_iff, unmodified_crossing_overlap_card]
  decide

theorem unmodified_surface_candidates_not_cross_commuting :
    ∃ xCheck ∈ layerSurfaceXCheckCandidates (n := 2) (nX := 1) (nZ := 2),
      ∃ zCheck ∈ layerSurfaceZCheckCandidates (n := 2) (nX := 1) (nZ := 2),
        xCheck * zCheck ≠ zCheck * xCheck := by
  classical
  refine ⟨xySurfaceStar 0 0 0, ?_, yzSurfacePlaquette 1 0 0, ?_,
    unmodified_crossing_checks_not_commuting⟩
  · simp only [layerSurfaceXCheckCandidates, layerInteriorStarCandidates, List.mem_append]
    left
    right
    left
    apply List.mem_map.mpr
    exact ⟨(0, 0, 0), by simp, rfl⟩
  · simp only [layerSurfaceZCheckCandidates, layerSurfacePlaquetteCandidates, List.mem_append]
    left
    right
    right
    apply List.mem_map.mpr
    exact ⟨(1, 0, 0), by simp, rfl⟩

/-- Stabilizer subgroup generated by the unmodified bulk Z plaquettes. -/
noncomputable def layerBulkZStabilizerGroup {n nX nZ : ℕ} :
    StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerSurfacePlaquetteCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.ZType_commutes
        (layerSurfacePlaquetteCandidates_zType g hg)
        (layerSurfacePlaquetteCandidates_zType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        (NQubitPauliGroupElement.listToSet
          (n := LayerOutputSize n nX nZ) layerSurfacePlaquetteCandidates)
        (∅ : Set (NQubitPauliGroupElement (LayerOutputSize n nX nZ)))
        (by
          intro z hz
          exact layerSurfacePlaquetteCandidates_zType z hz)
        (by
          intro x hx
          simp at hx)
        (by
          intro z hz x hx
          simp at hx)
      simpa using hNoNeg)

/-- Stabilizer subgroup generated by the unmodified bulk X stars. -/
noncomputable def layerBulkXStabilizerGroup {n nX nZ : ℕ} :
    StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerInteriorStarCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.XType_commutes
        (layerInteriorStarCandidates_xType g hg)
        (layerInteriorStarCandidates_xType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        (∅ : Set (NQubitPauliGroupElement (LayerOutputSize n nX nZ)))
        (NQubitPauliGroupElement.listToSet
          (n := LayerOutputSize n nX nZ) layerInteriorStarCandidates)
        (by
          intro z hz
          simp at hz)
        (by
          intro x hx
          exact layerInteriorStarCandidates_xType x hx)
        (by
          intro z hz
          simp at hz)
      simpa using hNoNeg)

/-- Stabilizer subgroup generated by unmodified surface X stars and boundaries. -/
noncomputable def layerSurfaceXStabilizerGroup {n nX nZ : ℕ} :
    StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerSurfaceXCheckCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.XType_commutes
        (layerSurfaceXCheckCandidates_xType g hg)
        (layerSurfaceXCheckCandidates_xType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        (∅ : Set (NQubitPauliGroupElement (LayerOutputSize n nX nZ)))
        (NQubitPauliGroupElement.listToSet
          (n := LayerOutputSize n nX nZ) layerSurfaceXCheckCandidates)
        (by
          intro z hz
          simp at hz)
        (by
          intro x hx
          exact layerSurfaceXCheckCandidates_xType x hx)
        (by
          intro z hz
          simp at hz)
      simpa using hNoNeg)

/-- Stabilizer subgroup generated by unmodified surface Z plaquettes and boundaries. -/
noncomputable def layerSurfaceZStabilizerGroup {n nX nZ : ℕ} :
    StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerSurfaceZCheckCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.ZType_commutes
        (layerSurfaceZCheckCandidates_zType g hg)
        (layerSurfaceZCheckCandidates_zType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        (NQubitPauliGroupElement.listToSet
          (n := LayerOutputSize n nX nZ) layerSurfaceZCheckCandidates)
        (∅ : Set (NQubitPauliGroupElement (LayerOutputSize n nX nZ)))
        (by
          intro z hz
          exact layerSurfaceZCheckCandidates_zType z hz)
        (by
          intro x hx
          simp at hx)
        (by
          intro z hz x hx
          simp at hx)
      simpa using hNoNeg)

/-- An X-check/physical-qubit Tanner incidence, hence an X junction. -/
abbrev XJunction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  { p : Fin nX × Fin n // input.xCheck p.1 p.2 = 1 }

/-- A Z-check/physical-qubit Tanner incidence, hence a Z junction. -/
abbrev ZJunction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  { p : Fin nZ × Fin n // input.zCheck p.1 p.2 = 1 }

/-- A junction of either CSS sector. -/
abbrev Junction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  XJunction input ⊕ ZJunction input

/-- Recover the X-check incidence carried by an X-junction index. -/
lemma xJunction_incident {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input) :
    input.xCheck junction.1.1 junction.1.2 = 1 :=
  junction.2

/-- Recover the Z-check incidence carried by a Z-junction index. -/
lemma zJunction_incident {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input) :
    input.zCheck junction.1.1 junction.1.2 = 1 :=
  junction.2

/-- The CSS commutation law for the input check system. -/
lemma css_commutes {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    ∑ q : Fin n, input.xCheck x q * input.zCheck z q = 0 :=
  input.css_commutation x z

/-- The shared support of commuting binary X and Z checks has even cardinality. -/
lemma css_check_overlap_even {n : ℕ} (xCheck zCheck : Fin n → ZMod 2)
    (hcomm : ∑ q : Fin n, xCheck q * zCheck q = 0) :
    Even (Finset.univ.filter (fun q => xCheck q = 1 ∧ zCheck q = 1)).card := by
  classical
  have hprod : ∀ x z : ZMod 2,
      x * z = if x = 1 ∧ z = 1 then 1 else 0 := by
    intro x z
    fin_cases x <;> fin_cases z <;> decide
  have hsum :
      (∑ q : Fin n, xCheck q * zCheck q) =
        ((Finset.univ.filter (fun q => xCheck q = 1 ∧ zCheck q = 1)).card : ZMod 2) := by
    conv_lhs =>
      arg 2; ext q
      rw [hprod (xCheck q) (zCheck q)]
    rw [Finset.sum_boole]
  rw [hsum, ZMod.natCast_eq_zero_iff_even] at hcomm
  exact hcomm

/-- Pair a finite linearly ordered set by consecutive elements. -/
private def adjacentPairingFin (m : ℕ) :
    (Fin m × Fin 2) ≃ Fin (2 * m) where
  toFun p := ⟨2 * p.1.val + p.2.val, by omega⟩
  invFun i :=
    ⟨⟨i.val / 2, by omega⟩, ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩⟩
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    apply Prod.ext <;> apply Fin.ext <;> simp <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    simp
    omega

/-- An even finite set has a perfect matching that respects its linear order. -/
private noncomputable def orderedPairing {α : Type*} [LinearOrder α]
    (s : Finset α) (heven : Even s.card) :
    (Fin (s.card / 2) × Fin 2) ≃ {x // x ∈ s} := by
  have hcard : 2 * (s.card / 2) = s.card := by
    obtain ⟨m, hm⟩ := heven
    omega
  exact (adjacentPairingFin (s.card / 2)).trans
    ((Equiv.cast (congrArg Fin hcard)).trans (s.orderIsoOfFin rfl).toEquiv)

/-- Pair the shared qubits of an X/Z check pair in the canonical `Fin n` order. -/
def CSSLayerInput.xzCheckOverlap {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) : Finset (Fin n) :=
  Finset.univ.filter (fun q => input.xCheck x q = 1 ∧ input.zCheck z q = 1)

/-- Pair the shared qubits of an X/Z check pair in the canonical `Fin n` order. -/
noncomputable def CSSLayerInput.xzJunctionPairing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    (Fin ((input.xzCheckOverlap x z).card / 2) × Fin 2) ≃
      {q : Fin n // q ∈ input.xzCheckOverlap x z} :=
  orderedPairing _ (css_check_overlap_even (input.xCheck x) (input.zCheck z)
      (css_commutes input x z))

/-- One endpoint in the canonical matching of an X/Z overlap. -/
noncomputable def CSSLayerInput.xzPairEndpoint {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) (endpoint : Fin 2) : Fin n :=
  (input.xzJunctionPairing x z (pair, endpoint)).val

/-- Each paired endpoint is incident to both input checks. -/
lemma CSSLayerInput.xzPairEndpoint_incident {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) (endpoint : Fin 2) :
    input.xCheck x (input.xzPairEndpoint x z pair endpoint) = 1 ∧
      input.zCheck z (input.xzPairEndpoint x z pair endpoint) = 1 := by
  have hmem := (input.xzJunctionPairing x z (pair, endpoint)).property
  change input.xzPairEndpoint x z pair endpoint ∈
    Finset.univ.filter (fun q => input.xCheck x q = 1 ∧ input.zCheck z q = 1) at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- The endpoints in each junction pair are distinct. -/
lemma CSSLayerInput.xzPairEndpoint_ne {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) :
    input.xzPairEndpoint x z pair 0 ≠ input.xzPairEndpoint x z pair 1 := by
  intro h
  have hsub : input.xzJunctionPairing x z (pair, (0 : Fin 2)) =
      input.xzJunctionPairing x z (pair, (1 : Fin 2)) := Subtype.ext h
  have hinj := (input.xzJunctionPairing x z).injective hsub
  have h01 := congrArg Prod.snd hinj
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- Y-directed lattice edges joining one paired pair of X/Z incidences. -/
noncomputable def CSSLayerInput.xzPairYEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
  (pair : Fin ((input.xzCheckOverlap x z).card / 2)) : Finset (Fin n) := by
  classical
  let first := input.xzPairEndpoint x z pair 0
  let second := input.xzPairEndpoint x z pair 1
  exact Finset.univ.filter (fun edge =>
    min first.val second.val ≤ edge.val ∧ edge.val < max first.val second.val)

/-- Every matched overlap pair determines a nonempty y-directed segment. -/
lemma CSSLayerInput.xzPairYEdges_nonempty {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) :
    (input.xzPairYEdges x z pair).Nonempty := by
  classical
  let first := input.xzPairEndpoint x z pair 0
  let second := input.xzPairEndpoint x z pair 1
  have hne : first ≠ second := input.xzPairEndpoint_ne x z pair
  have hval_ne : first.val ≠ second.val := by
    intro hval
    exact hne (Fin.ext hval)
  have hlt : min first.val second.val < max first.val second.val := by
    by_cases h : first.val ≤ second.val
    · rw [min_eq_left h, max_eq_right h]
      exact lt_of_le_of_ne h hval_ne
    · have h' : second.val ≤ first.val := Nat.le_of_not_ge h
      rw [min_eq_right h', max_eq_left h']
      exact lt_of_le_of_ne h' (Ne.symm hval_ne)
  have hmax : max first.val second.val < n := max_lt first.isLt second.isLt
  have hbound : min first.val second.val < n := lt_trans hlt hmax
  let edge : Fin n := ⟨min first.val second.val, hbound⟩
  refine ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  change min first.val second.val ≤ edge.val ∧ edge.val < max first.val second.val
  constructor
  · simp [edge]
  · simpa [edge] using hlt

/-- A local nontrivial-y check cell whose two consecutive y-edges lie in a matched segment. -/
structure NontrivialYJunctionCellIndex {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) where
  xCheck : Fin nX
  zCheck : Fin nZ
  pair : Fin ((input.xzCheckOverlap xCheck zCheck).card / 2)
  yCell : Fin (n - 1)
  firstEdge_mem : interiorCast yCell ∈ input.xzPairYEdges xCheck zCheck pair
  secondEdge_mem : interiorSucc yCell ∈ input.xzPairYEdges xCheck zCheck pair

/-- Mixed four-edge X star along the interior of a nontrivial y junction. -/
noncomputable def CSSLayerInput.nontrivialYJunctionXStarEdges
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact {layerXEdge cell.zCheck (interiorSuccVertex cell.yCell) cell.xCheck.castSucc,
    layerYEdge cell.zCheck.castSucc (interiorCast cell.yCell) cell.xCheck.castSucc,
    layerYEdge cell.zCheck.castSucc (interiorSucc cell.yCell) cell.xCheck.castSucc,
    layerZEdge cell.zCheck.castSucc (interiorSuccVertex cell.yCell) cell.xCheck}

/-- Augmented five-edge Z plaquette along the interior of a nontrivial y junction. -/
noncomputable def CSSLayerInput.nontrivialYJunctionZPlaquetteEdges
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    Finset (LayerLatticeEdge n nX nZ) :=
  insert (layerYEdge cell.zCheck.castSucc (interiorSucc cell.yCell) cell.xCheck.succ)
    (yzSurfacePlaquetteEdges cell.zCheck (interiorCast cell.yCell) cell.xCheck)

/-- The local nontrivial-y X star has four distinct edges. -/
lemma CSSLayerInput.nontrivialYJunctionXStarEdges_card
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    (input.nontrivialYJunctionXStarEdges cell).card = 4 := by
  classical
  simp [nontrivialYJunctionXStarEdges, layerXEdge, layerYEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- The augmented local nontrivial-y Z plaquette has five distinct edges. -/
lemma CSSLayerInput.nontrivialYJunctionZPlaquetteEdges_card
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    (input.nontrivialYJunctionZPlaquetteEdges cell).card = 5 := by
  classical
  rw [nontrivialYJunctionZPlaquetteEdges]
  have hnew :
      layerYEdge cell.zCheck.castSucc (interiorSucc cell.yCell) cell.xCheck.succ ∉
        yzSurfacePlaquetteEdges cell.zCheck (interiorCast cell.yCell) cell.xCheck := by
    simp [yzSurfacePlaquetteEdges, layerYEdge, layerZEdge,
      interiorCast_ne_succ, interiorSucc_ne_cast]
  rw [Finset.card_insert_of_notMem hnew, card_yzSurfacePlaquetteEdges]

lemma CSSLayerInput.nontrivialYJunctionEdges_overlap
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    input.nontrivialYJunctionXStarEdges cell ∩
        input.nontrivialYJunctionZPlaquetteEdges cell =
      {layerYEdge cell.zCheck.castSucc (interiorCast cell.yCell) cell.xCheck.castSucc,
        layerZEdge cell.zCheck.castSucc (interiorSuccVertex cell.yCell) cell.xCheck} := by
  classical
  have hvertex : interiorSuccVertex cell.yCell = (interiorCast cell.yCell).succ := by
    apply Fin.ext
    simp [interiorSuccVertex, interiorCast, interiorSucc]
  simp [nontrivialYJunctionXStarEdges, nontrivialYJunctionZPlaquetteEdges,
    yzSurfacePlaquetteEdges, layerXEdge, layerYEdge, layerZEdge,
    hvertex, interiorCast_ne_succ, interiorSucc_ne_cast,
    fin_castSucc_ne_succ, fin_succ_ne_castSucc]

lemma CSSLayerInput.nontrivialYJunctionEdges_overlap_card
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    (input.nontrivialYJunctionXStarEdges cell ∩
      input.nontrivialYJunctionZPlaquetteEdges cell).card = 2 := by
  classical
  rw [nontrivialYJunctionEdges_overlap]
  simp [layerYEdge, layerZEdge]

/-- X-Pauli candidate at an interior nontrivial-y junction cell. -/
noncomputable def CSSLayerInput.nontrivialYJunctionXStarCandidate
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (input.nontrivialYJunctionXStarEdges cell)

/-- Z-Pauli candidate at an interior nontrivial-y junction cell. -/
noncomputable def CSSLayerInput.nontrivialYJunctionZPlaquetteCandidate
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (input.nontrivialYJunctionZPlaquetteEdges cell)

lemma CSSLayerInput.nontrivialYJunctionXStarCandidate_weight
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement.weight (input.nontrivialYJunctionXStarCandidate cell) = 4 := by
  rw [nontrivialYJunctionXStarCandidate, weight_layerXPauli,
    nontrivialYJunctionXStarEdges_card]

lemma CSSLayerInput.nontrivialYJunctionZPlaquetteCandidate_weight
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement.weight
      (input.nontrivialYJunctionZPlaquetteCandidate cell) = 5 := by
  rw [nontrivialYJunctionZPlaquetteCandidate, weight_layerZPauli,
    nontrivialYJunctionZPlaquetteEdges_card]

lemma CSSLayerInput.nontrivialYJunctionXStarCandidate_isXType
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement.IsXTypeElement
      (input.nontrivialYJunctionXStarCandidate cell) :=
  layerXPauli_isXType _

lemma CSSLayerInput.nontrivialYJunctionZPlaquetteCandidate_isZType
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    NQubitPauliGroupElement.IsZTypeElement
      (input.nontrivialYJunctionZPlaquetteCandidate cell) :=
  layerZPauli_isZType _

lemma CSSLayerInput.nontrivialYJunctionCandidates_commute
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (cell : NontrivialYJunctionCellIndex input) :
    input.nontrivialYJunctionXStarCandidate cell *
        input.nontrivialYJunctionZPlaquetteCandidate cell =
      input.nontrivialYJunctionZPlaquetteCandidate cell *
        input.nontrivialYJunctionXStarCandidate cell := by
  rw [nontrivialYJunctionXStarCandidate, nontrivialYJunctionZPlaquetteCandidate,
    layerXPauli_commutes_layerZPauli_iff, nontrivialYJunctionEdges_overlap_card]
  decide

/-- The y-directed defect segment for a matched X/Z overlap pair. -/
noncomputable def CSSLayerInput.xzPairYJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact (input.xzPairYEdges x z pair).image
    (fun edge => Sum.inr (Sum.inl (z.castSucc, edge, x.castSucc)))

/-- The complete y-directed crossing of one X-check and one Z-check layer. -/
def CSSLayerInput.xzYCrossingEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    Finset (LayerLatticeEdge n nX nZ) :=
  Finset.univ.image (fun y : Fin n => layerYEdge z.castSucc y x.castSucc)

/-- Union of nontrivial y-junction segments selected by the ordered overlap matching. -/
noncomputable def CSSLayerInput.xzNontrivialYJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact Finset.univ.biUnion fun pair : Fin ((input.xzCheckOverlap x z).card / 2) =>
    input.xzPairYJunctionEdges x z pair

/-- The remaining edges at the y crossing form trivial junction segments. -/
noncomputable def CSSLayerInput.xzTrivialYJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    Finset (LayerLatticeEdge n nX nZ) :=
  input.xzYCrossingEdges x z \ input.xzNontrivialYJunctionEdges x z

/-- Each matched segment lies inside the complete y-directed crossing. -/
lemma CSSLayerInput.xzPairYJunctionEdges_subset_crossing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) :
    input.xzPairYJunctionEdges x z pair ⊆ input.xzYCrossingEdges x z := by
  classical
  change
    Finset.image (fun edge => Sum.inr (Sum.inl (z.castSucc, edge, x.castSucc)))
        (input.xzPairYEdges x z pair) ⊆
      Finset.image (fun y => Sum.inr (Sum.inl (z.castSucc, y, x.castSucc))) Finset.univ
  apply Finset.image_subset_iff.mpr
  intro edge hedge
  exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, rfl⟩

/-- The union of matched segments lies inside the complete crossing. -/
lemma CSSLayerInput.xzNontrivialYJunctionEdges_subset_crossing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    input.xzNontrivialYJunctionEdges x z ⊆ input.xzYCrossingEdges x z := by
  classical
  intro edge hedge
  simp only [xzNontrivialYJunctionEdges, Finset.mem_biUnion,
    Finset.mem_univ, true_and] at hedge
  rcases hedge with ⟨pair, hpair⟩
  exact input.xzPairYJunctionEdges_subset_crossing x z pair hpair

/-- The trivial crossing remainder is a subset of the complete crossing. -/
lemma CSSLayerInput.xzTrivialYJunctionEdges_subset_crossing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    input.xzTrivialYJunctionEdges x z ⊆ input.xzYCrossingEdges x z :=
  Finset.sdiff_subset

/-- Trivial and matched nontrivial y-segments are disjoint. -/
lemma CSSLayerInput.xzYJunctionEdges_disjoint {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    Disjoint (input.xzNontrivialYJunctionEdges x z)
      (input.xzTrivialYJunctionEdges x z) := by
  classical
  rw [Finset.disjoint_left]
  intro edge hnontrivial htrivial
  change edge ∈ (input.xzYCrossingEdges x z \
    input.xzNontrivialYJunctionEdges x z : Finset _ ) at htrivial
  exact (Finset.mem_sdiff.mp htrivial).2 hnontrivial

/-- Matched nontrivial and residual trivial y-segments partition each crossing. -/
lemma CSSLayerInput.xzYJunctionEdges_union_eq_crossing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    input.xzNontrivialYJunctionEdges x z ∪
      input.xzTrivialYJunctionEdges x z = input.xzYCrossingEdges x z := by
  classical
  ext edge
  by_cases hnontrivial : edge ∈ input.xzNontrivialYJunctionEdges x z
  · have hcrossing := input.xzNontrivialYJunctionEdges_subset_crossing x z hnontrivial
    simp [xzTrivialYJunctionEdges, hnontrivial, hcrossing]
  · simp [xzTrivialYJunctionEdges, hnontrivial]

/-- The X-oriented defect line where an X-check layer meets an incident data layer. -/
def CSSLayerInput.xJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input) :
    Finset (LayerLatticeEdge n nX nZ) :=
  Finset.univ.image (fun xCoord : Fin nZ =>
    layerXEdge xCoord junction.1.2.castSucc junction.1.1.castSucc)

/-- The Z-oriented defect line where a Z-check layer meets an incident data layer. -/
def CSSLayerInput.zJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input) :
    Finset (LayerLatticeEdge n nX nZ) :=
  Finset.univ.image (fun zCoord : Fin nX =>
    layerZEdge junction.1.1.castSucc junction.1.2.castSucc zCoord)

/-- Position of an incident data layer along one ordered check layer. -/
inductive CheckLayerJunctionPosition
  | single
  | first
  | middle
  | last
  deriving DecidableEq, Repr

/-- Classify an element of a finite ordered support as first, middle, or last. -/
noncomputable def Finset.orderedSupportPosition {α : Type*} [LinearOrder α]
    (support : Finset α) (q : {q // q ∈ support}) : CheckLayerJunctionPosition := by
  have hcard_pos : 0 < support.card := Finset.card_pos.mpr ⟨q.val, q.property⟩
  let order := support.orderIsoOfFin rfl
  let rank := order.symm q
  exact if hsingle : support.card = 1 then .single
    else if hfirst : rank.val = 0 then .first
    else if hlast : rank.val + 1 = support.card then .last
    else .middle

/-- Position of an X-check/data-layer junction in the X-check's ordered support. -/
noncomputable def CSSLayerInput.xJunctionPosition {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input) :
    CheckLayerJunctionPosition := by
  let support := Finset.univ.filter (fun q : Fin n => input.xCheck junction.1.1 q = 1)
  have hmem : junction.1.2 ∈ support := Finset.mem_filter.mpr ⟨Finset.mem_univ _, junction.2⟩
  exact Finset.orderedSupportPosition support ⟨junction.1.2, hmem⟩

/-- Position of a Z-check/data-layer junction in the Z-check's ordered support. -/
noncomputable def CSSLayerInput.zJunctionPosition {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input) :
    CheckLayerJunctionPosition := by
  let support := Finset.univ.filter (fun q : Fin n => input.zCheck junction.1.1 q = 1)
  have hmem : junction.1.2 ∈ support := Finset.mem_filter.mpr ⟨Finset.mem_univ _, junction.2⟩
  exact Finset.orderedSupportPosition support ⟨junction.1.2, hmem⟩

/-- X-star support at a Z-check incidence, with the y-edge chosen by position. -/
noncomputable def CSSLayerInput.zJunctionXStarEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) : Finset (LayerLatticeEdge n nX nZ) := by
  let dataEdge : Fin n :=
    if input.zJunctionPosition junction = .last then
      ⟨junction.1.2.val - 1, by omega⟩
    else junction.1.2
  exact insert
    (layerXEdge junction.1.1 junction.1.2.castSucc
      (interiorSuccVertex (m := nX) xCoord))
    (insert
      (layerYEdge junction.1.1.castSucc dataEdge (interiorSuccVertex (m := nX) xCoord))
      (insert
        (layerZEdge junction.1.1.castSucc junction.1.2.castSucc
          (interiorCast (m := nX) xCoord))
        ({
          (layerZEdge junction.1.1.castSucc junction.1.2.castSucc
            (interiorSucc (m := nX) xCoord))})))

/-- X-star support at an X-check incidence, with its y-edge oriented by position. -/
noncomputable def CSSLayerInput.xJunctionXStarEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) : Finset (LayerLatticeEdge n nX nZ) := by
  let dataEdge : Fin n :=
    if input.xJunctionPosition junction = .last then
      ⟨junction.1.2.val - 1, by omega⟩
    else junction.1.2
  exact insert
    (layerXEdge (interiorCast (m := nZ) zCoord) junction.1.2.castSucc
      junction.1.1.castSucc)
    (insert
      (layerXEdge (interiorSucc (m := nZ) zCoord) junction.1.2.castSucc
        junction.1.1.castSucc)
      (insert
        (layerYEdge (interiorSuccVertex (m := nZ) zCoord) dataEdge
          junction.1.1.castSucc)
        ({
          (layerZEdge (interiorSuccVertex (m := nZ) zCoord) junction.1.2.castSucc
            junction.1.1)})))

/-- Both line-junction star templates have support cardinality four. -/
lemma CSSLayerInput.zJunctionXStarEdges_card {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    (input.zJunctionXStarEdges junction xCoord).card = 4 := by
  classical
  simp [zJunctionXStarEdges, layerXEdge, layerYEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

lemma CSSLayerInput.xJunctionXStarEdges_card {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    (input.xJunctionXStarEdges junction zCoord).card = 4 := by
  classical
  simp [xJunctionXStarEdges, layerXEdge, layerYEdge, layerZEdge,
    interiorCast_ne_succ, interiorSucc_ne_cast]

/-- Candidate Z-plaquette support at an X junction, in the adjacent xy face. -/
noncomputable def CSSLayerInput.xJunctionZPlaquetteEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) : Finset (LayerLatticeEdge n nX nZ) := by
  let dataCell : Fin n :=
    if input.xJunctionPosition junction = .last then
      ⟨junction.1.2.val - 1, by omega⟩
    else junction.1.2
  exact xySurfacePlaquetteEdges junction.1.1 (interiorCast zCoord) dataCell

/-- Candidate Z-plaquette support at a Z junction, in the adjacent yz face.

The paper uses this additional check for middle z junctions; the constructor is
total so callers can state that applicability condition separately. -/
noncomputable def CSSLayerInput.zJunctionZPlaquetteEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) : Finset (LayerLatticeEdge n nX nZ) := by
  let dataCell : Fin n :=
    if input.zJunctionPosition junction = .last then
      ⟨junction.1.2.val - 1, by omega⟩
    else junction.1.2
  exact yzSurfacePlaquetteEdges junction.1.1 dataCell (interiorCast xCoord)

/-- Candidate x-junction plaquettes retain the four-edge xy face weight. -/
lemma CSSLayerInput.xJunctionZPlaquetteEdges_card {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    (input.xJunctionZPlaquetteEdges junction zCoord).card = 4 := by
  rw [xJunctionZPlaquetteEdges, card_xySurfacePlaquetteEdges]

/-- Candidate z-junction plaquettes retain the four-edge yz face weight. -/
lemma CSSLayerInput.zJunctionZPlaquetteEdges_card {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    (input.zJunctionZPlaquetteEdges junction xCoord).card = 4 := by
  rw [zJunctionZPlaquetteEdges, card_yzSurfacePlaquetteEdges]

/-- Candidate X-star generator at an X junction. -/
noncomputable def CSSLayerInput.xJunctionXStar {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (input.xJunctionXStarEdges junction zCoord)

/-- Candidate X-star generator at a Z junction. -/
noncomputable def CSSLayerInput.zJunctionXStar {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (input.zJunctionXStarEdges junction xCoord)

/-- Candidate Z-plaquette generator at an X junction. -/
noncomputable def CSSLayerInput.xJunctionZPlaquette {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (input.xJunctionZPlaquetteEdges junction zCoord)

/-- Candidate Z-plaquette generator at a Z junction. -/
noncomputable def CSSLayerInput.zJunctionZPlaquette {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (input.zJunctionZPlaquetteEdges junction xCoord)

/-- The paper's extra Z plaquette at a z junction is present only in the middle case. -/
noncomputable def CSSLayerInput.zJunctionMiddleZPlaquetteCandidate
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : ZJunction input) (xCoord : Fin (nX - 1)) :
    Option (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  if input.zJunctionPosition junction = .middle then
    some (input.zJunctionZPlaquette junction xCoord)
  else none

lemma CSSLayerInput.zJunctionMiddleZPlaquetteCandidate_eq_some
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : ZJunction input) (xCoord : Fin (nX - 1))
    (hposition : input.zJunctionPosition junction = .middle) :
    input.zJunctionMiddleZPlaquetteCandidate junction xCoord =
      some (input.zJunctionZPlaquette junction xCoord) := by
  simp [zJunctionMiddleZPlaquetteCandidate, hposition]

lemma CSSLayerInput.zJunctionMiddleZPlaquetteCandidate_eq_none
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : ZJunction input) (xCoord : Fin (nX - 1))
    (hposition : input.zJunctionPosition junction ≠ .middle) :
    input.zJunctionMiddleZPlaquetteCandidate junction xCoord = none := by
  simp [zJunctionMiddleZPlaquetteCandidate, hposition]

/-- The paper adds x-junction plaquette checks for first and middle incidences. -/
noncomputable def CSSLayerInput.xJunctionFirstOrMiddleZPlaquetteCandidate
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : XJunction input) (zCoord : Fin (nZ - 1)) :
    Option (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  if input.xJunctionPosition junction = .first ∨
      input.xJunctionPosition junction = .middle then
    some (input.xJunctionZPlaquette junction zCoord)
  else none

lemma CSSLayerInput.xJunctionFirstOrMiddleZPlaquetteCandidate_eq_some
  {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : XJunction input) (zCoord : Fin (nZ - 1))
    (hposition : input.xJunctionPosition junction = .first ∨
      input.xJunctionPosition junction = .middle) :
    input.xJunctionFirstOrMiddleZPlaquetteCandidate junction zCoord =
      some (input.xJunctionZPlaquette junction zCoord) := by
  simp [xJunctionFirstOrMiddleZPlaquetteCandidate, hposition]

lemma CSSLayerInput.xJunctionFirstOrMiddleZPlaquetteCandidate_eq_none
    {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ)
    (junction : XJunction input) (zCoord : Fin (nZ - 1))
    (hposition : input.xJunctionPosition junction ≠ .first ∧
      input.xJunctionPosition junction ≠ .middle) :
    input.xJunctionFirstOrMiddleZPlaquetteCandidate junction zCoord = none := by
  simp [xJunctionFirstOrMiddleZPlaquetteCandidate, hposition.1, hposition.2]

lemma CSSLayerInput.xJunctionXStar_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement.weight (input.xJunctionXStar junction zCoord) = 4 := by
  rw [xJunctionXStar, weight_layerXPauli, xJunctionXStarEdges_card]

lemma CSSLayerInput.zJunctionXStar_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement.weight (input.zJunctionXStar junction xCoord) = 4 := by
  rw [zJunctionXStar, weight_layerXPauli, zJunctionXStarEdges_card]

lemma CSSLayerInput.xJunctionZPlaquette_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement.weight (input.xJunctionZPlaquette junction zCoord) = 4 := by
  rw [xJunctionZPlaquette, weight_layerZPauli, xJunctionZPlaquetteEdges_card]

lemma CSSLayerInput.zJunctionZPlaquette_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement.weight (input.zJunctionZPlaquette junction xCoord) = 4 := by
  rw [zJunctionZPlaquette, weight_layerZPauli, zJunctionZPlaquetteEdges_card]

lemma CSSLayerInput.xJunctionXStar_isXType {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement.IsXTypeElement (input.xJunctionXStar junction zCoord) :=
  layerXPauli_isXType _

lemma CSSLayerInput.zJunctionXStar_isXType {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement.IsXTypeElement (input.zJunctionXStar junction xCoord) :=
  layerXPauli_isXType _

lemma CSSLayerInput.xJunctionZPlaquette_isZType {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input)
    (zCoord : Fin (nZ - 1)) :
    NQubitPauliGroupElement.IsZTypeElement
      (input.xJunctionZPlaquette junction zCoord) :=
  layerZPauli_isZType _

lemma CSSLayerInput.zJunctionZPlaquette_isZType {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : ZJunction input)
    (xCoord : Fin (nX - 1)) :
    NQubitPauliGroupElement.IsZTypeElement
      (input.zJunctionZPlaquette junction xCoord) :=
  layerZPauli_isZType _

noncomputable def CSSLayerInput.xJunctionXStarCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact (Finset.univ : Finset (XJunction input × Fin (nZ - 1))).toList.map
    (fun index => input.xJunctionXStar index.1 index.2)

noncomputable def CSSLayerInput.zJunctionXStarCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact (Finset.univ : Finset (ZJunction input × Fin (nX - 1))).toList.map
    (fun index => input.zJunctionXStar index.1 index.2)

noncomputable def CSSLayerInput.xJunctionZPlaquetteCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact (Finset.univ : Finset (XJunction input × Fin (nZ - 1))).toList.filterMap
    (fun index => input.xJunctionFirstOrMiddleZPlaquetteCandidate index.1 index.2)

noncomputable def CSSLayerInput.zJunctionZPlaquetteCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) := by
  classical
  exact (Finset.univ : Finset (ZJunction input × Fin (nX - 1))).toList.filterMap
    (fun index => input.zJunctionMiddleZPlaquetteCandidate index.1 index.2)

lemma CSSLayerInput.mem_xJunctionXStarCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :
    check ∈ input.xJunctionXStarCandidates ↔
      ∃ junction coord, input.xJunctionXStar junction coord = check := by
  classical
  simp [xJunctionXStarCandidates]

lemma CSSLayerInput.mem_zJunctionXStarCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :
    check ∈ input.zJunctionXStarCandidates ↔
      ∃ junction coord, input.zJunctionXStar junction coord = check := by
  classical
  simp [zJunctionXStarCandidates]

lemma CSSLayerInput.mem_xJunctionZPlaquetteCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :
    check ∈ input.xJunctionZPlaquetteCandidates ↔
      ∃ junction coord,
        (input.xJunctionPosition junction = .first ∨
          input.xJunctionPosition junction = .middle) ∧
        input.xJunctionZPlaquette junction coord = check := by
  classical
  simp [xJunctionZPlaquetteCandidates, xJunctionFirstOrMiddleZPlaquetteCandidate]

lemma CSSLayerInput.mem_zJunctionZPlaquetteCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :
    check ∈ input.zJunctionZPlaquetteCandidates ↔
      ∃ junction coord, input.zJunctionPosition junction = .middle ∧
        input.zJunctionZPlaquette junction coord = check := by
  classical
  simp [zJunctionZPlaquetteCandidates, zJunctionMiddleZPlaquetteCandidate]

noncomputable def CSSLayerInput.xzLineXCheckCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  input.xJunctionXStarCandidates ++ input.zJunctionXStarCandidates

noncomputable def CSSLayerInput.xzLineZCheckCandidates {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  input.xJunctionZPlaquetteCandidates ++ input.zJunctionZPlaquetteCandidates

lemma CSSLayerInput.xzLineXCheckCandidates_type_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hcheck : check ∈ input.xzLineXCheckCandidates) :
    NQubitPauliGroupElement.IsXTypeElement check ∧
      NQubitPauliGroupElement.weight check = 4 := by
  rw [xzLineXCheckCandidates, List.mem_append] at hcheck
  rcases hcheck with hx | hz
  · obtain ⟨junction, coord, rfl⟩ := (input.mem_xJunctionXStarCandidates check).mp hx
    exact ⟨input.xJunctionXStar_isXType junction coord,
      input.xJunctionXStar_weight junction coord⟩
  · obtain ⟨junction, coord, rfl⟩ := (input.mem_zJunctionXStarCandidates check).mp hz
    exact ⟨input.zJunctionXStar_isXType junction coord,
      input.zJunctionXStar_weight junction coord⟩

lemma CSSLayerInput.xzLineZCheckCandidates_type_weight {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (check : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hcheck : check ∈ input.xzLineZCheckCandidates) :
    NQubitPauliGroupElement.IsZTypeElement check ∧
      NQubitPauliGroupElement.weight check = 4 := by
  rw [xzLineZCheckCandidates, List.mem_append] at hcheck
  rcases hcheck with hx | hz
  · obtain ⟨junction, coord, _, rfl⟩ := (input.mem_xJunctionZPlaquetteCandidates check).mp hx
    exact ⟨input.xJunctionZPlaquette_isZType junction coord,
      input.xJunctionZPlaquette_weight junction coord⟩
  · obtain ⟨junction, coord, _, rfl⟩ := (input.mem_zJunctionZPlaquetteCandidates check).mp hz
    exact ⟨input.zJunctionZPlaquette_isZType junction coord,
      input.zJunctionZPlaquette_weight junction coord⟩

/-- A Y-junction is one matched pair on the intersection of an X and Z check layer. -/
abbrev YJunctionPairIndex {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) :=
  Σ x : Fin nX, Σ z : Fin nZ, Fin ((input.xzCheckOverlap x z).card / 2)

/-- One unpaired edge on the trivial crossing of X and Z check layers. -/
abbrev TrivialYJunctionEdgeIndex {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :=
  Σ x : Fin nX, Σ z : Fin nZ,
    {y : Fin n // layerYEdge z.castSucc y x.castSucc ∈
      input.xzTrivialYJunctionEdges x z}

/-- A geometric y-junction segment is trivial or belongs to one matched pair. -/
abbrev YJunctionLineIndex {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) :=
  TrivialYJunctionEdgeIndex input ⊕ YJunctionPairIndex input

/-- Every Tanner-incidence and trivial or matched-overlap line defect. -/
abbrev LayerLineDefectIndex {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) :=
  XJunction input ⊕ (ZJunction input ⊕ YJunctionLineIndex input)

/-- Edge support of one of the three line-defect orientations. -/
noncomputable def CSSLayerInput.layerLineDefectEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    LayerLineDefectIndex input → Finset (LayerLatticeEdge n nX nZ)
  | Sum.inl junction => input.xJunctionEdges junction
  | Sum.inr (Sum.inl junction) => input.zJunctionEdges junction
  | Sum.inr (Sum.inr (Sum.inl ⟨x, z, ⟨y, _⟩⟩)) =>
      {layerYEdge z.castSucc y x.castSucc}
  | Sum.inr (Sum.inr (Sum.inr ⟨x, z, pair⟩)) =>
      input.xzPairYJunctionEdges x z pair

/-- The support of an indexed trivial y-segment is its single crossing edge. -/
lemma CSSLayerInput.layerLineDefectEdges_trivialY {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (segment : TrivialYJunctionEdgeIndex input) :
    input.layerLineDefectEdges (Sum.inr (Sum.inr (Sum.inl segment))) =
      {layerYEdge segment.2.1.castSucc segment.2.2.val segment.1.castSucc} := rfl

/-- Vertices of the finite cuboid lattice. -/
abbrev LayerLatticeVertex (n nX nZ : ℕ) : Type :=
  Fin (nZ + 1) × Fin (n + 1) × Fin (nX + 1)

/-- The two endpoint vertices of an oriented cuboid edge. -/
def layerEdgeEndpoints {n nX nZ : ℕ} :
    LayerLatticeEdge n nX nZ → LayerLatticeVertex n nX nZ × LayerLatticeVertex n nX nZ
  | Sum.inl (x, y, z) => ((x.castSucc, y, z), (x.succ, y, z))
  | Sum.inr (Sum.inl (x, y, z)) => ((x, y.castSucc, z), (x, y.succ, z))
  | Sum.inr (Sum.inr (x, y, z)) => ((x, y, z.castSucc), (x, y, z.succ))

/-- Vertices touched by the edge support of one line defect. -/
noncomputable def CSSLayerInput.layerLineDefectVertices {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (line : LayerLineDefectIndex input) :
    Finset (LayerLatticeVertex n nX nZ) := by
  classical
  exact (input.layerLineDefectEdges line).biUnion fun edge =>
    { (layerEdgeEndpoints edge).1, (layerEdgeEndpoints edge).2 }

/-- A point defect is a vertex where two distinct line defects meet. -/
structure LayerPointDefect {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) where
  firstLine : LayerLineDefectIndex input
  secondLine : LayerLineDefectIndex input
  lines_distinct : firstLine ≠ secondLine
  vertex : LayerLatticeVertex n nX nZ
  vertex_on_first : vertex ∈ input.layerLineDefectVertices firstLine
  vertex_on_second : vertex ∈ input.layerLineDefectVertices secondLine

/-- The ten bulk point-defect configurations enumerated in the Layer-codes paper.

These constructors classify local line orientations only; they do not yet
specify the modified Pauli supports shown in the paper's diagrams. -/
inductive LayerBulkPointDefectCase
  | firstXFirstZNontrivialY
  | lastXLastZNontrivialY
  | middleXMiddleZTrivialBelowNontrivialAbove
  | middleXMiddleZNontrivialBelowTrivialAbove
  | middleXFirstZNontrivialYAbove
  | middleXLastZNontrivialYBelow
  | firstXMiddleZNontrivialYAbove
  | lastXMiddleZNontrivialYBelow
  | trivialXMiddleZNontrivialYThrough
  | middleXTrivialZNontrivialYThrough
  deriving DecidableEq

/-- The local y-junction arrangement at a bulk point defect. -/
inductive LayerBulkPointDefectYPattern
  | nontrivial
  | trivialBelowNontrivialAbove
  | nontrivialBelowTrivialAbove
  | nontrivialAbove
  | nontrivialBelow
  | nontrivialThrough
  deriving DecidableEq, Repr

/-- X-incidence position at a bulk point; `none` marks a trivial X crossing. -/
def LayerBulkPointDefectCase.xPosition :
    LayerBulkPointDefectCase → Option CheckLayerJunctionPosition
  | .firstXFirstZNontrivialY => some .first
  | .lastXLastZNontrivialY => some .last
  | .middleXMiddleZTrivialBelowNontrivialAbove => some .middle
  | .middleXMiddleZNontrivialBelowTrivialAbove => some .middle
  | .middleXFirstZNontrivialYAbove => some .middle
  | .middleXLastZNontrivialYBelow => some .middle
  | .firstXMiddleZNontrivialYAbove => some .first
  | .lastXMiddleZNontrivialYBelow => some .last
  | .trivialXMiddleZNontrivialYThrough => none
  | .middleXTrivialZNontrivialYThrough => some .middle

/-- Z-incidence position at a bulk point; `none` marks a trivial Z crossing. -/
def LayerBulkPointDefectCase.zPosition :
    LayerBulkPointDefectCase → Option CheckLayerJunctionPosition
  | .firstXFirstZNontrivialY => some .first
  | .lastXLastZNontrivialY => some .last
  | .middleXMiddleZTrivialBelowNontrivialAbove => some .middle
  | .middleXMiddleZNontrivialBelowTrivialAbove => some .middle
  | .middleXFirstZNontrivialYAbove => some .first
  | .middleXLastZNontrivialYBelow => some .last
  | .firstXMiddleZNontrivialYAbove => some .middle
  | .lastXMiddleZNontrivialYBelow => some .middle
  | .trivialXMiddleZNontrivialYThrough => some .middle
  | .middleXTrivialZNontrivialYThrough => none

/-- Y-junction arrangement at each bulk point, preserving above/below orientation. -/
def LayerBulkPointDefectCase.yPattern :
    LayerBulkPointDefectCase → LayerBulkPointDefectYPattern
  | .firstXFirstZNontrivialY => .nontrivial
  | .lastXLastZNontrivialY => .nontrivial
  | .middleXMiddleZTrivialBelowNontrivialAbove => .trivialBelowNontrivialAbove
  | .middleXMiddleZNontrivialBelowTrivialAbove => .nontrivialBelowTrivialAbove
  | .middleXFirstZNontrivialYAbove => .nontrivialAbove
  | .middleXLastZNontrivialYBelow => .nontrivialBelow
  | .firstXMiddleZNontrivialYAbove => .nontrivialAbove
  | .lastXMiddleZNontrivialYBelow => .nontrivialBelow
  | .trivialXMiddleZNontrivialYThrough => .nontrivialThrough
  | .middleXTrivialZNontrivialYThrough => .nontrivialThrough

instance : Fintype LayerBulkPointDefectCase where
  elems := {
    .firstXFirstZNontrivialY,
    .lastXLastZNontrivialY,
    .middleXMiddleZTrivialBelowNontrivialAbove,
    .middleXMiddleZNontrivialBelowTrivialAbove,
    .middleXFirstZNontrivialYAbove,
    .middleXLastZNontrivialYBelow,
    .firstXMiddleZNontrivialYAbove,
    .lastXMiddleZNontrivialYBelow,
    .trivialXMiddleZNontrivialYThrough,
    .middleXTrivialZNontrivialYThrough }
  complete := by
    intro x
    cases x <;> simp

/-- The bulk taxonomy has one trivial crossing in each x/z orientation and two through-y cases. -/
theorem layerBulkPointDefectGeometry_counts :
    (Finset.univ.filter (fun c : LayerBulkPointDefectCase =>
      LayerBulkPointDefectCase.xPosition c = none)).card = 1 ∧
    (Finset.univ.filter (fun c : LayerBulkPointDefectCase =>
      LayerBulkPointDefectCase.zPosition c = none)).card = 1 ∧
    (Finset.univ.filter (fun c : LayerBulkPointDefectCase =>
      LayerBulkPointDefectCase.yPattern c = .nontrivialThrough)).card = 2 := by
  decide

/-- The twelve boundary point-defect configurations enumerated in the paper. -/
inductive LayerBoundaryPointDefectCase
  | firstZFrontYZ
  | firstZBackYZ
  | lastZFrontYZ
  | lastZBackYZ
  | middleZFrontYZ
  | middleZBackYZ
  | firstXLeftYZ
  | firstXRightYZ
  | lastXLeftYZ
  | lastXRightYZ
  | middleXLeftYZ
  | middleXRightYZ
  deriving DecidableEq

instance : Fintype LayerBoundaryPointDefectCase where
  elems := {
    .firstZFrontYZ,
    .firstZBackYZ,
    .lastZFrontYZ,
    .lastZBackYZ,
    .middleZFrontYZ,
    .middleZBackYZ,
    .firstXLeftYZ,
    .firstXRightYZ,
    .lastXLeftYZ,
    .lastXRightYZ,
    .middleXLeftYZ,
    .middleXRightYZ }
  complete := by
    intro x
    cases x <;> simp

/-- Boundary point cases that require an extra point-defect plaquette. -/
def LayerBoundaryPointDefectCase.hasModifiedPlaquette :
    LayerBoundaryPointDefectCase → Bool
  | .middleZFrontYZ | .middleZBackYZ => true
  | _ => false

/-- Boundary point cases that require modified smooth-boundary stars. -/
def LayerBoundaryPointDefectCase.hasModifiedBoundaryStar :
    LayerBoundaryPointDefectCase → Bool
  | .firstXLeftYZ | .firstXRightYZ | .lastXLeftYZ | .lastXRightYZ
  | .middleXLeftYZ | .middleXRightYZ => true
  | _ => false

/-- Exactly the two middle-z boundary cases add a point-defect plaquette. -/
theorem layerBoundaryCasesWithModifiedPlaquette_card :
    (Finset.univ.filter
      (fun case : LayerBoundaryPointDefectCase =>
        LayerBoundaryPointDefectCase.hasModifiedPlaquette case = true)).card = 2 := by
  decide

/-- Exactly the six x-junction boundary cases modify boundary stars. -/
theorem layerBoundaryCasesWithModifiedBoundaryStar_card :
    (Finset.univ.filter
      (fun case : LayerBoundaryPointDefectCase =>
        LayerBoundaryPointDefectCase.hasModifiedBoundaryStar case = true)).card = 6 := by
  decide

/-- The disjoint sum of all ten bulk and twelve boundary point-defect cases. -/
abbrev LayerPointDefectCase :=
  LayerBulkPointDefectCase ⊕ LayerBoundaryPointDefectCase

/-- The point-defect taxonomy has exactly the 22 cases listed by the paper. -/
theorem layerPointDefectCase_card : Fintype.card LayerPointDefectCase = 22 := by
  decide

/-- A cuboid vertex is on the physical boundary iff one coordinate is an endpoint. -/
def LayerLatticeVertex.onBoundary {n nX nZ : ℕ}
    (vertex : LayerLatticeVertex n nX nZ) : Prop :=
  vertex.1.val = 0 ∨ vertex.1.val = nZ ∨
    vertex.2.1.val = 0 ∨ vertex.2.1.val = n ∨
      vertex.2.2.val = 0 ∨ vertex.2.2.val = nX

/-- Whether a point defect lies on the cuboid boundary. -/
def LayerPointDefect.onBoundary {n k nX nZ : ℕ}
    {input : CSSLayerInput n k nX nZ} (point : LayerPointDefect input) : Prop :=
  point.vertex.onBoundary

/-- All lattice vertices where two distinct generated line defects meet. -/
noncomputable def CSSLayerInput.layerPointDefectVertices {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) : Finset (LayerLatticeVertex n nX nZ) := by
  classical
  exact Finset.univ.filter fun vertex =>
    ∃ first second : LayerLineDefectIndex input,
      first ≠ second ∧
        vertex ∈ input.layerLineDefectVertices first ∧
          vertex ∈ input.layerLineDefectVertices second

/-- Point-defect vertices on the physical boundary of the cuboid. -/
noncomputable def CSSLayerInput.layerBoundaryPointDefectVertices {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) : Finset (LayerLatticeVertex n nX nZ) := by
  classical
  exact (input.layerPointDefectVertices).filter LayerLatticeVertex.onBoundary

/-- Point-defect vertices strictly inside the cuboid. -/
noncomputable def CSSLayerInput.layerBulkPointDefectVertices {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) : Finset (LayerLatticeVertex n nX nZ) := by
  classical
  exact (input.layerPointDefectVertices).filter fun vertex => ¬ vertex.onBoundary

/-- Every geometric point defect is either a bulk or a boundary point defect. -/
lemma layerPointDefectVertices_eq_bulk_union_boundary {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    input.layerPointDefectVertices =
      input.layerBulkPointDefectVertices ∪ input.layerBoundaryPointDefectVertices := by
  classical
  ext vertex
  simp only [CSSLayerInput.layerBulkPointDefectVertices,
    CSSLayerInput.layerBoundaryPointDefectVertices, Finset.mem_filter,
    Finset.mem_union]
  by_cases hboundary : vertex.onBoundary <;> simp [hboundary]

/-- Bulk and boundary point-defect vertex sets are disjoint. -/
lemma layerBulkPointDefectVertices_disjoint_boundary {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) :
    Disjoint input.layerBulkPointDefectVertices input.layerBoundaryPointDefectVertices := by
  classical
  rw [Finset.disjoint_left]
  intro vertex hbulk hboundary
  exact (Finset.mem_filter.mp hbulk).2 (Finset.mem_filter.mp hboundary).2

/-- An output Layer code certificate using QECLean's actual stabilizer-code
representation.

The output size is fixed by the cuboid edge lattice and its logical-qubit count
matches the input. Its generators and distance lower bound remain explicit
certificates until the line- and point-defect checks are constructed. -/
structure LayerCode {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (outputDistance : ℕ) where
  outputCode : StabilizerGroup.StabilizerCode (LayerOutputSize n nX nZ) k
  outputCheckWeight_le_six :
    ∀ g ∈ outputCode.generatorsList,
      NQubitPauliGroupElement.weight g ≤ 6
  outputDistance_lower_bound : ∀ g,
    StabilizerGroup.IsNontrivialLogicalOperator g outputCode.toStabilizerGroup →
      0 < NQubitPauliGroupElement.weight g →
        NQubitPauliGroupElement.weight g ≥ outputDistance

namespace LayerCode

variable {n k nX nZ : ℕ}
variable {input : CSSLayerInput n k nX nZ}
variable {outputDistance : ℕ}

/-- Exhaustive minimum-weight decoding for the packaged output code. -/
noncomputable def decode
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode) :
    Option (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  StabilizerGroup.minimumWeightDecoder layer.outputCode target

/-- Every realizable output syndrome decodes to a matching minimum-weight Pauli. -/
theorem decode_spec
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
    (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target) :
    ∃ recovery, decode layer target = some recovery ∧
      StabilizerGroup.stabilizerSyndrome layer.outputCode recovery = target ∧
      ∀ other, StabilizerGroup.stabilizerSyndrome layer.outputCode other = target →
        NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other :=
  StabilizerGroup.minimumWeightDecoder_spec layer.outputCode target error herror

/-- Exhaustive minimum-weight decoding restricted to X-type output errors. -/
noncomputable def decodeX
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode) :
    Option (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  StabilizerGroup.minimumWeightXDecoder layer.outputCode target

/-- A realizable X-type syndrome decodes to a minimum-weight X correction. -/
theorem decodeX_spec
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
    (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herrorType : NQubitPauliGroupElement.IsXTypeElement error)
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target) :
    ∃ recovery, decodeX layer target = some recovery ∧
      NQubitPauliGroupElement.IsXTypeElement recovery ∧
      StabilizerGroup.stabilizerSyndrome layer.outputCode recovery = target ∧
      ∀ other, NQubitPauliGroupElement.IsXTypeElement other →
        StabilizerGroup.stabilizerSyndrome layer.outputCode other = target →
          NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other :=
  StabilizerGroup.minimumWeightXDecoder_spec layer.outputCode target error herrorType herror

/-- The X-sector decoder corrects errors below half the certified distance. -/
theorem decodeX_corrects_below_half_distance
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
    (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herrorType : NQubitPauliGroupElement.IsXTypeElement error)
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < outputDistance)
    (recovery : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hdecoded : decodeX layer target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ layer.outputCode.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  simpa only [decodeX] using
    StabilizerGroup.minimumWeightXDecoder_corrects_below_half_distance
      layer.outputCode outputDistance layer.outputDistance_lower_bound target error
      herrorType herror hweight recovery hdecoded

/-- Exhaustive minimum-weight decoding restricted to Z-type output errors. -/
noncomputable def decodeZ
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode) :
    Option (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  StabilizerGroup.minimumWeightZDecoder layer.outputCode target

/-- A realizable Z-type syndrome decodes to a minimum-weight Z correction. -/
theorem decodeZ_spec
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
    (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herrorType : NQubitPauliGroupElement.IsZTypeElement error)
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target) :
    ∃ recovery, decodeZ layer target = some recovery ∧
      NQubitPauliGroupElement.IsZTypeElement recovery ∧
      StabilizerGroup.stabilizerSyndrome layer.outputCode recovery = target ∧
      ∀ other, NQubitPauliGroupElement.IsZTypeElement other →
        StabilizerGroup.stabilizerSyndrome layer.outputCode other = target →
          NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other :=
  StabilizerGroup.minimumWeightZDecoder_spec layer.outputCode target error herrorType herror

/-- The Z-sector decoder corrects errors below half the certified distance. -/
theorem decodeZ_corrects_below_half_distance
    (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
    (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herrorType : NQubitPauliGroupElement.IsZTypeElement error)
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < outputDistance)
    (recovery : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hdecoded : decodeZ layer target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ layer.outputCode.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  simpa only [decodeZ] using
    StabilizerGroup.minimumWeightZDecoder_corrects_below_half_distance
      layer.outputCode outputDistance layer.outputDistance_lower_bound target error
      herrorType herror hweight recovery hdecoded

/-- The LayerCode decoder corrects every error below half the certified output distance. -/
theorem decode_corrects_below_half_distance
  (layer : LayerCode input outputDistance)
    (target : StabilizerGroup.StabilizerSyndrome layer.outputCode)
  (error : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (herror : StabilizerGroup.stabilizerSyndrome layer.outputCode error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < outputDistance)
    (recovery : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hdecoded : decode layer target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ layer.outputCode.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  simpa only [decode] using
    StabilizerGroup.minimumWeightDecoder_corrects_below_half_distance
        layer.outputCode outputDistance layer.outputDistance_lower_bound target error herror hweight
      recovery hdecoded

/-- The packaged output is a QECLean stabilizer code with the input logical
qubit count in its type. -/
def toStabilizerCode
  (layer : LayerCode input outputDistance) :
  StabilizerGroup.StabilizerCode (LayerOutputSize n nX nZ) k :=
  layer.outputCode

/-- Every packaged output generator has the original CSS Layer-code weight
bound. -/
lemma generator_weight_le_six
  (layer : LayerCode input outputDistance)
  (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layer.outputCode.generatorsList) :
    NQubitPauliGroupElement.weight g ≤ 6 :=
  layer.outputCheckWeight_le_six g hg

/-- Every nontrivial output logical satisfies the certified distance lower bound. -/
lemma distance_lower_bound
  (layer : LayerCode input outputDistance)
  (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
  (hg : StabilizerGroup.IsNontrivialLogicalOperator g layer.outputCode.toStabilizerGroup)
  (hw : 0 < NQubitPauliGroupElement.weight g) :
  NQubitPauliGroupElement.weight g ≥ outputDistance :=
  layer.outputDistance_lower_bound g hg hw

end LayerCode

end Stabilizer
end Quantum
