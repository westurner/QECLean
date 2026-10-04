import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.Decoder

namespace Quantum
namespace Stabilizer

open scoped BigOperators

/-!
# Layer-code construction boundary

This module formalizes the finite combinatorial layer used by the Layer-code
construction of Williamson and Baspin. An input CSS check system supplies
physical-qubit, X-check, and Z-check indices together with the binary CSS
commutation law. Each input item is assigned a surface-code layer, and the
Tanner incidences define the junctions.

The `LayerCode` structure packages an actual QECLean `StabilizerCode` as the
output certificate. A generic exhaustive minimum-weight decoder is provided
for that certificate, with a correction guarantee below half the supplied
distance lower bound. The layer-code defect stabilizers are not yet constructed
from the CSS input.

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

@[simp] lemma layerPlane_physical {n nX nZ : ℕ} (q : Fin n) :
    layerPlane (Sum.inl q : LayerIndex n nX nZ) = LayerPlane.xz := rfl

@[simp] lemma layerPlane_xCheck {n nX nZ : ℕ} (x : Fin nX) :
    layerPlane (Sum.inr (Sum.inl x) : LayerIndex n nX nZ) = LayerPlane.xy := rfl

@[simp] lemma layerPlane_zCheck {n nX nZ : ℕ} (z : Fin nZ) :
    layerPlane (Sum.inr (Sum.inr z) : LayerIndex n nX nZ) = LayerPlane.yz := rfl

/-- A square cell in one of the finite surface-code layers. -/
abbrev LayerCell (n nX nZ side : ℕ) : Type :=
  LayerIndex n nX nZ × Fin side × Fin side

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
      (Fin (nZ + 1) × Fin (n + 1) × Fin nX)

/-- The exact number of edge-qubits in the finite cuboid lattice. -/
lemma card_layerLatticeEdge (n nX nZ : ℕ) :
    Fintype.card (LayerLatticeEdge n nX nZ) =
      nZ * (n + 1) * (nX + 1) +
        (nZ + 1) * n * (nX + 1) + (nZ + 1) * (n + 1) * nX := by
  simp only [LayerLatticeEdge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Output physical-qubit count fixed by the finite cuboid edge lattice. -/
abbrev LayerOutputSize (n nX nZ : ℕ) : ℕ :=
  Fintype.card (LayerLatticeEdge n nX nZ)

/-- Canonically number the cuboid edge-qubits for QECLean's `Fin`-indexed Paulis. -/
noncomputable def layerEdgeEquiv (n nX nZ : ℕ) :
    LayerLatticeEdge n nX nZ ≃ Fin (LayerOutputSize n nX nZ) :=
  Fintype.equivFin _

/-- X-type Pauli check supported on a finite set of cuboid edges. -/
noncomputable def layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  NQubitPauliGroupElement.ofOperator (fun q =>
    if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.X else PauliOperator.I)

/-- Z-type Pauli check supported on a finite set of cuboid edges. -/
noncomputable def layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  NQubitPauliGroupElement.ofOperator (fun q =>
    if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.Z else PauliOperator.I)

lemma support_layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.support (layerZPauli support) =
      support.image (layerEdgeEquiv n nX nZ) := by
  classical
  ext q
  simp only [NQubitPauliGroupElement.support, NQubitPauliOperator.support,
    Finset.mem_filter, Finset.mem_univ, true_and, NQubitPauliGroupElement.ofOperator_operators,
    layerZPauli]
  change ((layerEdgeEquiv n nX nZ).symm q ∈ support) ↔
    ∃ edge ∈ support, layerEdgeEquiv n nX nZ edge = q
  constructor
  · intro h
    exact ⟨(layerEdgeEquiv n nX nZ).symm q, h, Equiv.apply_symm_apply _ _⟩
  · rintro ⟨edge, hedge, hq⟩
    have heq : edge = (layerEdgeEquiv n nX nZ).symm q := by
      calc
        edge = (layerEdgeEquiv n nX nZ).symm (layerEdgeEquiv n nX nZ edge) :=
          (Equiv.symm_apply_apply _ _).symm
        _ = (layerEdgeEquiv n nX nZ).symm q := by rw [hq]
    simpa [heq] using hedge

lemma weight_layerZPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.weight (layerZPauli support) = support.card := by
  rw [NQubitPauliGroupElement.weight, NQubitPauliOperator.weight, support_layerZPauli]
  exact Finset.card_image_of_injective _ (layerEdgeEquiv n nX nZ).injective

lemma support_layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.support (layerXPauli support) =
      support.image (layerEdgeEquiv n nX nZ) := by
  classical
  ext q
  simp only [NQubitPauliGroupElement.support, NQubitPauliOperator.support,
    Finset.mem_filter, Finset.mem_univ, true_and, NQubitPauliGroupElement.ofOperator_operators,
    layerXPauli]
  change ((layerEdgeEquiv n nX nZ).symm q ∈ support) ↔
    ∃ edge ∈ support, layerEdgeEquiv n nX nZ edge = q
  constructor
  · intro h
    exact ⟨(layerEdgeEquiv n nX nZ).symm q, h, Equiv.apply_symm_apply _ _⟩
  · rintro ⟨edge, hedge, hq⟩
    have heq : edge = (layerEdgeEquiv n nX nZ).symm q := by
      calc
        edge = (layerEdgeEquiv n nX nZ).symm (layerEdgeEquiv n nX nZ edge) :=
          (Equiv.symm_apply_apply _ _).symm
        _ = (layerEdgeEquiv n nX nZ).symm q := by rw [hq]
    simpa [heq] using hedge

lemma weight_layerXPauli {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.weight (layerXPauli support) = support.card := by
  rw [NQubitPauliGroupElement.weight, NQubitPauliOperator.weight, support_layerXPauli]
  exact Finset.card_image_of_injective _ (layerEdgeEquiv n nX nZ).injective

lemma layerZPauli_isZType {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.IsZTypeElement (layerZPauli support) := by
  refine ⟨rfl, ?_⟩
  intro q
  change PauliOperator.IsZType
    (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.Z else PauliOperator.I)
  split_ifs <;> simp [PauliOperator.IsZType]

lemma layerXPauli_isXType {n nX nZ : ℕ}
    (support : Finset (LayerLatticeEdge n nX nZ)) :
    NQubitPauliGroupElement.IsXTypeElement (layerXPauli support) := by
  refine ⟨rfl, ?_⟩
  intro q
  change PauliOperator.IsXType
    (if (layerEdgeEquiv n nX nZ).symm q ∈ support then PauliOperator.X else PauliOperator.I)
  split_ifs <;> simp [PauliOperator.IsXType]

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

/-- The four boundary edges of a square in one physical-qubit xz layer. -/
def xzSurfacePlaquetteEdges {n nX nZ : ℕ} (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x q.castSucc z.castSucc,
    layerZEdge x.succ q.castSucc z,
    layerXEdge x q.castSucc z.succ,
    layerZEdge x.castSucc q.castSucc z}

lemma card_xzSurfacePlaquetteEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    (xzSurfacePlaquetteEdges q x z).card = 4 := by
  classical
  simp [xzSurfacePlaquetteEdges, layerXEdge, layerZEdge]

/-- The four boundary edges of a square in one X-check xy layer. -/
def xySurfacePlaquetteEdges {n nX nZ : ℕ} (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x q.castSucc check.castSucc,
    layerYEdge x.succ q check.castSucc,
    layerXEdge x q.succ check.castSucc,
    layerYEdge x.castSucc q check.castSucc}

lemma card_xySurfacePlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    (xySurfacePlaquetteEdges check x q).card = 4 := by
  classical
  simp [xySurfacePlaquetteEdges, layerXEdge, layerYEdge]

/-- The four boundary edges of a square in one Z-check yz layer. -/
def yzSurfacePlaquetteEdges {n nX nZ : ℕ} (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerYEdge check.castSucc q z.castSucc,
    layerZEdge check.castSucc q.succ z,
    layerYEdge check.castSucc q z.succ,
    layerZEdge check.castSucc q.castSucc z}

lemma card_yzSurfacePlaquetteEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    (yzSurfacePlaquetteEdges check q z).card = 4 := by
  classical
  simp [yzSurfacePlaquetteEdges, layerYEdge, layerZEdge]

/-- Canonical Z-plaquette generator in a physical-qubit xz layer. -/
noncomputable def xzSurfacePlaquette {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (xzSurfacePlaquetteEdges q x z)

lemma weight_xzSurfacePlaquette {n nX nZ : ℕ}
    (q : Fin n) (x : Fin nZ) (z : Fin nX) :
    NQubitPauliGroupElement.weight (xzSurfacePlaquette q x z) = 4 := by
  rw [xzSurfacePlaquette, weight_layerZPauli, card_xzSurfacePlaquetteEdges]

/-- Canonical Z-plaquette generator in an X-check xy layer. -/
noncomputable def xySurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (xySurfacePlaquetteEdges check x q)

lemma weight_xySurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin nZ) (q : Fin n) :
    NQubitPauliGroupElement.weight (xySurfacePlaquette check x q) = 4 := by
  rw [xySurfacePlaquette, weight_layerZPauli, card_xySurfacePlaquetteEdges]

/-- Canonical Z-plaquette generator in a Z-check yz layer. -/
noncomputable def yzSurfacePlaquette {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin n) (z : Fin nX) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerZPauli (yzSurfacePlaquetteEdges check q z)

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
  xzSurfacePlaquetteCandidates ++ xySurfacePlaquetteCandidates ++
    yzSurfacePlaquetteCandidates

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
  · simp only [List.mem_append] at hrest
    rcases hrest with hxy | hyz
    · simp only [xySurfacePlaquetteCandidates, List.mem_map] at hxy
      rcases hxy with ⟨face, hface, rfl⟩
      exact weight_xySurfacePlaquette _ _ _
    · simp only [yzSurfacePlaquetteCandidates, List.mem_map] at hyz
      rcases hyz with ⟨face, hface, rfl⟩
      exact weight_yzSurfacePlaquette _ _ _

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
  · simp only [List.mem_append] at hrest
    rcases hrest with hxy | hyz
    · simp only [xySurfacePlaquetteCandidates, List.mem_map] at hxy
      rcases hxy with ⟨face, hface, rfl⟩
      exact layerZPauli_isZType _
    · simp only [yzSurfacePlaquetteCandidates, List.mem_map] at hyz
      rcases hyz with ⟨face, hface, rfl⟩
      exact layerZPauli_isZType _

/-- The four in-plane edges incident to an interior vertex of an xz layer. -/
def xzSurfaceStarEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x.castSucc q.castSucc z.succ,
    layerXEdge x.succ q.castSucc z.succ,
    layerZEdge x.succ q.castSucc z.castSucc,
    layerZEdge x.succ q.castSucc z.succ}

lemma card_xzSurfaceStarEdges {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    (xzSurfaceStarEdges q x z).card = 4 := by
  classical
  simp [xzSurfaceStarEdges, layerXEdge, layerZEdge]

/-- The four in-plane edges incident to an interior vertex of an xy layer. -/
def xySurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerXEdge x.castSucc q.succ check.castSucc,
    layerXEdge x.succ q.succ check.castSucc,
    layerYEdge x.succ q.castSucc check.castSucc,
    layerYEdge x.succ q.succ check.castSucc}

lemma card_xySurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    (xySurfaceStarEdges check x q).card = 4 := by
  classical
  simp [xySurfaceStarEdges, layerXEdge, layerYEdge]

/-- The four in-plane edges incident to an interior vertex of a yz layer. -/
def yzSurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    Finset (LayerLatticeEdge n nX nZ) :=
  {layerYEdge check.castSucc q.castSucc z.succ,
    layerYEdge check.castSucc q.succ z.succ,
    layerZEdge check.castSucc q.succ z.castSucc,
    layerZEdge check.castSucc q.succ z.succ}

lemma card_yzSurfaceStarEdges {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    (yzSurfaceStarEdges check q z).card = 4 := by
  classical
  simp [yzSurfaceStarEdges, layerYEdge, layerZEdge]

/-- Canonical X-star generator at an interior vertex of an xz layer. -/
noncomputable def xzSurfaceStar {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (xzSurfaceStarEdges q x z)

lemma weight_xzSurfaceStar {n nX nZ : ℕ}
    (q : Fin n) (x : Fin (nZ - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement.weight (xzSurfaceStar q x z) = 4 := by
  rw [xzSurfaceStar, weight_layerXPauli, card_xzSurfaceStarEdges]

/-- Canonical X-star generator at an interior vertex of an xy layer. -/
noncomputable def xySurfaceStar {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (xySurfaceStarEdges check x q)

lemma weight_xySurfaceStar {n nX nZ : ℕ}
    (check : Fin nX) (x : Fin (nZ - 1)) (q : Fin (n - 1)) :
    NQubitPauliGroupElement.weight (xySurfaceStar check x q) = 4 := by
  rw [xySurfaceStar, weight_layerXPauli, card_xySurfaceStarEdges]

/-- Canonical X-star generator at an interior vertex of a yz layer. -/
noncomputable def yzSurfaceStar {n nX nZ : ℕ}
    (check : Fin nZ) (q : Fin (n - 1)) (z : Fin (nX - 1)) :
    NQubitPauliGroupElement (LayerOutputSize n nX nZ) :=
  layerXPauli (yzSurfaceStarEdges check q z)

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
  exact xz ++ xy ++ yz

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
  · simp only [List.mem_append] at hrest
    rcases hrest with hxy | hyz
    · simp only [List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      exact weight_xySurfaceStar _ _ _
    · simp only [List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      exact weight_yzSurfaceStar _ _ _

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
  · simp only [List.mem_append] at hrest
    rcases hrest with hxy | hyz
    · simp only [List.mem_map] at hxy
      rcases hxy with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _
    · simp only [List.mem_map] at hyz
      rcases hyz with ⟨p, hp, rfl⟩
      exact layerXPauli_isXType _

/-- Surface-layer check candidates before line- and point-defect replacement. -/
noncomputable def layerSurfaceCheckCandidates {n nX nZ : ℕ} :
    List (NQubitPauliGroupElement (LayerOutputSize n nX nZ)) :=
  layerInteriorStarCandidates ++ layerSurfacePlaquetteCandidates

/-- Every unmodified surface-layer check candidate has weight at most four. -/
theorem layerSurfaceCheckCandidates_weight_le_four {n nX nZ : ℕ}
    (g : NQubitPauliGroupElement (LayerOutputSize n nX nZ))
    (hg : g ∈ layerSurfaceCheckCandidates) :
    NQubitPauliGroupElement.weight g ≤ 4 := by
  simp only [layerSurfaceCheckCandidates, List.mem_append] at hg
  rcases hg with hstar | hplaquette
  · rw [layerInteriorStarCandidates_weight g hstar]
  · rw [layerSurfacePlaquetteCandidates_weight g hplaquette]

/-- Stabilizer subgroup generated by the unmodified bulk Z plaquettes. -/
noncomputable def layerBulkZStabilizerGroup {n nX nZ : ℕ} :
    StabilizerGroup.StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerSurfacePlaquetteCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.ZType_commutes
        (layerSurfacePlaquetteCandidates_zType g hg)
        (layerSurfacePlaquetteCandidates_zType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        (NQubitPauliGroupElement.listToSet layerSurfacePlaquetteCandidates) ∅
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
    StabilizerGroup.StabilizerGroup (LayerOutputSize n nX nZ) :=
  StabilizerGroup.mkStabilizerFromGenerators (LayerOutputSize n nX nZ)
    layerInteriorStarCandidates
    (by
      intro g hg h hh
      exact StabilizerGroup.CSSCommutationLemmas.XType_commutes
        (layerInteriorStarCandidates_xType g hg)
        (layerInteriorStarCandidates_xType h hh))
    (by
      have hNoNeg := CSS.negIdentity_not_mem_closure_union
        ∅ (NQubitPauliGroupElement.listToSet layerInteriorStarCandidates)
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

/-- An X-check/physical-qubit Tanner incidence, hence an X junction. -/
abbrev XJunction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  { p : Fin nX × Fin n // input.xCheck p.1 p.2 = 1 }

/-- A Z-check/physical-qubit Tanner incidence, hence a Z junction. -/
abbrev ZJunction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  { p : Fin nZ × Fin n // input.zCheck p.1 p.2 = 1 }

/-- A junction of either CSS sector. -/
abbrev Junction {n k nX nZ : ℕ} (input : CSSLayerInput n k nX nZ) : Type :=
  XJunction input ⊕ ZJunction input

lemma xJunction_incident {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (junction : XJunction input) :
    input.xCheck junction.1.1 junction.1.2 = 1 :=
  junction.2

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
    fin_cases x <;> fin_cases z <;> norm_num
  have hsum :
      (∑ q : Fin n, xCheck q * zCheck q) =
        ((Finset.univ.filter (fun q => xCheck q = 1 ∧ zCheck q = 1)).card : ZMod 2) := by
    conv_lhs =>
      arg 2; ext q
      rw [hprod (xCheck q) (zCheck q)]
    rw [Finset.sum_boole]
    rfl
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
    ((Fin.cast hcard).trans (s.orderIsoOfFin rfl).toEquiv)

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
    (input.css_commutes x z))

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
  simpa [xzPairEndpoint, xzCheckOverlap, Finset.mem_filter] using hmem

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
  have hlt : min first.val second.val < max first.val second.val := by
    by_cases h : first.val ≤ second.val
    · simp [min_eq_left h, max_eq_right h]
    · have h' : second.val ≤ first.val := Nat.le_of_lt (Nat.lt_of_not_ge h)
      simp [min_eq_right h', max_eq_left h']
  have hmax : max first.val second.val < n := Nat.max_lt_iff.mpr ⟨first.isLt, second.isLt⟩
  have hbound : min first.val second.val < n := lt_trans hlt hmax
  let edge : Fin n := ⟨min first.val second.val, hbound⟩
  refine ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp [edge, hlt.le]

/-- The y-directed defect segment for a matched X/Z overlap pair. -/
noncomputable def CSSLayerInput.xzPairYJunctionEdges {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ)
    (pair : Fin ((input.xzCheckOverlap x z).card / 2)) :
    Finset (LayerLatticeEdge n nX nZ) := by
  classical
  exact (input.xzPairYEdges x z pair).image
    (fun edge => Sum.inr (Sum.inl (z.castSucc, edge, x.castSucc)))

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
