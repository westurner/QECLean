import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
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

The x, y, and z coordinate lengths are the numbers of Z checks, input physical
qubits, and X checks, respectively. The three sum components index edges along
each coordinate direction. -/
abbrev LayerLatticeEdge (n nX nZ : ℕ) : Type :=
  (Fin (nZ - 1) × Fin n × Fin nX) ⊕
    ((Fin nZ × Fin (n - 1) × Fin nX) ⊕
      (Fin nZ × Fin n × Fin (nX - 1)))

/-- The exact number of edge-qubits in the finite cuboid lattice. -/
lemma card_layerLatticeEdge (n nX nZ : ℕ) :
    Fintype.card (LayerLatticeEdge n nX nZ) =
      (nZ - 1) * n * nX + nZ * (n - 1) * nX + nZ * n * (nX - 1) := by
  simp only [LayerLatticeEdge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Output physical-qubit count fixed by the finite cuboid edge lattice. -/
abbrev LayerOutputSize (n nX nZ : ℕ) : ℕ :=
  Fintype.card (LayerLatticeEdge n nX nZ)

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
noncomputable def CSSLayerInput.xzJunctionPairing {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ) (x : Fin nX) (z : Fin nZ) :
    (Fin ((Finset.univ.filter
      (fun q => input.xCheck x q = 1 ∧ input.zCheck z q = 1)).card / 2) × Fin 2) ≃
      {q : Fin n // q ∈ Finset.univ.filter
        (fun q => input.xCheck x q = 1 ∧ input.zCheck z q = 1)} :=
  orderedPairing _ (css_check_overlap_even (input.xCheck x) (input.zCheck z)
    (input.css_commutes x z))

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
