import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

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

The `LayerCode` structure then packages an actual QECLean `StabilizerCode` as
the output certificate. This keeps the difficult construction and distance
proof obligations explicit: the module does not claim to construct the output
stabilizers or a decoder from arbitrary input data yet.

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

/-- Finite CSS check data used to index a layer-code construction.

The fields record the binary X/Z check matrices and their CSS commutation law.
They deliberately do not call this data a complete quantum code: independence,
logical operators, and distance belong to the QECLean `StabilizerCode` output
certificate below. -/
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

/-- An output Layer code certificate using QECLean's actual stabilizer-code
representation.

The output code, its exact distance, and its generator-weight bound are fields
because the full CSS-to-3D construction is not defined by this module yet.
The type does enforce preservation of the declared logical-qubit count: the
output is `StabilizerCode outputN input.k`. -/
structure LayerCode {n k nX nZ : ℕ}
    (input : CSSLayerInput n k nX nZ)
    (outputN side outputDistance : ℕ) where
  outputCode : StabilizerGroup.StabilizerCode outputN k
  sideLength_at_least_two : 2 ≤ side
  outputCheckWeight_le_six :
    ∀ g ∈ outputCode.generatorsList,
      NQubitPauliGroupElement.weight g ≤ 6
  outputHasDistance :
    StabilizerGroup.HasCodeDistance outputCode outputDistance

namespace LayerCode

variable {n k nX nZ : ℕ}
variable {input : CSSLayerInput n k nX nZ}
variable {outputN side outputDistance : ℕ}

/-- The packaged output is a QECLean stabilizer code with the input logical
qubit count in its type. -/
def toStabilizerCode
    (layer : LayerCode input outputN side outputDistance) :
    StabilizerGroup.StabilizerCode outputN k :=
  layer.outputCode

/-- Every packaged output generator has the original CSS Layer-code weight
bound. -/
lemma generator_weight_le_six
    (layer : LayerCode input outputN side outputDistance)
    (g : NQubitPauliGroupElement outputN)
    (hg : g ∈ layer.outputCode.generatorsList) :
    NQubitPauliGroupElement.weight g ≤ 6 :=
  layer.outputCheckWeight_le_six g hg

/-- The output has the exact distance supplied by its certificate. -/
lemma has_distance
    (layer : LayerCode input outputN side outputDistance) :
    StabilizerGroup.HasCodeDistance layer.outputCode outputDistance :=
  layer.outputHasDistance

end LayerCode

end Stabilizer
end Quantum
