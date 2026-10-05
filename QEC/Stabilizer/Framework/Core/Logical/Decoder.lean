import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Generic Minimum-Weight Decoder

Exhaustive syndrome decoding for a supplied finite stabilizer code, with a
logical-correction guarantee below half of a supplied distance lower bound.
This is a correctness reference, not an efficient or Layer-specific decoder.
-/

namespace Quantum
namespace StabilizerGroup

/-- Enumerate the four single-qubit Pauli operators. -/
private instance pauliOperatorFintype : Fintype PauliOperator where
  elems := {PauliOperator.I, PauliOperator.X, PauliOperator.Y, PauliOperator.Z}
  complete := by
    intro operator
    cases operator <;> simp

/-- Represent an n-qubit Pauli by its phase and per-qubit operators. -/
private def pauliElementEquiv (n : ℕ) :
    NQubitPauliGroupElement n ≃ (Fin 4 × (Fin n → PauliOperator)) where
  toFun p := (p.phasePower, p.operators)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- Obtain finiteness of n-qubit Paulis from their phase/operator representation. -/
private noncomputable instance pauliElementFintype {n : ℕ} :
    Fintype (NQubitPauliGroupElement n) :=
  Fintype.ofEquiv (Fin 4 × (Fin n → PauliOperator)) (pauliElementEquiv n).symm

/-- The support of a Pauli product is contained in the union of the supports. -/
lemma pauliSupport_mul_subset {n : ℕ} (p q : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.support (p * q) ⊆
      NQubitPauliGroupElement.support p ∪ NQubitPauliGroupElement.support q := by
  classical
  intro i hi
  by_contra hnot
  have hpI : p.operators i = PauliOperator.I := by
    by_contra h
    exact hnot (Finset.mem_union.mpr (Or.inl ((NQubitPauliGroupElement.mem_support p i).2 h)))
  have hqI : q.operators i = PauliOperator.I := by
    by_contra h
    exact hnot (Finset.mem_union.mpr (Or.inr ((NQubitPauliGroupElement.mem_support q i).2 h)))
  have hprodI : (p * q).operators i = PauliOperator.I := by
    simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp, hpI, hqI]
  exact (NQubitPauliGroupElement.mem_support (p * q) i).1 hi hprodI

/-- Pauli multiplication is subadditive in support weight. -/
lemma pauliWeight_mul_le {n : ℕ} (p q : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.weight (p * q) ≤
      NQubitPauliGroupElement.weight p + NQubitPauliGroupElement.weight q := by
  change (NQubitPauliGroupElement.support (p * q)).card ≤
    (NQubitPauliGroupElement.support p).card +
      (NQubitPauliGroupElement.support q).card
  calc
    (NQubitPauliGroupElement.support (p * q)).card ≤
        (NQubitPauliGroupElement.support p ∪ NQubitPauliGroupElement.support q).card :=
      Finset.card_le_card (pauliSupport_mul_subset p q)
    _ ≤ (NQubitPauliGroupElement.support p).card +
        (NQubitPauliGroupElement.support q).card := Finset.card_union_le _ _

/-- The global phase `-1` commutes with every Pauli element. -/
private lemma minusOne_mul_comm {n : ℕ} (p : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.minusOne n * p = p * NQubitPauliGroupElement.minusOne n := by
  apply NQubitPauliGroupElement.ext
  · simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.minusOne,
      NQubitPauliGroupElement.mulOp_identity_left_phase,
      NQubitPauliGroupElement.mulOp_identity_right_phase, add_comm]
  · change
      (NQubitPauliGroupElement.mulOp (NQubitPauliOperator.identity n) p.operators).operators =
        (NQubitPauliGroupElement.mulOp p.operators (NQubitPauliOperator.identity n)).operators
    rw [NQubitPauliGroupElement.mulOp_identity_left_op,
      ← NQubitPauliGroupElement.one_operators,
      NQubitPauliGroupElement.mulOp_identity_right_op]

/-- The global phase `-1` squares to the identity element. -/
private lemma minusOne_sq (n : ℕ) :
    NQubitPauliGroupElement.minusOne n * NQubitPauliGroupElement.minusOne n = 1 := by
  ext <;>
    simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.minusOne,
      NQubitPauliGroupElement.one, NQubitPauliGroupElement.mulOp,
      NQubitPauliOperator.identity, PauliOperator.mulOp]

/-- Equal anticommutation parity with both factors implies commutation with their product. -/
private theorem commutes_mul_of_same_anticommutes {n : ℕ}
    (g p e : NQubitPauliGroupElement n)
    (hsame : NQubitPauliGroupElement.Anticommute g p ↔
      NQubitPauliGroupElement.Anticommute g e) :
    g * (p * e) = (p * e) * g := by
  classical
  by_cases hgp : NQubitPauliGroupElement.Anticommute g p
  · have hge := hsame.mp hgp
    unfold NQubitPauliGroupElement.Anticommute at hgp hge
    calc
      g * (p * e) = (g * p) * e := by rw [← mul_assoc]
      _ = (NQubitPauliGroupElement.minusOne n * (p * g)) * e := by rw [hgp]
      _ = NQubitPauliGroupElement.minusOne n * (p * (g * e)) := by group
      _ = NQubitPauliGroupElement.minusOne n *
          (p * (NQubitPauliGroupElement.minusOne n * (e * g))) := by rw [hge]
      _ = NQubitPauliGroupElement.minusOne n *
          (NQubitPauliGroupElement.minusOne n * (p * (e * g))) := by
            rw [← mul_assoc p (NQubitPauliGroupElement.minusOne n) (e * g),
              ← minusOne_mul_comm p, mul_assoc]
      _ = (p * e) * g := by
        rw [← mul_assoc, minusOne_sq, one_mul, ← mul_assoc]
  · have hge : ¬NQubitPauliGroupElement.Anticommute g e := by
      intro hge
      exact hgp (hsame.mpr hge)
    have hcomm_gp : g * p = p * g :=
      (NQubitPauliGroupElement.commute_or_anticommute g p).resolve_right hgp
    have hcomm_ge : g * e = e * g :=
      (NQubitPauliGroupElement.commute_or_anticommute g e).resolve_right hge
    calc
      g * (p * e) = (g * p) * e := by rw [← mul_assoc]
      _ = (p * g) * e := by rw [hcomm_gp]
      _ = p * (g * e) := by rw [mul_assoc]
      _ = p * (e * g) := by rw [hcomm_ge]
      _ = (p * e) * g := by rw [← mul_assoc]

/-! ## Syndromes -/

/-- A binary syndrome bit for each stabilizer generator, in generator-list order. -/
abbrev StabilizerSyndrome {n k : ℕ} (code : StabilizerCode n k) :=
  Fin code.generatorsList.length → Bool

/-- Compute the syndrome of a Pauli by recording which generators anticommute with it. -/
noncomputable def stabilizerSyndrome {n k : ℕ} (code : StabilizerCode n k)
    (error : NQubitPauliGroupElement n) : StabilizerSyndrome code := by
  classical
  exact fun i => decide
    (NQubitPauliGroupElement.Anticommute (code.generatorsList.get i) error)

/-- The product of two errors with the same syndrome centralizes the code. -/
private theorem same_syndrome_product_mem_centralizer {n k : ℕ}
    (code : StabilizerCode n k) (recovery error : NQubitPauliGroupElement n)
    (hsame : stabilizerSyndrome code recovery = stabilizerSyndrome code error) :
    recovery * error ∈ centralizer code.toStabilizerGroup := by
  rw [mem_centralizer_iff_closure (recovery * error) code.toStabilizerGroup
    (NQubitPauliGroupElement.listToSet code.generatorsList) rfl]
  intro generator hgenerator
  have hgeneratorList : generator ∈ code.generatorsList := by
    simpa [NQubitPauliGroupElement.listToSet] using hgenerator
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hgeneratorList
  have hbit := congrFun hsame i
  change decide (NQubitPauliGroupElement.Anticommute
    (code.generatorsList.get i) recovery) =
    decide (NQubitPauliGroupElement.Anticommute
      (code.generatorsList.get i) error) at hbit
  have hbit' : decide (NQubitPauliGroupElement.Anticommute generator recovery) =
      decide (NQubitPauliGroupElement.Anticommute generator error) := by
    rw [← hi]
    exact hbit
  have hanticommutes : NQubitPauliGroupElement.Anticommute generator recovery ↔
      NQubitPauliGroupElement.Anticommute generator error := by
    constructor
    · intro hrec
      by_contra herr
      simp [hrec, herr] at hbit'
    · intro herr
      by_contra hrec
      simp [hrec, herr] at hbit'
  exact commutes_mul_of_same_anticommutes generator recovery error hanticommutes

/-- The finite set of Pauli errors realizing a requested syndrome. -/
private noncomputable def syndromeCandidates {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) : Finset (NQubitPauliGroupElement n) := by
  classical
  exact Finset.univ.filter (fun error => stabilizerSyndrome code error = target)

/-- A nonempty finite Pauli set contains an element of minimum weight. -/
private theorem exists_minimum_weight_in {n : ℕ}
    (candidates : Finset (NQubitPauliGroupElement n))
    (hcandidates : candidates.Nonempty) :
    ∃ recovery ∈ candidates,
      ∀ error ∈ candidates,
        NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight error := by
  classical
  let weights := candidates.image NQubitPauliGroupElement.weight
  have hweights : weights.Nonempty := by
    rcases hcandidates with ⟨error, herror⟩
    exact ⟨NQubitPauliGroupElement.weight error,
      Finset.mem_image.mpr ⟨error, herror, rfl⟩⟩
  obtain ⟨recovery, hrecovery, hweight⟩ :
      ∃ recovery ∈ candidates,
        NQubitPauliGroupElement.weight recovery = weights.min' hweights := by
    rcases Finset.mem_image.mp (Finset.min'_mem weights hweights) with
      ⟨recovery, hrecovery, hweight⟩
    exact ⟨recovery, hrecovery, hweight⟩
  refine ⟨recovery, hrecovery, ?_⟩
  intro error herror
  have herrorWeight : NQubitPauliGroupElement.weight error ∈ weights :=
    Finset.mem_image.mpr ⟨error, herror, rfl⟩
  have hmin := Finset.min'_le weights (NQubitPauliGroupElement.weight error) herrorWeight
  rw [← hweight] at hmin
  exact hmin

/-- Every nonempty finite syndrome class contains a minimum-weight recovery. -/
private theorem exists_minimum_weight_syndrome_recovery {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (hcandidates : (syndromeCandidates code target).Nonempty) :
    ∃ recovery ∈ syndromeCandidates code target,
      ∀ error ∈ syndromeCandidates code target,
        NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight error :=
  exists_minimum_weight_in (syndromeCandidates code target) hcandidates

/-- Choose a minimum-weight Pauli with the requested syndrome. -/
noncomputable def minimumWeightSyndromeRecovery {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (hcandidates : (syndromeCandidates code target).Nonempty) :
    NQubitPauliGroupElement n :=
  Classical.choose (exists_minimum_weight_syndrome_recovery code target hcandidates)

/-- The chosen recovery has the requested syndrome and minimum weight. -/
theorem minimumWeightSyndromeRecovery_spec {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (hcandidates : (syndromeCandidates code target).Nonempty) :
    minimumWeightSyndromeRecovery code target hcandidates ∈ syndromeCandidates code target ∧
      ∀ error ∈ syndromeCandidates code target,
        NQubitPauliGroupElement.weight
            (minimumWeightSyndromeRecovery code target hcandidates) ≤
          NQubitPauliGroupElement.weight error :=
  Classical.choose_spec (exists_minimum_weight_syndrome_recovery code target hcandidates)

/-- Exhaustive minimum-weight decoding; impossible syndromes return `none`. -/
noncomputable def minimumWeightDecoder {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) : Option (NQubitPauliGroupElement n) := by
  classical
  by_cases h : (syndromeCandidates code target).Nonempty
  · exact some (minimumWeightSyndromeRecovery code target h)
  · exact none

/-- A realizable syndrome decodes to a minimum-weight Pauli with that syndrome. -/
theorem minimumWeightDecoder_spec {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herror : stabilizerSyndrome code error = target) :
    ∃ recovery, minimumWeightDecoder code target = some recovery ∧
      stabilizerSyndrome code recovery = target ∧
      ∀ other, stabilizerSyndrome code other = target →
        NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other := by
  classical
  let candidates := syndromeCandidates code target
  have hcandidates : candidates.Nonempty := by
    refine ⟨error, Finset.mem_filter.mpr ⟨Finset.mem_univ _, herror⟩⟩
  let recovery := minimumWeightSyndromeRecovery code target hcandidates
  have hspec := minimumWeightSyndromeRecovery_spec code target hcandidates
  refine ⟨recovery, ?_, (Finset.mem_filter.mp hspec.1).2, ?_⟩
  · simp [minimumWeightDecoder, candidates, hcandidates, recovery]
  · intro other hother
    exact hspec.2 other (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩)

/-- Errors in a requested syndrome class restricted to one Pauli sector. -/
private noncomputable def sectorSyndromeCandidates {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (sector : NQubitPauliGroupElement n → Prop) : Finset (NQubitPauliGroupElement n) := by
  classical
  exact Finset.univ.filter fun error =>
    sector error ∧ stabilizerSyndrome code error = target

/-- Exhaustive minimum-weight decoding restricted to a supplied Pauli sector. -/
private noncomputable def minimumWeightSectorDecoder {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (sector : NQubitPauliGroupElement n → Prop) :
    Option (NQubitPauliGroupElement n) := by
  classical
  let candidates := sectorSyndromeCandidates code target sector
  by_cases h : candidates.Nonempty
  · exact some (Classical.choose (exists_minimum_weight_in candidates h))
  · exact none

/-- A realizable sector syndrome returns a minimum-weight sector correction. -/
private theorem minimumWeightSectorDecoder_spec {n k : ℕ}
    (code : StabilizerCode n k) (target : StabilizerSyndrome code)
    (sector : NQubitPauliGroupElement n → Prop)
    (error : NQubitPauliGroupElement n)
    (hsector : sector error)
    (herror : stabilizerSyndrome code error = target) :
    ∃ recovery, minimumWeightSectorDecoder code target sector = some recovery ∧
      sector recovery ∧ stabilizerSyndrome code recovery = target ∧
      ∀ other, sector other → stabilizerSyndrome code other = target →
        NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other := by
  classical
  let candidates := sectorSyndromeCandidates code target sector
  have hcandidates : candidates.Nonempty := by
    refine ⟨error, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsector, herror⟩⟩
  let recovery := Classical.choose (exists_minimum_weight_in candidates hcandidates)
  have hspec := Classical.choose_spec (exists_minimum_weight_in candidates hcandidates)
  have hmem : recovery ∈ candidates := hspec.1
  have hproperties := Finset.mem_filter.mp hmem
  refine ⟨recovery, ?_, hproperties.2.1, hproperties.2.2, ?_⟩
  · simp [minimumWeightSectorDecoder, candidates, hcandidates, recovery]
  · intro other hotherSector hotherSyndrome
    exact hspec.2 other (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hotherSector, hotherSyndrome⟩)

/-- Exhaustive minimum-weight decoder restricted to X-type Pauli errors. -/
noncomputable def minimumWeightXDecoder {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) : Option (NQubitPauliGroupElement n) :=
  minimumWeightSectorDecoder code target NQubitPauliGroupElement.IsXTypeElement

/-- Correctness and sector-minimality of `minimumWeightXDecoder`. -/
theorem minimumWeightXDecoder_spec {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herrorType : NQubitPauliGroupElement.IsXTypeElement error)
    (herror : stabilizerSyndrome code error = target) :
    ∃ recovery, minimumWeightXDecoder code target = some recovery ∧
      NQubitPauliGroupElement.IsXTypeElement recovery ∧
      stabilizerSyndrome code recovery = target ∧
      ∀ other, NQubitPauliGroupElement.IsXTypeElement other →
        stabilizerSyndrome code other = target →
          NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other := by
  exact minimumWeightSectorDecoder_spec code target
    NQubitPauliGroupElement.IsXTypeElement error herrorType herror

/-- Exhaustive minimum-weight decoder restricted to Z-type Pauli errors. -/
noncomputable def minimumWeightZDecoder {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) : Option (NQubitPauliGroupElement n) :=
  minimumWeightSectorDecoder code target NQubitPauliGroupElement.IsZTypeElement

/-- Correctness and sector-minimality of `minimumWeightZDecoder`. -/
theorem minimumWeightZDecoder_spec {n k : ℕ} (code : StabilizerCode n k)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herrorType : NQubitPauliGroupElement.IsZTypeElement error)
    (herror : stabilizerSyndrome code error = target) :
    ∃ recovery, minimumWeightZDecoder code target = some recovery ∧
      NQubitPauliGroupElement.IsZTypeElement recovery ∧
      stabilizerSyndrome code recovery = target ∧
      ∀ other, NQubitPauliGroupElement.IsZTypeElement other →
        stabilizerSyndrome code other = target →
          NQubitPauliGroupElement.weight recovery ≤ NQubitPauliGroupElement.weight other := by
  exact minimumWeightSectorDecoder_spec code target
    NQubitPauliGroupElement.IsZTypeElement error herrorType herror

/-- A same-syndrome recovery no heavier than the error is correct below half-distance. -/
theorem minimumWeightRecovery_corrects_below_half_distance {n k : ℕ}
    (code : StabilizerCode n k) (distance : ℕ)
    (hdistance_lower_bound : ∀ g,
      IsNontrivialLogicalOperator g code.toStabilizerGroup →
        0 < NQubitPauliGroupElement.weight g →
          NQubitPauliGroupElement.weight g ≥ distance)
    (recovery error : NQubitPauliGroupElement n)
    (hsame : stabilizerSyndrome code recovery = stabilizerSyndrome code error)
    (hminimum : NQubitPauliGroupElement.weight recovery ≤
      NQubitPauliGroupElement.weight error)
    (hweight : 2 * NQubitPauliGroupElement.weight error < distance) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ code.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  let combined := recovery * error
  by_cases hzero : NQubitPauliGroupElement.weight combined = 0
  · exact Or.inl hzero
  · right
    by_contra hno_stabilizer
    have hcentral : combined ∈ centralizer code.toStabilizerGroup :=
      same_syndrome_product_mem_centralizer code recovery error hsame
    have hno_same_operators : ∀ s ∈ code.toStabilizerGroup.toSubgroup,
        s.operators ≠ combined.operators := by
      intro s hs heq
      exact hno_stabilizer ⟨s, hs, heq⟩
    have hlogical : IsNontrivialLogicalOperator combined code.toStabilizerGroup :=
      (IsNontrivialLogicalOperator_iff combined code.toStabilizerGroup).2
        ⟨hcentral, hno_same_operators⟩
    have hpositive : 0 < NQubitPauliGroupElement.weight combined :=
      Nat.pos_of_ne_zero hzero
    have hdistance_lower := hdistance_lower_bound combined hlogical hpositive
    have hproduct_upper :
        NQubitPauliGroupElement.weight combined ≤
          2 * NQubitPauliGroupElement.weight error := by
      calc
      NQubitPauliGroupElement.weight combined =
        NQubitPauliGroupElement.weight (recovery * error) := rfl
      _ ≤ NQubitPauliGroupElement.weight recovery +
        NQubitPauliGroupElement.weight error := pauliWeight_mul_le recovery error
      _ ≤ NQubitPauliGroupElement.weight error +
        NQubitPauliGroupElement.weight error :=
          Nat.add_le_add_right hminimum _
      _ = 2 * NQubitPauliGroupElement.weight error := by rw [two_mul]
    omega

/-- The minimum-weight decoder corrects every error of weight strictly below `distance / 2`.

The returned correction is equivalent to the original error up to a stabilizer and a global
Pauli phase. -/
theorem minimumWeightDecoder_corrects_below_half_distance {n k : ℕ}
    (code : StabilizerCode n k) (distance : ℕ)
    (hdistance_lower_bound : ∀ g,
      IsNontrivialLogicalOperator g code.toStabilizerGroup →
        0 < NQubitPauliGroupElement.weight g →
          NQubitPauliGroupElement.weight g ≥ distance)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herror : stabilizerSyndrome code error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < distance)
    (recovery : NQubitPauliGroupElement n)
    (hdecoded : minimumWeightDecoder code target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ code.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  obtain ⟨decoded, hdecode, hsyndrome, hminimum⟩ :=
    minimumWeightDecoder_spec code target error herror
  have hdecoded_eq : recovery = decoded := Option.some.inj (hdecoded.symm.trans hdecode)
  subst recovery
  have hsame' : stabilizerSyndrome code decoded = stabilizerSyndrome code error :=
    hsyndrome.trans herror.symm
  exact minimumWeightRecovery_corrects_below_half_distance code distance hdistance_lower_bound
    decoded error hsame' (hminimum error herror) hweight

/-- The X-sector decoder corrects X-type errors below half the code distance. -/
theorem minimumWeightXDecoder_corrects_below_half_distance {n k : ℕ}
    (code : StabilizerCode n k) (distance : ℕ)
    (hdistance_lower_bound : ∀ g,
      IsNontrivialLogicalOperator g code.toStabilizerGroup →
        0 < NQubitPauliGroupElement.weight g →
          NQubitPauliGroupElement.weight g ≥ distance)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herrorType : NQubitPauliGroupElement.IsXTypeElement error)
    (herror : stabilizerSyndrome code error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < distance)
    (recovery : NQubitPauliGroupElement n)
    (hdecoded : minimumWeightXDecoder code target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ code.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  obtain ⟨decoded, hdecode, _, hsyndrome, hminimum⟩ :=
    minimumWeightXDecoder_spec code target error herrorType herror
  have hdecoded_eq : recovery = decoded := Option.some.inj (hdecoded.symm.trans hdecode)
  subst recovery
  have hsame' : stabilizerSyndrome code decoded = stabilizerSyndrome code error :=
    hsyndrome.trans herror.symm
  exact minimumWeightRecovery_corrects_below_half_distance code distance hdistance_lower_bound
    decoded error hsame' (hminimum error herrorType herror) hweight

/-- The Z-sector decoder corrects Z-type errors below half the code distance. -/
theorem minimumWeightZDecoder_corrects_below_half_distance {n k : ℕ}
    (code : StabilizerCode n k) (distance : ℕ)
    (hdistance_lower_bound : ∀ g,
      IsNontrivialLogicalOperator g code.toStabilizerGroup →
        0 < NQubitPauliGroupElement.weight g →
          NQubitPauliGroupElement.weight g ≥ distance)
    (target : StabilizerSyndrome code) (error : NQubitPauliGroupElement n)
    (herrorType : NQubitPauliGroupElement.IsZTypeElement error)
    (herror : stabilizerSyndrome code error = target)
    (hweight : 2 * NQubitPauliGroupElement.weight error < distance)
    (recovery : NQubitPauliGroupElement n)
    (hdecoded : minimumWeightZDecoder code target = some recovery) :
    NQubitPauliGroupElement.weight (recovery * error) = 0 ∨
      ∃ s ∈ code.toStabilizerGroup.toSubgroup,
        s.operators = (recovery * error).operators := by
  obtain ⟨decoded, hdecode, _, hsyndrome, hminimum⟩ :=
    minimumWeightZDecoder_spec code target error herrorType herror
  have hdecoded_eq : recovery = decoded := Option.some.inj (hdecoded.symm.trans hdecode)
  subst recovery
  have hsame' : stabilizerSyndrome code decoded = stabilizerSyndrome code error :=
    hsyndrome.trans herror.symm
  exact minimumWeightRecovery_corrects_below_half_distance code distance hdistance_lower_bound
    decoded error hsame' (hminimum error herrorType herror) hweight

end StabilizerGroup
end Quantum
