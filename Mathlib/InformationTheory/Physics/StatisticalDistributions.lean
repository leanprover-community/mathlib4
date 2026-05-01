/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.InformationTheory.EntropyNumber.Basic
public import Mathlib.InformationTheory.Entropy.Shannon
public import Mathlib.InformationTheory.Entropy.Axioms
public import Mathlib.InformationTheory.Physics.Common
public import Mathlib.InformationTheory.Entropy.Uniqueness
public import Mathlib.InformationTheory.Physics.UniformSystems



/-!
# Statistical Distributions: Bose--Einstein, Fermi--Dirac, and Maxwell--Boltzmann

This file defines the three canonical statistical-mechanics distributions
(Bose--Einstein, Fermi--Dirac, Maxwell--Boltzmann), proves their
cardinalities, and shows that in each case the physical entropy equals
`C * shannonEntropy`.

## Main definitions

* `p_BE` -- the uniform Bose--Einstein distribution on `OmegaUD N M`.
* `OmegaFD` -- the Fermi--Dirac microstate space.
* `p_FD`, `p_FD_fin` -- the uniform Fermi--Dirac distributions.
* `OmegaMB` -- the Maxwell--Boltzmann microstate space.
* `p_MB`, `p_MB_fin` -- the uniform Maxwell--Boltzmann distributions.

## Main statements

* `card_omega_be` -- BE cardinality is `Nat.multichoose N M`.
* `card_omega_FD` -- FD cardinality is `Nat.choose N M`.
* `card_omega_MB` -- MB cardinality is `N ^ M`.
* `H_BE_from_Multiset_eq_C_shannon` -- BE entropy = C * Shannon.
* `H_FD_eq_C_shannon` -- FD entropy = C * Shannon.
* `H_MB_eq_C_shannon` -- MB entropy = C * Shannon.

## Tags

Bose--Einstein, Fermi--Dirac, Maxwell--Boltzmann, statistical mechanics, entropy
-/

@[expose] public section

namespace InformationTheory.Physics.StatisticalDistributions

open Multiset NNReal Finset Function

open InformationTheory

open InformationTheory.Physics.Common
open InformationTheory.Physics.UniformSystems

/-! ## Bose-Einstein -/

/-!
### Phase 1: Combinatorial Structure (Uniform Distribution
Statespace & Equivalence to Multisets)

Defines the standard BE state space to be uniform `OmegaUD` over
the microstates (occupancy vectors summing to M) and shows it is
equivalent to `SymFin N M` (multisets of size M over Fin N).
-/
/-- Bose-Einstein probability mass on `OmegaUD N M`: the uniform distribution
on the occupancy-vector microstates. -/
noncomputable def p_BE (N M : ℕ) :
    OmegaUD N M → NNReal :=
   p_UD N M

/-!
### Bose Einstein: Cardinality and Iteration
With the equivalence established, we can now define a `Fintype`
instance for `OmegaUD`.
-/

/--
Proves that the cardinality of the Bose-Einstein state space
OmegaUD N M is positive under the condition that either the
number of states N is non-zero or the number of particles M is
zero.
-/
lemma card_omega_BE_pos' (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaUD N M) := by
  simpa [card_omega_be, multichoose_pos_iff] using h

/-!
### Phase 3: Probability Distribution
With cardinality established, we can define the Bose-Einstein
probability distribution. We assume equiprobability of all
microstates (configurations).
-/

lemma p_BE_sums_to_one (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ q : OmegaUD N M, (p_UD N M q) = 1 := by
  let card_val := Fintype.card (OmegaUD N M)
  have h_card_pos : card_val > 0 :=
    card_omega_BE_pos N M h_domain_valid
  simp_rw [p_UD]
  simp_rw [uniformProb]
  rw [dif_pos h_card_pos]
  rw [Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul]
  have h_card_nnreal_ne_zero :
      (card_val : NNReal) ≠ 0 := by
    norm_cast
    exact Nat.pos_iff_ne_zero.mp h_card_pos
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]

/--
Proves that the adapted Bose-Einstein probability distribution
`p_UD_fin N M` (which is uniform over
`Fin (Fintype.card (OmegaUD N M))`) sums to 1.
-/
lemma p_BE_fin_sums_to_one (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    ∑ i : Fin (Fintype.card (OmegaUD N M)),
      (p_UD_fin N M i) = 1 := by
  let k := Fintype.card (OmegaUD N M)
  have hk_pos : k > 0 :=
    card_omega_BE_pos N M h_domain_valid
  simp_rw [p_UD_fin]
  exact sum_uniform_eq_one hk_pos

/--
Helper lemma to show that `p_UD_fin N M` is pointwise equal to
`uniformDist` on `Fin k_card`.
-/
lemma p_BE_fin_is_uniformDist (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    let k_card := Fintype.card (OmegaUD N M)
    have hk_card_pos : k_card > 0 :=
      card_omega_BE_pos N M h_domain_valid
    p_UD_fin N M =
      uniformDist
        (Fintype.card_fin_pos hk_card_pos) := by
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : k_card > 0 :=
    card_omega_BE_pos N M h_domain_valid
  funext i
  simp only [p_UD_fin, uniformProb, uniformDist,
    Fintype.card_fin]
  rw [dif_pos hk_card_pos]

/--
Helper lemma to show that applying an entropy function `H_func`
to `p_UD_fin N M` (coerced to `Real`) is equivalent to evaluating
`entropyUniform₀ H_func k_card` (coerced to `Real`), where
`k_card` is the cardinality of the state space.
-/
lemma H_p_BE_fin_eq_f_H_card (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0)
    (H_func : ∀ {α : Type} [Fintype α],
      (α → NNReal) → NNReal)
    (hH_axioms : HasRotaEntropyAxioms H_func) :
    (H_func (p_UD_fin N M) : ℝ) =
      (entropyUniform₀ hH_axioms
        (Fintype.card (OmegaUD N M)) : ℝ) := by
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : k_card > 0 :=
    card_omega_BE_pos N M h_domain_valid
  rw [p_BE_fin_is_uniformDist N M h_domain_valid]
  simp only [entropyUniform₀]
  rw [dif_pos hk_card_pos]
  simp only [entropyUniform]

theorem H_BE_from_Multiset_eq_C_shannon (N M : ℕ)
    (h_domain_valid : N ≠ 0 ∨ M = 0) :
    (InformationTheory.Physics.Common.H_physical_system
      (p_UD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) *
      shannonEntropy (p_UD_fin N M) := by
  exact H_physical_system_is_rota_uniform N M
    h_domain_valid

/-! ## Fermi-Dirac -/

/-- The Fermi-Dirac microstate space: subsets of `Fin N` of size
exactly `M`. Each element represents a valid FD configuration
(at most one particle per box). -/
def OmegaFD (N M : ℕ) :=
  { s : Finset (Fin N) // s.card = M }

/-- Fintype instance for OmegaFD. Since `Finset (Fin N)` is finite
and the predicate `s.card = M` is decidable, the subtype is
finite. -/
instance fintypeOmegaFD (N M : ℕ) :
    Fintype (OmegaFD N M) :=
  Fintype.subtype
    ((Finset.univ : Finset (Finset (Fin N))).filter
      (fun s => s.card = M))
    (by simp [OmegaFD])

/-- The cardinality of the FD state space is
`Nat.choose N M`. -/
lemma card_omega_FD (N M : ℕ) :
    Fintype.card (OmegaFD N M) = Nat.choose N M := by
  have h : Fintype.card (OmegaFD N M) =
      ((Finset.univ : Finset (Fin N)).powersetCard M).card := by
    unfold OmegaFD
    apply Fintype.card_of_subtype
    intro x
    simp [Finset.mem_powersetCard, Finset.subset_univ]
  rw [h, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-- The cardinality of the FD state space is positive when
`M ≤ N`. -/
lemma card_omega_FD_pos (N M : ℕ) (h : M ≤ N) :
    0 < Fintype.card (OmegaFD N M) := by
  rw [card_omega_FD]
  exact Nat.choose_pos h

/-- The domain validity condition for FD: `M ≤ N` implies
`N ≠ 0 ∨ M = 0`. -/
lemma fd_domain_valid_of_le (N M : ℕ) (h : M ≤ N) :
    N ≠ 0 ∨ M = 0 := by
  by_cases hm : M = 0
  · exact Or.inr hm
  · exact Or.inl
      (Nat.ne_of_gt
        (Nat.lt_of_lt_of_le
          (Nat.pos_of_ne_zero hm) h))

/-!
### Probability Distribution

The uniform FD distribution assigns equal probability
`1 / (N choose M)` to each microstate.
-/

/-- The FD probability distribution over the original state
space. -/
@[nolint unusedArguments]
noncomputable def p_FD (N M : ℕ) :
    OmegaFD N M → NNReal :=
  fun _q => uniformProb (Fintype.card (OmegaFD N M))

/-- The FD probability distribution indexed over
`Fin (Fintype.card (OmegaFD N M))`. -/
@[nolint unusedArguments]
noncomputable def p_FD_fin (N M : ℕ) :
    Fin (Fintype.card (OmegaFD N M)) → NNReal :=
  fun _i => uniformProb (Fintype.card (OmegaFD N M))

/-- The FD distribution sums to 1. -/
lemma p_FD_sums_to_one (N M : ℕ) (h : M ≤ N) :
    ∑ q : OmegaFD N M, (p_FD N M q) = 1 := by
  have h_card_pos :
      Fintype.card (OmegaFD N M) > 0 :=
    card_omega_FD_pos N M h
  simp_rw [p_FD, uniformProb, dif_pos h_card_pos]
  rw [Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  norm_cast
  exact Nat.pos_iff_ne_zero.mp h_card_pos

/-- The Fin-indexed FD distribution sums to 1. -/
lemma p_FD_fin_sums_to_one (N M : ℕ) (h : M ≤ N) :
    ∑ i : Fin (Fintype.card (OmegaFD N M)),
      (p_FD_fin N M i) = 1 := by
  have hk_pos :
      Fintype.card (OmegaFD N M) > 0 :=
    card_omega_FD_pos N M h
  simp_rw [p_FD_fin]
  exact sum_uniform_eq_one hk_pos

/-- The Fin-indexed FD distribution is the canonical uniform
distribution. -/
lemma p_FD_fin_is_uniformDist (N M : ℕ)
    (h : M ≤ N) :
    let k_card := Fintype.card (OmegaFD N M)
    have hk_card_pos : k_card > 0 :=
      card_omega_FD_pos N M h
    p_FD_fin N M =
      uniformDist
        (Fintype.card_fin_pos hk_card_pos) := by
  have hk_card_pos :
      Fintype.card (OmegaFD N M) > 0 :=
    card_omega_FD_pos N M h
  funext i
  simp only [p_FD_fin, uniformProb, uniformDist,
    Fintype.card_fin]
  rw [dif_pos hk_card_pos]

/-- `p_FD_fin` is recognized as uniform input by
`H_physical_system`. -/
lemma p_FD_fin_is_H_physical_system_uniform_input
    (N M : ℕ) (h : M ≤ N) :
    p_FD_fin N M =
      uniformDist
        (α := Fin (Fintype.card (OmegaFD N M)))
        (by {
          simp only [Fintype.card_fin]
          exact card_omega_FD_pos N M h
        }) := by
  have hk_card_pos :
      Fintype.card (OmegaFD N M) > 0 :=
    card_omega_FD_pos N M h
  funext i
  simp [p_FD_fin, uniformProb, uniformDist,
    Fintype.card_fin, if_pos hk_card_pos]

/-- Evaluating `H_physical_system` on `p_FD_fin`. -/
lemma eval_H_physical_system_on_p_FD_fin (N M : ℕ)
    (h : M ≤ N) :
    H_physical_system (p_FD_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaFD N M))
        (Nat.one_le_of_lt
          (card_omega_FD_pos N M h)) := by
  have hk_card_pos :
      Fintype.card (OmegaFD N M) > 0 :=
    card_omega_FD_pos N M h
  simp only [H_physical_system, Fintype.card_fin]
  rw [dif_neg (Nat.ne_of_gt hk_card_pos)]
  simp only [p_FD_fin_is_H_physical_system_uniform_input
    N M h]
  rfl

/-- Shannon entropy of `p_FD_fin` when cardinality is 1. -/
lemma shannonEntropy_of_p_FD_fin_when_k_is_1
    (N M : ℕ)
    (h_k_is_1 :
      Fintype.card (OmegaFD N M) = 1) :
    shannonEntropy (p_FD_fin N M) = 0 := by
  unfold shannonEntropy
  conv_lhs =>
    arg 1
    simp [h_k_is_1]
  simp [p_FD_fin, h_k_is_1, uniformProb, inv_one,
    NNReal.coe_one, Real.negMulLog_one]

/-!
### Main Theorem: FD Entropy = C * Shannon Entropy
-/

/-- **Rota's Entropy Theorem applied to Fermi-Dirac statistics.**
The physical entropy of the FD distribution equals `C` times its
Shannon entropy. -/
theorem H_FD_eq_C_shannon (N M : ℕ) (h : M ≤ N) :
    (InformationTheory.Physics.Common.H_physical_system
      (p_FD_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) *
      shannonEntropy (p_FD_fin N M) := by
  let k_card := Fintype.card (OmegaFD N M)
  have hk_card_ge1 : k_card ≥ 1 :=
    Nat.one_le_of_lt (card_omega_FD_pos N M h)
  rw [eval_H_physical_system_on_p_FD_fin N M h]
  rw [H_physical_system_uniform_only_calc]
  if hk_eq_1 : k_card = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero]
    rw [shannonEntropy_of_p_FD_fin_when_k_is_1 N M
      hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul,
      (Real.log_nonneg
        (Nat.one_le_cast.mpr hk_card_ge1))]
    have h_shannon_eq_log_k :
        shannonEntropy (p_FD_fin N M) =
          Real.log (k_card : ℝ) := by
      rw [p_FD_fin_is_H_physical_system_uniform_input
        N M h]
      rw [shannonEntropy_uniformDist]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl

/-! ## Maxwell-Boltzmann -/

/-- The Maxwell-Boltzmann microstate space: functions from
`Fin M` (labeled balls) to `Fin N` (labeled boxes). Each function
assigns each ball to a box. -/
def OmegaMB (N M : ℕ) := Fin M → Fin N

/-- Fintype instance for OmegaMB. Lean/Mathlib provides
`Pi.instFintype` for functions from a Fintype to a Fintype. -/
instance fintypeOmegaMB (N M : ℕ) :
    Fintype (OmegaMB N M) :=
  show Fintype (Fin M → Fin N) from inferInstance

/-- The cardinality of the MB state space is `N ^ M`. -/
lemma card_omega_MB (N M : ℕ) :
    Fintype.card (OmegaMB N M) = N ^ M := by
  unfold OmegaMB
  rw [Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- The cardinality of the MB state space is positive when
`N ≠ 0 ∨ M = 0`. -/
lemma card_omega_MB_pos (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    0 < Fintype.card (OmegaMB N M) := by
  rw [card_omega_MB]
  cases h with
  | inl hN =>
    exact Nat.pos_of_ne_zero
      (pow_ne_zero M
        (Nat.pos_iff_ne_zero.mp
          (Nat.pos_of_ne_zero hN)))
  | inr hM => simp [hM]

/-!
### Probability Distribution

The uniform MB distribution assigns equal probability
`1 / (N ^ M)` to each microstate.
-/

/-- The MB probability distribution over the original state
space. -/
@[nolint unusedArguments]
noncomputable def p_MB (N M : ℕ) :
    OmegaMB N M → NNReal :=
  fun _q => uniformProb
    (Fintype.card (OmegaMB N M))

/-- The MB probability distribution indexed over
`Fin (Fintype.card (OmegaMB N M))`. -/
@[nolint unusedArguments]
noncomputable def p_MB_fin (N M : ℕ) :
    Fin (Fintype.card (OmegaMB N M)) → NNReal :=
  fun _i => uniformProb
    (Fintype.card (OmegaMB N M))

/-- The MB distribution sums to 1. -/
lemma p_MB_sums_to_one (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    ∑ q : OmegaMB N M, (p_MB N M q) = 1 := by
  have h_card_pos :
      Fintype.card (OmegaMB N M) > 0 :=
    card_omega_MB_pos N M h
  simp_rw [p_MB, uniformProb, dif_pos h_card_pos]
  rw [Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [mul_inv_cancel₀]
  norm_cast
  exact Nat.pos_iff_ne_zero.mp h_card_pos

/-- The Fin-indexed MB distribution sums to 1. -/
lemma p_MB_fin_sums_to_one (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    ∑ i : Fin (Fintype.card (OmegaMB N M)),
      (p_MB_fin N M i) = 1 := by
  have hk_pos :
      Fintype.card (OmegaMB N M) > 0 :=
    card_omega_MB_pos N M h
  simp_rw [p_MB_fin]
  exact sum_uniform_eq_one hk_pos

/-- The Fin-indexed MB distribution is the canonical uniform
distribution. -/
lemma p_MB_fin_is_uniformDist (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    let k_card := Fintype.card (OmegaMB N M)
    have hk_card_pos : k_card > 0 :=
      card_omega_MB_pos N M h
    p_MB_fin N M =
      uniformDist
        (Fintype.card_fin_pos hk_card_pos) := by
  have hk_card_pos :
      Fintype.card (OmegaMB N M) > 0 :=
    card_omega_MB_pos N M h
  funext i
  simp only [p_MB_fin, uniformProb, uniformDist,
    Fintype.card_fin]
  rw [dif_pos hk_card_pos]

/-- `p_MB_fin` is recognized as uniform input by
`H_physical_system`. -/
lemma p_MB_fin_is_H_physical_system_uniform_input
    (N M : ℕ) (h : N ≠ 0 ∨ M = 0) :
    p_MB_fin N M =
      uniformDist
        (α := Fin (Fintype.card (OmegaMB N M)))
        (by {
          simp only [Fintype.card_fin]
          exact card_omega_MB_pos N M h
        }) := by
  have hk_card_pos :
      Fintype.card (OmegaMB N M) > 0 :=
    card_omega_MB_pos N M h
  funext i
  simp [p_MB_fin, uniformProb, uniformDist,
    Fintype.card_fin, if_pos hk_card_pos]

/-- Evaluating `H_physical_system` on `p_MB_fin`. -/
lemma eval_H_physical_system_on_p_MB_fin (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    H_physical_system (p_MB_fin N M) =
      H_physical_system_uniform_only_calc
        (Fintype.card (OmegaMB N M))
        (Nat.one_le_of_lt
          (card_omega_MB_pos N M h)) := by
  have hk_card_pos :
      Fintype.card (OmegaMB N M) > 0 :=
    card_omega_MB_pos N M h
  simp only [H_physical_system, Fintype.card_fin]
  rw [dif_neg (Nat.ne_of_gt hk_card_pos)]
  simp only [
    p_MB_fin_is_H_physical_system_uniform_input
      N M h]
  rfl

/-- Shannon entropy of `p_MB_fin` when cardinality is 1. -/
lemma shannonEntropy_of_p_MB_fin_when_k_is_1
    (N M : ℕ)
    (h_k_is_1 :
      Fintype.card (OmegaMB N M) = 1) :
    shannonEntropy (p_MB_fin N M) = 0 := by
  unfold shannonEntropy
  conv_lhs =>
    arg 1
    simp [h_k_is_1]
  simp [p_MB_fin, h_k_is_1, uniformProb, inv_one,
    NNReal.coe_one, Real.negMulLog_one]

/-!
### Main Theorem: MB Entropy = C * Shannon Entropy
-/

/-- **Rota's Entropy Theorem applied to Maxwell-Boltzmann
statistics.** The physical entropy of the MB distribution equals
`C` times its Shannon entropy. -/
theorem H_MB_eq_C_shannon (N M : ℕ)
    (h : N ≠ 0 ∨ M = 0) :
    (InformationTheory.Physics.Common.H_physical_system
      (p_MB_fin N M) : ℝ) =
      (C_physical_NNReal : ℝ) *
      shannonEntropy (p_MB_fin N M) := by
  let k_card := Fintype.card (OmegaMB N M)
  have hk_card_ge1 : k_card ≥ 1 :=
    Nat.one_le_of_lt (card_omega_MB_pos N M h)
  rw [eval_H_physical_system_on_p_MB_fin N M h]
  rw [H_physical_system_uniform_only_calc]
  if hk_eq_1 : k_card = 1 then
    rw [dif_pos hk_eq_1]
    simp only [NNReal.coe_zero]
    rw [shannonEntropy_of_p_MB_fin_when_k_is_1 N M
      hk_eq_1]
    simp only [mul_zero]
  else
    rw [dif_neg hk_eq_1]
    simp only [RealLogNatToNNReal, NNReal.coe_mul,
      (Real.log_nonneg
        (Nat.one_le_cast.mpr hk_card_ge1))]
    have h_shannon_eq_log_k :
        shannonEntropy (p_MB_fin N M) =
          Real.log (k_card : ℝ) := by
      rw [p_MB_fin_is_H_physical_system_uniform_input
        N M h]
      rw [shannonEntropy_uniformDist]
      simp only [Fintype.card_fin]
      rfl
    rw [h_shannon_eq_log_k]
    rfl

end InformationTheory.Physics.StatisticalDistributions
