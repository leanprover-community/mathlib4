/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.NNReal.Basic



/-!
# Shannon Entropy on Finite Distributions

This file defines the Shannon entropy for discrete probability distributions
on finite types using `NNReal`-valued inputs and proves its basic properties.

## Main definitions

* `shannonEntropy`: `H(p) = ∑ i, negMulLog (p i)` for `p : α → NNReal`
  over `[Fintype α]`, using natural logarithm. This equals `-∑ pᵢ ln pᵢ`.
* `uniformDist`: the uniform distribution on a finite type with positive
  cardinality, valued in `NNReal`.
* `uniformProb`: `uniformProb n = n⁻¹` when `n > 0`, else `0`.
* `canonicalUniformDist`: the uniform distribution on `Fin k`.
* `probabilitySimplex`: the set of `NNReal`-valued distributions summing
  to `1`.

## Main statements

* `shannonEntropy_nonneg`: Shannon entropy is non-negative for probability
  distributions (those summing to 1).
* `shannonEntropy_uniformDist`: Shannon entropy of the uniform distribution
  equals `log (Fintype.card α)`.
* `shannonEntropy_canonicalUniform`: Shannon entropy of the canonical
  uniform distribution on `Fin k` equals `log k`.
* `shannonEntropy_comp_equiv`: Shannon entropy is invariant under
  equivalence of outcome types.

## Tags

entropy, shannon, information theory
-/

@[expose] public section

-- Cosmetic linters disabled for this initial drop of the InformationTheory
-- subtree. These do not affect correctness; reviewers may request a per-call
-- cleanup as a follow-up PR.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.style.emptyLine false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.longFile 0
set_option linter.style.show false
set_option linter.style.whitespace false
set_option linter.style.lambdaSyntax false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


open Finset Real

namespace InformationTheory

variable {α : Type*} [Fintype α]

/-- Shannon entropy of an `NNReal`-valued function on a finite type, using
natural logarithm:
`H(p) = ∑ i, negMulLog (↑(p i)) = -∑ i, (p i) * log (p i)`. -/
noncomputable def shannonEntropy (p : α → NNReal) : ℝ :=
  ∑ i : α, negMulLog (p i : ℝ)

/-- Shannon entropy is non-negative for probability distributions. -/
lemma shannonEntropy_nonneg (p : α → NNReal)
    (hp_sum : ∑ i, p i = 1) : 0 ≤ shannonEntropy p := by
  apply Finset.sum_nonneg
  intro i _
  apply negMulLog_nonneg
  · exact NNReal.coe_nonneg (p i)
  · rw [← NNReal.coe_one, NNReal.coe_le_coe]
    calc p i
        ≤ ∑ j, p j := Finset.single_le_sum
          (fun _ _ => bot_le) (Finset.mem_univ i)
      _ = 1 := hp_sum

/-- Shannon entropy is invariant under equivalence of outcome types. -/
theorem shannonEntropy_comp_equiv {β : Type*} [Fintype β]
    (p_target : β → NNReal) (e : α ≃ β) :
    shannonEntropy (p_target ∘ e) = shannonEntropy p_target := by
  unfold shannonEntropy
  simp_rw [Function.comp_apply]
  exact Equiv.sum_comp e (fun (y : β) => negMulLog ((p_target y : ℝ)))

section Uniform

/-- Probability of each outcome in a uniform distribution on `n`
outcomes. Returns `n⁻¹` when `n > 0`, else `0`. -/
noncomputable def uniformProb (n : ℕ) : NNReal :=
  if _hn : n > 0 then (n⁻¹ : NNReal) else 0

/-- The uniform distribution on a finite type with positive
cardinality, valued in `NNReal`. -/
@[nolint unusedArguments]
noncomputable def uniformDist
    (_h_card_pos : 0 < Fintype.card α) : α → NNReal :=
  fun _ => (Fintype.card α : NNReal)⁻¹

/-- The uniform distribution sums to `1`. -/
lemma sum_uniformDist (h_card_pos : 0 < Fintype.card α) :
    (∑ x, uniformDist h_card_pos x) = 1 := by
  have h_card_nnreal_ne_zero : (Fintype.card α : NNReal) ≠ 0 := by
    have h_card_nat_ne_zero : (Fintype.card α : ℕ) ≠ 0 :=
      Nat.ne_of_gt h_card_pos
    simpa using h_card_nat_ne_zero
  simp only [uniformDist, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [mul_inv_cancel₀ h_card_nnreal_ne_zero]

/-- Helper: if `k > 0`, then `0 < Fintype.card (Fin k)`. -/
lemma Fintype.card_fin_pos {k : ℕ} (hk_pos : k > 0) :
    0 < Fintype.card (Fin k) := by
  simp only [Fintype.card_fin]
  exact hk_pos

/-- The canonical uniform distribution on `Fin k`, defined as
`uniformDist` specialised to `Fin k`. -/
noncomputable def canonicalUniformDist (k : ℕ)
    (hk_pos : k > 0) : Fin k → NNReal :=
  uniformDist (Fintype.card_fin_pos hk_pos)

/-- The canonical uniform distribution on `Fin k` sums to `1`. -/
lemma sum_canonicalUniformDist (k : ℕ) (hk_pos : k > 0) :
    (∑ i, canonicalUniformDist k hk_pos i) = 1 := by
  simp only [canonicalUniformDist]
  exact sum_uniformDist (Fintype.card_fin_pos hk_pos)

/-- Auxiliary cancellation:
`(k : ℝ) * (k : ℝ)⁻¹ * log k = log k`. -/
lemma mul_inv_cancel_mul_log {k : ℕ} (hk_pos_nat : k > 0) :
    ((k : ℝ) * (k : ℝ)⁻¹) * log k = log k := by
  have hk_real_ne_zero : (k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk_pos_nat)
  rw [mul_inv_cancel₀ hk_real_ne_zero, one_mul]

set_option linter.flexible false in
/-- Shannon entropy of the uniform distribution equals
`log (Fintype.card α)`. -/
lemma shannonEntropy_uniformDist (h_card_pos : 0 < Fintype.card α) :
    shannonEntropy (uniformDist h_card_pos) =
      log (Fintype.card α) := by
  let k := Fintype.card α
  have hk_pos_nat : k > 0 := h_card_pos
  simp [shannonEntropy, uniformDist, negMulLog_def,
    NNReal.coe_inv, NNReal.coe_natCast]
  rw [← mul_assoc]
  exact mul_inv_cancel_mul_log hk_pos_nat

/-- Shannon entropy of the canonical uniform distribution on `Fin k`
equals `log k`. -/
lemma shannonEntropy_canonicalUniform (k : ℕ) (hk_pos : k > 0) :
    shannonEntropy (canonicalUniformDist k hk_pos) = log k := by
  simp only [canonicalUniformDist]
  rw [shannonEntropy_uniformDist (Fintype.card_fin_pos hk_pos)]
  rw [Fintype.card_fin k]

end Uniform

/-- The set of valid probability distributions over `Fin n`. -/
def probabilitySimplex {n : ℕ} : Set (Fin n → NNReal) :=
  { p | ∑ i, p i = 1 }

end InformationTheory
