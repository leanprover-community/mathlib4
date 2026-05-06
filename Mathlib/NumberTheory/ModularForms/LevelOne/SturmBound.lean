/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The Sturm bound for level-1 modular forms

This file proves the *Sturm bound* for level-1 modular forms: a modular form of weight `k` for
`SL(2, ℤ)` whose first `⌊k/12⌋ + 1` q-expansion coefficients all vanish must be identically zero.

The proof iterates the isomorphism
`CuspForm.discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`
(division by the modular discriminant `Δ`): a sufficiently-vanishing form is divisible by a power
of `Δ`, landing eventually in negative weight where everything is zero.

## Main results

* `ModularForm.sturm_bound_levelOne`: the Sturm bound stated in the standard form: if every
  coefficient of `q^i` in `qExpansion 1 f` with `12 * i ≤ k` is zero, then `f = 0`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm CuspForm MatrixGroups

namespace ModularForm

private lemma qExpansion_eq_qExpansion_discriminant_mul {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (hcusp : (qExpansion 1 f).coeff 0 = 0) :
    qExpansion 1 f = qExpansion 1 ModularForm.discriminant *
      qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp)) := by
  set g := CuspForm.discriminantEquiv (toCuspForm f hcusp) with hg_def
  have hsymm : CuspForm.discriminantEquiv.symm g = toCuspForm f hcusp := by simp [hg_def]
  have hfun : (f : ℍ → ℂ) = ModularForm.discriminant * (g : ℍ → ℂ) := by
    funext z
    have h1 := CuspForm.ofMulDiscriminant_apply g z
    rw [show CuspForm.ofMulDiscriminant g = toCuspForm f hcusp from hsymm,
      toCuspForm_apply] at h1
    exact h1
  rw [hfun]
  exact UpperHalfPlane.qExpansion_mul
    (CuspForm.coe_discriminant ▸ ModularFormClass.analyticAt_cuspFunction_zero
      (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL)
    (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods_SL)

private lemma orderOf_qExpansion_discriminant :
    (qExpansion 1 ModularForm.discriminant).order = 1 := by
  refine PowerSeries.order_eq_nat.mpr ⟨?_, ?_⟩
  · rw [ModularForm.discriminant_qExpansion_coeff_one]
    exact one_ne_zero
  · intro i hi
    obtain rfl : i = 0 := by omega
    have h0 := (isCuspForm_iff_coeffZero_eq_zero
      ((CuspForm.discriminant : ModularForm 𝒮ℒ 12))).mp ⟨CuspForm.discriminant, rfl⟩
    rwa [show ((CuspForm.discriminant : ModularForm 𝒮ℒ 12) : ℍ → ℂ) =
      ModularForm.discriminant from CuspForm.coe_discriminant] at h0

private lemma eq_zero_of_qExpansion_coeff_zero_lt :
    ∀ (n : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k),
    k < 12 * n → (∀ i < n, (qExpansion 1 f).coeff i = 0) → f = 0 := by
  intro n
  induction n with
  | zero =>
    intro k f hk _
    push_cast at hk
    exact rank_zero_iff_forall_zero.mp
      (ModularForm.levelOne_neg_weight_rank_zero (by omega)) f
  | succ n ih =>
    intro k f hk hcoeff
    have h0 : (qExpansion 1 f).coeff 0 = 0 := hcoeff 0 (Nat.zero_lt_succ n)
    set g := CuspForm.discriminantEquiv (toCuspForm f h0) with hg_def
    have hg_order : ↑(n : ℕ) ≤ (qExpansion 1 g).order := by
      have hmul : (qExpansion 1 f).order = 1 + (qExpansion 1 g).order := by
        rw [qExpansion_eq_qExpansion_discriminant_mul f h0, PowerSeries.order_mul,
          orderOf_qExpansion_discriminant]
      have hf_order : (1 : ℕ∞) + ↑n ≤ 1 + (qExpansion 1 g).order := by
        have heq : ((n + 1 : ℕ) : ℕ∞) = 1 + ↑n := by push_cast; ring
        rw [← heq, ← hmul]
        exact PowerSeries.nat_le_order _ _ hcoeff
      exact (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp hf_order
    have hg_zero : g = 0 := ih g (by push_cast at hk; linarith) fun i hi =>
      PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hi) hg_order)
    have hf' : toCuspForm f h0 = 0 :=
      CuspForm.discriminantEquiv.injective (by simpa [← hg_def] using hg_zero)
    ext z
    simpa [toCuspForm_apply] using DFunLike.congr_fun hf' z

/-- **Sturm bound for level-1 modular forms.** If a modular form `f` of weight `k` for `SL(2, ℤ)`
has zero coefficient on `q^i` in its q-expansion for every `i ≥ 0` with `12 * i ≤ k`, then
`f` is identically zero. -/
theorem sturm_bound_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (h : ∀ i : ℕ, 12 * (i : ℤ) ≤ k → (qExpansion 1 f).coeff i = 0) : f = 0 := by
  by_cases hk_neg : k < 0
  · exact rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk_neg) f
  push Not at hk_neg
  refine eq_zero_of_qExpansion_coeff_zero_lt (k.toNat / 12 + 1) f ?_ fun i hi => h i ?_
  · omega
  · omega

end ModularForm

end
