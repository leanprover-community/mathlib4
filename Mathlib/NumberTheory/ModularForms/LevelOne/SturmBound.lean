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

variable {k : ℤ} (f : ModularForm 𝒮ℒ k)

/-- **Sturm bound for level-1 modular forms.** If a modular form `f` of weight `k` for `SL(2, ℤ)`
has zero coefficient on `q^i` in its q-expansion for every `i ≥ 0` with `12 * i ≤ k`, then
`f` is identically zero. -/
theorem sturm_bound_levelOne
    (h : ∀ i : ℕ, 12 * (i : ℤ) ≤ k → (qExpansion 1 f).coeff i = 0) : f = 0 := by
  suffices key : ∀ (n : ℕ) ⦃k : ℤ⦄ (f : ModularForm 𝒮ℒ k), k < 12 * n →
      (∀ i < n, (qExpansion 1 f).coeff i = 0) → f = 0 by
    by_cases hk_neg : k < 0
    · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk_neg) f
    push Not at hk_neg
    exact key (k.toNat / 12 + 1) f (by omega) fun i hi ↦ h i (by omega)
  intro n
  induction n with
  | zero => intro k f hk _; push_cast at hk
            exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by omega)) f
  | succ n ih =>
    intro k f hk hcoeff
    have h0 : (qExpansion 1 f).coeff 0 = 0 := hcoeff 0 (Nat.zero_lt_succ n)
    set g := CuspForm.discriminantEquiv (toCuspForm f h0) with hg_def
    have hg_order : ↑(n : ℕ) ≤ (qExpansion 1 g).order := by
      refine (ENat.add_le_add_iff_left ENat.one_ne_top (k := 1)).mp ?_
      rw [show (1 : ℕ∞) + ↑n = ((n + 1 : ℕ) : ℕ∞) by push_cast; ring,
        ← discriminant_qExpansion_order, ← PowerSeries.order_mul,
        ← qExpansion_eq_qExpansion_discriminant_mul f h0]
      exact PowerSeries.nat_le_order _ _ hcoeff
    have hg_zero : g = 0 := ih g (by push_cast at hk; linarith) fun i hi ↦
      PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hi) hg_order)
    have hf' : toCuspForm f h0 = 0 :=
      CuspForm.discriminantEquiv.injective (by simpa [← hg_def] using hg_zero)
    ext z
    simpa [toCuspForm_apply] using DFunLike.congr_fun hf' z

end ModularForm

end
