/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function, defined as a Dirichlet series. It is not
  continued beyond the half-plane of convergence `1 < re s`.
* `NumberField.dedekindZetaResidue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.LSeriesSummable_dedekindZeta_iff`: the Dirichlet series of the Dedekind zeta
  function converges absolutely if and only if `1 < re s`.
* `NumberField.hasSum_dedekindZeta_of_one_lt_re`: for `1 < re s`, the Dedekind zeta function at `s`
  is the sum of `N(I) ^ (-s)` over the integral ideals `I`.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units nonZeroDivisors

open scoped Topology

namespace NumberField

open scoped Real

/--
The Dedekind zeta function of a number field, defined as the Dirichlet series whose `n`-th
coefficient is the number of integral ideals of norm `n`. Its half-plane of convergence is
`1 < re s`.

This is not the meromorphic continuation of the Dedekind zeta function: for `re s ≤ 1`,
`dedekindZeta K s` is `0`, the junk value of `LSeries`. For example, `dedekindZeta ℚ 0 = 0`,
whereas `riemannZeta 0 = -1 / 2`.
-/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/--
The value of the residue at `s = 1` of the Dedekind zeta function, see
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
-/
def dedekindZetaResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

@[deprecated (since := "2026-11-11")] alias dedekindZeta_residue := dedekindZetaResidue

theorem dedekindZetaResidue_def :
    dedekindZetaResidue K =
      (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|) := rfl

@[deprecated (since := "2026-11-11")] alias dedekindZeta_residue_def := dedekindZetaResidue_def

theorem dedekindZetaResidue_pos : 0 < dedekindZetaResidue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K)) <|
      Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

@[deprecated (since := "2026-11-11")] alias dedekindZeta_residue_pos := dedekindZetaResidue_pos

theorem dedekindZetaResidue_ne_zero : dedekindZetaResidue K ≠ 0 :=
  (dedekindZetaResidue_pos K).ne'

@[deprecated (since := "2026-11-11")]
alias dedekindZeta_residue_ne_zero := dedekindZetaResidue_ne_zero

-- The partial sums of the coefficients of the Dirichlet series of `dedekindZeta K` grow like
-- `dedekindZetaResidue K * n`.
private theorem tendsto_sum_card_absNorm_eq_div_atTop :
    Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / n) atTop
        (𝓝 (dedekindZetaResidue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/--
**Dirichlet class number formula**
-/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZetaResidue K)) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _
    (tendsto_sum_card_absNorm_eq_div_atTop K) fun _ ↦ Nat.cast_nonneg _

/-- The Dirichlet series of the Dedekind zeta function converges absolutely at `s` if and only if
`1 < re s`. -/
theorem LSeriesSummable_dedekindZeta_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s ↔ 1 < s.re := by
  refine ⟨fun h ↦ ?_, fun hs ↦ ?_⟩
  · -- If the series converged at some `s` with `re s ≤ 1`, it would converge at `1`, so
    -- `dedekindZeta K σ` would stay bounded as `σ → 1⁺`, contradicting the class number formula.
    by_contra! hs
    replace h := h.of_re_le_re (s' := 1) (by simpa using hs)
    obtain ⟨M, hM⟩ : ∃ M, ∀ σ : ℝ, 1 < σ → ‖dedekindZeta K σ‖ ≤ M :=
      ⟨_, fun σ hσ ↦
        have hσ' := h.of_re_le_re (s' := σ) (by simpa using hσ.le)
        (norm_tsum_le_tsum_norm hσ'.norm).trans <|
          hσ'.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re _ (by simpa using hσ.le))
            h.norm⟩
    have h₀ : Tendsto (fun σ : ℝ ↦ (σ - 1) * dedekindZeta K σ) (𝓝[>] 1) (𝓝 0) := by
      refine Tendsto.zero_mul_isBoundedUnder_le ?_
        (isBoundedUnder_of_eventually_le (eventually_nhdsWithin_of_forall hM))
      exact (Continuous.tendsto' (by fun_prop) _ _ (by simp)).mono_left nhdsWithin_le_nhds
    exact dedekindZetaResidue_ne_zero K <| by
      exact_mod_cast tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) h₀
  · exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
        (by simpa using tendsto_sum_card_absNorm_eq_div_atTop K))
      (fun _ ↦ Nat.cast_nonneg _) zero_le_one hs

/-- For `1 < re s`, `dedekindZeta K s` is the sum of `N(I) ^ (-s)` over the integral ideals `I`
of `K` (the zero ideal contributes `0`). -/
theorem hasSum_dedekindZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℂ) ^ (-s)) (dedekindZeta K s) := by
  have hs₀ : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_one_lt_re hs)
  have hsum := (LSeriesSummable_dedekindZeta_iff K).mpr hs
  have (n : ℕ) : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).fintype
  -- Group the ideals by their norm: those of norm `n` contribute the `n`-th term of the series.
  have hterm (n : ℕ) : LSeries.term (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s n =
      ∑ _ : {I : Ideal (𝓞 K) // absNorm I = n}, (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Complex.zero_cpow hs₀]
    · simp [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv, Nat.card_eq_fintype_card]
  let e := Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ)
  rw [← e.hasSum_iff, show (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℂ) ^ (-s)) ∘ e =
    fun x ↦ (x.1 : ℂ) ^ (-s) from funext fun x ↦ by simp [e, x.2.2]]
  refine HasSum.sigma_of_hasSum hsum.LSeriesHasSum (fun n ↦ ?_) (.of_norm ?_)
  · rw [hterm]
    exact hasSum_fintype _
  · rw [summable_sigma_of_nonneg fun _ ↦ norm_nonneg _]
    refine ⟨fun _ ↦ .of_finite, hsum.norm.congr fun n ↦ ?_⟩
    rw [hterm]
    simp

end NumberField
