/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Probability.IdentDistrib

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality.

The Marcinkiewicz-Zygmund inequality states that, if `X₁, ... Xₐ ∈ L^p` are independent random
variables of mean zero valued in some inner product space, then the `L^p`-norm of `X₁ + ... + Xₐ` is
at most `Cₚ` times the `L^(p/2)`-norm of `|X₁|² + ... + |Xₐ|²`, where `Cₚ` is a constant depending
on `p` alone.

## Notation

Throughout this file, `A ^^ n` denotes `A × ... × A` (with `n` factors). Formally, this is
`Fintype.piFinset fun _ : Fin n ↦ A`.

## TODO

We currently only prove the inequality for `p = 2 * m` an even natural number. The general `p` case
can be obtained from this specific one by nesting of Lp norms.
-/

public section

open Finset Fintype Function Nat MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

variable {ι Ω E : Type*} {A : Finset ι} {m n : ℕ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [mE : MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : ι → Ω → E}

local notation:70 A:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ A

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for symmetric random variables.
-/
noncomputable def marcinkiewiczZygmundSymmConst (p : ℝ≥0) : ℝ := (p / 2) ^ (p / 2 : ℝ)

/-- The **Marcinkiewicz-Zygmund inequality** for symmetric random variables, with a slightly better
constant than `marcinkiewicz_zygmund`. -/
theorem marcinkiewicz_zygmund_symmetric (iIndepFun_X : iIndepFun X μ)
    (identDistrib_neg_X : ∀ i, IdentDistrib (X i) (-X i) μ μ)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  have : DecidableEq ι := Classical.decEq _
  -- Turn the `L^p` assumption on the `X i` into various integrability conditions.
  have integrable_prod_norm_X I (hI : I ∈ A ×ˢ A ^^ m) :
      Integrable (fun ω ↦ ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖) μ := by
    obtain rfl | hm := eq_or_ne m 0
    · simp
    simp_rw [Finset.prod_mul_distrib]
    rw [← memLp_one_iff_integrable]
    have aux : (∑ _k : Fin m, (2 * (m : ℝ≥0∞))⁻¹)⁻¹ = 2 := by
      rw [ENNReal.mul_inv (a := 2) (.inl <| by norm_num) (.inl <| by norm_num)]
      simp [hm, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel]
    refine .mul' (p := 2) (q := 2) ?_ ?_ <;>
    · rw [← aux]
      exact .prod' fun k _ ↦ (memLp_X _ <| by simp_all).norm
  have integrable_prod_inner_X I (hI : I ∈ A ×ˢ A ^^ m) :
    Integrable (fun ω ↦ ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)) μ := sorry
  -- Call a family of indices `i₁, ..., iₙ, j₁, ..., jₙ` *even* if each `i ∈ A` appears an even
  -- number of times among the `2n` indices.
  let EvenIndex (I : Fin m → ι × ι) : Prop :=
    ∀ i ∈ A, Even (#{k | (I k).1 = i} + #{k | (I k).2 = i})
  -- Now, let the calculation begin...
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ
    -- Expand out the power of the sum into a sum over families of indices
    -- `i₁, ..., iₙ, j₁, ..., jₙ` of `∏ k, ⟨X iₖ, X jₖ⟩`. Push the integral inside the sum.
    _ = ∑ I ∈ A ×ˢ A ^^ m, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
      simp_rw [pow_mul, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum, ← sum_product',
        Finset.sum_pow', integral_finsetSum _ integrable_prod_inner_X]
    -- Show that the terms coming from odd families of indices `i₁, ..., iₙ, j₁, ..., jₙ` integrate
    -- to zero.
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
      rw [Finset.sum_filter_of_ne]
      -- Assume that `I = (i₁, ..., iₙ, j₁, ..., jₙ)` is an odd family.
      -- Say `i` appears an odd number of times in it.
      rintro I hI hI' i hi
      contrapose! hI'
      replace hI' : Odd (#{k | (I k).1 = i} + #{k | (I k).2 = i}) := by simpa using hI'
      -- Let `Y` be the family of random variables `X` where `X i` has been replaced by `-X i`.
      let Y : ι → Ω → E := update X i (-X i)
      -- By the assumption that `X i` is symmetric, we get that `X j` and `Y j` are identically
      -- distributed for all `j`.
      have identDistrib_X_Y j : IdentDistrib (X j) (Y j) μ μ := by
        obtain rfl | hji := eq_or_ne j i
        · simpa [Y] using identDistrib_neg_X _
        · simpa [Y, hji] using .refl (identDistrib_neg_X _).aemeasurable_fst
      -- To show that `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 0`, we will show
      -- `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩ = -𝔼 ∏ k, ⟨X iₖ, X jₖ⟩`.
      rw [← neg_eq_self, ← integral_neg, eq_comm]
      calc
        -- `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩ = 𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩` because `𝔼 ∏ k, ⟨X iₖ, X jₖ⟩` and
        -- `∏ k, ⟨Y iₖ, Y jₖ⟩` are identically distributed.
        ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ
        _ = ∫ ω, ∏ k, inner ℝ (Y (I k).1 ω) (Y (I k).2 ω) ∂μ := by
          refine IdentDistrib.integral_eq ?_
          sorry -- TODO: Upstream result from PFR
        -- `𝔼 ∏ k, ⟨Y iₖ, Y jₖ⟩ = -𝔼 ∏ k, ⟨X iₖ, X jₖ⟩` by the assumption that `i` appears an odd
        -- number of times in `I`.
        _ = ∫ ω, -∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ := by
          congr with ω
          calc
            ∏ k, inner ℝ (Y (I k).1 ω) (Y (I k).2 ω)
            _ = ∏ k, (if (I k).1 = i then -1 else 1) * (if (I k).2 = i then -1 else 1) *
                inner ℝ (X (I k).1 ω) (X (I k).2 ω) := by
              congr! with k; split_ifs with hk₁ hk₂ hk₂ <;> simp [hk₁, hk₂, Y]
            _ = -∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) := by
              rw [prod_mul_distrib, prod_mul_distrib]
              simp [prod_ite, ← pow_add, hI']
    -- Upper bound the sum by its absolute value and push the absolute value inside.
    _ ≤ |∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ| :=
      le_abs_self _
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, |∫ ω, ∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω) ∂μ| :=
      abs_sum_le_sum_abs ..
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, |∏ k, inner ℝ (X (I k).1 ω) (X (I k).2 ω)| ∂μ := by
      gcongr with I; exact abs_integral_le_integral_abs
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, |inner ℝ (X (I k).1 ω) (X (I k).2 ω)| ∂μ := by
      simp_rw [abs_prod]
    -- Finish pushing the absolute value inside using Cauchy-Schwarz.
    _ ≤ ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I, ∫ ω, ∏ k, ‖X (I k).1 ω‖ * ‖X (I k).2 ω‖ ∂μ := by
      gcongr with I hI
      · simpa [abs_prod] using (integrable_prod_inner_X I <| filter_subset _ _ hI).abs
      · exact integrable_prod_norm_X I <| filter_subset _ _ hI
      rintro ω
      dsimp
      gcongr with k
      exact abs_real_inner_le_norm ..
    -- Rewrite the sum of `𝔼 ∏ k, ‖X iₖ ω‖ * ‖X jₖ ω‖` over even families of indices
    -- `i₁, ..., iₙ, j₁, ..., jₙ` into the sum over `w₁ + ... + wₐ = m` of
    -- `(2m choose 2w₁, ..., 2wₐ) * 𝔼 ∏ i, ‖X i‖ ^ wᵢ`.
    _ = ∑ I ∈ A ×ˢ A ^^ m with EvenIndex I,
          ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (#{k | (I k).1 = i} + #{k | (I k).2 = i}) ∂μ := by
      congr! with I hI ω
      simp only [mem_filter, mem_piFinset, mem_product, forall_and] at hI
      simp_rw [pow_add, prod_mul_distrib, ← prod_const]
      rw [prod_fiberwise_of_maps_to', prod_fiberwise_of_maps_to']
      · simpa using hI.1.2
      · simpa using hI.1.1
    _ = ∑ w ∈ piAntidiag A (2 * m) with ∀ i ∈ A, 2 ∣ w i,
          multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
      sorry
    _ = ∑ w ∈ (piAntidiag A m).map
          ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
        multinomial A w * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ w i ∂μ := by
      rw [map_nsmul_piAntidiag _ _ two_ne_zero]
    _ = ∑ w ∈ piAntidiag A m, multinomial A (2 • w) * ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ := by
      simp
    -- Use the fact that `(2m choose 2w₁, ..., 2wₐ) ≤ m ^ m * (m choose w₁, ..., wₐ)`.
    _ ≤ ∑ w ∈ piAntidiag A m, marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w *
          ∫ ω, ∏ i ∈ A, ‖X i ω‖ ^ (2 * w i) ∂μ := by
      gcongr with w hw
      calc
        (multinomial A (2 • w) : ℝ)
        _ ≤ ((∑ i ∈ A, w i) ^ ∑ i ∈ A, w i) * multinomial A w :=
          mod_cast multinomial_two_mul_le_mul_multinomial
        _ = marcinkiewiczZygmundSymmConst (2 * m) * multinomial A w := by
          simp [(mem_piAntidiag.1 hw).1, marcinkiewiczZygmundSymmConst]
    -- Put the sum back together.
    _ = marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
      simp_rw [sum_pow_eq_sum_piAntidiag, ← pow_mul, ← integral_const_mul, mul_sum, ← mul_assoc]
      rw [integral_finsetSum]
      rintro w hw
      exact .const_mul sorry _

/-- The constant appearing in the Marcinkiewicz-Zygmund inequality for random variables with zero
mean. -/
noncomputable def marcinkiewiczZygmundConst (p : ℝ≥0) : ℝ :=
  2 ^ (p / 2 : ℝ) * marcinkiewiczZygmundSymmConst p

/-- The **Marcinkiewicz-Zygmund inequality** for random variables with zero mean.

For symmetric random variables, `marcinkiewicz_zygmund` provides a slightly better constant. -/
theorem marcinkiewicz_zygmund (iIndepFun_X : iIndepFun X μ)
    (integral_X : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (memLp_X : ∀ i ∈ A, MemLp (X i) (2 * m) μ) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      marcinkiewiczZygmundConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := by
  let X₁ i : Ω × Ω → E := X i ∘ Prod.fst
  let X₂ i : Ω × Ω → E := X i ∘ Prod.snd
  let X' i : Ω × Ω → E := X₁ i - X₂ i
  have : DecidableEq ι := Classical.decEq _
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ
    _ ≤ ∫ ω, ‖∑ i ∈ A, X' i ω‖ ^ (2 * m) ∂μ.prod μ := by
      sorry
    _ ≤ marcinkiewiczZygmundSymmConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X' i ω‖ ^ 2) ^ m ∂μ.prod μ :=
      marcinkiewicz_zygmund_symmetric sorry (fun i ↦ sorry) sorry
    _ ≤ marcinkiewiczZygmundConst (2 * m) * ∫ ω, (∑ i ∈ A, ‖X i ω‖ ^ 2) ^ m ∂μ := sorry
