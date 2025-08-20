/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular


/-!
# Lemmas on infinite sums over the antidiagonal of the divisors function

This file contains lemmas about the antidiagonal of the divisors function. It defines the map from
`Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b` to `(a, b)`.

-/

/-- The map from `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b`
to `(a , b)`. -/
def divisorsAntidiagonalFactors (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ :=
    fun x ↦
   ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : ℕ+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩

lemma divisorsAntidiagonalFactors_eq {n : ℕ+} (x : Nat.divisorsAntidiagonal n) :
    (divisorsAntidiagonalFactors n x).1.1 * (divisorsAntidiagonalFactors n x).2.1 = n := by
  simp [divisorsAntidiagonalFactors, (Nat.mem_divisorsAntidiagonal.mp x.2).1]

lemma divisorsAntidiagonalFactors_one (x : Nat.divisorsAntidiagonal 1) :
    (divisorsAntidiagonalFactors 1 x) = (1, 1) := by
  have h := Nat.mem_divisorsAntidiagonal.mp x.2
  simp only [mul_eq_one, ne_eq, one_ne_zero, not_false_eq_true, and_true] at h
  simp [divisorsAntidiagonalFactors, h.1, h.2]

/-- The equivalence from the union over `n` of `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+`
given by sending `n = a * b` to `(a , b)`. -/
def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+ where
  toFun x := divisorsAntidiagonalFactors x.1 x.2
  invFun x :=
    ⟨⟨x.1.val * x.2.val, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by simp [Nat.mem_divisorsAntidiagonal]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    ext <;> simp [divisorsAntidiagonalFactors, ← PNat.coe_injective.eq_iff, h.1]
  right_inv _ := rfl

lemma sigmaAntidiagonalEquivProd_symm_apply_fst (x : ℕ+ × ℕ+) :
    (sigmaAntidiagonalEquivProd.symm x).1 = x.1.1 * x.2.1 := rfl

lemma sigmaAntidiagonalEquivProd_symm_apply_snd (x : ℕ+ × ℕ+) :
    (sigmaAntidiagonalEquivProd.symm x).2 = (x.1.1, x.2.1) := rfl

section tsum

open Filter Complex ArithmeticFunction Nat Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

lemma natCast_norm [NormSMulClass ℤ 𝕜]
    (a : ℕ) : ‖(a : 𝕜)‖ = a := by
  have h0 := norm_natCast_eq_mul_norm_one 𝕜 a
  simpa using h0

lemma summable_norm_pow_mul_geometric_div_one_sub [CompleteSpace 𝕜] (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun n : ℕ ↦ n ^ k * r ^ n / (1 - r ^ n) := by
  rw [show (fun n : ℕ ↦ n ^ k * r ^ n / (1 - r ^ n)) =
    fun n : ℕ ↦ (n ^ k * r ^ n) * (1 / (1 - r ^ n)) by grind]
  apply summable_mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using (summable_norm_pow_mul_geometric_of_norm_lt_one k hr))
  rw [Nat.cofinite_eq_atTop]
  have : Tendsto (fun n : ℕ ↦ 1 - r ^ n) atTop (𝓝 (1 - 0)) :=
    Filter.Tendsto.sub (by simp) (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr)
  have h1 : Tendsto (fun n : ℕ ↦ (1 : 𝕜)) atTop (𝓝 1) := by simp only [tendsto_const_nhds_iff]
  apply (Filter.Tendsto.div h1 this (by simp)).congr
  simp

variable [CompleteSpace 𝕜] [NormSMulClass ℤ 𝕜]

theorem summable_divisorsAntidiagonal_aux (k : ℕ) (r : 𝕜) (hr : ‖r‖ < 1) :
    Summable fun c : (n : ℕ+) × { x // x ∈ (n : ℕ).divisorsAntidiagonal } ↦
    (c.2.1).1 ^ k * (r ^ (c.2.1.2 * c.2.1.1)) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg]
  constructor
  · apply fun n => (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    · apply Summable.of_nonneg_of_le (f := fun c : ℕ+ ↦ ‖(c : 𝕜) ^ (k + 1) * r ^ (c : ℕ)‖)
        (fun b => Finset.sum_nonneg (fun _ _ => by apply mul_nonneg (by simp) (by simp))) ?_
        (by apply (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) hr).subtype)
      intro b
      apply le_trans (b := ∑ _ ∈ (b : ℕ).divisors, ‖(b : 𝕜)‖ ^ k * ‖r ^ (b : ℕ)‖)
      · rw [Finset.sum_attach ((b : ℕ).divisorsAntidiagonal) (fun x ↦
            ‖(x.1 : 𝕜)‖ ^ (k : ℕ) * ‖r‖^ (x.2 * x.1)), Nat.sum_divisorsAntidiagonal
            ((fun x y ↦ ‖(x : 𝕜)‖ ^ k * ‖r‖ ^ (y * x))) (n := b)]
        gcongr <;> rename_i i hi <;> simp [natCast_norm] at *
        · exact Nat.le_of_dvd b.2 hi
        · apply le_of_eq
          nth_rw 2 [← Nat.mul_div_cancel' hi]
          ring_nf
      · simp only [norm_pow, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, add_comm k 1, pow_add,
          pow_one, norm_mul]
        gcongr
        simpa [natCast_norm] using (Nat.card_divisors_le_self b)
  · intro a
    simpa using mul_nonneg (by simp) (by simp)

theorem summable_prod_mul_pow (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (ℕ+ × ℕ+) ↦ (c.1 : 𝕜) ^ k * (r ^ (c.2 * c.1 : ℕ)) :=by
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk]
  apply summable_divisorsAntidiagonal_aux k r hr

theorem tsum_prod_pow_eq_tsum_sigma (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' d : ℕ+, ∑' (c : ℕ+), (c ^ k : 𝕜) * (r ^ (d * c : ℕ)) = ∑' e : ℕ+, σ k e * r ^ (e : ℕ) := by
  suffices  ∑' (c : ℕ+ × ℕ+), (c.1 ^ k : 𝕜) * (r ^ ((c.2 : ℕ) * (c.1 : ℕ))) =
    ∑' e : ℕ+, σ k e * r ^ (e : ℕ) by
    rw [Summable.tsum_prod (by apply summable_prod_mul_pow  k hr), Summable.tsum_comm] at this
    · simpa using this
    · apply (summable_prod_mul_pow  k hr).prod_symm.congr
      simp
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div', cast_sum,
    cast_pow]
  rw [Summable.tsum_sigma (summable_divisorsAntidiagonal_aux k r hr)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Finset.univ_eq_attach, Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
    (fun (x : ℕ × ℕ) ↦ (x.1 : 𝕜) ^ k * r ^ (x.2 * x.1)),
    Nat.sum_divisorsAntidiagonal' (fun x y ↦ (x : 𝕜) ^ k * r ^ (y * x)),
    Finset.sum_mul]
  refine Finset.sum_congr (rfl) fun i hi ↦ ?_
  have hni : (n / i : ℕ) * (i : ℕ) = n := by
    simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at *
    have :=  Nat.div_mul_cancel hi
    nth_rw 2 [← this]
  simp
  left
  norm_cast at *
  nth_rw 2 [← hni]
  ring

lemma tsum_eq_tsum_sigma {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ+, n * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) = ∑' n : ℕ+, σ 1 n * r ^ (n : ℕ) := by
  have := fun m : ℕ+ => tsum_choose_mul_geometric_of_norm_lt_one
    (r := r ^ (m : ℕ)) 0 (by simpa using (pow_lt_one₀ (by simp) hr (by apply PNat.ne_zero)))
  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, pow_one,
    one_div] at this
  conv =>
    enter [1,1]
    ext n
    rw [div_eq_mul_one_div]
    simp only [one_div, ← this n, ← tsum_mul_left]
    conv =>
      enter [1]
      ext m
      rw [mul_assoc, ← pow_succ' (r ^ (n : ℕ)) m]
    rw [← tsum_pnat_eq_tsum_succ (fun m =>  n * (r ^ (n : ℕ)) ^ (m : ℕ))]
  have h00 := (tsum_prod_pow_eq_tsum_sigma 1 hr)
  rw [Summable.tsum_comm (by apply summable_prod_mul_pow 1 hr)] at h00
  rw [← h00]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro c
  simp only [← pow_mul, pow_one, mul_eq_mul_left_iff]
  left
  ring

end tsum
