/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Lemmas on infinite sums over the antidiagonal of the divisors function

This file contains lemmas about the antidiagonal of the divisors function. It defines the map from
`Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b` to `(a, b)`.

We then prove some identities about the infinite sums over this antidiagonal, such as
`∑' n : ℕ+, n ^ k * r ^ n / (1 - r ^ n) = ∑' n : ℕ+, σ k n * r ^ n`
which are used for Eisenstein series and their q-expansions. This is also a special case of
Lambert series.

-/

open Filter Complex ArithmeticFunction Nat Topology

/-- The map from `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b`
to `(a, b)`. -/
def divisorsAntidiagonalFactors (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ := fun x ↦
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
given by sending `n = a * b` to `(a, b)`. -/
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormSMulClass ℤ 𝕜]

omit [NormSMulClass ℤ 𝕜] in
lemma summable_norm_pow_mul_geometric_div_one_sub (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun n : ℕ ↦ n ^ k * r ^ n / (1 - r ^ n) := by
  simp only [div_eq_mul_one_div ( _ * _ ^ _)]
  apply Summable.mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using summable_norm_pow_mul_geometric_of_norm_lt_one k hr)
  simpa only [Nat.cofinite_eq_atTop] using
   tendsto_const_nhds.div ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const_sub 1) (by simp)

private lemma summable_divisorsAntidiagonal_aux (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
    (c.2.1.2) ^ k * (r ^ (c.2.1.1 * c.2.1.2)) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a ↦ by positivity)]
  constructor
  · exact fun n ↦ (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    apply Summable.of_nonneg_of_le (f := fun c : ℕ+ ↦ ‖(c : 𝕜) ^ (k + 1) * r ^ (c : ℕ)‖)
      (fun b ↦ Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (by simp) (by simp))) (fun b ↦ ?_)
      (by apply (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) hr).subtype)
    transitivity ∑ _ ∈ (b : ℕ).divisors, ‖(b : 𝕜)‖ ^ k * ‖r ^ (b : ℕ)‖
    · rw [(b : ℕ).divisorsAntidiagonal.sum_attach (fun x ↦ ‖(x.2 : 𝕜)‖ ^ _ * _ ^ (x.1 * x.2)),
          sum_divisorsAntidiagonal ((fun x y ↦ ‖(y : 𝕜)‖ ^ k * _ ^ (x * y)))]
      gcongr with i hi
      · simpa using le_of_dvd b.2 (div_dvd_of_dvd (dvd_of_mem_divisors hi))
      · rw [norm_pow, mul_comm,  Nat.div_mul_cancel (dvd_of_mem_divisors hi)]
    · simp only [norm_pow, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, add_comm k 1, pow_add,
        pow_one, norm_mul]
      gcongr
      simpa using Nat.card_divisors_le_self b

theorem summable_prod_mul_pow (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (ℕ+ × ℕ+) ↦ c.2 ^ k * (r ^ (c.1 * c.2 : ℕ)) := by
  simpa [sigmaAntidiagonalEquivProd.summable_iff.symm] using summable_divisorsAntidiagonal_aux k hr

-- access notation `σ`
open scoped sigma

theorem tsum_prod_pow_eq_tsum_sigma (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' d : ℕ+, ∑' c : ℕ+, c ^ k * r ^ (d * c : ℕ) = ∑' e : ℕ+, σ k e * r ^ (e : ℕ) := by
  suffices ∑' c : ℕ+ × ℕ+, c.2 ^ k * r ^ (c.1 * c.2 : ℕ) =
    ∑' e : ℕ+, σ k e * r ^ (e : ℕ) by rwa [← (summable_prod_mul_pow k hr).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div, cast_sum,
    cast_pow, Summable.tsum_sigma (summable_divisorsAntidiagonal_aux k hr)]
  refine tsum_congr fun n ↦ ?_
  simpa [tsum_fintype, Finset.sum_mul,
    (n : ℕ).divisorsAntidiagonal.sum_attach fun x : ℕ × ℕ ↦ x.2 ^ k * r ^ (x.1 * x.2),
    sum_divisorsAntidiagonal fun x y ↦ y ^ k * r ^ (x * y)]
      using Finset.sum_congr rfl fun i hi ↦ by rw [Nat.mul_div_cancel' (dvd_of_mem_divisors hi)]

lemma tsum_pow_div_one_sub_eq_tsum_sigma {r : 𝕜} (hr : ‖r‖ < 1) (k : ℕ) :
    ∑' n : ℕ+, n ^ k * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) = ∑' n : ℕ+, σ k n * r ^ (n : ℕ) := by
  have (m : ℕ) [NeZero m] := tsum_geometric_of_norm_lt_one (ξ := r ^ m)
    (by simpa using pow_lt_one₀ (by simp) hr (NeZero.ne _))
  simp only [div_eq_mul_inv, ← this, ← tsum_mul_left, mul_assoc, ← _root_.pow_succ',
    ← fun (n : ℕ) ↦ tsum_pnat_eq_tsum_succ (f := fun m ↦ n ^ k * (r ^ n) ^ m)]
  have h00 := tsum_prod_pow_eq_tsum_sigma k hr
  rw [Summable.tsum_comm (by apply (summable_prod_mul_pow k hr).prod_symm)] at h00
  rw [← h00]
  exact tsum_congr₂ <| fun b c ↦ by simp [mul_comm c.val b.val, pow_mul]

end tsum
