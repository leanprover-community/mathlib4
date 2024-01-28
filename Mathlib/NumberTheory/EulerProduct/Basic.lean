/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Euler Products

The main result in this file is `EulerProduct.eulerProduct`, which says that
if `f : ℕ → R` is norm-summable, where `R` is a complete normed commutative ring and `f` is
multiplicative on coprime arguments with `f 0 = 0`, then
`∏ p in primesBelow N, ∑' e : ℕ, f (p^e)` tends to `∑' n, f n` as `N` tends to infinity.
`Nat.ArithmeticFunction.IsMultiplicative.eulerProduct` is a version of
`EulerProduct.eulerProduct` for multiplicative arithmetic functions in the sense of
`Nat.ArithmeticFunction.IsMultiplicative`.

There is also a version `EulerProduct.eulerProduct_completely_multiplicative`, which states that
`∏ p in primesBelow N, (1 - f p)⁻¹` tends to `∑' n, f n` as `N` tends to infinity,
when `f` is completely multiplicative with values in a complete normed field `F`
(implemented as `f : ℕ →*₀ F`).

An intermediate step is `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
(and its variant `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum_geometric`),
which relates the finite product over primes to the sum of `f n` over `N`-smooth `n`.

## Tags

Euler product
-/

/-- If `f` is multiplicative and summable, then its values at natural numbers `> 1`
have norm strictly less than `1`. -/
lemma Summable.norm_lt_one {F : Type*} [NormedField F] [CompleteSpace F] {f : ℕ →* F}
    (hsum : Summable f) {p : ℕ} (hp : 1 < p) :
    ‖f p‖ < 1 := by
  refine summable_geometric_iff_norm_lt_1.mp ?_
  simp_rw [← map_pow]
  exact hsum.comp_injective <| Nat.pow_right_injective hp

open scoped Topology

open Nat BigOperators

namespace EulerProduct

section General

/-!
### General Euler Products

In this section we consider multiplicative (on coprime arguments) functions `f : ℕ → R`,
where `R` is a complete normed commutative ring. The main result is `EulerProduct.eulerProduct`.
-/

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {f : ℕ → R}
variable (hf₁ : f 1 = 1) (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)

/-- We relate a finite product over primes to an infinite sum over smooth numbers. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖f (p ^ n)‖)) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p in N.primesBelow, ∑' (n : ℕ), f (p ^ n)) := by
  induction' N with N ih
  · rw [smoothNumbers_zero, primesBelow_zero, Finset.prod_empty]
    exact ⟨(Set.finite_singleton 1).summable (‖f ·‖), hf₁ ▸ hasSum_singleton 1 f⟩
  · rw [primesBelow_succ]
    split_ifs with hN
    · constructor
      · simp_rw [← (equivProdNatSmoothNumbers hN).summable_iff, Function.comp_def,
                 equivProdNatSmoothNumbers_apply', map_prime_pow_mul hmul hN]
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_mul_le ..) ?_
        apply summable_mul_of_summable_norm (f := fun (x : ℕ) ↦ ‖f (N ^ x)‖)
          (g := fun (x : N.smoothNumbers) ↦ ‖f x.val‖) <;>
          simp_rw [norm_norm]
        exacts [hsum hN, ih.1]
      · simp_rw [Finset.prod_insert (not_mem_primesBelow N),
                 ← (equivProdNatSmoothNumbers hN).hasSum_iff, Function.comp_def,
                 equivProdNatSmoothNumbers_apply', map_prime_pow_mul hmul hN]
        apply (hsum hN).of_norm.hasSum.mul ih.2
        -- `exact summable_mul_of_summable_norm (hsum hN) ih.1` gives a time-out
        convert summable_mul_of_summable_norm (hsum hN) ih.1
    · rwa [smoothNumbers_succ hN]

/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`
in terms of the value of the series. -/
lemma prod_primesBelow_tsum_eq_tsum_smoothNumbers (hsum : Summable (‖f ·‖)) (N : ℕ) :
    ∏ p in N.primesBelow, ∑' (n : ℕ), f (p ^ n) = ∑' m : N.smoothNumbers, f m :=
  (summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
    (fun hp ↦ hsum.comp_injective <| Nat.pow_right_injective hp.one_lt) _).2.tsum_eq.symm

/-- The following statement says that summing over `N`-smooth numbers
for large enough `N` gets us arbitrarily close to the sum over all natural numbers
(assuming `f` is norm-summable and `f 0 = 0`; the latter since `0` is not smooth). -/
lemma norm_tsum_smoothNumbers_sub_tsum_lt (hsum : Summable f) (hf₀ : f 0 = 0)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖(∑' m : ℕ, f m) - (∑' m : N.smoothNumbers, f m)‖ < ε := by
  obtain ⟨N₀, hN₀⟩ :=
    summable_iff_nat_tsum_vanishing.mp hsum (Metric.ball 0 ε) <| Metric.ball_mem_nhds 0 εpos
  simp_rw [mem_ball_zero_iff] at hN₀
  refine ⟨N₀, fun N hN₁ ↦ ?_⟩
  convert hN₀ _ <| N.smoothNumbers_compl.trans fun _ ↦ hN₁.le.trans
  simp_rw [← tsum_subtype_add_tsum_subtype_compl hsum N.smoothNumbers,
    add_sub_cancel', tsum_eq_tsum_diff_singleton (N.smoothNumbers)ᶜ hf₀]

open Filter

/-- The *Euler Product* for multiplicative (on coprime arguments) functions.
If `f : ℕ → R`, where `R` is a complete normed commutative ring, `f 0 = 0`,
`f 1 = 1`, `f` is multiplicative on coprime arguments,
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
theorem eulerProduct (hsum : Summable (‖f ·‖)) (hf₀ : f 0 = 0) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) := by
  rw [Metric.tendsto_nhds]
  intro ε εpos
  simp only [Finset.mem_range, eventually_atTop, ge_iff_le]
  obtain ⟨N₀, hN₀⟩ := norm_tsum_smoothNumbers_sub_tsum_lt hsum.of_norm hf₀ εpos
  use N₀
  convert hN₀ using 3 with m
  rw [dist_eq_norm, norm_sub_rev, prod_primesBelow_tsum_eq_tsum_smoothNumbers hf₁ hmul hsum m]

/-- The *Euler Product* for a multiplicative arithmetic function `f` with values in a
complete normed commutative ring `R`: if `‖f ·‖` is summable, then
`∏' p : {p : ℕ | p.Prime}, ∑' e, f (p ^ e) = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
nonrec theorem _root_.Nat.ArithmeticFunction.IsMultiplicative.eulerProduct
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, ∑' e, f (p ^ e)) atTop (𝓝 (∑' n, f n)) :=
  eulerProduct hf.1 hf.2 hsum f.map_zero

end General

section CompletelyMultiplicative

/-!
### Euler Products for completely multiplicative functions

We now assume that `f` is completely multiplicative and has values in a complete normed field `F`.
Then we can use the formula for geometric series to simplify the statement. This leads to
`EulerProduct.eulerProduct_completely_multiplicative`.
-/

variable {F : Type*} [NormedField F] [CompleteSpace F]

/-- Given a (completely) multiplicative function `f : ℕ → F`, where `F` is a normed field,
such that `‖f p‖ < 1` for all primes `p`, we can express the sum of `f n` over all `N`-smooth
positive integers `n` as a product of `(1 - f p)⁻¹` over the primes `p < N`. At the same time,
we show that the sum involved converges absolutely. -/
lemma summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric {f : ℕ →* F}
    (h : ∀ {p : ℕ}, p.Prime → ‖f p‖ < 1) (N : ℕ) :
    Summable (fun m : N.smoothNumbers ↦ ‖f m‖) ∧
      HasSum (fun m : N.smoothNumbers ↦ f m) (∏ p in N.primesBelow, (1 - f p)⁻¹) := by
  have hmul {m n} (_ : Nat.Coprime m n) := f.map_mul m n
  convert summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum f.map_one hmul ?_ N with M hM <;>
    simp_rw [map_pow]
  · exact (tsum_geometric_of_norm_lt_1 <| h <| prime_of_mem_primesBelow hM).symm
  · intro p hp
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_pow_le ..) ?_
    exact summable_geometric_iff_norm_lt_1.mpr <| (norm_norm (f p)).symm ▸ h hp

/-- A version of `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`
in terms of the value of the series. -/
lemma prod_primesBelow_geometric_eq_tsum_smoothNumbers {f : ℕ →* F} (hsum : Summable f) (N : ℕ) :
    ∏ p in N.primesBelow, (1 - f p)⁻¹ = ∑' m : N.smoothNumbers, f m := by
  refine (summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric ?_ N).2.tsum_eq.symm
  exact fun {_} hp ↦ hsum.norm_lt_one hp.one_lt

open Filter in
/-- The *Euler Product* for completely multiplicative functions.
If `f : ℕ →*₀ F`, where `F` is a complete normed field
and `‖f ·‖` is summable, then `∏' p : {p : ℕ | p.Prime}, (1 - f p)⁻¹ = ∑' n, f n`.
Since there are no infinite products yet in Mathlib, we state it in the form of
convergence of finite partial products. -/
-- TODO: Change to use `∏'` once infinite products are in Mathlib
theorem eulerProduct_completely_multiplicative {f : ℕ →*₀ F} (hsum : Summable fun x => ‖f x‖) :
    Tendsto (fun n : ℕ ↦ ∏ p in primesBelow n, (1 - f p)⁻¹) atTop (𝓝 (∑' n, f n)) := by
  convert eulerProduct f.map_one (fun {m n} _ ↦ f.map_mul m n) hsum f.map_zero with N p hN
  simp_rw [map_pow]
  refine (tsum_geometric_of_norm_lt_1 <| summable_geometric_iff_norm_lt_1.mp ?_).symm
  refine Summable.of_norm ?_
  convert hsum.comp_injective <| Nat.pow_right_injective (prime_of_mem_primesBelow hN).one_lt
  simp only [norm_pow, Function.comp_apply, map_pow]

end CompletelyMultiplicative

end EulerProduct
