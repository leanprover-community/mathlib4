/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

This will be done in the following steps:

1. Some auxiliary lemmas on infinite products and sums
2. Results on the von Mangoldt function restricted to a residue class
3. (TODO) Results on its L-series and an auxiliary function related to it
4. (TODO) Derivation of Dirichlet's Theorem
-/

/-!
### Auxiliary statements

An infinite product or sum over a function supported in prime powers can be written
as an iterated product or sum over primes and natural numbers.
-/

section auxiliary

variable {α β γ : Type*} [CommGroup α] [UniformSpace α] [UniformGroup α] [CompleteSpace α]
  [T0Space α]

open Nat.Primes in
@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1)) := by
  have hfm' : Multipliable fun pk : Nat.Primes × ℕ ↦ f (pk.fst ^ (pk.snd + 1)) :=
    prodNatEquiv.symm.multipliable_iff.mp <| by
      simpa only [← coe_prodNatEquiv_apply, Prod.eta, Function.comp_def, Equiv.apply_symm_apply]
        using hfm.subtype _
  simp only [← tprod_subtype_eq_of_mulSupport_subset hf, Set.coe_setOf, ← prodNatEquiv.tprod_eq,
    ← tprod_prod hfm']
  refine tprod_congr fun (p, k) ↦ congrArg f <| coe_prodNatEquiv_apply ..

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = (∏' p : Nat.Primes, f p) *  ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k : ℕ ↦ f (p ^ (k + 1)) :=
    hfm.comp_injective <| (strictMono_nat_of_lt_succ
      fun k ↦ pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one (k + 1)).injective
  conv_lhs =>
    enter [1, p]; rw [tprod_eq_zero_mul (hfs' p), zero_add, pow_one]
    enter [2, 1, k]; rw [add_assoc, one_add_one_eq_two]
  exact tprod_mul (Multipliable.subtype hfm _) <|
    Multipliable.prod (f := fun (pk : Nat.Primes × ℕ) ↦ f (pk.1 ^ (pk.2 + 2))) <|
    hfm.comp_injective <| Subtype.val_injective |>.comp
    Nat.Primes.prodNatEquiv.injective |>.comp <|
    Function.Injective.prodMap (fun ⦃_ _⦄ a ↦ a) <| add_left_injective 1

end auxiliary

/-!
### The L-series of the von Mangoldt function restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction.vonMangoldt

open Complex LSeries DirichletCharacter

open scoped LSeries.notation

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residueClass_nonneg : 0 ≤ residueClass a :=
  fun _ ↦ Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg

lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_zero, map_zero, ofReal_zero,
    implies_true]

lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  unfold LSeriesSummable
  have := LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert this.indicator {n : ℕ | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +contextual only [term, Set.indicator, Set.mem_setOf_eq, hn, ↓reduceIte, apply_ite,
      ite_self]
  · simp +contextual only [term, Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_not_mem,
      ofReal_zero, zero_div, ite_self]

variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_setOf_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is a linear combination of logarithmic derivatives of L-functions of the Dirichlet characters
mod `q` (on `re s > 1`). -/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
    ← LSeries_sum <| fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr s fun {n} _ ↦ ?_
  simp only [Pi.smul_apply, residueClass_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

end ArithmeticFunction.vonMangoldt

end arith_prog
