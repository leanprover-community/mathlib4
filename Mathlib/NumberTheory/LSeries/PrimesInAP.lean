/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

This will be done in the following steps:

1. Some auxiliary lemmas on infinite products and sums
2. (TODO) Results on the von Mangoldt function restricted to a residue class
3. (TODO) Results on its L-series
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
