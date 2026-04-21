/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Arend Mellendijk, Jeremy Tan
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# The radical in `ℕ` and `ℤ`

## Declarations for `ℕ`

- `UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors`: The prime factors of a natural number
  are the same as the prime factors defined in `Nat.primeFactors`.
- `Nat.radical_eq_prod_primeFactors`: The radical is computable for natural numbers.
- `Nat.radical_le_self_iff`: if `n ≠ 0`, `radical n ≤ n`.
- `Nat.two_le_radical_iff`: `2 ≤ n.radical` iff `2 ≤ n`.

## Declarations for `ℤ`

- `UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs`: The prime factors of an integer
  are the same as the prime factors of its absolute value.
- `Int.radical_eq_prod_primeFactors`: The radical is computable for integers.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open UniqueFactorizationMonoid

/-! ### Lemmas about natural numbers -/

lemma UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors :
    primeFactors = Nat.primeFactors := by
  ext n : 1
  rw [primeFactors, Nat.factors_eq, Nat.primeFactors]
  -- this convert is necessary because of the different DecidableEq instances
  convert List.toFinset_coe _

namespace Nat

variable {n : ℕ}

lemma radical_eq_prod_primeFactors : radical n = ∏ p ∈ n.primeFactors, p := by
  simp [radical, primeFactors_eq_natPrimeFactors]

lemma radical_pos (n) : 0 < radical n := pos_of_ne_zero radical_ne_zero

@[simp] lemma one_lt_radical_iff : 1 < radical n ↔ 1 < n := by
  have pp (p) (h : p ∈ n.primeFactors) : 1 ≤ p := pos_of_mem_primeFactors h
  rw [radical_eq_prod_primeFactors, ← @nonempty_primeFactors n, Finset.one_lt_prod_iff_of_one_le pp]
  exact ⟨fun ⟨p, h⟩ ↦ ⟨p, h.1⟩, fun ⟨p, h⟩ ↦ ⟨p, h, (mem_primeFactors.mp h).1.one_lt⟩⟩

@[simp] lemma two_le_radical_iff : 2 ≤ radical n ↔ 2 ≤ n := one_lt_radical_iff

@[simp] lemma radical_le_one_iff : radical n ≤ 1 ↔ n ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

@[simp] lemma radical_eq_one_iff : radical n = 1 ↔ n ≤ 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos n]

@[simp] lemma radical_le_self_iff : radical n ≤ n ↔ n ≠ 0 :=
  ⟨by aesop, fun h ↦ Nat.le_of_dvd (by lia) radical_dvd_self⟩

@[simp] lemma self_lt_radical_iff : n < radical n ↔ n = 0 := by
  simpa only [not_le, not_not] using radical_le_self_iff.not

open Qq Lean Mathlib.Meta Finset

namespace Mathlib.Meta.Positivity
open Positivity

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for radical. Proves radicals are nonzero. -/
@[positivity UniqueFactorizationMonoid.radical _]
meta def evalRadical : PositivityExt where eval {u α} _ _ e := do
  match e with
  | ~q(@radical _ $inst $inst' $inst'' $n) =>
    have _ := ← synthInstanceQ q(Nontrivial $α)
    assertInstancesCommute
    return .nonzero q(radical_ne_zero)
  | _ => throwError "not radical"

example : 0 < radical 100 := by positivity

end Mathlib.Meta.Positivity

end Nat

/-! ### Lemmas about integers -/

variable {z : ℤ}

lemma UniqueFactorizationMonoid.primeFactors_eq_primeFactors_natAbs :
    primeFactors z = z.natAbs.primeFactors.map Nat.castEmbedding := by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors, mem_normalizedFactors_iff' hz, irreducible_iff_prime,
    Int.nonneg_iff_normalize_eq_self, Finset.mem_map, Function.Embedding.coeFn_mk]
  refine ⟨fun ⟨pp, nnp, dp⟩ ↦ ?_, fun h ↦ ?_⟩
  · lift p to ℕ using nnp
    rw [← Nat.prime_iff_prime_int] at pp
    rw [Int.natCast_dvd] at dp
    exact ⟨p, by simp_all, rfl⟩
  · simp_rw [Nat.mem_primeFactors, Function.Embedding.toFun_eq_coe, Nat.castEmbedding_apply] at h
    obtain ⟨n, ⟨pn, dn, -⟩, rfl⟩ := h
    rw [Int.natCast_dvd, ← Nat.prime_iff_prime_int]
    exact ⟨pn, by simp, dn⟩

namespace Int

@[simp] lemma radical_natAbs_eq_radical : radical z.natAbs = radical z := by
  rw [Nat.radical_eq_prod_primeFactors, radical]
  simp [primeFactors_eq_primeFactors_natAbs]

lemma radical_eq_prod_primeFactors : radical z = ∏ p ∈ z.natAbs.primeFactors, p := by
  rw [← radical_natAbs_eq_radical, Nat.radical_eq_prod_primeFactors]

lemma radical_pos (z : ℤ) : 0 < radical z := by
  rw [← radical_natAbs_eq_radical, natCast_pos]
  exact Nat.radical_pos _

@[simp] lemma one_lt_radical_iff : 1 < radical z ↔ 1 < z.natAbs := by
  rw [← radical_natAbs_eq_radical, Nat.one_lt_cast]
  exact Nat.one_lt_radical_iff

@[simp] lemma two_le_radical_iff : 2 ≤ radical z ↔ 2 ≤ z.natAbs := one_lt_radical_iff

@[simp] lemma radical_le_one_iff : radical z ≤ 1 ↔ z.natAbs ≤ 1 := by
  simpa only [not_lt] using one_lt_radical_iff.not

@[simp] lemma radical_eq_one_iff : radical z = 1 ↔ z.natAbs ≤ 1 := by
  rw [← radical_le_one_iff]
  grind [radical_pos z]

@[simp, norm_cast] lemma radical_natCast {n : ℕ} : radical (n : ℤ) = radical n := by
  simp [Int.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors]

end Int
