/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
Extending an `F` which is
a function from primes to a monoid `M`
such that all `F p`, `F q`... commute
multiplicatively so that it is a
totally multiplicative function on all `ℕ_{≥1}` -/

namespace PrimeExtend

open scoped Function

-- `Nat.Primes` is a `def` (semireducible), not an `abbrev`
set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [Monoid M]
variable (F : Nat.Primes → M) (Hcomm : ∀ p q : Nat.Primes, Commute (F p) (F q))

include Hcomm in
private theorem pc (s : Finset Nat.Primes) (e : Nat.Primes → ℕ) :
    (↑s : Set Nat.Primes).Pairwise (Commute on fun p => F p ^ e p) :=
  fun p _ q _ _ => (Hcomm p q).pow_pow _ _

/-- The extension: `n ↦ ∏_{q prime, q^e || n} F(q)^e`
This is well-defined because the pairwise-commuting hypothesis `Hcomm` -/
public noncomputable def extendPrimes (n : ℕ) : M :=
  (n.factorization.support.subtype Nat.Prime).noncommProd
    (fun q => F q ^ n.factorization q.1) (pc F Hcomm _ _)

include Hcomm in
/-- When `n=1`, the product is empty and so the result is `1 ∈ M` -/
public theorem extendPrimes_one : extendPrimes F Hcomm 1 = 1 := by
  change ((1 : ℕ).factorization.support.subtype Nat.Prime).noncommProd
    (fun q => F q ^ (1 : ℕ).factorization q.1) (pc F Hcomm _ _) = 1
  have h1 : ((1 : ℕ).factorization.support.subtype Nat.Prime) = ∅ := by
    rw [Finset.subtype_eq_empty]
    intro x _
    simp [Nat.factorization_one]
  have step : ((1 : ℕ).factorization.support.subtype Nat.Prime).noncommProd
      (fun q => F q ^ (1 : ℕ).factorization q.1) (pc F Hcomm _ _) =
      (∅ : Finset Nat.Primes).noncommProd (fun q => F q ^ (1 : ℕ).factorization q.1)
        (pc F Hcomm _ _) :=
    Finset.noncommProd_congr h1 (fun _ _ => rfl) _
  rw [step]
  exact Finset.noncommProd_empty _ _

private theorem support_single_add (q : ℕ) (g : ℕ →₀ ℕ) :
    (Finsupp.single q 1 + g).support = insert q g.support := by
  ext p
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_insert]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp [hpq]

private theorem subtype_insert_of_prime (q : ℕ) (hq : q.Prime) (s : Finset ℕ) :
    (insert q s).subtype Nat.Prime = insert (⟨q, hq⟩ : Nat.Primes) (s.subtype Nat.Prime) := by
  ext ⟨p, hp⟩
  simp [Finset.mem_insert, Subtype.ext_iff]

include Hcomm in
private theorem extendPrimes_prime_mul_notMem (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k)
    (hnotmem : q ∉ k.factorization.support) :
    extendPrimes F Hcomm (q * k) = F ⟨q, hq⟩ * extendPrimes F Hcomm k := by
  have hqk : (q * k).factorization = Finsupp.single q 1 + k.factorization :=
    hq.factorization ▸ Nat.factorization_mul hq.ne_zero hk.ne'
  have hsupp : (q * k).factorization.support.subtype Nat.Prime =
      insert (⟨q, hq⟩ : Nat.Primes) (k.factorization.support.subtype Nat.Prime) := by
    rw [hqk, support_single_add, subtype_insert_of_prime q hq]
  have hnotmem' : (⟨q, hq⟩ : Nat.Primes) ∉ k.factorization.support.subtype Nat.Prime :=
    fun h => hnotmem (Finset.mem_subtype.1 h)
  have step1 : extendPrimes F Hcomm (q * k) =
      (insert (⟨q, hq⟩ : Nat.Primes) (k.factorization.support.subtype Nat.Prime)).noncommProd
        (fun p => F p ^ (q * k).factorization p.1) (pc F Hcomm _ _) :=
    Finset.noncommProd_congr hsupp (fun _ _ => rfl) _
  rw [step1, Finset.noncommProd_insert_of_notMem _ _ _ _ hnotmem']
  have hq1 : (q * k).factorization q = 1 := by
    rw [hqk, Finsupp.add_apply, Finsupp.notMem_support_iff.1 hnotmem, Finsupp.single_eq_same,
      add_zero]
  rw [show (q * k).factorization (⟨q, hq⟩ : Nat.Primes).1 = 1 from hq1, pow_one]
  congr 1
  apply Finset.noncommProd_congr rfl
  intro p hp
  rw [hqk]
  have : (p : ℕ) ≠ q := fun h => hnotmem (h ▸ (Finset.mem_subtype.1 hp))
  simp [this]

private theorem subtype_erase_insert_of_prime (q : ℕ) (hq : q.Prime) (s : Finset ℕ)
    (hmem : q ∈ s) :
    s.subtype Nat.Prime = insert (⟨q, hq⟩ : Nat.Primes) ((s.erase q).subtype Nat.Prime) := by
  ext ⟨p, hp⟩
  simp only [Finset.mem_subtype, Finset.mem_insert, Subtype.ext_iff, Finset.mem_erase]
  constructor
  · intro h; by_cases hpq : p = q
    · exact Or.inl hpq
    · exact Or.inr ⟨hpq, h⟩
  · rintro (rfl | ⟨_, h⟩)
    · exact hmem
    · exact h

include Hcomm in
private theorem extendPrimes_prime_mul_mem (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k)
    (hmem : q ∈ k.factorization.support) :
    extendPrimes F Hcomm (q * k) = F ⟨q, hq⟩ * extendPrimes F Hcomm k := by
  have hqk : (q * k).factorization = Finsupp.single q 1 + k.factorization :=
    hq.factorization ▸ Nat.factorization_mul hq.ne_zero hk.ne'
  have hsupp : (q * k).factorization.support = k.factorization.support := by
    rw [hqk, support_single_add]; exact Finset.insert_eq_self.2 hmem
  have herase : k.factorization.support.subtype Nat.Prime =
      insert (⟨q, hq⟩ : Nat.Primes) ((k.factorization.support.erase q).subtype Nat.Prime) :=
    subtype_erase_insert_of_prime q hq k.factorization.support hmem
  have hnotmem' :
      (⟨q, hq⟩ : Nat.Primes) ∉ (k.factorization.support.erase q).subtype Nat.Prime :=
    fun h => (Finset.mem_erase.1 (Finset.mem_subtype.1 h)).1 rfl
  have step1 : extendPrimes F Hcomm (q * k) =
      (insert (⟨q, hq⟩ : Nat.Primes)
          ((k.factorization.support.erase q).subtype Nat.Prime)).noncommProd
        (fun p => F p ^ (q * k).factorization p.1) (pc F Hcomm _ _) :=
    Finset.noncommProd_congr (hsupp ▸ herase) (fun _ _ => rfl) _
  rw [step1, Finset.noncommProd_insert_of_notMem _ _ _ _ hnotmem']
  have hqval : (q * k).factorization q = 1 + k.factorization q := by
    rw [hqk, Finsupp.add_apply, Finsupp.single_eq_same]
  rw [show (q * k).factorization (⟨q, hq⟩ : Nat.Primes).1 = 1 + k.factorization q from hqval,
    pow_add, pow_one, mul_assoc]
  congr 1
  have step3 : ((k.factorization.support.erase q).subtype Nat.Prime).noncommProd
      (fun p => F p ^ (q * k).factorization p.1) (pc F Hcomm _ _)
      = ((k.factorization.support.erase q).subtype Nat.Prime).noncommProd
        (fun p => F p ^ k.factorization p.1) (pc F Hcomm _ _) := by
    apply Finset.noncommProd_congr rfl
    intro p hp
    have hpq : (p : ℕ) ≠ q := (Finset.mem_erase.1 (Finset.mem_subtype.1 hp)).1
    rw [hqk]; simp [hpq]
  rw [step3]
  have step4 : extendPrimes F Hcomm k =
      (insert (⟨q, hq⟩ : Nat.Primes)
          ((k.factorization.support.erase q).subtype Nat.Prime)).noncommProd
        (fun p => F p ^ k.factorization p.1) (pc F Hcomm _ _) :=
    Finset.noncommProd_congr herase (fun _ _ => rfl) _
  rw [step4, Finset.noncommProd_insert_of_notMem _ _ _ _ hnotmem']

include Hcomm in
private theorem extendPrimes_prime_mul (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k) :
    extendPrimes F Hcomm (q * k) = F ⟨q, hq⟩ * extendPrimes F Hcomm k := by
  by_cases hmem : q ∈ k.factorization.support
  · exact extendPrimes_prime_mul_mem F Hcomm q hq k hk hmem
  · exact extendPrimes_prime_mul_notMem F Hcomm q hq k hk hmem

include Hcomm in
/-- The extension agrees with `F` on the primes themselves. -/
public theorem extendPrimes_prime (q : ℕ) (hq : q.Prime) :
    extendPrimes F Hcomm q = F ⟨q, hq⟩ := by
  have h := extendPrimes_prime_mul F Hcomm q hq 1 Nat.one_pos
  rwa [mul_one, extendPrimes_one, mul_one] at h

include Hcomm in
/-- `F(m*n) = F(m)*F(n)` for `m, n ≥ 1`. -/
public theorem extendPrimes_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    extendPrimes F Hcomm (m * n) = extendPrimes F Hcomm m * extendPrimes F Hcomm n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [one_mul, extendPrimes_one, one_mul]
    · have hq : m.minFac.Prime := Nat.minFac_prime hm1
      have hdvd : m.minFac ∣ m := Nat.minFac_dvd m
      obtain ⟨m', hm'⟩ := hdvd
      have hm'pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · simp [h0] at hm'; omega
        · exact h0
      have hlt : m' < m := by
        rw [hm']; exact lt_mul_left hm'pos hq.one_lt
      rw [hm', mul_assoc, extendPrimes_prime_mul F Hcomm _ hq _ (Nat.mul_pos hm'pos hn),
        ih m' hlt hm'pos, extendPrimes_prime_mul F Hcomm _ hq _ hm'pos, mul_assoc]

end PrimeExtend
