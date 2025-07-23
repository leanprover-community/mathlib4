/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Prime factorizations

`n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
* `factorization 2000 2` is 4
* `factorization 2000 5` is 3
* `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
  https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
  We have lots of disparate ways of talking about the multiplicity of a prime
  in a natural number, including `factors.count`, `padicValNat`, `multiplicity`,
  and the material in `Data/PNat/Factors`.  Move some of this material to this file,
  prove results about the relationships between these definitions,
  and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
  with a normalization function, and then deduplicated.  The basics of this have been started in
  `Mathlib/RingTheory/UniqueFactorizationDomain/`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`. -/
def factorization (n : ℕ) : ℕ →₀ ℕ where
  support := n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

/-- The support of `n.factorization` is exactly `n.primeFactors`. -/
@[simp] lemma support_factorization (n : ℕ) : (factorization n).support = n.primeFactors := rfl

theorem factorization_def (n : ℕ) {p : ℕ} (pp : p.Prime) : n.factorization p = padicValNat p n := by
  simpa [factorization] using absurd pp

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form. -/
@[simp]
theorem primeFactorsList_count_eq {n p : ℕ} : n.primeFactorsList.count p = n.factorization p := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    exact List.replicate_sublist_iff.mpr le_rfl |>.subperm
  · rw [← Nat.lt_add_one_iff, lt_iff_not_ge,
      le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    intro h
    have := h.count_le p
    simp at this

theorem factorization_eq_primeFactorsList_multiset (n : ℕ) :
    n.factorization = Multiset.toFinsupp (n.primeFactorsList : Multiset ℕ) := by
  ext p
  simp

theorem Prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ∣ n) :
    0 < n.factorization p := by
  rwa [← primeFactorsList_count_eq, count_pos_iff, mem_primeFactorsList_iff_dvd hn hp]

theorem multiplicity_eq_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    multiplicity p n = n.factorization p := by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn.bot_lt]

/-! ### Basic facts about factorization -/


@[simp]
theorem factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod (· ^ ·) = n := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp only [← prod_toMultiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset]
  exact prod_primeFactorsList hn

theorem eq_of_factorization_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
  eq_of_perm_primeFactorsList ha hb
    (by simpa only [List.perm_iff_count, primeFactorsList_count_eq] using h)


/-- Every nonzero natural number has a unique prime factorization -/
theorem factorization_inj : Set.InjOn factorization { x : ℕ | x ≠ 0 } := fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]

@[simp]
theorem factorization_zero : factorization 0 = 0 := by ext; simp [factorization]

@[simp]
theorem factorization_one : factorization 1 = 0 := by ext; simp [factorization]

/-! ## Lemmas characterising when `n.factorization p = 0` -/

theorem factorization_eq_zero_iff (n p : ℕ) :
    n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  simp_rw [← notMem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]
theorem factorization_eq_zero_of_non_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := by simp [factorization_eq_zero_iff, hp]

-- TODO: Replace
alias factorization_eq_zero_of_not_prime := factorization_eq_zero_of_non_prime

@[simp]
theorem factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_zero

@[simp]
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_not_prime _ not_prime_one

theorem factorization_eq_zero_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : n.factorization p = 0 := by
  simp [factorization_eq_zero_iff, h]

theorem factorization_eq_zero_of_remainder {p r : ℕ} (i : ℕ) (hr : ¬p ∣ r) :
    (p * i + r).factorization p = 0 := by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

/-! ## Lemmas about factorizations of products and powers -/

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext p
  simp only [add_apply, ← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul ha hb) p, count_append]

theorem factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    d.factorization ≤ n.factorization ↔ d ∣ n := by
  constructor
  · intro hdn
    set K := n.factorization - d.factorization with hK
    use K.prod (· ^ ·)
    rw [← factorization_prod_pow_eq_self hn, ← factorization_prod_pow_eq_self hd,
        ← Finsupp.prod_add_index' pow_zero pow_add, hK, add_tsub_cancel_of_le hdn]
  · rintro ⟨c, rfl⟩
    rw [factorization_mul hd (right_ne_zero_of_mul hn)]
    simp

/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : Finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `#S = 2` and `g = id`. -/
theorem factorization_prod {α : Type*} {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization = S.sum fun x => (g x).factorization := by
  classical
    ext p
    refine Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, IH, factorization_mul (hS x hxS) hT]

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp]
theorem factorization_pow (n k : ℕ) : factorization (n ^ k) = k • n.factorization := by
  induction' k with k ih; · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rw [Nat.pow_succ, mul_comm, factorization_mul hn (pow_ne_zero _ hn), ih,
    add_smul, one_smul, add_comm]

/-! ## Lemmas about factorizations of primes and prime powers -/


/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp]
protected theorem Prime.factorization {p : ℕ} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  rw [← primeFactorsList_count_eq, primeFactorsList_prime hp, single_apply, count_singleton',
    if_congr eq_comm] <;> rfl

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
theorem Prime.factorization_pow {p k : ℕ} (hp : Prime p) : (p ^ k).factorization = single p k := by
  simp [hp]

theorem pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ¬p ^ (n.factorization p + 1) ∣ n := by
  intro h
  rw [← factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn] at h
  simpa [hp.factorization] using h p

lemma factorization_minFac_ne_zero {n : ℕ} (hn : 1 < n) :
    n.factorization n.minFac ≠ 0 := by
  refine mt (factorization_eq_zero_iff _ _).mp ?_
  push_neg
  exact ⟨minFac_prime (by omega), minFac_dvd n, Nat.ne_zero_of_lt hn⟩

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


/-- Any Finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) ∈ f.support, a ^ f a`. -/
theorem prod_pow_factorization_eq_self {f : ℕ →₀ ℕ} (hf : ∀ p : ℕ, p ∈ f.support → Prime p) :
    (f.prod (· ^ ·)).factorization = f := by
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := fun p hp =>
    pow_ne_zero _ (Prime.ne_zero (hf p hp))
  simp only [Finsupp.prod, factorization_prod h]
  conv =>
    rhs
    rw [(sum_single f).symm]
  exact sum_congr rfl fun p hp => Prime.factorization_pow (hf p hp)

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
def factorizationEquiv : ℕ+ ≃ { f : ℕ →₀ ℕ | ∀ p ∈ f.support, Prime p } where
  toFun := fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_notMem_support fun H => not_prime_zero (hf 0 H)⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| factorization_prod_pow_eq_self hx.ne.symm
  right_inv := fun ⟨_, hf⟩ => Subtype.ext <| prod_pow_factorization_eq_self hf

/-! ### Factorization and coprimes -/


/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_apply_of_coprime {p a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  rw [Finsupp.add_apply, factorization_mul_apply_of_coprime hab]

/-! ### Generalisation of the "even part" and "odd part" of a natural number -/

/-- We introduce the notations `ordProj[p] n` for the largest power of the prime `p` that
divides `n` and `ordCompl[p] n` for the complementary part. The `ord` naming comes from
the $p$-adic order/valuation of a number, and `proj` and `compl` are for the projection and
complementary projection. The term `n.factorization p` is the $p$-adic order itself.
For example, `ordProj[2] n` is the even part of `n` and `ordCompl[2] n` is the odd part. -/
notation "ordProj[" p "] " n:arg => p ^ Nat.factorization n p

@[inherit_doc «termOrdProj[_]_»]
notation "ordCompl[" p "] " n:arg => n / ordProj[p] n

theorem ordProj_dvd (n p : ℕ) : ordProj[p] n ∣ n := by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow, List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]

@[deprecated (since := "2024-10-24")] alias ord_proj_dvd := ordProj_dvd

lemma ordProj_dvd_ordProj_iff_dvd (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ p : ℕ, ordProj[p] a ∣ ordProj[p] b) ↔ a ∣ b := by
  rw [← factorization_le_iff_dvd ha hb, Finsupp.le_def]
  congr! 1 with p
  obtain _ | _ | p := p <;> simp [Nat.pow_dvd_pow_iff_le_right]

/-! ### Factorization LCM definitions -/


/-- If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMLeft = ∏ pᵢ ^ kᵢ`, where
`kᵢ = nᵢ` if `mᵢ ≤ nᵢ` and `0` otherwise. Note that the product is over the divisors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`. -/
def factorizationLCMLeft (a b : ℕ) : ℕ :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then p ^ n else 1

/-- If `a = ∏ pᵢ ^ nᵢ` and `b = ∏ pᵢ ^ mᵢ`, then `factorizationLCMRight = ∏ pᵢ ^ kᵢ`, where
`kᵢ = mᵢ` if `nᵢ < mᵢ` and `0` otherwise. Note that the product is over the divisors of `lcm a b`,
so if one of `a` or `b` is `0` then the result is `1`.

Note that `factorizationLCMRight a b` is *not* `factorizationLCMLeft b a`: the difference is
that in `factorizationLCMLeft a b` there are the primes whose exponent in `a` is bigger or equal
than the exponent in `b`, while in `factorizationLCMRight a b` there are the primes whose
exponent in `b` is strictly bigger than in `a`. For example `factorizationLCMLeft 2 2 = 2`, but
`factorizationLCMRight 2 2 = 1`. -/
def factorizationLCMRight (a b : ℕ) :=
  (Nat.lcm a b).factorization.prod fun p n ↦
    if b.factorization p ≤ a.factorization p then 1 else p ^ n

end Nat
