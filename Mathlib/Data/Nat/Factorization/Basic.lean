/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Nat.Interval
import Mathlib.Tactic.IntervalCases

#align_import data.nat.factorization.basic from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

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
`RingTheory/UniqueFactorizationDomain`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

-- Workaround for lean4#2038
attribute [-instance] instBEqNat

open Nat Finset List Finsupp

open BigOperators

namespace Nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
def factorization (n : ℕ) : ℕ →₀ ℕ where
  support := n.factors.toFinset
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by
    rcases eq_or_ne n 0 with (rfl | hn0)
    -- ⊢ ∀ (a : ℕ), a ∈ toFinset (factors 0) ↔ (fun p => if Prime p then padicValNat  …
    · simp
      -- 🎉 no goals
    simp only [mem_factors hn0, mem_toFinset, Ne.def, ite_eq_right_iff, not_forall, exists_prop,
      and_congr_right_iff]
    rintro p hp
    -- ⊢ p ∣ n ↔ ¬padicValNat p n = 0
    haveI := fact_iff.mpr hp
    -- ⊢ p ∣ n ↔ ¬padicValNat p n = 0
    exact dvd_iff_padicValNat_ne_zero hn0
    -- 🎉 no goals
#align nat.factorization Nat.factorization

theorem factorization_def (n : ℕ) {p : ℕ} (pp : p.Prime) : n.factorization p = padicValNat p n := by
  simpa [factorization] using absurd pp
  -- 🎉 no goals
#align nat.factorization_def Nat.factorization_def

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form. -/
@[simp]
theorem factors_count_eq {n p : ℕ} : n.factors.count p = n.factorization p := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  -- ⊢ count p (factors 0) = ↑(factorization 0) p
  · simp [factorization, count]
    -- 🎉 no goals
  by_cases pp : p.Prime
  -- ⊢ count p (factors n) = ↑(factorization n) p
  case neg =>
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_factors pp)]
    simp [factorization, pp]
  simp only [factorization, coe_mk, pp, if_true]
  -- ⊢ count p (factors n) = padicValNat p n
  rw [← PartENat.natCast_inj, padicValNat_def' pp.ne_one hn0,
    UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors pp hn0.ne']
  simp [factors_eq]
  -- 🎉 no goals
#align nat.factors_count_eq Nat.factors_count_eq

theorem factorization_eq_factors_multiset (n : ℕ) :
    n.factorization = Multiset.toFinsupp (n.factors : Multiset ℕ) := by
  ext p
  -- ⊢ ↑(factorization n) p = ↑(↑Multiset.toFinsupp ↑(factors n)) p
  simp
  -- 🎉 no goals
#align nat.factorization_eq_factors_multiset Nat.factorization_eq_factors_multiset

theorem multiplicity_eq_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    multiplicity p n = n.factorization p := by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn.bot_lt]
  -- 🎉 no goals
#align nat.multiplicity_eq_factorization Nat.multiplicity_eq_factorization

/-! ### Basic facts about factorization -/


@[simp]
theorem factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.prod (· ^ ·) = n := by
  rw [factorization_eq_factors_multiset n]
  -- ⊢ (Finsupp.prod (↑Multiset.toFinsupp ↑(factors n)) fun x x_1 => x ^ x_1) = n
  simp only [← prod_toMultiset, factorization, Multiset.coe_prod, Multiset.toFinsupp_toMultiset]
  -- ⊢ List.prod (factors n) = n
  exact prod_factors hn
  -- 🎉 no goals
#align nat.factorization_prod_pow_eq_self Nat.factorization_prod_pow_eq_self

theorem eq_of_factorization_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
  eq_of_perm_factors ha hb (by simpa only [List.perm_iff_count, factors_count_eq] using h)
                               -- 🎉 no goals
#align nat.eq_of_factorization_eq Nat.eq_of_factorization_eq

/-- Every nonzero natural number has a unique prime factorization -/
theorem factorization_inj : Set.InjOn factorization { x : ℕ | x ≠ 0 } := fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]
                                           -- 🎉 no goals
#align nat.factorization_inj Nat.factorization_inj

@[simp]
theorem factorization_zero : factorization 0 = 0 := by simp [factorization]
                                                       -- 🎉 no goals
#align nat.factorization_zero Nat.factorization_zero

@[simp]
theorem factorization_one : factorization 1 = 0 := by simp [factorization]
                                                      -- 🎉 no goals
#align nat.factorization_one Nat.factorization_one

/-- The support of `n.factorization` is exactly `n.factors.toFinset` -/
@[simp]
theorem support_factorization {n : ℕ} : n.factorization.support = n.factors.toFinset := by
  simp [factorization]
  -- 🎉 no goals
#align nat.support_factorization Nat.support_factorization

theorem factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors := by
  simp only [support_factorization, List.mem_toFinset]
  -- 🎉 no goals
#align nat.factor_iff_mem_factorization Nat.factor_iff_mem_factorization

theorem prime_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : p.Prime :=
  prime_of_mem_factors (factor_iff_mem_factorization.mp hp)
#align nat.prime_of_mem_factorization Nat.prime_of_mem_factorization

theorem pos_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : 0 < p :=
  Prime.pos (prime_of_mem_factorization hp)
#align nat.pos_of_mem_factorization Nat.pos_of_mem_factorization

theorem le_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ≤ n :=
  le_of_mem_factors (factor_iff_mem_factorization.mp h)
#align nat.le_of_mem_factorization Nat.le_of_mem_factorization

/-! ## Lemmas characterising when `n.factorization p = 0` -/


theorem factorization_eq_zero_iff (n p : ℕ) :
    n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  rw [← not_mem_support_iff, support_factorization, mem_toFinset]
  -- ⊢ ¬p ∈ factors n ↔ ¬Prime p ∨ ¬p ∣ n ∨ n = 0
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ ¬p ∈ factors 0 ↔ ¬Prime p ∨ ¬p ∣ 0 ∨ 0 = 0
  · simp
    -- 🎉 no goals
  · simp [hn, Nat.mem_factors, not_and_or, -not_and]
    -- 🎉 no goals
#align nat.factorization_eq_zero_iff Nat.factorization_eq_zero_iff

@[simp]
theorem factorization_eq_zero_of_non_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := by simp [factorization_eq_zero_iff, hp]
                                -- 🎉 no goals
#align nat.factorization_eq_zero_of_non_prime Nat.factorization_eq_zero_of_non_prime

theorem factorization_eq_zero_of_not_dvd {n p : ℕ} (h : ¬p ∣ n) : n.factorization p = 0 := by
  simp [factorization_eq_zero_iff, h]
  -- 🎉 no goals
#align nat.factorization_eq_zero_of_not_dvd Nat.factorization_eq_zero_of_not_dvd

theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.not_mem_support_iff.mp (mt le_of_mem_factorization (not_le_of_lt h))
#align nat.factorization_eq_zero_of_lt Nat.factorization_eq_zero_of_lt

@[simp]
theorem factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_zero
#align nat.factorization_zero_right Nat.factorization_zero_right

@[simp]
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_one
#align nat.factorization_one_right Nat.factorization_one_right

theorem dvd_of_factorization_pos {n p : ℕ} (hn : n.factorization p ≠ 0) : p ∣ n :=
  dvd_of_mem_factors (factor_iff_mem_factorization.1 (mem_support_iff.2 hn))
#align nat.dvd_of_factorization_pos Nat.dvd_of_factorization_pos

theorem Prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ∣ n) :
    0 < n.factorization p := by
    rwa [← factors_count_eq, count_pos_iff_mem, mem_factors_iff_dvd hn hp]
    -- 🎉 no goals
#align nat.prime.factorization_pos_of_dvd Nat.Prime.factorization_pos_of_dvd

theorem factorization_eq_zero_of_remainder {p r : ℕ} (i : ℕ) (hr : ¬p ∣ r) :
    (p * i + r).factorization p = 0 := by
  apply factorization_eq_zero_of_not_dvd
  -- ⊢ ¬p ∣ p * i + r
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]
  -- 🎉 no goals
#align nat.factorization_eq_zero_of_remainder Nat.factorization_eq_zero_of_remainder

theorem factorization_eq_zero_iff_remainder {p r : ℕ} (i : ℕ) (pp : p.Prime) (hr0 : r ≠ 0) :
    ¬p ∣ r ↔ (p * i + r).factorization p = 0 := by
  refine' ⟨factorization_eq_zero_of_remainder i, fun h => _⟩
  -- ⊢ ¬p ∣ r
  rw [factorization_eq_zero_iff] at h
  -- ⊢ ¬p ∣ r
  contrapose! h
  -- ⊢ Prime p ∧ p ∣ p * i + r ∧ p * i + r ≠ 0
  refine' ⟨pp, _, _⟩
  -- ⊢ p ∣ p * i + r
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
    -- 🎉 no goals
  · contrapose! hr0
    -- ⊢ r = 0
    exact (add_eq_zero_iff.mp hr0).2
    -- 🎉 no goals
#align nat.factorization_eq_zero_iff_remainder Nat.factorization_eq_zero_iff_remainder

/-- The only numbers with empty prime factorization are `0` and `1` -/
theorem factorization_eq_zero_iff' (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_factors_multiset n]
  -- ⊢ ↑Multiset.toFinsupp ↑(factors n) = 0 ↔ n = 0 ∨ n = 1
  simp [factorization, AddEquiv.map_eq_zero_iff, Multiset.coe_eq_zero]
  -- 🎉 no goals
#align nat.factorization_eq_zero_iff' Nat.factorization_eq_zero_iff'

/-! ## Lemmas about factorizations of products and powers -/


/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext p
  -- ⊢ ↑(factorization (a * b)) p = ↑(factorization a + factorization b) p
  simp only [add_apply, ← factors_count_eq, perm_iff_count.mp (perm_factors_mul ha hb) p,
    count_append]
#align nat.factorization_mul Nat.factorization_mul

theorem factorization_mul_support {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  ext q
  -- ⊢ q ∈ (factorization (a * b)).support ↔ q ∈ (factorization a).support ∪ (facto …
  simp only [Finset.mem_union, factor_iff_mem_factorization]
  -- ⊢ q ∈ factors (a * b) ↔ q ∈ factors a ∨ q ∈ factors b
  exact mem_factors_mul ha hb
  -- 🎉 no goals
#align nat.factorization_mul_support Nat.factorization_mul_support

/-- If a product over `n.factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.toFinset` -/
theorem prod_factorization_eq_prod_factors {n : ℕ} {β : Type*} [CommMonoid β] (f : ℕ → β) :
    (n.factorization.prod fun p _ => f p) = ∏ p in n.factors.toFinset, f p := by
  apply prod_congr support_factorization
  -- ⊢ ∀ (x : ℕ), x ∈ toFinset (factors n) → (fun p x => f p) x (↑(factorization n) …
  simp
  -- 🎉 no goals
#align nat.prod_factorization_eq_prod_factors Nat.prod_factorization_eq_prod_factors

/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : Finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`. -/
theorem factorization_prod {α : Type*} {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization = S.sum fun x => (g x).factorization := by
  classical
    ext p
    refine' Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, ← IH, factorization_mul (hS x hxS) hT]
#align nat.factorization_prod Nat.factorization_prod

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp]
theorem factorization_pow (n k : ℕ) : factorization (n ^ k) = k • n.factorization := by
  induction' k with k ih; · simp
  -- ⊢ factorization (n ^ zero) = zero • factorization n
                            -- 🎉 no goals
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ factorization (0 ^ succ k) = succ k • factorization 0
  · simp
    -- 🎉 no goals
  rw [pow_succ, mul_comm, factorization_mul hn (pow_ne_zero _ hn), ih, succ_eq_one_add, add_smul,
   one_smul]
#align nat.factorization_pow Nat.factorization_pow

/-! ## Lemmas about factorizations of primes and prime powers -/


/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp]
theorem Prime.factorization {p : ℕ} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  -- ⊢ ↑(Nat.factorization p) q = ↑(single p 1) q
  rw [← factors_count_eq, factors_prime hp, single_apply, count_singleton', if_congr eq_comm] <;>
  -- ⊢ 1 = 1
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
#align nat.prime.factorization Nat.Prime.factorization

/-- The multiplicity of prime `p` in `p` is `1` -/
@[simp]
theorem Prime.factorization_self {p : ℕ} (hp : Prime p) : p.factorization p = 1 := by simp [hp]
                                                                                      -- 🎉 no goals
#align nat.prime.factorization_self Nat.Prime.factorization_self

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
theorem Prime.factorization_pow {p k : ℕ} (hp : Prime p) : (p ^ k).factorization = single p k := by
  simp [hp]
  -- 🎉 no goals
#align nat.prime.factorization_pow Nat.Prime.factorization_pow

/-- If the factorization of `n` contains just one number `p` then `n` is a power of `p` -/
theorem eq_pow_of_factorization_eq_single {n p k : ℕ} (hn : n ≠ 0)
    (h : n.factorization = Finsupp.single p k) : n = p ^ k := by
  -- Porting note: explicitly added `Finsupp.prod_single_index`
  rw [← Nat.factorization_prod_pow_eq_self hn, h, Finsupp.prod_single_index]
  -- ⊢ p ^ 0 = 1
  simp
  -- 🎉 no goals
#align nat.eq_pow_of_factorization_eq_single Nat.eq_pow_of_factorization_eq_single

/-- The only prime factor of prime `p` is `p` itself. -/
theorem Prime.eq_of_factorization_pos {p q : ℕ} (hp : Prime p) (h : p.factorization q ≠ 0) :
    p = q := by simpa [hp.factorization, single_apply] using h
                -- 🎉 no goals
#align nat.prime.eq_of_factorization_pos Nat.Prime.eq_of_factorization_pos

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


/-- Any Finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) in f.support, a ^ f a`. -/
theorem prod_pow_factorization_eq_self {f : ℕ →₀ ℕ} (hf : ∀ p : ℕ, p ∈ f.support → Prime p) :
    (f.prod (· ^ ·)).factorization = f := by
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := fun p hp =>
    pow_ne_zero _ (Prime.ne_zero (hf p hp))
  simp only [Finsupp.prod, factorization_prod h]
  -- ⊢ ∑ x in f.support, factorization (x ^ ↑f x) = f
  conv =>
    rhs
    rw [(sum_single f).symm]
  exact sum_congr rfl fun p hp => Prime.factorization_pow (hf p hp)
  -- 🎉 no goals
#align nat.prod_pow_factorization_eq_self Nat.prod_pow_factorization_eq_self

theorem eq_factorization_iff {n : ℕ} {f : ℕ →₀ ℕ} (hn : n ≠ 0) (hf : ∀ p ∈ f.support, Prime p) :
    f = n.factorization ↔ f.prod (· ^ ·) = n :=
  ⟨fun h => by rw [h, factorization_prod_pow_eq_self hn], fun h => by
               -- 🎉 no goals
    rw [← h, prod_pow_factorization_eq_self hf]⟩
    -- 🎉 no goals
#align nat.eq_factorization_iff Nat.eq_factorization_iff

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
def factorizationEquiv : ℕ+ ≃ { f : ℕ →₀ ℕ | ∀ p ∈ f.support, Prime p } where
  toFun := fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_factorization⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_not_mem_support fun H => not_prime_zero (hf 0 H)⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| factorization_prod_pow_eq_self hx.ne.symm
  right_inv := fun ⟨_, hf⟩ => Subtype.ext <| prod_pow_factorization_eq_self hf
#align nat.factorization_equiv Nat.factorizationEquiv

theorem factorizationEquiv_apply (n : ℕ+) : (factorizationEquiv n).1 = n.1.factorization := by
  cases n
  -- ⊢ ↑(↑factorizationEquiv { val := val✝, property := property✝ }) = factorizatio …
  rfl
  -- 🎉 no goals
#align nat.factorization_equiv_apply Nat.factorizationEquiv_apply

theorem factorizationEquiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·) :=
  rfl
#align nat.factorization_equiv_inv_apply Nat.factorizationEquiv_inv_apply

/-! ### Generalisation of the "even part" and "odd part" of a natural number

We introduce the notations `ord_proj[p] n` for the largest power of the prime `p` that
divides `n` and `ord_compl[p] n` for the complementary part. The `ord` naming comes from
the $p$-adic order/valuation of a number, and `proj` and `compl` are for the projection and
complementary projection. The term `n.factorization p` is the $p$-adic order itself.
For example, `ord_proj[2] n` is the even part of `n` and `ord_compl[2] n` is the odd part. -/


-- porting note: Lean 4 thinks we need `HPow` without this
set_option quotPrecheck false in
notation "ord_proj[" p "] " n:arg => p ^ Nat.factorization n p

notation "ord_compl[" p "] " n:arg => n / ord_proj[p] n

@[simp]
theorem ord_proj_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ord_proj[p] n = 1 := by
  simp [factorization_eq_zero_of_non_prime n hp]
  -- 🎉 no goals
#align nat.ord_proj_of_not_prime Nat.ord_proj_of_not_prime

@[simp]
theorem ord_compl_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ord_compl[p] n = n := by
  simp [factorization_eq_zero_of_non_prime n hp]
  -- 🎉 no goals
#align nat.ord_compl_of_not_prime Nat.ord_compl_of_not_prime

theorem ord_proj_dvd (n p : ℕ) : ord_proj[p] n ∣ n := by
  by_cases hp : p.Prime
  -- ⊢ p ^ ↑(factorization n) p ∣ n
  case neg => simp [hp]
  -- ⊢ p ^ ↑(factorization n) p ∣ n
  -- 🎉 no goals
  rw [← factors_count_eq]
  -- ⊢ p ^ count p (factors n) ∣ n
  apply dvd_of_factors_subperm (pow_ne_zero _ hp.ne_zero)
  -- ⊢ factors (p ^ count p (factors n)) <+~ factors n
  rw [hp.factors_pow, List.subperm_ext_iff]
  -- ⊢ ∀ (x : ℕ), x ∈ replicate (count p (factors n)) p → count x (replicate (count …
  intro q hq
  -- ⊢ count q (replicate (count p (factors n)) p) ≤ count q (factors n)
  simp [List.eq_of_mem_replicate hq]
  -- 🎉 no goals
#align nat.ord_proj_dvd Nat.ord_proj_dvd

theorem ord_compl_dvd (n p : ℕ) : ord_compl[p] n ∣ n :=
  div_dvd_of_dvd (ord_proj_dvd n p)
#align nat.ord_compl_dvd Nat.ord_compl_dvd

theorem ord_proj_pos (n p : ℕ) : 0 < ord_proj[p] n := by
  by_cases pp : p.Prime
  -- ⊢ 0 < p ^ ↑(factorization n) p
  · simp [pow_pos pp.pos]
    -- 🎉 no goals
  · simp [pp]
    -- 🎉 no goals
#align nat.ord_proj_pos Nat.ord_proj_pos

theorem ord_proj_le {n : ℕ} (p : ℕ) (hn : n ≠ 0) : ord_proj[p] n ≤ n :=
  le_of_dvd hn.bot_lt (Nat.ord_proj_dvd n p)
#align nat.ord_proj_le Nat.ord_proj_le

theorem ord_compl_pos {n : ℕ} (p : ℕ) (hn : n ≠ 0) : 0 < ord_compl[p] n := by
  cases' em' p.Prime with pp pp
  -- ⊢ 0 < n / p ^ ↑(factorization n) p
  · simpa [Nat.factorization_eq_zero_of_non_prime n pp] using hn.bot_lt
    -- 🎉 no goals
  exact Nat.div_pos (ord_proj_le p hn) (ord_proj_pos n p)
  -- 🎉 no goals
#align nat.ord_compl_pos Nat.ord_compl_pos

theorem ord_compl_le (n p : ℕ) : ord_compl[p] n ≤ n :=
  Nat.div_le_self _ _
#align nat.ord_compl_le Nat.ord_compl_le

theorem ord_proj_mul_ord_compl_eq_self (n p : ℕ) : ord_proj[p] n * ord_compl[p] n = n :=
  Nat.mul_div_cancel' (ord_proj_dvd n p)
#align nat.ord_proj_mul_ord_compl_eq_self Nat.ord_proj_mul_ord_compl_eq_self

theorem ord_proj_mul {a b : ℕ} (p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ord_proj[p] (a * b) = ord_proj[p] a * ord_proj[p] b := by
  simp [factorization_mul ha hb, pow_add]
  -- 🎉 no goals
#align nat.ord_proj_mul Nat.ord_proj_mul

theorem ord_compl_mul (a b p : ℕ) : ord_compl[p] (a * b) = ord_compl[p] a * ord_compl[p] b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ 0 * b / p ^ ↑(factorization (0 * b)) p = 0 / p ^ ↑(factorization 0) p * (b / …
  · simp
    -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb)
  -- ⊢ a * 0 / p ^ ↑(factorization (a * 0)) p = a / p ^ ↑(factorization a) p * (0 / …
  · simp
    -- 🎉 no goals
  simp only [ord_proj_mul p ha hb]
  -- ⊢ a * b / (p ^ ↑(factorization a) p * p ^ ↑(factorization b) p) = a / p ^ ↑(fa …
  rw [mul_div_mul_comm_of_dvd_dvd (ord_proj_dvd a p) (ord_proj_dvd b p)]
  -- 🎉 no goals
#align nat.ord_compl_mul Nat.ord_compl_mul

/-! ### Factorization and divisibility -/


theorem dvd_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ p ∣ 0
  · simp
    -- 🎉 no goals
  simp [← mem_factors_iff_dvd hn (prime_of_mem_factorization h), factor_iff_mem_factorization.mp h]
  -- 🎉 no goals
#align nat.dvd_of_mem_factorization Nat.dvd_of_mem_factorization

/-- A crude upper bound on `n.factorization p` -/
theorem factorization_lt {n : ℕ} (p : ℕ) (hn : n ≠ 0) : n.factorization p < n := by
  by_cases pp : p.Prime
  -- ⊢ ↑(factorization n) p < n
  case neg =>
    simp [factorization_eq_zero_of_non_prime n pp]
    exact hn.bot_lt
  rw [← pow_lt_iff_lt_right pp.two_le]
  -- ⊢ p ^ ↑(factorization n) p < p ^ n
  apply lt_of_le_of_lt (ord_proj_le p hn)
  -- ⊢ n < p ^ n
  exact lt_of_lt_of_le (lt_two_pow n) (pow_le_pow_of_le_left pp.two_le n)
  -- 🎉 no goals
#align nat.factorization_lt Nat.factorization_lt

/-- An upper bound on `n.factorization p` -/
theorem factorization_le_of_le_pow {n p b : ℕ} (hb : n ≤ p ^ b) : n.factorization p ≤ b := by
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ ↑(factorization 0) p ≤ b
  · simp
    -- 🎉 no goals
  by_cases pp : p.Prime
  -- ⊢ ↑(factorization n) p ≤ b
  · exact (pow_le_iff_le_right pp.two_le).1 (le_trans (ord_proj_le p hn) hb)
    -- 🎉 no goals
  · simp [factorization_eq_zero_of_non_prime n pp]
    -- 🎉 no goals
#align nat.factorization_le_of_le_pow Nat.factorization_le_of_le_pow

theorem factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    d.factorization ≤ n.factorization ↔ d ∣ n := by
  constructor
  -- ⊢ factorization d ≤ factorization n → d ∣ n
  · intro hdn
    -- ⊢ d ∣ n
    set K := n.factorization - d.factorization with hK
    -- ⊢ d ∣ n
    use K.prod (· ^ ·)
    -- ⊢ n = d * Finsupp.prod K fun x x_1 => x ^ x_1
    rw [← factorization_prod_pow_eq_self hn, ← factorization_prod_pow_eq_self hd,
        ←Finsupp.prod_add_index' pow_zero pow_add, hK, add_tsub_cancel_of_le hdn]
  · rintro ⟨c, rfl⟩
    -- ⊢ factorization d ≤ factorization (d * c)
    rw [factorization_mul hd (right_ne_zero_of_mul hn)]
    -- ⊢ factorization d ≤ factorization d + factorization c
    simp
    -- 🎉 no goals
#align nat.factorization_le_iff_dvd Nat.factorization_le_iff_dvd

theorem factorization_prime_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → d.factorization p ≤ n.factorization p) ↔ d ∣ n := by
  rw [← factorization_le_iff_dvd hd hn]
  -- ⊢ (∀ (p : ℕ), Prime p → ↑(factorization d) p ≤ ↑(factorization n) p) ↔ factori …
  refine' ⟨fun h p => (em p.Prime).elim (h p) fun hp => _, fun h p _ => h p⟩
  -- ⊢ ↑(factorization d) p ≤ ↑(factorization n) p
  simp_rw [factorization_eq_zero_of_non_prime _ hp, le_refl]
  -- 🎉 no goals
#align nat.factorization_prime_le_iff_dvd Nat.factorization_prime_le_iff_dvd

theorem pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ¬p ^ (n.factorization p + 1) ∣ n := by
  intro h
  -- ⊢ False
  rw [← factorization_le_iff_dvd (pow_pos hp.pos _).ne' hn] at h
  -- ⊢ False
  simpa [hp.factorization] using h p
  -- 🎉 no goals
#align nat.pow_succ_factorization_not_dvd Nat.pow_succ_factorization_not_dvd

theorem factorization_le_factorization_mul_left {a b : ℕ} (hb : b ≠ 0) :
    a.factorization ≤ (a * b).factorization := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ factorization 0 ≤ factorization (0 * b)
  · simp
    -- 🎉 no goals
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  -- ⊢ a ∣ a * b
  exact Dvd.intro b rfl
  -- 🎉 no goals
#align nat.factorization_le_factorization_mul_left Nat.factorization_le_factorization_mul_left

theorem factorization_le_factorization_mul_right {a b : ℕ} (ha : a ≠ 0) :
    b.factorization ≤ (a * b).factorization := by
  rw [mul_comm]
  -- ⊢ factorization b ≤ factorization (b * a)
  apply factorization_le_factorization_mul_left ha
  -- 🎉 no goals
#align nat.factorization_le_factorization_mul_right Nat.factorization_le_factorization_mul_right

theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p := by
  rw [← factorization_le_iff_dvd (pow_pos pp.pos k).ne' hn, pp.factorization_pow, single_le_iff]
  -- 🎉 no goals
#align nat.prime.pow_dvd_iff_le_factorization Nat.Prime.pow_dvd_iff_le_factorization

theorem Prime.pow_dvd_iff_dvd_ord_proj {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ p ^ k ∣ ord_proj[p] n := by
  rw [pow_dvd_pow_iff_le_right pp.one_lt, pp.pow_dvd_iff_le_factorization hn]
  -- 🎉 no goals
#align nat.prime.pow_dvd_iff_dvd_ord_proj Nat.Prime.pow_dvd_iff_dvd_ord_proj

theorem Prime.dvd_iff_one_le_factorization {p n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ∣ n ↔ 1 ≤ n.factorization p :=
  Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)
                -- 🎉 no goals
#align nat.prime.dvd_iff_one_le_factorization Nat.Prime.dvd_iff_one_le_factorization

theorem exists_factorization_lt_of_lt {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    ∃ p : ℕ, a.factorization p < b.factorization p := by
  have hb : b ≠ 0 := (ha.bot_lt.trans hab).ne'
  -- ⊢ ∃ p, ↑(factorization a) p < ↑(factorization b) p
  contrapose! hab
  -- ⊢ b ≤ a
  rw [← Finsupp.le_def, factorization_le_iff_dvd hb ha] at hab
  -- ⊢ b ≤ a
  exact le_of_dvd ha.bot_lt hab
  -- 🎉 no goals
#align nat.exists_factorization_lt_of_lt Nat.exists_factorization_lt_of_lt

@[simp]
theorem factorization_div {d n : ℕ} (h : d ∣ n) :
    (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  -- ⊢ factorization (n / 0) = factorization n - factorization 0
                                         -- 🎉 no goals
  rcases eq_or_ne n 0 with (rfl | hn); · simp
  -- ⊢ factorization (0 / d) = factorization 0 - factorization d
                                         -- 🎉 no goals
  apply add_left_injective d.factorization
  -- ⊢ (fun x => x + factorization d) (factorization (n / d)) = (fun x => x + facto …
  simp only
  -- ⊢ factorization (n / d) + factorization d = factorization n - factorization d  …
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h, ←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd,
    Nat.div_mul_cancel h]
#align nat.factorization_div Nat.factorization_div

theorem dvd_ord_proj_of_dvd {n p : ℕ} (hn : n ≠ 0) (pp : p.Prime) (h : p ∣ n) : p ∣ ord_proj[p] n :=
  dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'
#align nat.dvd_ord_proj_of_dvd Nat.dvd_ord_proj_of_dvd

theorem not_dvd_ord_compl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : ¬p ∣ ord_compl[p] n := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ord_compl_pos p hn).ne']
  -- ⊢ ¬1 ≤ ↑(factorization (n / p ^ ↑(factorization n) p)) p
  rw [Nat.factorization_div (Nat.ord_proj_dvd n p)]
  -- ⊢ ¬1 ≤ ↑(factorization n - factorization (p ^ ↑(factorization n) p)) p
  simp [hp.factorization]
  -- 🎉 no goals
#align nat.not_dvd_ord_compl Nat.not_dvd_ord_compl

theorem coprime_ord_compl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : coprime p (ord_compl[p] n) :=
  (or_iff_left (not_dvd_ord_compl hp hn)).mp <| coprime_or_dvd_of_prime hp _
#align nat.coprime_ord_compl Nat.coprime_ord_compl

theorem factorization_ord_compl (n p : ℕ) :
    (ord_compl[p] n).factorization = n.factorization.erase p := by
  rcases eq_or_ne n 0 with (rfl | hn); · simp
  -- ⊢ factorization (0 / p ^ ↑(factorization 0) p) = Finsupp.erase p (factorizatio …
                                         -- 🎉 no goals
  by_cases pp : p.Prime
  -- ⊢ factorization (n / p ^ ↑(factorization n) p) = Finsupp.erase p (factorizatio …
  case neg =>
    -- porting note: needed to solve side goal explicitly
    rw [Finsupp.erase_of_not_mem_support]
    · simp [pp]
    · simp [mt prime_of_mem_factors pp]
  ext q
  -- ⊢ ↑(factorization (n / p ^ ↑(factorization n) p)) q = ↑(Finsupp.erase p (facto …
  rcases eq_or_ne q p with (rfl | hqp)
  -- ⊢ ↑(factorization (n / q ^ ↑(factorization n) q)) q = ↑(Finsupp.erase q (facto …
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ord_compl pp hn]
    -- ⊢ ¬Prime q ∨ True ∨ n / q ^ ↑(factorization n) q = 0
    simp
    -- 🎉 no goals
  · rw [Finsupp.erase_ne hqp, factorization_div (ord_proj_dvd n p)]
    -- ⊢ ↑(factorization n - factorization (p ^ ↑(factorization n) p)) q = ↑(factoriz …
    simp [pp.factorization, hqp.symm]
    -- 🎉 no goals
#align nat.factorization_ord_compl Nat.factorization_ord_compl

-- `ord_compl[p] n` is the largest divisor of `n` not divisible by `p`.
theorem dvd_ord_compl_of_dvd_not_dvd {p d n : ℕ} (hdn : d ∣ n) (hpd : ¬p ∣ d) :
    d ∣ ord_compl[p] n := by
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  -- ⊢ d ∣ 0 / p ^ ↑(factorization 0) p
                                          -- 🎉 no goals
  rcases eq_or_ne d 0 with (rfl | hd0);
  -- ⊢ 0 ∣ n / p ^ ↑(factorization n) p
  · simp at hpd
    -- 🎉 no goals
  rw [← factorization_le_iff_dvd hd0 (ord_compl_pos p hn0).ne', factorization_ord_compl]
  -- ⊢ factorization d ≤ Finsupp.erase p (factorization n)
  intro q
  -- ⊢ ↑(factorization d) q ≤ ↑(Finsupp.erase p (factorization n)) q
  rcases eq_or_ne q p with (rfl | hqp)
  -- ⊢ ↑(factorization d) q ≤ ↑(Finsupp.erase q (factorization n)) q
  · simp [factorization_eq_zero_iff, hpd]
    -- 🎉 no goals
  · simp [hqp, (factorization_le_iff_dvd hd0 hn0).2 hdn q]
    -- 🎉 no goals
#align nat.dvd_ord_compl_of_dvd_not_dvd Nat.dvd_ord_compl_of_dvd_not_dvd

/-- If `n` is a nonzero natural number and `p ≠ 1`, then there are natural numbers `e`
and `n'` such that `n'` is not divisible by `p` and `n = p^e * n'`. -/
theorem exists_eq_pow_mul_and_not_dvd {n : ℕ} (hn : n ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ e n' : ℕ, ¬p ∣ n' ∧ n = p ^ e * n' :=
  let ⟨a', h₁, h₂⟩ :=
    multiplicity.exists_eq_pow_mul_and_not_dvd
      (multiplicity.finite_nat_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩)
  ⟨_, a', h₂, h₁⟩
#align nat.exists_eq_pow_mul_and_not_dvd Nat.exists_eq_pow_mul_and_not_dvd

theorem dvd_iff_div_factorization_eq_tsub {d n : ℕ} (hd : d ≠ 0) (hdn : d ≤ n) :
    d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization := by
  refine' ⟨factorization_div, _⟩
  -- ⊢ factorization (n / d) = factorization n - factorization d → d ∣ n
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  -- ⊢ factorization (d / d) = factorization d - factorization d → d ∣ d
                                                    -- 🎉 no goals
  have h1 : n / d ≠ 0 := fun H => Nat.lt_asymm hd_lt_n ((Nat.div_eq_zero_iff hd.bot_lt).mp H)
  -- ⊢ factorization (n / d) = factorization n - factorization d → d ∣ n
  intro h
  -- ⊢ d ∣ n
  rw [dvd_iff_le_div_mul n d]
  -- ⊢ n ≤ n / d * d
  by_contra h2
  -- ⊢ False
  cases' exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2) with p hp
  -- ⊢ False
  rwa [factorization_mul h1 hd, add_apply, ← lt_tsub_iff_right, h, tsub_apply,
   lt_self_iff_false] at hp
#align nat.dvd_iff_div_factorization_eq_tsub Nat.dvd_iff_div_factorization_eq_tsub

theorem ord_proj_dvd_ord_proj_of_dvd {a b : ℕ} (hb0 : b ≠ 0) (hab : a ∣ b) (p : ℕ) :
    ord_proj[p] a ∣ ord_proj[p] b := by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  -- ⊢ p ^ ↑(factorization a) p ∣ p ^ ↑(factorization b) p
                                       -- 🎉 no goals
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  -- ⊢ p ^ ↑(factorization 0) p ∣ p ^ ↑(factorization b) p
                                          -- 🎉 no goals
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  -- ⊢ ↑(factorization a) p ≤ ↑(factorization b) p
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p
  -- 🎉 no goals
#align nat.ord_proj_dvd_ord_proj_of_dvd Nat.ord_proj_dvd_ord_proj_of_dvd

theorem ord_proj_dvd_ord_proj_iff_dvd {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ p : ℕ, ord_proj[p] a ∣ ord_proj[p] b) ↔ a ∣ b := by
  refine' ⟨fun h => _, fun hab p => ord_proj_dvd_ord_proj_of_dvd hb0 hab p⟩
  -- ⊢ a ∣ b
  rw [← factorization_le_iff_dvd ha0 hb0]
  -- ⊢ factorization a ≤ factorization b
  intro q
  -- ⊢ ↑(factorization a) q ≤ ↑(factorization b) q
  rcases le_or_lt q 1 with (hq_le | hq1)
  -- ⊢ ↑(factorization a) q ≤ ↑(factorization b) q
  · interval_cases q <;> simp
    -- ⊢ ↑(factorization a) 0 ≤ ↑(factorization b) 0
                         -- 🎉 no goals
                         -- 🎉 no goals
  exact (pow_dvd_pow_iff_le_right hq1).1 (h q)
  -- 🎉 no goals
#align nat.ord_proj_dvd_ord_proj_iff_dvd Nat.ord_proj_dvd_ord_proj_iff_dvd

theorem ord_compl_dvd_ord_compl_of_dvd {a b : ℕ} (hab : a ∣ b) (p : ℕ) :
    ord_compl[p] a ∣ ord_compl[p] b := by
  rcases em' p.Prime with (pp | pp)
  -- ⊢ a / p ^ ↑(factorization a) p ∣ b / p ^ ↑(factorization b) p
  · simp [pp, hab]
    -- 🎉 no goals
  rcases eq_or_ne b 0 with (rfl | hb0)
  -- ⊢ a / p ^ ↑(factorization a) p ∣ 0 / p ^ ↑(factorization 0) p
  · simp
    -- 🎉 no goals
  rcases eq_or_ne a 0 with (rfl | ha0)
  -- ⊢ 0 / p ^ ↑(factorization 0) p ∣ b / p ^ ↑(factorization b) p
  · cases hb0 (zero_dvd_iff.1 hab)
    -- 🎉 no goals
  have ha := (Nat.div_pos (ord_proj_le p ha0) (ord_proj_pos a p)).ne'
  -- ⊢ a / p ^ ↑(factorization a) p ∣ b / p ^ ↑(factorization b) p
  have hb := (Nat.div_pos (ord_proj_le p hb0) (ord_proj_pos b p)).ne'
  -- ⊢ a / p ^ ↑(factorization a) p ∣ b / p ^ ↑(factorization b) p
  rw [← factorization_le_iff_dvd ha hb, factorization_ord_compl a p, factorization_ord_compl b p]
  -- ⊢ Finsupp.erase p (factorization a) ≤ Finsupp.erase p (factorization b)
  intro q
  -- ⊢ ↑(Finsupp.erase p (factorization a)) q ≤ ↑(Finsupp.erase p (factorization b) …
  rcases eq_or_ne q p with (rfl | hqp)
  -- ⊢ ↑(Finsupp.erase q (factorization a)) q ≤ ↑(Finsupp.erase q (factorization b) …
  · simp
    -- 🎉 no goals
  simp_rw [erase_ne hqp]
  -- ⊢ ↑(factorization a) q ≤ ↑(factorization b) q
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q
  -- 🎉 no goals
#align nat.ord_compl_dvd_ord_compl_of_dvd Nat.ord_compl_dvd_ord_compl_of_dvd

theorem ord_compl_dvd_ord_compl_iff_dvd (a b : ℕ) :
    (∀ p : ℕ, ord_compl[p] a ∣ ord_compl[p] b) ↔ a ∣ b := by
  refine' ⟨fun h => _, fun hab p => ord_compl_dvd_ord_compl_of_dvd hab p⟩
  -- ⊢ a ∣ b
  rcases eq_or_ne b 0 with (rfl | hb0)
  -- ⊢ a ∣ 0
  · simp
    -- 🎉 no goals
  by_cases pa : a.Prime
  -- ⊢ a ∣ b
  case neg => simpa [pa] using h a
  -- ⊢ a ∣ b
  -- 🎉 no goals
  by_cases pb : b.Prime
  -- ⊢ a ∣ b
  case neg => simpa [pb] using h b
  -- ⊢ a ∣ b
  -- 🎉 no goals
  rw [prime_dvd_prime_iff_eq pa pb]
  -- ⊢ a = b
  by_contra hab
  -- ⊢ False
  apply pa.ne_one
  -- ⊢ a = 1
  rw [← Nat.dvd_one, ← Nat.mul_dvd_mul_iff_left hb0.bot_lt, mul_one]
  -- ⊢ b * a ∣ b
  simpa [Prime.factorization_self pb, Prime.factorization pa, hab] using h b
  -- 🎉 no goals
#align nat.ord_compl_dvd_ord_compl_iff_dvd Nat.ord_compl_dvd_ord_compl_iff_dvd

theorem dvd_iff_prime_pow_dvd_dvd (n d : ℕ) :
    d ∣ n ↔ ∀ p k : ℕ, Prime p → p ^ k ∣ d → p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ d ∣ 0 ↔ ∀ (p k : ℕ), Prime p → p ^ k ∣ d → p ^ k ∣ 0
  · simp
    -- 🎉 no goals
  rcases eq_or_ne d 0 with (rfl | hd)
  -- ⊢ 0 ∣ n ↔ ∀ (p k : ℕ), Prime p → p ^ k ∣ 0 → p ^ k ∣ n
  · simp only [zero_dvd_iff, hn, false_iff_iff, not_forall]
    -- ⊢ ∃ x x_1 h x_2, ¬x ^ x_1 ∣ n
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (lt_two_pow n).not_le⟩
    -- 🎉 no goals
  refine' ⟨fun h p k _ hpkd => dvd_trans hpkd h, _⟩
  -- ⊢ (∀ (p k : ℕ), Prime p → p ^ k ∣ d → p ^ k ∣ n) → d ∣ n
  rw [← factorization_prime_le_iff_dvd hd hn]
  -- ⊢ (∀ (p k : ℕ), Prime p → p ^ k ∣ d → p ^ k ∣ n) → ∀ (p : ℕ), Prime p → ↑(fact …
  intro h p pp
  -- ⊢ ↑(factorization d) p ≤ ↑(factorization n) p
  simp_rw [← pp.pow_dvd_iff_le_factorization hn]
  -- ⊢ p ^ ↑(factorization d) p ∣ n
  exact h p _ pp (ord_proj_dvd _ _)
  -- 🎉 no goals
#align nat.dvd_iff_prime_pow_dvd_dvd Nat.dvd_iff_prime_pow_dvd_dvd

theorem prod_prime_factors_dvd (n : ℕ) : (∏ p : ℕ in n.factors.toFinset, p) ∣ n := by
  by_cases hn : n = 0
  -- ⊢ ∏ p in toFinset (factors n), p ∣ n
  · subst hn
    -- ⊢ ∏ p in toFinset (factors 0), p ∣ 0
    simp
    -- 🎉 no goals
  simpa [prod_factors hn] using Multiset.toFinset_prod_dvd_prod (n.factors : Multiset ℕ)
  -- 🎉 no goals
#align nat.prod_prime_factors_dvd Nat.prod_prime_factors_dvd

theorem factorization_gcd {a b : ℕ} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
    (gcd a b).factorization = a.factorization ⊓ b.factorization := by
  let dfac := a.factorization ⊓ b.factorization
  -- ⊢ factorization (gcd a b) = factorization a ⊓ factorization b
  let d := dfac.prod Nat.pow
  -- ⊢ factorization (gcd a b) = factorization a ⊓ factorization b
  have dfac_prime : ∀ p : ℕ, p ∈ dfac.support → Prime p := by
    intro p hp
    have : p ∈ a.factors ∧ p ∈ b.factors := by simpa using hp
    exact prime_of_mem_factors this.1
  have h1 : d.factorization = dfac := prod_pow_factorization_eq_self dfac_prime
  -- ⊢ factorization (gcd a b) = factorization a ⊓ factorization b
  have hd_pos : d ≠ 0 := (factorizationEquiv.invFun ⟨dfac, dfac_prime⟩).2.ne'
  -- ⊢ factorization (gcd a b) = factorization a ⊓ factorization b
  suffices d = gcd a b by rwa [← this]
  -- ⊢ d = gcd a b
  apply gcd_greatest
  · rw [← factorization_le_iff_dvd hd_pos ha_pos, h1]
    -- ⊢ dfac ≤ factorization a
    exact inf_le_left
    -- 🎉 no goals
  · rw [← factorization_le_iff_dvd hd_pos hb_pos, h1]
    -- ⊢ dfac ≤ factorization b
    exact inf_le_right
    -- 🎉 no goals
  · intro e hea heb
    -- ⊢ e ∣ d
    rcases Decidable.eq_or_ne e 0 with (rfl | he_pos)
    -- ⊢ 0 ∣ d
    · simp only [zero_dvd_iff] at hea
      -- ⊢ 0 ∣ d
      contradiction
      -- 🎉 no goals
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea
    -- ⊢ e ∣ d
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb
    -- ⊢ e ∣ d
    simp [← factorization_le_iff_dvd he_pos hd_pos, h1, hea', heb']
    -- 🎉 no goals
#align nat.factorization_gcd Nat.factorization_gcd

theorem factorization_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).factorization = a.factorization ⊔ b.factorization := by
  rw [← add_right_inj (a.gcd b).factorization, ←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb), gcd_mul_lcm,
    factorization_gcd ha hb, factorization_mul ha hb]
  ext1
  -- ⊢ ↑(factorization a + factorization b) a✝ = ↑(factorization a ⊓ factorization  …
  exact (min_add_max _ _).symm
  -- 🎉 no goals
#align nat.factorization_lcm Nat.factorization_lcm

@[to_additive sum_factors_gcd_add_sum_factors_mul]
theorem prod_factors_gcd_mul_prod_factors_mul {β : Type*} [CommMonoid β] (m n : ℕ) (f : ℕ → β) :
    (m.gcd n).factors.toFinset.prod f * (m * n).factors.toFinset.prod f =
      m.factors.toFinset.prod f * n.factors.toFinset.prod f := by
  rcases eq_or_ne n 0 with (rfl | hm0)
  -- ⊢ Finset.prod (toFinset (factors (gcd m 0))) f * Finset.prod (toFinset (factor …
  · simp
    -- 🎉 no goals
  rcases eq_or_ne m 0 with (rfl | hn0)
  -- ⊢ Finset.prod (toFinset (factors (gcd 0 n))) f * Finset.prod (toFinset (factor …
  · simp
    -- 🎉 no goals
  rw [← @Finset.prod_union_inter _ _ m.factors.toFinset n.factors.toFinset, mul_comm]
  -- ⊢ Finset.prod (toFinset (factors (m * n))) f * Finset.prod (toFinset (factors  …
  congr
  -- ⊢ toFinset (factors (m * n)) = toFinset (factors m) ∪ toFinset (factors n)
  · apply factors_mul_toFinset <;> assumption
    -- ⊢ m ≠ 0
                                   -- 🎉 no goals
                                   -- 🎉 no goals
  · simp only [← support_factorization, factorization_gcd hn0 hm0, Finsupp.support_inf]
    -- 🎉 no goals
#align nat.prod_factors_gcd_mul_prod_factors_mul Nat.prod_factors_gcd_mul_prod_factors_mul
#align nat.sum_factors_gcd_add_sum_factors_mul Nat.sum_factors_gcd_add_sum_factors_mul

theorem setOf_pow_dvd_eq_Icc_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    { i : ℕ | i ≠ 0 ∧ p ^ i ∣ n } = Set.Icc 1 (n.factorization p) := by
  ext
  -- ⊢ x✝ ∈ {i | i ≠ 0 ∧ p ^ i ∣ n} ↔ x✝ ∈ Set.Icc 1 (↑(factorization n) p)
  simp [lt_succ_iff, one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]
  -- 🎉 no goals
#align nat.set_of_pow_dvd_eq_Icc_factorization Nat.setOf_pow_dvd_eq_Icc_factorization

/-- The set of positive powers of prime `p` that divide `n` is exactly the set of
positive natural numbers up to `n.factorization p`. -/
theorem Icc_factorization_eq_pow_dvd (n : ℕ) {p : ℕ} (pp : Prime p) :
    Icc 1 (n.factorization p) = (Ico 1 n).filter fun i : ℕ => p ^ i ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  -- ⊢ Icc 1 (↑(factorization 0) p) = Finset.filter (fun i => p ^ i ∣ 0) (Ico 1 0)
  · simp
    -- 🎉 no goals
  ext x
  -- ⊢ x ∈ Icc 1 (↑(factorization n) p) ↔ x ∈ Finset.filter (fun i => p ^ i ∣ n) (I …
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)
  -- 🎉 no goals
#align nat.Icc_factorization_eq_pow_dvd Nat.Icc_factorization_eq_pow_dvd

theorem factorization_eq_card_pow_dvd (n : ℕ) {p : ℕ} (pp : p.Prime) :
    n.factorization p = ((Ico 1 n).filter fun i => p ^ i ∣ n).card := by
  simp [← Icc_factorization_eq_pow_dvd n pp]
  -- 🎉 no goals
#align nat.factorization_eq_card_pow_dvd Nat.factorization_eq_card_pow_dvd

theorem Ico_filter_pow_dvd_eq {n p b : ℕ} (pp : p.Prime) (hn : n ≠ 0) (hb : n ≤ p ^ b) :
    ((Ico 1 n).filter fun i => p ^ i ∣ n) = (Icc 1 b).filter fun i => p ^ i ∣ n := by
  ext x
  -- ⊢ x ∈ Finset.filter (fun i => p ^ i ∣ n) (Ico 1 n) ↔ x ∈ Finset.filter (fun i  …
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  -- ⊢ p ^ x ∣ n → 1 ≤ x → (x < n ↔ x ≤ b)
  rintro h1 -
  -- ⊢ x < n ↔ x ≤ b
  simp [lt_of_pow_dvd_right hn pp.two_le h1,
    (pow_le_iff_le_right pp.two_le).1 ((le_of_dvd hn.bot_lt h1).trans hb)]
#align nat.Ico_filter_pow_dvd_eq Nat.Ico_filter_pow_dvd_eq

/-! ### Factorization and coprimes -/


/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_apply_of_coprime {p a b : ℕ} (hab : coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← factors_count_eq, perm_iff_count.mp (perm_factors_mul_of_coprime hab), count_append]
  -- 🎉 no goals
#align nat.factorization_mul_apply_of_coprime Nat.factorization_mul_apply_of_coprime

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_of_coprime {a b : ℕ} (hab : coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  -- ⊢ ↑(factorization (a * b)) q = ↑(factorization a + factorization b) q
  rw [Finsupp.add_apply, factorization_mul_apply_of_coprime hab]
  -- 🎉 no goals
#align nat.factorization_mul_of_coprime Nat.factorization_mul_of_coprime

/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
theorem factorization_eq_of_coprime_left {p a b : ℕ} (hab : coprime a b) (hpa : p ∈ a.factors) :
    (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab, ← factors_count_eq, ← factors_count_eq,
    count_eq_zero_of_not_mem (coprime_factors_disjoint hab hpa), add_zero]
#align nat.factorization_eq_of_coprime_left Nat.factorization_eq_of_coprime_left

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
theorem factorization_eq_of_coprime_right {p a b : ℕ} (hab : coprime a b) (hpb : p ∈ b.factors) :
    (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  -- ⊢ ↑(factorization (b * a)) p = ↑(factorization b) p
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb
  -- 🎉 no goals
#align nat.factorization_eq_of_coprime_right Nat.factorization_eq_of_coprime_right

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
theorem factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
    Disjoint a.factorization.support b.factorization.support := by
  simpa only [support_factorization] using
    disjoint_toFinset_iff_disjoint.mpr (coprime_factors_disjoint hab)
#align nat.factorization_disjoint_of_coprime Nat.factorization_disjoint_of_coprime

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
theorem factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
    (a * b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  rw [factorization_mul_of_coprime hab]
  -- ⊢ (factorization a + factorization b).support = (factorization a).support ∪ (f …
  exact support_add_eq (factorization_disjoint_of_coprime hab)
  -- 🎉 no goals
#align nat.factorization_mul_support_of_coprime Nat.factorization_mul_support_of_coprime

/-! ### Induction principles involving factorizations -/


/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimePow {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1)
    (h : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → P a → P (p ^ n * a)) : ∀ a : ℕ, P a := fun a =>
  Nat.strongRecOn a fun n =>
    match n with
    | 0 => fun _ => h0
    | 1 => fun _ => h1
    | k + 2 => fun hk => by
      let p := (k + 2).minFac
      -- ⊢ P (k + 2)
      have hp : Prime p := minFac_prime (succ_succ_ne_one k)
      -- ⊢ P (k + 2)
      -- the awkward `let` stuff here is because `factorization` is noncomputable (Finsupp);
      -- we get around this by using the computable `factors.count`, and rewriting when we want
      -- to use the `factorization` API
      let t := (k + 2).factors.count p
      -- ⊢ P (k + 2)
      have ht : t = (k + 2).factorization p := factors_count_eq
      -- ⊢ P (k + 2)
      have hpt : p ^ t ∣ k + 2 := by
        rw [ht]
        exact ord_proj_dvd _ _
      have htp : 0 < t := by
        rw [ht]
        exact hp.factorization_pos_of_dvd (Nat.succ_ne_zero _) (minFac_dvd _)
      convert h ((k + 2) / p ^ t) p t hp _ _ _ using 1
      · rw [Nat.mul_div_cancel' hpt]
        -- 🎉 no goals
      · rw [Nat.dvd_div_iff hpt, ← pow_succ, ht]
        -- ⊢ ¬p ^ succ (↑(factorization (k + 2)) p) ∣ k + 2
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
        -- 🎉 no goals
      · exact htp
        -- 🎉 no goals
      · apply hk _ (Nat.div_lt_of_lt_mul _)
        -- ⊢ k + 2 < p ^ t * (k + 2)
        rw [lt_mul_iff_one_lt_left Nat.succ_pos', one_lt_pow_iff htp.ne]
        -- ⊢ 1 < p
        exact hp.one_lt
        -- 🎉 no goals
        -- Porting note: was
        -- simp [lt_mul_iff_one_lt_left Nat.succ_pos', one_lt_pow_iff htp.ne, hp.one_lt]
#align nat.rec_on_prime_pow Nat.recOnPrimePow

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPosPrimePosCoprime {P : ℕ → Sort*} (hp : ∀ p n : ℕ, Prime p → 0 < n → P (p ^ n))
    (h0 : P 0) (h1 : P 1) (h : ∀ a b, 1 < a → 1 < b → coprime a b → P a → P b → P (a * b)) :
    ∀ a, P a :=
  recOnPrimePow h0 h1 <| by
    intro a p n hp' hpa hn hPa
    -- ⊢ P (p ^ n * a)
    by_cases ha1 : a = 1
    -- ⊢ P (p ^ n * a)
    · rw [ha1, mul_one]
      -- ⊢ P (p ^ n)
      exact hp p n hp' hn
      -- 🎉 no goals
    refine' h (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) _ _ (hp _ _ hp' hn) hPa
    -- ⊢ 1 < a
    · contrapose! hpa
      -- ⊢ p ∣ a
      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]
      -- 🎉 no goals
    simpa [hn, Prime.coprime_iff_not_dvd hp']
    -- 🎉 no goals
#align nat.rec_on_pos_prime_pos_coprime Nat.recOnPosPrimePosCoprime

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
def recOnPrimeCoprime {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, Prime p → P (p ^ n))
    (h : ∀ a b, 1 < a → 1 < b → coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
  recOnPosPrimePosCoprime (fun p n h _ => hp p n h) h0 (hp 2 0 prime_two) h
#align nat.rec_on_prime_coprime Nat.recOnPrimeCoprime

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_elim]
noncomputable def recOnMul {P : ℕ → Sort*} (h0 : P 0) (h1 : P 1) (hp : ∀ p, Prime p → P p)
    (h : ∀ a b, P a → P b → P (a * b)) : ∀ a, P a :=
  let hp : ∀ p n : ℕ, Prime p → P (p ^ n) := fun p n hp' =>
    n.recOn h1 (fun n hn => by rw [pow_succ]; apply h _ _ hn (hp p hp'))
                               -- ⊢ P (p ^ n * p)
                                              -- 🎉 no goals
    -- Porting note: was
    -- match n with
    -- | 0 => h1
    -- | n + 1 => h _ _ (hp p hp') (_match _)
  recOnPrimeCoprime h0 hp fun a b _ _ _ => h a b
#align nat.rec_on_mul Nat.recOnMul

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
    ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    -- ⊢ f (p ^ k) = Finsupp.prod (factorization (p ^ k)) fun p k => f (p ^ k)
    -- Porting note: replaced `simp` with `rw`
    rw [Prime.factorization_pow hp, Finsupp.prod_single_index _]
    -- ⊢ f (p ^ 0) = 1
    rwa [pow_zero]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · rintro -
    -- ⊢ f 1 = Finsupp.prod (factorization 1) fun p k => f (p ^ k)
    rw [factorization_one, hf]
    -- ⊢ 1 = Finsupp.prod 0 fun p k => f (p ^ k)
    simp
    -- 🎉 no goals
  · intro a b _ _ hab ha hb hab_pos
    -- ⊢ f (a * b) = Finsupp.prod (factorization (a * b)) fun p k => f (p ^ k)
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
      factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    convert factorization_disjoint_of_coprime hab
    -- 🎉 no goals
#align nat.multiplicative_factorization Nat.multiplicative_factorization

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization' {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
    ∀ {n : ℕ}, f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp -
    -- ⊢ f (p ^ k) = Finsupp.prod (factorization (p ^ k)) fun p k => f (p ^ k)
    simp only [hp.factorization_pow]
    -- ⊢ f (p ^ k) = Finsupp.prod (single p k) fun p k => f (p ^ k)
    rw [prod_single_index _]
    -- ⊢ f (p ^ 0) = 1
    simp [hf1]
    -- 🎉 no goals
  · simp [hf0]
    -- 🎉 no goals
  · rw [factorization_one, hf1]
    -- ⊢ 1 = Finsupp.prod 0 fun p k => f (p ^ k)
    simp
    -- 🎉 no goals
  · intro a b _ _ hab ha hb
    -- ⊢ f (a * b) = Finsupp.prod (factorization (a * b)) fun p k => f (p ^ k)
    rw [h_mult a b hab, ha, hb, factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    -- ⊢ _root_.Disjoint (factorization a).support (factorization b).support
    exact factorization_disjoint_of_coprime hab
    -- 🎉 no goals
#align nat.multiplicative_factorization' Nat.multiplicative_factorization'

/-- Two positive naturals are equal if their prime padic valuations are equal -/
theorem eq_iff_prime_padicValNat_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔ ∀ p : ℕ, p.Prime → padicValNat p a = padicValNat p b := by
  constructor
  -- ⊢ a = b → ∀ (p : ℕ), Prime p → padicValNat p a = padicValNat p b
  · rintro rfl
    -- ⊢ ∀ (p : ℕ), Prime p → padicValNat p a = padicValNat p a
    simp
    -- 🎉 no goals
  · intro h
    -- ⊢ a = b
    refine' eq_of_factorization_eq ha hb fun p => _
    -- ⊢ ↑(factorization a) p = ↑(factorization b) p
    by_cases pp : p.Prime
    -- ⊢ ↑(factorization a) p = ↑(factorization b) p
    · simp [factorization_def, pp, h p pp]
      -- 🎉 no goals
    · simp [factorization_eq_zero_of_non_prime, pp]
      -- 🎉 no goals
#align nat.eq_iff_prime_padic_val_nat_eq Nat.eq_iff_prime_padicValNat_eq

theorem prod_pow_prime_padicValNat (n : Nat) (hn : n ≠ 0) (m : Nat) (pr : n < m) :
    (∏ p in Finset.filter Nat.Prime (Finset.range m), p ^ padicValNat p n) = n := by
  -- Porting note: was `nth_rw_rhs`
  conv =>
    rhs
    rw [← factorization_prod_pow_eq_self hn]
  rw [eq_comm]
  -- ⊢ (Finsupp.prod (factorization n) fun x x_1 => x ^ x_1) = ∏ p in Finset.filter …
  apply Finset.prod_subset_one_on_sdiff
  · exact fun p hp =>
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (gt_of_gt_of_ge pr (le_of_mem_factorization hp)),
          prime_of_mem_factorization hp⟩
  · intro p hp
    -- ⊢ p ^ padicValNat p n = 1
    cases' Finset.mem_sdiff.mp hp with hp1 hp2
    -- ⊢ p ^ padicValNat p n = 1
    rw [← factorization_def n (Finset.mem_filter.mp hp1).2]
    -- ⊢ p ^ ↑(factorization n) p = 1
    simp [Finsupp.not_mem_support_iff.mp hp2]
    -- 🎉 no goals
  · intro p hp
    -- ⊢ (fun x x_1 => x ^ x_1) p (↑(factorization n) p) = p ^ padicValNat p n
    simp [factorization_def n (prime_of_mem_factorization hp)]
    -- 🎉 no goals
#align nat.prod_pow_prime_padic_val_nat Nat.prod_pow_prime_padicValNat

/-! ### Lemmas about factorizations of particular functions -/


-- TODO: Port lemmas from `Data/Nat/Multiplicity` to here, re-written in terms of `factorization`
/-- Exactly `n / p` naturals in `[1, n]` are multiples of `p`. -/
theorem card_multiples (n p : ℕ) : card ((Finset.range n).filter fun e => p ∣ e + 1) = n / p := by
  induction' n with n hn
  -- ⊢ card (Finset.filter (fun e => p ∣ e + 1) (Finset.range zero)) = zero / p
  · simp
    -- 🎉 no goals
  simp [Nat.succ_div, add_ite, add_zero, Finset.range_succ, filter_insert, apply_ite card,
    card_insert_of_not_mem, hn]
#align nat.card_multiples Nat.card_multiples

/-- Exactly `n / p` naturals in `(0, n]` are multiples of `p`. -/
theorem Ioc_filter_dvd_card_eq_div (n p : ℕ) : ((Ioc 0 n).filter fun x => p ∣ x).card = n / p := by
  induction' n with n IH
  -- ⊢ card (Finset.filter (fun x => p ∣ x) (Ioc 0 zero)) = zero / p
  · simp
    -- 🎉 no goals
  -- TODO: Golf away `h1` after Yaël PRs a lemma asserting this
  have h1 : Ioc 0 n.succ = insert n.succ (Ioc 0 n) := by
    rcases n.eq_zero_or_pos with (rfl | hn)
    · simp
    simp_rw [← Ico_succ_succ, Ico_insert_right (succ_le_succ hn.le), Ico_succ_right]
  simp [Nat.succ_div, add_ite, add_zero, h1, filter_insert, apply_ite card, card_insert_eq_ite, IH,
    Finset.mem_filter, mem_Ioc, not_le.2 (lt_add_one n), Nat.succ_eq_add_one]
#align nat.Ioc_filter_dvd_card_eq_div Nat.Ioc_filter_dvd_card_eq_div

end Nat
