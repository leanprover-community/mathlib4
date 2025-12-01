/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Factorization.PrimePow
/-!
# Miscellaneous arithmetic Functions

This file defines some simple examples of arithmetic functions (functions `ℕ → R` vanishing at
`0`, considered as a ring under Dirichlet convolution). Note that the Von Mangoldt and Möbius
functions are in separate files.

## Main Definitions

* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.

## Notation

The arithmetic functions `σ`, `ω` and `Ω` have Greek letter names.
This notation is scoped to the separate locales `ArithmeticFunction.sigma` for `σ`,
`ArithmeticFunction.omega` for `ω` and `ArithmeticFunction.Omega` for `Ω`, to allow for selective
access.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

section SpecialFunctions

open scoped zeta

section ProdPrimeFactors

/-- The map $n \mapsto \prod_{p \mid n} f(p)$ as an arithmetic function -/
def prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun d := if d = 0 then 0 else ∏ p ∈ d.primeFactors, f p
  map_zero' := if_pos rfl

open Batteries.ExtendedBinder

/-- `∏ᵖ p ∣ n, f p` is custom notation for `prodPrimeFactors f n` -/
scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x ↦ $r) $n)

@[simp]
theorem prodPrimeFactors_apply [CommMonoidWithZero R] {f : ℕ → R} {n : ℕ} (hn : n ≠ 0) :
    ∏ᵖ p ∣ n, f p = ∏ p ∈ n.primeFactors, f p :=
  if_neg hn

namespace IsMultiplicative

@[arith_mult]
theorem prodPrimeFactors [CommMonoidWithZero R] (f : ℕ → R) :
    IsMultiplicative (prodPrimeFactors f) := by
  rw [iff_ne_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, prodPrimeFactors_apply, primeFactors_one,
    prod_empty, true_and]
  intro x y hx hy hxy
  have hxy₀ : x * y ≠ 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀, prodPrimeFactors_apply hx, prodPrimeFactors_apply hy,
    primeFactors_mul hx hy, ← prod_union hxy.disjoint_primeFactors]

theorem prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : ℕ} (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f := f) (g := g)]
  rw [prod_add, mul_apply, sum_divisorsAntidiagonal (f · * g ·),
    ← divisors_filter_squarefree_of_squarefree hn, sum_divisors_filter_squarefree hn.ne_zero,
    factors_eq]
  apply sum_congr rfl
  intro t ht
  rw [t.prod_val, Function.id_def,
    ← prod_primeFactors_sdiff_of_squarefree hn (mem_powerset.mp ht),
    hf.map_prod_of_subset_primeFactors n t (mem_powerset.mp ht),
    ← hg.map_prod_of_subset_primeFactors n (_ \ t) sdiff_subset]

end IsMultiplicative

end ProdPrimeFactors

section Id

/-- The identity on `ℕ` as an `ArithmeticFunction`. -/
def id : ArithmeticFunction ℕ :=
  ⟨_root_.id, rfl⟩

@[simp]
theorem id_apply {x : ℕ} : id x = x :=
  rfl

@[arith_mult]
theorem isMultiplicative_id : IsMultiplicative ArithmeticFunction.id :=
  ⟨rfl, fun _ => rfl⟩

end Id

section Pow

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : ArithmeticFunction ℕ :=
  id.ppow k

@[simp]
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k <;> simp [pow]

theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp

theorem pow_one_eq_id : pow 1 = id := by
  ext n
  simp

@[arith_mult]
theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
end Pow

section Sigma

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

open scoped sigma

theorem sigma_apply {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl

@[simp]
theorem sigma_eq_zero {k n : ℕ} : σ k n = 0 ↔ n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]
theorem sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < n := by
  simp [pos_iff_ne_zero]

theorem sigma_apply_prime_pow {k p i : ℕ} (hp : p.Prime) :
    σ k (p ^ i) = ∑ j ∈ .range (i + 1), p ^ (j * k) := by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]

theorem sigma_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σ 1 (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp [sigma_apply_prime_pow hp]

theorem sigma_eq_sum_div (k n : ℕ) : sigma k n = ∑ d ∈ divisors n, (n / d) ^ k := by
  rw [sigma_apply, ← sum_div_divisors]

theorem sigma_zero_apply (n : ℕ) : σ 0 n = #n.divisors := by simp [sigma_apply]

theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  simp [sigma_apply_prime_pow hp]

@[simp]
theorem sigma_one (k : ℕ) : σ k 1 = 1 := by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]

theorem sigma_pos (k n : ℕ) (hn0 : n ≠ 0) : 0 < σ k n := by
  rwa [sigma_pos_iff, pos_iff_ne_zero]

theorem sigma_mono (k k' n : ℕ) (hk : k ≤ k') : σ k n ≤ σ k' n := by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd

theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  rw [sigma, zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]
theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

theorem sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul {k n : ℕ} (hn : n ≠ 0) :
    σ k n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), p ^ (i * k) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigma_apply_prime_pow <| prime_of_mem_primeFactors h

end Sigma

open scoped sigma

theorem _root_.Nat.card_divisors {n : ℕ} (hn : n ≠ 0) :
    #n.divisors = n.primeFactors.prod (n.factorization · + 1) := by
  rw [← sigma_zero_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_zero_apply_prime_pow <| prime_of_mem_primeFactors h

@[simp]
theorem _root_.Nat.divisors_card_eq_one_iff (n : ℕ) : #n.divisors = 1 ↔ n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

/-- `sigma_eq_one_iff` is to be preferred. -/
private theorem sigma_zero_eq_one_iff (n : ℕ) : σ 0 n = 1 ↔ n = 1 := by
  simp [sigma_zero_apply]

@[simp]
theorem sigma_eq_one_iff (k n : ℕ) : σ k n = 1 ↔ n = 1 := by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    lia
  · simp +contextual

theorem _root_.Nat.sum_divisors {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, d = ∏ p ∈ n.primeFactors, ∑ k ∈ .range (n.factorization p + 1), p ^ k := by
  rw [← sigma_one_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_one_apply_prime_pow <| prime_of_mem_primeFactors h

/-- `Ω n` is the number of prime factors of `n`. -/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

open scoped Omega

theorem cardFactors_apply {n : ℕ} : Ω n = n.primeFactorsList.length :=
  rfl

lemma cardFactors_zero : Ω 0 = 0 := by simp

@[simp] theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors_apply]

@[simp]
theorem cardFactors_eq_zero_iff_eq_zero_or_one {n : ℕ} : Ω n = 0 ↔ n = 0 ∨ n = 1 := by
  rw [cardFactors_apply, List.length_eq_zero_iff, primeFactorsList_eq_nil]

@[simp]
theorem cardFactors_pos_iff_one_lt {n : ℕ} : 0 < Ω n ↔ 1 < n := by
  rw [cardFactors_apply, List.length_pos_iff, primeFactorsList_ne_nil]

@[simp]
theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero, hx, List.prod_singleton]
  apply prime_of_mem_primeFactorsList
  rw [hx, List.mem_singleton]

theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]

theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp

lemma cardFactors_pow {m k : ℕ} : Ω (m ^ k) = k * Ω m := by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, cardFactors_mul (pow_ne_zero n hm) hm, ih]
    ring

@[simp]
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  simp [cardFactors_pow, hp]

theorem cardFactors_eq_sum_factorization {n : ℕ} :
    Ω n = n.factorization.sum fun _ k => k := by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

/-- `ω n` is the number of distinct prime factors of `n`. -/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

open scoped omega

theorem cardDistinctFactors_zero : ω 0 = 0 := by simp

@[simp]
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]

theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.primeFactorsList.dedup.length :=
  rfl

@[simp]
theorem cardDistinctFactors_eq_zero {n : ℕ} : ω n = 0 ↔ n ≤ 1 := by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]
theorem cardDistinctFactors_pos {n : ℕ} : 0 < ω n ↔ 1 < n := by simp [pos_iff_ne_zero]

theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList h0, cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]

theorem cardDistinctFactors_eq_one_iff {n : ℕ} : ω n = 1 ↔ IsPrimePow n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, isPrimePow_iff_card_primeFactors_eq_one,
    ← toFinset_factors, List.card_toFinset]

@[simp]
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 :=
  cardDistinctFactors_eq_one_iff.mpr <| hp.isPrimePow.pow hk

@[simp]
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]

theorem cardDistinctFactors_mul {m n : ℕ} (h : m.Coprime n) : ω (m * n) = ω m + ω n := by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
    coprime_primeFactorsList_disjoint h |>.dedup_append]

open scoped Function in
theorem cardDistinctFactors_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : (s : Set ι).Pairwise (Coprime on f)) : ω (∏ i ∈ s, f i) = ∑ i ∈ s, ω (f i) := by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, cardDistinctFactors_mul, ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi ha).symm

end SpecialFunctions

section Sum

theorem sum_Ioc_zeta (N : ℕ) : ∑ n ∈ Ioc 0 N, zeta n = N := by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x ∈ Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; lia]
  simp

variable {R : Type*} [Semiring R]

theorem sum_Ioc_mul_eq_sum_prod_filter (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, f x.1 * g x.2 := by
  simp only [mul_apply]
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ (by simp_all)

theorem sum_Ioc_mul_eq_sum_sum (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ n ∈ Ioc 0 N, f n * ∑ m ∈ Ioc 0 (N / n), g m := by
  rw [sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
  refine sum_congr rfl fun n hn ↦ ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by lia)]
  · intro hm
    grw [hm]
    simp [mul_div_le, div_le_self]

theorem sum_Ioc_mul_zeta_eq_sum (f : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * zeta) n = ∑ n ∈ Ioc 0 N, f n * ↑(N / n) := by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

--TODO: Dirichlet hyperbola method to get sums of length `sqrt N`
/-- An `O(N)` formula for the sum of the number of divisors function. -/
theorem sum_Ioc_sigma0_eq_sum_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, sigma 0 n = ∑ n ∈ Ioc 0 N, (N / n) := by
  rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

end Sum

end ArithmeticFunction

namespace Nat.Coprime

open ArithmeticFunction

theorem card_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors := by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

theorem sum_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

end Nat.Coprime

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.sigma`. -/
@[positivity ArithmeticFunction.sigma _ _]
meta def evalArithmeticFunctionSigma : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(ArithmeticFunction.sigma $k $n) =>
    let rn ← core z p n
    assumeInstancesCommute
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.sigma_pos_iff $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.sigma"


end Mathlib.Meta.Positivity
