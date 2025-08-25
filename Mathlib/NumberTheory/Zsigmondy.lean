/-
Copyright (c) 2022 Johan Commelin. All rights reserved.
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yury Kudryashov, Alex Best
-/
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.NormNum.Prime

/-!
## Zsigmondy's theorem

In this file I prove Zsigmondy's theorem in Number theory, which states that for natural number `n`
such that `2 ≤ n` and integers `0 < b < a` with `a` and `b` coprime, with the exceptions :
`n = 2` and `a + b` - a power of `2` and `(a, b, n) = (2, 1 6)`, there exists a prime `p` such
`p ∣ a ^ n - b ^ n` but for all `0 < k < n` we have `¬ p ∣ a ^ k - b ^ k`, i.e `a ^ n - b ^ n` has a
primitive prime divisor `p`.

Inspired by Mathlib 3 code at https://github.com/leanprover-community/mathlib3/tree/zsigmondy
-/

open Finset

protected theorem MvPolynomial.IsWeightedHomogeneous.expand {σ R M : Type*} [CommSemiring R]
    [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R} {n : M} (h : φ.IsWeightedHomogeneous w n)
    (p : ℕ) : (φ.expand p).IsWeightedHomogeneous w (p • n) := by
  classical
  intro m hm
  grw [← mem_support_iff, support_expand_subset, mem_image] at hm
  rcases hm with ⟨m, hm, rfl⟩
  rw [map_nsmul, h]
  rwa [← mem_support_iff]

protected nonrec theorem MvPolynomial.IsHomogeneous.expand {σ R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} {n : ℕ} (h : φ.IsHomogeneous n) (p : ℕ) :
    (φ.expand p).IsHomogeneous (p • n) :=
  h.expand p

theorem MvPolynomial.expand_mul_eq_comp {σ R : Type*} [CommSemiring R] (p q : ℕ) :
    expand (σ := σ) (R := R) (p * q) = (expand p).comp (expand q) := by
  ext1 i
  simp [pow_mul]

theorem MvPolynomial.expand_mul {σ R : Type*} [CommSemiring R] (p q : ℕ)
    (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p :=
  DFunLike.congr_fun (expand_mul_eq_comp p q) φ

open scoped BigOperators Nat

namespace Polynomial

variable {R : Type*} [CommSemiring R]

lemma homogenize_expand_mul (p : R[X]) (m n : ℕ) (h : p.natDegree ≤ n) :
    homogenize (expand R m p) (n * m) = .expand (σ := Fin 2) (R := R) m (homogenize p n) := by
  apply homogenize_eq_of_isHomogeneous
  · rw [mul_comm]
    apply MvPolynomial.IsHomogeneous.expand
    apply isHomogeneous_homogenize
  · rw [MvPolynomial.aeval_expand, aeval_homogenize_of_eq_one]
    · simp [← expand_aeval]
    · exact h
    · simp

end Polynomial

namespace MvPolynomial

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- Homogenized cyclotomic polynomial. -/
noncomputable def cyclotomic₂ (n : ℕ) (R : Type*) [CommRing R] :=
  (cyclotomic n R).homogenize (φ n)

@[simp]
lemma cyclotomic₂_zero : cyclotomic₂ 0 R = 1 := by simp [cyclotomic₂]

@[simp]
lemma cyclotomic₂_one : cyclotomic₂ 1 R = X 0 - X 1 := by simp [cyclotomic₂]

@[simp]
lemma cyclotomic₂_two : cyclotomic₂ 2 R = X 0 + X 1 := by simp [cyclotomic₂]

@[simp]
lemma cyclotomic₂_three : cyclotomic₂ 3 R = X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 := by
  have : φ 3 = 2 := rfl
  simp [cyclotomic₂, this]

@[simp]
lemma cyclotomic₂_six : cyclotomic₂ 6 R = X 0 ^ 2 - X 0 * X 1 + X 1 ^ 2 := by
  have : φ 6 = 2 := rfl
  simp [cyclotomic₂, this]

lemma cyclotomic₂_prime_pow_add_one {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cyclotomic₂ (p ^ (n + 1)) R =
      ∑ i ∈ .range p, X 0 ^ (p ^ n * i) * X 1 ^ (p ^ n * (p - 1 - i)) := by
  simp only [cyclotomic₂, hp, cyclotomic_prime_pow_eq_geom_sum, ← pow_mul,
    Nat.totient_prime_pow_succ, homogenize_finsetSum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mem_range] at hi
  rw [homogenize_X_pow, ← mul_tsub]
  gcongr
  omega

lemma cyclotomic₂_two_pow_add_one (n : ℕ) :
    cyclotomic₂ (2 ^ (n + 1)) R = X 0 ^ (2 ^ n) + X 1 ^ (2 ^ n) := by
  norm_num [cyclotomic₂_prime_pow_add_one, Finset.sum_range_succ']

@[simp]
lemma prod_divisors_cyclotomic₂ {n : ℕ} (hn : n ≠ 0) :
    ∏ d ∈ n.divisors, cyclotomic₂ d R = .X 0 ^ n - .X 1 ^ n := by
  unfold cyclotomic₂
  rw [← homogenize_finsetProd, prod_cyclotomic_eq_X_pow_sub_one, homogenize_sub, homogenize_X_pow,
    homogenize_one]
  · simp [Nat.sum_totient]
  · simp [Nat.sum_totient]
  · rwa [pos_iff_ne_zero]
  · exact fun _ _ ↦ natDegree_cyclotomic_le

@[simp]
lemma prod_divisors_eval_cyclotomic₂ {n : ℕ} (hn : n ≠ 0) (a b : R) :
    ∏ d ∈ n.divisors, eval ![a, b] (cyclotomic₂ d R) = a ^ n - b ^ n := by
  simp [← eval_prod, hn]

lemma cyclotomic₂_dvd_pow_sub_pow (n : ℕ) : cyclotomic₂ n R ∣ X 0 ^ n - X 1 ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [← prod_divisors_cyclotomic₂ hn]
    apply Finset.dvd_prod_of_mem
    simpa

lemma cyclotomic₂_mul_prime_of_dvd {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    cyclotomic₂ (n * p) R = expand p (R := R) (cyclotomic₂ n R) := by
  rw [cyclotomic₂, ← cyclotomic_expand_eq_cyclotomic hp hpn,
    mul_comm n p, Nat.totient_mul_of_prime_of_dvd hp hpn, mul_comm,
    homogenize_expand_mul, cyclotomic₂]
  apply natDegree_cyclotomic_le

lemma cyclotomic₂_mul_prime_pow_of_dvd {n p k : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    cyclotomic₂ (n * p ^ k) R = expand (p ^ k) (R := R) (cyclotomic₂ n R) := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [pow_succ, ← mul_assoc, cyclotomic₂_mul_prime_of_dvd hp, ihk, ← expand_mul, mul_comm]
    exact dvd_mul_of_dvd_left hpn _

lemma cyclotomic₂_mul_prime_mul_cyclotomic₂_of_not_dvd {n p : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) :
    cyclotomic₂ (n * p) R * cyclotomic₂ n R = expand p (R := R) (cyclotomic₂ n R) := by
  conv_rhs =>
    rw [cyclotomic₂, ← homogenize_expand_mul _ _ _ natDegree_cyclotomic_le]
  rw [cyclotomic_expand_eq_cyclotomic_mul hp hpn, cyclotomic₂, cyclotomic₂,
    ← homogenize_mul, mul_comm n p, Nat.totient_mul_of_prime_of_not_dvd, tsub_mul, one_mul,
    tsub_add_cancel_of_le, mul_comm (φ n)]
  · exact le_mul_of_one_le_left (zero_le _) hp.one_lt.le
  all_goals apply_rules [natDegree_cyclotomic_le]

lemma cyclotomic₂_mul_prime_pow_mul_of_not_dvd {n p k : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) :
    cyclotomic₂ (n * p ^ (k + 1)) R * expand (p ^ k) (R := R) (cyclotomic₂ n R) =
      expand (p ^ (k + 1)) (R := R) (cyclotomic₂ n R) := by
  rw [pow_succ', ← mul_assoc, cyclotomic₂_mul_prime_pow_of_dvd hp (dvd_mul_left _ _), ← map_mul,
    cyclotomic₂_mul_prime_mul_cyclotomic₂_of_not_dvd hp hpn, ← expand_mul, mul_comm]

variable {S : Type*} [CommRing S]

@[simp]
lemma map_cyclotomic₂ (f : R →+* S) (n : ℕ) : map f (cyclotomic₂ n R) = cyclotomic₂ n S := by
  rw [cyclotomic₂, ← homogenize_map, map_cyclotomic, cyclotomic₂]

lemma map_cyclotomic₂_eval (f : R →+* S) (n : ℕ) (x : Fin 2 → R) :
    f (eval x (cyclotomic₂ n R)) = eval (f ∘ x) (cyclotomic₂ n S) := by
  rw [← map_cyclotomic₂ f, MvPolynomial.eval₂_comp, eval_map]

lemma intCast_cyclotomic₂_eval (n : ℕ) (x : Fin 2 → ℤ) :
    ↑(eval x (cyclotomic₂ n ℤ)) = eval ((↑) ∘ x) (cyclotomic₂ n R) :=
  map_cyclotomic₂_eval (Int.castRingHom R) n x

lemma eval₂_cyclotomic₂_dvd_pow_sub_pow {n : ℕ} (f : R →+* S) (x : Fin 2 → S) :
    eval₂ f x (cyclotomic₂ n R) ∣ x 0 ^ n - x 1 ^ n := calc
  eval₂ f x (cyclotomic₂ n R) ∣ eval₂ f x (X 0 ^ n - X 1 ^ n) := by
    gcongr
    apply cyclotomic₂_dvd_pow_sub_pow
  _ = x 0 ^ n - x 1 ^ n := by simp

lemma eval_cyclotomic₂_dvd_pow_sub_pow {n : ℕ} (x : Fin 2 → R) :
    eval x (cyclotomic₂ n R) ∣ x 0 ^ n - x 1 ^ n :=
  eval₂_cyclotomic₂_dvd_pow_sub_pow ..

lemma eval_cyclotomic₂_vec_dvd_pow_sub_pow {n : ℕ} (a b : R) :
    eval ![a, b] (cyclotomic₂ n R) ∣ a ^ n - b ^ n :=
  eval_cyclotomic₂_dvd_pow_sub_pow ![a, b]

end CommRing

section Field

variable {K : Type*} [Field K]

lemma eval_cyclotomic₂ (n : ℕ) (x : Fin 2 → K) (hx : x 1 ≠ 0) :
    eval x (cyclotomic₂ n K) = (cyclotomic n K).eval (x 0 / x 1) * x 1 ^ φ n := by
  rw [cyclotomic₂, eval_homogenize natDegree_cyclotomic_le _ hx]

lemma eval_cyclotomic₂_vec (n : ℕ) (a : K) {b : K} (hb : b ≠ 0) :
    eval ![a, b] (cyclotomic₂ n K) = (cyclotomic n K).eval (a / b) * b ^ φ n :=
  eval_cyclotomic₂ n ![a, b] hb

end Field

section Real

variable {n : ℕ} {a b : ℝ}

-- TODO: can we unify `Int` and `Real` inequalities?
lemma sub_pow_totient_lt_eval_cyclotomic₂_real (hn : 1 < n) (hab : b < a) (hb : 0 < b) :
    (a - b) ^ φ n < eval ![a, b] (cyclotomic₂ n ℝ) := calc
  (a - b) ^ φ n = (a / b - 1) ^ φ n * b ^ φ n := by simp [← mul_pow, hb.ne', sub_mul]
  _ < _ := by
    rw [eval_cyclotomic₂_vec n a hb.ne']
    gcongr
    apply sub_one_pow_totient_lt_cyclotomic_eval
    · omega
    · rwa [one_lt_div hb]

-- TODO: what are the right assumptions?
lemma sub_pow_totient_le_eval_cyclotomic₂_real (hab : b < a) (hb : 0 < b) :
    (a - b) ^ φ n ≤ eval ![a, b] (cyclotomic₂ n ℝ) := by
  cases le_or_gt n 1 with
  | inl h =>
    interval_cases n <;> simp
  | inr h =>
    exact (sub_pow_totient_lt_eval_cyclotomic₂_real h hab hb).le

lemma eval_cyclotomic₂_lt_add_pow_totient_real (hn : 2 < n) (hab : b < a) (hb : 0 < b) :
    eval ![a, b] (cyclotomic₂ n ℝ) < (a + b) ^ φ n := calc
  eval ![a, b] (cyclotomic₂ n ℝ) = (cyclotomic n ℝ).eval (a / b) * b ^ φ n :=
    eval_cyclotomic₂_vec n a hb.ne'
  _ < (a / b + 1) ^ φ n * b ^ φ n := by
    gcongr
    apply cyclotomic_eval_lt_add_one_pow_totient
    · assumption
    · rwa [one_lt_div hb]
  _ = (a + b) ^ φ n := by
    simp [← mul_pow, add_mul, hb.ne']

lemma eval_cyclotomic₂_le_add_pow_totient_real (hab : b < a) (hb : 0 < b) :
    eval ![a, b] (cyclotomic₂ n ℝ) ≤ (a + b) ^ φ n := by
  cases le_or_gt n 2 with
  | inl h =>
    interval_cases n <;> simp [add_assoc, hb.le]
  | inr h =>
    exact eval_cyclotomic₂_lt_add_pow_totient_real h hab hb |>.le

end Real

section Int

variable {n : ℕ} {a b : ℤ}

lemma sub_pow_totient_lt_eval_cyclotomic₂_int (hn : 1 < n) (hab : b < a) (hb : 0 < b) :
    (a - b) ^ φ n < eval ![a, b] (cyclotomic₂ n ℤ) := by
  rify at hab hb ⊢
  rw [intCast_cyclotomic₂_eval]
  convert sub_pow_totient_lt_eval_cyclotomic₂_real hn hab hb
  ext i; fin_cases i <;> rfl

lemma sub_pow_totient_le_eval_cyclotomic₂_int (hab : b < a) (hb : 0 < b) :
    (a - b) ^ φ n ≤ eval ![a, b] (cyclotomic₂ n ℤ) := by
  rify at hab hb ⊢
  rw [intCast_cyclotomic₂_eval]
  convert sub_pow_totient_le_eval_cyclotomic₂_real hab hb
  ext i; fin_cases i <;> rfl

lemma eval_cyclotomic₂_pos_int (hab : b < a) (hb : 0 < b) :
    0 < eval ![a, b] (cyclotomic₂ n ℤ) := by
  refine lt_of_lt_of_le ?_ (sub_pow_totient_le_eval_cyclotomic₂_int hab hb)
  rw [← sub_pos] at hab
  positivity

lemma eval_cyclotomic₂_lt_add_pow_totient_int (hn : 2 < n) (hab : b < a) (hb : 0 < b) :
    eval ![a, b] (cyclotomic₂ n ℤ) < (a + b) ^ φ n := by
  rify at hab hb ⊢
  rw [intCast_cyclotomic₂_eval]
  convert eval_cyclotomic₂_lt_add_pow_totient_real hn hab hb
  ext i; fin_cases i <;> rfl

lemma eval_cyclotomic₂_le_add_pow_totient_int (hab : b < a) (hb : 0 < b) :
    eval ![a, b] (cyclotomic₂ n ℤ) ≤ (a + b) ^ φ n := by
  rify at hab hb ⊢
  rw [intCast_cyclotomic₂_eval]
  convert eval_cyclotomic₂_le_add_pow_totient_real hab hb
  ext i; fin_cases i <;> rfl

end Int

end MvPolynomial

@[to_additive (attr := nontriviality)]
lemma Subsingleton.orderOf_eq {M : Type*} [Monoid M] [Subsingleton M] {x : M} :
    orderOf x = 1 := by
  rw [Subsingleton.elim x 1, orderOf_one]

@[to_additive]
lemma IsUnit.orderOf_eq_one {M : Type*} [Monoid M] [Subsingleton Mˣ] {x : M} (h : IsUnit x) :
    orderOf x = 1 := by
  rw [← h.unit_spec, orderOf_units, Subsingleton.orderOf_eq]

lemma multiplicity_eq_padicValInt {p : ℕ} {n : ℤ} (hp : p ≠ 1) (hn : n ≠ 0) :
    multiplicity (p : ℤ) n = padicValInt p n := by
  simp [padicValInt.of_ne_one_ne_zero hp hn]

lemma emultiplicity_eq_padicValInt {p : ℕ} {n : ℤ} (hp : p ≠ 1) (hn : n ≠ 0) :
    emultiplicity (p : ℤ) n = padicValInt p n := by
  rw [← multiplicity_eq_padicValInt hp hn, FiniteMultiplicity.emultiplicity_eq_multiplicity]
  simp [Int.finiteMultiplicity_iff, *]

lemma multiplicity_eq_padicValNat {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    multiplicity p n = padicValNat p n := by
  simp [padicValNat_def', *]

lemma emultiplicity_eq_padicValNat {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    emultiplicity p n = padicValNat p n := by
  rw [FiniteMultiplicity.emultiplicity_eq_multiplicity, multiplicity_eq_padicValNat] <;>
    simp [Nat.finiteMultiplicity_iff, pos_iff_ne_zero, *]

lemma abs_eq_abs_of_pow_eq_pow {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : R} {n : ℕ} (h : a ^ n = b ^ n) (hn₀ : n ≠ 0) : |a| = |b| := by
  rw [← pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hn₀, ← abs_pow, h, abs_pow]

lemma eq_or_eq_neg_and_even_of_pow_eq_pow {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b : R} {n : ℕ} (h : a ^ n = b ^ n) (hn₀ : n ≠ 0) :
    a = b ∨ (a = -b ∧ Even n) := by
  cases Nat.even_or_odd n with
  | inl hn =>
    simpa [hn, abs_eq_abs] using abs_eq_abs_of_pow_eq_pow h hn₀
  | inr hn =>
    left
    rwa [← hn.strictMono_pow.injective.eq_iff]

lemma ZMod.ofNat_eq_zero_iff {m n : ℕ} [m.AtLeastTwo] :
    (no_index(OfNat.ofNat m) : ZMod n) = 0 ↔ n ∣ OfNat.ofNat m := by
  rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]

lemma Odd.intCast_zmod_two {n : ℤ} (hn : Odd n) : (n : ZMod 2) = 1 := by
  rcases hn with ⟨m, rfl⟩
  simp [ZMod.ofNat_eq_zero_iff]

lemma Odd.natCast_zmod_two {n : ℕ} (hn : Odd n) : (n : ZMod 2) = 1 := by
  rcases hn with ⟨m, rfl⟩
  simp [ZMod.ofNat_eq_zero_iff]

lemma Odd.multiplicity_two_eq_zero_nat {n : ℕ} (hn : Odd n) : multiplicity 2 n = 0 := by
  rwa [multiplicity_eq_zero, ← even_iff_two_dvd, Nat.not_even_iff_odd]

lemma Odd.emultiplicity_two_eq_zero_nat {n : ℕ} (hn : Odd n) : emultiplicity 2 n = 0 := by
  rw [emultiplicity_eq_zero_iff_multiplicity_eq_zero, hn.multiplicity_two_eq_zero_nat]

lemma Odd.multiplicity_two_eq_zero_int {n : ℤ} (hn : Odd n) : multiplicity 2 n = 0 := by
  rwa [multiplicity_eq_zero, ← even_iff_two_dvd, Int.not_even_iff_odd]

/-- *Lifting the exponent* lemma for `p = 2` and odd `n`. -/
lemma Int.emultiplicity_two_pow_sub_pow_of_odd {x y : ℤ} {n : ℕ} (hx : Odd x) (hy : Odd y)
    (hn : Odd n) : emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) := by
  rw [← geom_sum₂_mul, emultiplicity_mul (by decide), emultiplicity_eq_zero.mpr, zero_add]
  rw [← Nat.cast_ofNat, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [hx.intCast_zmod_two, hy.intCast_zmod_two, hn.natCast_zmod_two]

/-- *Lifting the exponent* lemma for `p = 2` and odd `n`. -/
lemma Int.multiplicity_two_pow_sub_pow_of_odd {x y : ℤ} {n : ℕ} (hx : Odd x) (hy : Odd y)
    (hn : Odd n) : multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) := by
  simp only [multiplicity, emultiplicity_two_pow_sub_pow_of_odd hx hy hn]

/-- *Lifting the exponent* lemma, a version that assumes that either `p` or `n` is odd. -/
theorem Int.emultiplicity_pow_sub_pow' {p : ℕ} (hp : p.Prime) {x y : ℤ} (hxy : ↑p ∣ x - y)
    (hx : ¬↑p ∣ x) (n : ℕ) (hodd : Odd p ∨ Odd n) :
    emultiplicity (↑p) (x ^ n - y ^ n) = emultiplicity (↑p) (x - y) + emultiplicity p n := by
  rcases hp.eq_two_or_odd' with rfl | hpo
  · replace hodd : Odd n := hodd.resolve_left (by decide)
    replace hx : Odd x := by
      simpa [← Int.not_even_iff_odd, even_iff_two_dvd] using hx
    have hy : Odd y := by
      simp_all [← Int.not_even_iff_odd, ← even_iff_two_dvd, Int.even_sub]
    rw [Nat.cast_ofNat, Int.emultiplicity_two_pow_sub_pow_of_odd,
      hodd.emultiplicity_two_eq_zero_nat, add_zero] <;> assumption
  · apply emultiplicity_pow_sub_pow hp hpo hxy hx

/-- *Lifting the exponent* lemma, a version that assumes that either `p` or `n` is odd. -/
theorem Int.multiplicity_pow_sub_pow' {p : ℕ} (hp : p.Prime) {x y : ℤ} (hxy : ↑p ∣ x - y)
    (hx : ¬↑p ∣ x) (hne : x ≠ y) {n : ℕ} (hn : n ≠ 0) (hodd : Odd p ∨ Odd n) :
    multiplicity (↑p) (x ^ n - y ^ n) = multiplicity (↑p) (x - y) + multiplicity p n := by
  unfold multiplicity
  rw [emultiplicity_pow_sub_pow' hp hxy hx n hodd, WithTop.untopD_add]
  all_goals rw [ne_eq, emultiplicity_eq_top]
  all_goals simp [Nat.finiteMultiplicity_iff, Int.finiteMultiplicity_iff, sub_eq_zero, *, hp.ne_one]

-- TODO: add a version for `p = 2`
/-- *Lifting the exponent* lemma in the case if either the prime or the exponent is odd,
stated in terms of `padicValInt`. -/
lemma padicValInt_pow_sub_pow {p n : ℕ} [Fact p.Prime] (hpo : Odd p ∨ Odd n) {x y : ℤ} (hne : x ≠ y)
    (hmodEq : x ≡ y [ZMOD p]) (hpx : ¬↑p ∣ x) (hn : n ≠ 0) :
    padicValInt p (x ^ n - y ^ n) = padicValInt p (x - y) + padicValNat p n := by
  have hp : p.Prime := Fact.out
  rw [Int.modEq_comm, Int.modEq_iff_dvd] at hmodEq
  apply Nat.cast_injective (R := ENat)
  rw [← emultiplicity_eq_padicValInt, Nat.cast_add, ← emultiplicity_eq_padicValInt,
    ← emultiplicity_eq_padicValNat, Int.emultiplicity_pow_sub_pow']
  any_goals first | assumption | exact hp.ne_one
  · rwa [sub_ne_zero]
  · rw [sub_ne_zero]
    intro h
    rcases eq_or_eq_neg_and_even_of_pow_eq_pow h.symm hn with rfl | ⟨rfl, heven⟩
    · exact hne rfl
    · rw [sub_neg_eq_add, ← two_mul, (Nat.prime_iff_prime_int.mp hp).dvd_mul] at hmodEq
      refine hmodEq.elim ?_ hpx
      rw [← Nat.cast_ofNat, Int.ofNat_dvd, Nat.prime_two.dvd_iff_eq hp.ne_one]
      rintro rfl
      norm_num [Nat.not_odd_iff_even.mpr heven] at hpo

lemma padicValInt_two_pow_two_pow_add_pow_two_pow_of_zmodEq_four {a b : ℤ} (ha : Odd a)
    (hab : a ≡ b [ZMOD 4]) (i : ℕ) : padicValInt 2 (a ^ 2 ^ i + b ^ 2 ^ i) = 1 := by
  apply Nat.cast_injective (R := ENat)
  rw [← emultiplicity_eq_padicValInt, Nat.cast_ofNat, Int.two_pow_two_pow_add_two_pow_two_pow]
  · rwa [← even_iff_two_dvd, Int.not_even_iff_odd]
  · rwa [← Int.modEq_iff_dvd, Int.modEq_comm]
  · decide
  · cases i with
    | zero =>
      suffices a + b ≠ 0 by simpa
      contrapose! ha
      rw [← Int.not_even_iff_odd, not_not, even_iff_two_dvd, ← mul_dvd_mul_iff_left two_ne_zero]
      calc
        2 * 2 = 4 := by norm_num1
        _ ∣ a + b + (a - b) := dvd_add (by simp [ha]) hab.symm.dvd
        _ = 2 * a := by ring
    | succ i =>
      simp only [pow_succ' _ i, pow_mul]
      have : a ≠ 0 := by rintro rfl; simp at ha
      positivity

lemma padicValInt_two_pow_two_pow_add_pow_two_pow_of_ne_zero {a b : ℤ} (ha : Odd a) (hb : Odd b)
    {i : ℕ} (hi : i ≠ 0) : padicValInt 2 (a ^ 2 ^ i + b ^ 2 ^ i) = 1 := by
  cases i with
  | zero => simp at hi
  | succ i =>
    simp only [pow_succ' _ i, pow_mul]
    apply padicValInt_two_pow_two_pow_add_pow_two_pow_of_zmodEq_four
    · exact ha.pow
    · rw [Int.ModEq, Int.sq_mod_four_eq_one_of_odd ha, Int.sq_mod_four_eq_one_of_odd hb]

@[simp]
lemma orderOf_zero (M : Type*) [MonoidWithZero M] [Nontrivial M] : orderOf (0 : M) = 0 := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn₀, hn⟩
  simp [hn₀.ne'] at hn

@[simp]
lemma Units.isOfFinOrder_val {M : Type*} [Monoid M] {u : Mˣ} :
    IsOfFinOrder u.val ↔ IsOfFinOrder u :=
  Function.Injective.isOfFinOrder_iff (f := Units.coeHom M) (by
    intro x y h
    simp at h
    exact_mod_cast h
  )

lemma isOfFinOrder_iff_isUnit {M : Type*} [Monoid M] [Finite Mˣ] {x : M} :
    IsOfFinOrder x ↔ IsUnit x := by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

lemma orderOf_eq_zero_iff_eq_zero {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a : G₀} :
    orderOf a = 0 ↔ a = 0 := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_iff_isUnit, isUnit_iff_ne_zero, ne_eq, not_not]

lemma prime_not_dvd_pow_sub_pow_of_not_orderOf_dvd {p n : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpb : ¬↑p ∣ b) (hn : ¬orderOf (a / b : ZMod p) ∣ n) :
    ¬↑p ∣ a ^ n - b ^ n := by
  intro hp_dvd
  have : (a ^ n : ZMod p) = b ^ n := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at hp_dvd
    exact mod_cast hp_dvd.symm
  have : (a / b : ZMod p) ^ n = 1 := by
    have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [div_pow, this, div_self]
    exact pow_ne_zero _ hpb'
  exact hn <| orderOf_dvd_of_pow_eq_one this

lemma prime_not_dvd_eval_cyclotomic₂_of_not_orderOf_dvd {p n : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpb : ¬↑p ∣ b) (hn : ¬orderOf (a / b : ZMod p) ∣ n) :
    ¬↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := by
  intro hp_dvd
  apply prime_not_dvd_pow_sub_pow_of_not_orderOf_dvd hpb hn
  refine hp_dvd.trans ?_
  apply MvPolynomial.eval_cyclotomic₂_vec_dvd_pow_sub_pow

lemma padicValInt_cyclotomic₂_of_orderOf_eq {p n : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpa : ¬↑p ∣ a) (hpb : ¬↑p ∣ b) (hab : |a| ≠ |b|) (hn : orderOf (a / b : ZMod p) = n) :
    padicValInt p (MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) =
      padicValInt p (a ^ n - b ^ n) := by
  have hp : p.Prime := Fact.out
  have hpa' : (a : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hn_dvd : n ∣ p - 1 := by
    rw [← hn]
    apply ZMod.orderOf_dvd_card_sub_one (div_ne_zero hpa' hpb')
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp [hp.one_lt.not_ge, tsub_eq_zero_iff_le] at hn_dvd
  replace hab : a ^ n - b ^ n ≠ 0 :=
    sub_ne_zero.mpr <| mt (abs_eq_abs_of_pow_eq_pow · hn₀) hab
  have Hcyc₀ : ∀ d, d ∣ n → MvPolynomial.eval ![a, b] (.cyclotomic₂ d ℤ) ≠ 0 := by
    rw [← MvPolynomial.prod_divisors_eval_cyclotomic₂ hn₀, Finset.prod_ne_zero_iff] at hab
    exact fun d hd ↦ hab d <| Nat.mem_divisors.mpr ⟨hd, hn₀⟩
  rw [← MvPolynomial.prod_divisors_eval_cyclotomic₂ hn₀, ← Nat.cons_self_properDivisors hn₀,
    Finset.prod_cons, padicValInt.mul, left_eq_add]
  · apply padicValInt.eq_zero_of_not_dvd
    rw [(Nat.prime_iff_prime_int.mp hp).dvd_finset_prod_iff]
    rintro ⟨d, hdn, hpd⟩
    rw [Nat.mem_properDivisors] at hdn
    have hd₀ : 0 < d := by
      exact Nat.pos_of_dvd_of_pos hdn.1 (pos_iff_ne_zero.2 hn₀)
    refine prime_not_dvd_eval_cyclotomic₂_of_not_orderOf_dvd ?_ ?_ hpd
    any_goals assumption
    exact Nat.not_dvd_of_pos_of_lt hd₀ (hn ▸ hdn.2)
  · apply Hcyc₀
    rfl
  · simp only [Finset.prod_ne_zero_iff, Nat.mem_properDivisors]
    rintro d ⟨hd_dvd, -⟩
    apply Hcyc₀
    assumption

lemma padicValInt_cyclotomic₂_orderOf {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpa : ¬↑p ∣ a) (hpb : ¬↑p ∣ b) (hab : |a| ≠ |b|) :
    padicValInt p (MvPolynomial.eval ![a, b] (.cyclotomic₂ (orderOf (a / b : ZMod p)) ℤ)) =
      padicValInt p (a ^ (orderOf (a / b : ZMod p)) - b ^ (orderOf (a / b : ZMod p))) :=
  padicValInt_cyclotomic₂_of_orderOf_eq hpa hpb hab rfl

lemma padicValInt_prod {ι : Type*} {s : Finset ι} {f : ι → ℤ} (p : ℕ) [Fact p.Prime]
    (h : ∀ i ∈ s, f i ≠ 0) : padicValInt p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValInt p (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ihs =>
    simp only [forall_mem_cons, prod_cons, sum_cons] at h ⊢
    rw [padicValInt.mul h.1 (prod_ne_zero_iff.mpr h.2), ihs h.2]

lemma padicValInt_div (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : b ∣ a) :
    padicValInt p (a / b) = padicValInt p a - padicValInt p b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · apply eq_tsub_of_add_eq
    rw [← padicValInt.mul _ (ne_zero_of_dvd_ne_zero ha h), Int.ediv_mul_cancel h]
    exact ne_zero_of_dvd_ne_zero ha (Int.ediv_dvd_of_dvd h)

lemma padicValNat_of_le_one {p : ℕ} (hp : p ≤ 1) (a : ℕ) : padicValNat p a = 0 := by
  rw [padicValNat.padicValNat_eq_maxPowDiv, Nat.maxPowDiv, Nat.maxPowDiv.go, if_neg]
  simp [hp.not_gt]

@[gcongr]
lemma padicValNat_mono (p : ℕ) {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b := by
  rcases le_or_gt p 1 with hp₁ | hp₁
  · simp [padicValNat_of_le_one hp₁]
  · simp only [padicValNat.padicValNat_eq_maxPowDiv]
    apply Nat.maxPowDiv.le_of_dvd hp₁ (by simp [hb])
    refine dvd_trans ?_ h
    apply Nat.maxPowDiv.pow_dvd

@[gcongr]
lemma padicValInt_mono (p : ℕ) {a b : ℤ} (h : a ∣ b) (hb : b ≠ 0) :
    padicValInt p a ≤ padicValInt p b := by
  apply padicValNat_mono <;> simp [*]

-- TODO: what happens if `|a| = |b|`?
lemma padicValInt_cyclotomic₂_pow_mul_orderOf {p β : ℕ} [Fact p.Prime] {a b : ℤ} (hpo : Odd p)
    (hpa : ¬↑p ∣ a) (hpb : ¬↑p ∣ b) (hab : |a| ≠ |b|) (hβ : β ≠ 0) :
    padicValInt p (MvPolynomial.eval ![a, b]
      (.cyclotomic₂ (p ^ β * orderOf (a / b : ZMod p)) ℤ)) = 1 := by
  generalize hk : orderOf (a / b : ZMod p) = k
  have hp : p.Prime := Fact.out
  have hpa' : (a : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hk_dvd : k ∣ p - 1 := by
    rw [← hk]
    apply ZMod.orderOf_dvd_card_sub_one (div_ne_zero hpa' hpb')
  have hk₀ : k ≠ 0 := by
    rintro rfl
    simp [hp.one_lt.not_ge, tsub_eq_zero_iff_le] at hk_dvd
  have habk : a ^ k ≠ b ^ k := mt (abs_eq_abs_of_pow_eq_pow · hk₀) hab
  have habk_modEq : a ^ k ≡ b ^ k [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff, ← div_eq_one_iff_eq (by simp [hpb']),
      Int.cast_pow, Int.cast_pow, ← div_pow, ← hk, pow_orderOf_eq_one]
  have hpak : ¬↑p ∣ a ^ k := mt (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpa
  have hp₀ : 0 < p := hp.pos
  set Φ := fun d ↦ MvPolynomial.eval ![a, b] (.cyclotomic₂ d ℤ)
  set vℕ := padicValNat p
  set vℤ := padicValInt p
  induction β using Nat.strongRecOn with
  | ind β ihβ =>
    apply add_left_cancel (a := vℤ (a ^ k - b ^ k) + β - 1)
    calc
      vℤ (a ^ k - b ^ k) + β - 1 + vℤ (Φ (p ^ β * k))
        = vℤ (a ^ k - b ^ k) + ∑ _j ∈ .range (β - 1), 1 + vℤ (Φ (p ^ β * k)) := by
        rcases Nat.exists_eq_succ_of_ne_zero hβ with ⟨β, rfl⟩
        simp
      _ = vℤ (a ^ k - b ^ k) + ∑ j ∈ .range (β - 1), vℤ (Φ (p ^ (j + 1) * k)) +
            vℤ (Φ (p ^ β * k)) := by
        congr 2
        apply Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Finset.mem_range] at hj
        rw [ihβ] <;> omega
      _ = vℤ (a ^ k - b ^ k) + ∑ j ∈ .range β, vℤ (Φ (p ^ (j + 1) * k)) := by
        rcases Nat.exists_eq_succ_of_ne_zero hβ with ⟨β, rfl⟩
        simp [sum_range_succ, add_assoc]
      _ = ∑ j ∈ .range (β + 1), vℤ (Φ (p ^ j * k)) := by
        rw [sum_range_succ', add_comm, pow_zero, one_mul]
        simp only [vℤ, Φ, ← padicValInt_cyclotomic₂_of_orderOf_eq hpa hpb hab hk]
      _ = ∑ d ∈ .image (p ^ · * k) (.range (β + 1)), vℤ (Φ d) := by
        rw [Finset.sum_image]
        simp [hk₀, pow_right_inj₀ hp.pos, hp.ne_one]
      _ = ∑ d ∈ (p ^ β * k).divisors.filter (k ∣ ·), vℤ (Φ d) := by
        congr 1 with d
        simp only [mem_image, mem_filter, Nat.mem_divisors, mem_range, Nat.lt_succ]
        constructor
        · rintro ⟨j, hj_le, rfl⟩
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · gcongr
          · have := hp.pos
            positivity
          · simp
        · rintro ⟨⟨hd_dvd, -⟩, q, rfl⟩
          rw [mul_comm, mul_dvd_mul_iff_right hk₀, Nat.dvd_prime_pow hp] at hd_dvd
          rcases hd_dvd with ⟨j, hjβ, rfl⟩
          use j, hjβ
          apply mul_comm
      _ = ∑ d ∈ (p ^ β * k).divisors, vℤ (Φ d) := by
        apply sum_filter_of_ne
        intro d _hd hne
        contrapose! hne
        apply padicValInt.eq_zero_of_not_dvd
        apply prime_not_dvd_eval_cyclotomic₂_of_not_orderOf_dvd
        exacts [hpb, hk ▸ hne]
      _ = vℤ (∏ d ∈ (p ^ β * k).divisors, Φ d) := by
        rw [← padicValInt_prod]
        rw [← prod_ne_zero_iff, MvPolynomial.prod_divisors_eval_cyclotomic₂, sub_ne_zero,
          pow_mul', pow_mul']
        · rw [← pow_mul, ← pow_mul]
          exact mt (abs_eq_abs_of_pow_eq_pow · <| by positivity) hab
        · positivity
      _ = vℤ ((a ^ k) ^ (p ^ β) - (b ^ k) ^ (p ^ β)) := by
        rw [MvPolynomial.prod_divisors_eval_cyclotomic₂, pow_mul', pow_mul']
        positivity
      _ = vℤ (a ^ k - b ^ k) + β := by
        simp only [vℤ]
        rw [padicValInt_pow_sub_pow (n := p ^ β) (.inl hpo) habk habk_modEq hpak,
          padicValNat.prime_pow]
        positivity
      _ = vℤ (a ^ k - b ^ k) + β - 1 + 1 := by
        rw [Nat.sub_add_cancel]
        linarith only [pos_iff_ne_zero.mpr hβ]

-- TODO: move
lemma dvd_one_iff_isUnit {M : Type*} [CommMonoid M] {a : M} : a ∣ 1 ↔ IsUnit a :=
  ⟨(isUnit_of_dvd_unit · isUnit_one), IsUnit.dvd⟩

lemma Int.dvd_one_iff_natAbs {m : ℤ} : m ∣ 1 ↔ m.natAbs = 1 := by
  rw [dvd_one_iff_isUnit, isUnit_iff_natAbs_eq]

lemma Int.pow_modEq_pow_of_dvd_cyclotomic₂ {p a b : ℤ} {n : ℕ}
    (h : p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) : a ^ n ≡ b ^ n [ZMOD p] := by
  replace h := h.trans (MvPolynomial.eval_cyclotomic₂_vec_dvd_pow_sub_pow a b)
  rwa [Int.modEq_comm, Int.modEq_iff_dvd]

lemma Int.dvd_iff_dvd_of_pow_modEq_pow {a b : ℤ} {p n : ℕ} [Fact p.Prime] (hn₀ : n ≠ 0)
    (hmodEq : a ^ n ≡ b ^ n [ZMOD p]) : ↑p ∣ a ↔ ↑p ∣ b := by
  have hp : p.Prime := Fact.out
  rw [← (Nat.prime_iff_prime_int.mp hp).dvd_pow_iff_dvd hn₀,
    hmodEq.dvd_iff, (Nat.prime_iff_prime_int.mp hp).dvd_pow_iff_dvd hn₀]

lemma dvd_iff_dvd_of_dvd_cyclotomic₂ {a b : ℤ} {p n : ℕ} [Fact p.Prime]
    (hp_dvd : ↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) :
    ↑p ∣ a ↔ ↑p ∣ b :=
  have hp : p.Prime := Fact.out
  have hn₀ : n ≠ 0 := by rintro rfl; simp [Int.dvd_one_iff_natAbs, hp.ne_one] at hp_dvd
  Int.dvd_iff_dvd_of_pow_modEq_pow hn₀ <| Int.pow_modEq_pow_of_dvd_cyclotomic₂ hp_dvd

lemma Int.not_dvd_and_not_dvd_of_pow_modEq_pow {a b : ℤ} {p n : ℕ} [Fact p.Prime] (hn₀ : n ≠ 0)
    (hab : IsCoprime a b) (hmodEq : a ^ n ≡ b ^ n [ZMOD p]) :
    ¬↑p ∣ a ∧ ¬↑p ∣ b := by
  rw [dvd_iff_dvd_of_pow_modEq_pow hn₀ hmodEq, and_self]
  intro hpb
  have := hab.isUnit_of_dvd' ((dvd_iff_dvd_of_pow_modEq_pow hn₀ hmodEq).2 hpb) hpb
  exact (Nat.prime_iff_prime_int.mp Fact.out).not_unit this

lemma not_dvd_and_not_dvd_of_dvd_cyclotomic₂ {a b : ℤ} {p n : ℕ} [Fact p.Prime]
    (hab : IsCoprime a b) (hp_dvd : ↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) :
    ¬↑p ∣ a ∧ ¬↑p ∣ b := by
  rw [dvd_iff_dvd_of_dvd_cyclotomic₂ hp_dvd, and_self]
  intro hpb
  have := hab.isUnit_of_dvd' ((dvd_iff_dvd_of_dvd_cyclotomic₂ hp_dvd).2 hpb) hpb
  exact (Nat.prime_iff_prime_int.mp Fact.out).not_unit this

lemma not_dvd_cyclotomic₂_of_ne_pow_padicValNat_mul_orderOf_div {p n : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpa : ¬↑p ∣ a)  (hab : |a| ≠ |b|) (hn : n ≠ p ^ padicValNat p n * orderOf (a / b : ZMod p)) :
    ¬↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := by
  intro hpΦ
  have hp : p.Prime := Fact.out
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [Int.dvd_one_iff_natAbs, hp.ne_one] at hpΦ
  generalize hk : orderOf (a / b : ZMod p) = k at *
  generalize hβ : padicValNat p n = β at *
  have hp₁ : 1 < p := hp.one_lt
  have hpa' : (a : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpb : ¬↑p ∣ b := by rwa [← dvd_iff_dvd_of_dvd_cyclotomic₂ hpΦ]
  have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hk_dvd : k ∣ p - 1 := by
    rw [← hk]
    apply ZMod.orderOf_dvd_card_sub_one (div_ne_zero hpa' hpb')
  have hk₀ : k ≠ 0 := by
    rintro rfl
    simp [hp₁.not_ge, tsub_eq_zero_iff_le] at hk_dvd
  have Hsub : ∀ m ≠ 0, a ^ m - b ^ m ≠ 0 := fun m hm ↦
    sub_ne_zero.mpr <| mt (abs_eq_abs_of_pow_eq_pow · hm) hab
  have hkp : k < p := by refine (Nat.le_of_dvd ?_ hk_dvd).trans_lt ?_ <;> omega
  have hpk : ¬p ∣ k := Nat.not_dvd_of_pos_of_lt (by positivity) hkp
  rcases em (k ∣ n) with ⟨q, hq⟩ | hkn
  · obtain ⟨r, hr⟩ : p ^ β ∣ q := by
      subst n
      rw [← hβ, padicValNat.mul hk₀ (right_ne_zero_of_mul hn₀), padicValNat.eq_zero_of_not_dvd,
        zero_add]
      · exact pow_padicValNat_dvd
      · exact hpk
    have hr₁ : 1 < r := by
      contrapose! hn
      interval_cases r
      · simp [hq, hr] at hn₀
      · simp [mul_comm, hq, hr]
    set Φ := fun d ↦ MvPolynomial.eval ![a, b] (.cyclotomic₂ d ℤ)
    suffices ¬↑p ∣ ∏ d ∈ n.divisors \ (p ^ β * k).divisors, Φ d by
      apply this
      refine hpΦ.trans <| dvd_prod_of_mem _ ?_
      suffices ¬n ∣ p ^ β * k by simp [hn₀, hk₀, this]
      rw [hq, mul_comm, mul_dvd_mul_iff_right hk₀, ← mul_one (p ^ β), hr,
        mul_dvd_mul_iff_left (by positivity)]
      exact Nat.not_dvd_of_pos_of_lt one_pos hr₁
    suffices ¬p * (a ^ (p ^ β * k) - b ^ (p ^ β * k)) ∣ a ^ n - b ^ n by
      have H : a ^ n - b ^ n = (∏ d ∈ n.divisors \ (p ^ β * k).divisors, Φ d) *
          (a ^ (p ^ β * k) - b ^ (p ^ β * k)) := by
        rw [← MvPolynomial.prod_divisors_eval_cyclotomic₂,
          ← MvPolynomial.prod_divisors_eval_cyclotomic₂, prod_sdiff]
        · rw [hq, mul_comm, hr]
          gcongr
          use r
        · positivity
        · positivity
      rwa [H, mul_dvd_mul_iff_right (Hsub _ (by positivity))] at this
    intro Hdvd
    refine padicValInt_mono p Hdvd (Hsub _ (by positivity)) |>.not_gt ?_
    have hn' : n = p ^ β * k * r := by rw [hq, hr]; ring
    have hpr : ¬p ∣ r := by
      intro hpr
      have : p ^ (β + 1) ∣ n := calc
        p ^ (β + 1) = p ^ β * p := pow_succ ..
        _ ∣ p ^ β * r := by gcongr
        _ = q := hr.symm
        _ ∣ n := hq ▸ dvd_mul_left ..
      rw [padicValNat_dvd_iff_le hn₀, hβ] at this
      exact this.not_gt β.lt_succ_self
    rw [padicValInt.mul, hn', pow_mul _ (p ^ β * k), pow_mul _ (p ^ β * k),
      padicValInt_pow_sub_pow, add_comm, padicValInt_self]
    · gcongr
      simp [padicValNat.eq_zero_of_not_dvd hpr]
    · rcases hp.eq_two_or_odd' with rfl | hpo
      · right
        rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
      · exact .inl hpo
    · exact sub_ne_zero.mp <| Hsub _ (by positivity)
    · rw [pow_mul', pow_mul']
      gcongr ?_ ^ _
      rw [← ZMod.intCast_eq_intCast_iff, ← div_eq_one_iff_eq, Int.cast_pow, Int.cast_pow,
        ← div_pow, ← hk, pow_orderOf_eq_one]
      rw [Int.cast_pow]
      exact pow_ne_zero _ hpb'
    · exact mt (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpa
    · positivity
    · positivity
    · exact Hsub _ (by positivity)
  · refine prime_not_dvd_eval_cyclotomic₂_of_not_orderOf_dvd hpb ?_ hpΦ
    rwa [hk]

lemma padicValInt_cyclotomic₂_eq_zero {p n : ℕ} [Fact p.Prime] {a b : ℤ}
    (hpa : ¬↑p ∣ a) (hab : |a| ≠ |b|) (hn : n ≠ p ^ padicValNat p n * orderOf (a / b : ZMod p)) :
    padicValInt p (MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  apply not_dvd_cyclotomic₂_of_ne_pow_padicValNat_mul_orderOf_div <;> assumption

lemma padicValInt_two_cyclotomic₂_one (a b : ℤ) :
    padicValInt 2 (MvPolynomial.eval ![a, b] (.cyclotomic₂ 1 ℤ)) = padicValInt 2 (a - b) := by
  simp

lemma padicValInt_two_cyclotomic₂_two (a b : ℤ) :
    padicValInt 2 (MvPolynomial.eval ![a, b] (.cyclotomic₂ 2 ℤ)) = padicValInt 2 (a + b) := by
  simp

lemma padicValInt_two_cyclotomic₂_two_pow {a b : ℤ} (ha : Odd a) (hb : Odd b) {m : ℕ} (hm : 1 < m) :
    padicValInt 2 (MvPolynomial.eval ![a, b] (.cyclotomic₂ (2 ^ m) ℤ)) = 1 := by
  rcases Nat.exists_eq_add_of_lt hm with ⟨m, rfl⟩
  suffices padicValInt 2 (a ^ 2 ^ (1 + m) + b ^ 2 ^ (1 + m)) = 1 by
    simpa [MvPolynomial.cyclotomic₂_two_pow_add_one]
  apply padicValInt_two_pow_two_pow_add_pow_two_pow_of_ne_zero ha hb
  omega

lemma eq_pow_padicValNat_mul_orderOf_of_dvd_cyclotomic₂ {a b : ℤ} {p n : ℕ} [Fact p.Prime]
    (ha : ¬↑p ∣ a) (hab : |a| ≠ |b|) (hdvd : ↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ)) :
    n = p ^ padicValNat p n * orderOf (a / b : ZMod p) := by
  contrapose! hdvd
  apply not_dvd_cyclotomic₂_of_ne_pow_padicValNat_mul_orderOf_div <;> assumption

lemma isGreatest_primeFactors_of_dvd_cyclotomic₂ {a b : ℤ} {p n : ℕ} [Fact p.Prime]
    (ha : ¬↑p ∣ a) (hab : |a| ≠ |b|) (hdvd : ↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ))
    (hne : orderOf (a / b : ZMod p) ≠ n) :
    IsGreatest n.primeFactors p := by
  have hp : p.Prime := Fact.out
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp [Int.dvd_one_iff_natAbs, hp.ne_one] at hdvd
  have hpa' : (a : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpb : ¬↑p ∣ b := by rwa [← dvd_iff_dvd_of_dvd_cyclotomic₂ hdvd]
  have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · suffices p ∣ n by simp [*]
    contrapose! hne
    rw [eq_pow_padicValNat_mul_orderOf_of_dvd_cyclotomic₂ ha hab hdvd]
    simp [padicValNat.eq_zero_of_not_dvd hne]
  · rintro q hq
    obtain ⟨hqp, hqn⟩ : q.Prime ∧ q ∣ n := by simp_all
    contrapose! hqn
    rw [eq_pow_padicValNat_mul_orderOf_of_dvd_cyclotomic₂ ha hab hdvd, hqp.dvd_mul, not_or]
    refine ⟨mt hqp.dvd_of_dvd_pow <| by simp [Nat.prime_dvd_prime_iff_eq hqp hp, hqn.ne'], ?_⟩
    apply Nat.not_dvd_of_pos_of_lt
    · rw [orderOf_pos_iff, isOfFinOrder_iff_isUnit]
      exact .div (.mk0 _ hpa') (.mk0 _ hpb')
    · have hk_dvd : orderOf (a / b : ZMod p) ∣ p - 1 :=
        ZMod.orderOf_dvd_card_sub_one (div_ne_zero hpa' hpb')
      refine (Nat.le_of_dvd (by simp [hp.one_lt]) hk_dvd).trans_lt ?_
      exact p.pred_le.trans_lt ‹_›

lemma exists_isGreatest_setOf_prime_dvd_cyclotomic₂_eq_of_zsigmondy {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hn : 2 < n) (hcopr : IsCoprime a b)
    (hdvd : ∀ p : ℕ, p.Prime → a ^ n ≡ b ^ n [ZMOD p] → ∃ k ≠ 0, k < n ∧ a ^ k ≡ b ^ k [ZMOD p]) :
    ∃ p : ℕ, IsGreatest {p | p.Prime ∧ p ∣ n} p ∧
      MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) = p := by
  by_cases hΦ₁ : MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) = 1
  · apply absurd hΦ₁ (ne_of_gt ?_)
    calc
      1 = 1 ^ φ n := by rw [one_pow]
      _ ≤ (a - b) ^ φ n := by gcongr; omega
      _ < _ := by
        apply MvPolynomial.sub_pow_totient_lt_eval_cyclotomic₂_int <;> first | assumption | omega
  · have hn₀ : n ≠ 0 := by omega
    have hΦpos : 0 < MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := by
      apply MvPolynomial.eval_cyclotomic₂_pos_int <;> assumption
    lift MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) to ℕ using hΦpos.le with Φ hΦ
    have habs_ab : |a| ≠ |b| := by
      rw [abs_of_pos hpos, abs_of_pos (hpos.trans hlt)]
      exact hlt.ne'
    have H (p : ℕ) (hp : p.Prime) (hpΦ : p ∣ Φ) :
        ¬↑p ∣ a ∧ ¬↑p ∣ b ∧ (p : ℤ) ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) ∧
          IsGreatest n.primeFactors p := by
      have hp' := Fact.mk hp
      have hpΦ' : (p : ℤ) ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := hΦ ▸ mod_cast hpΦ
      have hab_modEq : a ^ n ≡ b ^ n [ZMOD p] := Int.pow_modEq_pow_of_dvd_cyclotomic₂ hpΦ'
      obtain ⟨hpa, hpb⟩ := not_dvd_and_not_dvd_of_dvd_cyclotomic₂ hcopr hpΦ'
      use hpa, hpb, hpΦ'
      apply isGreatest_primeFactors_of_dvd_cyclotomic₂ (b := b) (n := n) hpa habs_ab hpΦ'
      rcases hdvd p hp hab_modEq with ⟨k, hk₀, hkn, habk⟩
      contrapose! hkn
      rw [← hkn]
      apply orderOf_le_of_pow_eq_one (pos_iff_ne_zero.2 hk₀)
      rwa [div_pow, div_eq_one_iff_eq, ← Int.cast_pow, ← Int.cast_pow,
        ZMod.intCast_eq_intCast_iff]
      apply pow_ne_zero
      rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    choose Hpa Hpb HpΦ Hpn using H
    obtain ⟨p, β, hp, hβ₀, rfl⟩ : IsPrimePow Φ := by
      rw [isPrimePow_iff_unique_prime_dvd]
      rcases Nat.exists_prime_and_dvd (mod_cast hΦ₁) with ⟨p, hp, hpΦ⟩
      use! p, hp, hpΦ
      rintro q ⟨hqp, hqΦ⟩
      exact (Hpn q hqp hqΦ).unique (Hpn p hp hpΦ)
    rw [← Nat.prime_iff] at hp
    have := Fact.mk hp
    have hp_dvd : p ∣ p ^ β := dvd_pow_self _ hβ₀.ne'
    specialize Hpa p hp hp_dvd
    specialize Hpb p hp hp_dvd
    specialize Hpn p hp hp_dvd
    specialize HpΦ p hp hp_dvd
    suffices β = 1 by
      refine ⟨p, ?_, by simp [this]⟩
      convert Hpn
      ext q
      simp [hn₀]
    have Hn := eq_pow_padicValNat_mul_orderOf_of_dvd_cyclotomic₂ Hpa habs_ab HpΦ
    rw [← padicValNat.prime_pow (p := p) β, ← padicValInt.of_nat, hΦ, Hn]
    rcases hp.eq_two_or_odd' with rfl | hpo
    · have hk : orderOf (a / b : ZMod 2) = 1 := by
        have : IsUnit (a / b : ZMod 2) := by
          apply_rules [IsUnit.mk0, div_ne_zero]
          · simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using Hpa
          · simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using Hpb
        exact this.orderOf_eq_one
      rw [hk, mul_one]
      cases le_or_gt (padicValNat 2 n) 1 with
      | inl Hle =>
        refine absurd ?_ hn.not_ge
        calc
          n = 2 ^ padicValNat 2 n := by rw [Hn, hk]; simp
          _ ≤ 2 ^ 1 := by gcongr; decide
          _ = 2 := rfl
      | inr Hlt =>
        rw [padicValInt_two_cyclotomic₂_two_pow]
        · simpa [← Int.not_even_iff_odd, even_iff_two_dvd] using Hpa
        · simpa [← Int.not_even_iff_odd, even_iff_two_dvd] using Hpb
        · exact Hlt
    · rw [padicValInt_cyclotomic₂_pow_mul_orderOf hpo Hpa Hpb habs_ab]
      suffices p ∣ n by simpa [padicValNat.eq_zero_iff, hp.ne_one, hn₀]
      simpa [hn₀, hp] using Hpn.1

lemma eq_add_one_of_zsigmondy {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hn : 2 < n) (hcopr : IsCoprime a b)
    (hdvd : ∀ p : ℕ, p.Prime → a ^ n ≡ b ^ n [ZMOD p] → ∃ k ≠ 0, k < n ∧ a ^ k ≡ b ^ k [ZMOD p]) :
    a = b + 1 := by
  suffices a - b < 2 by linarith
  by_contra! hle
  rcases exists_isGreatest_setOf_prime_dvd_cyclotomic₂_eq_of_zsigmondy hpos hlt hn hcopr hdvd
    with ⟨p, ⟨⟨hp, hpn⟩, -⟩, hΦp⟩
  have H₁ : 2 ^ (p - 1) < p := by
    zify
    calc
      (2 : ℤ) ^ (p - 1) ≤ (a - b) ^ (p - 1) := by gcongr
      _ ≤ (a - b) ^ φ n := by
        gcongr
        · linarith
        · apply Nat.le_of_dvd
          · positivity
          · rw [← Nat.totient_prime hp]
            gcongr
      _ < MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := by
        apply MvPolynomial.sub_pow_totient_lt_eval_cyclotomic₂_int <;> omega
      _ = p := hΦp
  refine H₁.not_ge ?_
  calc
    p = p - 1 + 1 := by rw [Nat.sub_add_cancel hp.one_lt.le]
    _ ≤ 2 ^ (p - 1) := by
      rw [Nat.succ_le]
      apply Nat.lt_pow_self
      decide

/-- Zsigmondy's theorem for `n = 2`, a version for natural numbers. -/
lemma Nat.add_eq_two_pow_of_coprime_of_forall_prime_sq_modEq_imp_modEq {a b : ℕ} (hpos : 0 < b)
    (hlt : b < a) (hcopr : a.Coprime b)
    (hdvd : ∀ p : ℕ, p.Prime → a ^ 2 ≡ b ^ 2 [MOD p] → a ≡ b [MOD p]) :
    ∃ l, a + b = 2 ^ l := by
  suffices ∀ p : ℕ, p.Prime → p ∣ (a + b) → p = 2 by
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) @this⟩
  intro p hp hp_dvd
  have hab' : a ≡ b [MOD p] := by
    refine hdvd p hp ?_
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by gcongr), Nat.sq_sub_sq]
    exact dvd_mul_of_dvd_left hp_dvd _
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hlt.le] at hab'
  have : p ∣ 2 * a := calc
    p ∣ a + b + (a - b) := dvd_add ‹_› ‹_›
    _ = 2 * a := by omega
  rw [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at this
  refine this.resolve_right fun hpa ↦ ?_
  · rw [Nat.dvd_add_right hpa] at hp_dvd
    exact hp.ne_one <| Nat.eq_one_of_dvd_coprimes hcopr hpa hp_dvd

/-- Zsigmondy's theorem for `n = 2`, a version for integer numbers. -/
lemma Int.add_eq_two_pow_of_coprime_of_forall_prime_sq_modEq_imp_modEq {a b : ℤ} (hpos : 0 < b)
    (hlt : b < a) (hcopr : IsCoprime a b)
    (hdvd : ∀ p : ℕ, p.Prime → a ^ 2 ≡ b ^ 2 [ZMOD p] → a ≡ b [ZMOD p]) :
    ∃ l, a + b = 2 ^ l := by
  lift b to ℕ using hpos.le
  lift a to ℕ using by omega
  norm_cast at *
  apply Nat.add_eq_two_pow_of_coprime_of_forall_prime_sq_modEq_imp_modEq <;> try assumption

private lemma zsigmondy_aux {b : ℤ} {p k : ℕ} (hpos : 0 < b) (hn : 2 < p * k)
    (hp : p.Prime) (hΦp : MvPolynomial.eval ![b + 1, b] (.cyclotomic₂ (p * k) ℤ) = p)
    (hkp : k < p) (hpk : ¬p ∣ k) :
    b = 1 ∧ p = 3 ∧ k = 2 := by
  have hk₀ : 0 < k := pos_of_mul_pos_right (two_pos.trans hn) (zero_le _)
  have Hle₁ : (∑ i ∈ .range p, p.choose i * b ^ i) ^ φ k ≤ p * (2 * b + 1) ^ φ k := calc
    (∑ i ∈ .range p, p.choose i * b ^ i) ^ φ k = ((b + 1) ^ p - b ^ p) ^ φ k := by
      congr 1
      simp [add_pow, Finset.sum_range_succ, mul_comm]
    _ ≤ MvPolynomial.eval ![(b + 1) ^ p, b ^ p] (.cyclotomic₂ k ℤ) := by
      apply MvPolynomial.sub_pow_totient_le_eval_cyclotomic₂_int
      · gcongr
        exacts [hp.ne_zero, lt_add_one b]
      · positivity
    _ = MvPolynomial.eval ![b + 1, b] (.expand p (R := ℤ) (.cyclotomic₂ k ℤ)) := by
      rw [MvPolynomial.eval_expand]
      congr with i
      fin_cases i <;> rfl
    _ = p * MvPolynomial.eval ![b + 1, b] (.cyclotomic₂ k ℤ) := by
      rw [← MvPolynomial.cyclotomic₂_mul_prime_mul_cyclotomic₂_of_not_dvd hp hpk, map_mul,
        mul_comm k, hΦp]
    _ ≤ p * (b + 1 + b) ^ φ k := by
      gcongr
      apply MvPolynomial.eval_cyclotomic₂_le_add_pow_totient_int <;> try assumption
      apply lt_add_one
    _ = p * (2 * b + 1) ^ φ k := by
      ring_nf
  rcases hp.two_le.eq_or_lt with rfl | hp₂
  · obtain rfl : k = 1 := by omega
    norm_num1 at hn
  · have Hle₂ : (1 + p * b + p.choose 2 * b ^ 2) ^ φ k ≤ p * (2 * b + 1) ^ φ k := calc
      (1 + p * b + p.choose 2 * b ^ 2) ^ φ k = (∑ i ∈ .range 3, p.choose i * b ^ i) ^ φ k := by
        simp [Finset.sum_range_succ]
      _ ≤ (∑ i ∈ .range p, p.choose i * b ^ i) ^ φ k := by
        gcongr
        exact hp₂
      _ ≤ p * (2 * b + 1) ^ φ k := Hle₁
    have Hle₃ : 1 + p * b + p.choose 2 * b ^ 2 ≤ p * (2 * b + 1) := by
      have aux₁ : 0 < (2 * b + 1) ^ (φ k - 1) := by positivity
      refine le_of_mul_le_mul_right ?_ aux₁
      calc
        (1 + p * b + p.choose 2 * b ^ 2) * (2 * b + 1) ^ (φ k - 1)
          ≤ (1 + p * b + p.choose 2 * b ^ 2) ^ (φ k - 1 + 1) := by
          rw [pow_succ' _ (φ k - 1)]
          gcongr
          · nlinarith only [hpos, hp₂]
          · apply one_le_mul_of_one_le_of_one_le
            · norm_cast
              apply Nat.choose_pos
              exact hp₂.le
            · nlinarith only [hpos]
        _ ≤ p * (2 * b + 1) * (2 * b + 1) ^ (φ k - 1) := by
          conv_rhs => rw [mul_assoc, ← pow_succ']
          rwa [Nat.sub_add_cancel]
          rwa [Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, Nat.totient_pos]
    have Hlt₄ : (p.choose 2 * b ^ 2 : ℤ) < p * (b + 1) := by
      linarith only [Hle₃]
    have Hlt₅ : p.choose 2 < 2 * p := by
      zify
      refine lt_of_mul_lt_mul_right (Hlt₄.trans_le ?_) (sq_nonneg b)
      rw [mul_assoc, mul_left_comm, two_mul]
      gcongr
      · refine le_self_pow₀ ?_ two_ne_zero
        rwa [← Int.add_one_le_iff] at hpos
      · exact one_le_pow₀ hpos
    have Hp₅ : p < 5 := by
      rwa [mul_comm, Nat.choose_two_right, Nat.div_lt_iff_lt_mul two_pos, mul_assoc,
        mul_lt_mul_left, tsub_lt_iff_left] at Hlt₅
      all_goals exact hp.pos
    obtain rfl : p = 3 := by
      interval_cases p <;> first | rfl | norm_num1 at hp
    obtain rfl : b = 1 := by
      norm_num [Nat.choose_two_right] at Hlt₄
      nlinarith only [hpos, Hlt₄]
    interval_cases k
    · norm_num at hΦp
    · simp

/-- *Zsigmondy's theorem* for `n > 2`, a version for integer numbers. -/
lemma eq_two_one_six_of_zsigmondy {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hn : 2 < n) (hcopr : IsCoprime a b)
    (hdvd : ∀ p : ℕ, p.Prime → a ^ n ≡ b ^ n [ZMOD p] → ∃ k ≠ 0, k < n ∧ a ^ k ≡ b ^ k [ZMOD p]) :
    a = 2 ∧ b = 1 ∧ n = 6 := by
  rcases exists_isGreatest_setOf_prime_dvd_cyclotomic₂_eq_of_zsigmondy hpos hlt hn hcopr hdvd
    with ⟨p, ⟨⟨hp, hpn⟩, hp_max⟩, hΦp⟩
  have := Fact.mk hp
  have hp₀ : 0 < p := hp.pos
  have Hab₁ : a = b + 1 := eq_add_one_of_zsigmondy hpos hlt hn hcopr hdvd
  have hpΦ : ↑p ∣ MvPolynomial.eval ![a, b] (.cyclotomic₂ n ℤ) := by simp [hΦp]
  obtain ⟨hpa, hpb⟩ := not_dvd_and_not_dvd_of_dvd_cyclotomic₂ hcopr hpΦ
  have hpa' : (a : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpb' : (b : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have habs_ab : |a| ≠ |b| := by simp [abs_of_pos, add_pos, hpos, Hab₁]
  have Hn : n = p ^ padicValNat p n * orderOf (a / b : ZMod p) :=
    eq_pow_padicValNat_mul_orderOf_of_dvd_cyclotomic₂ hpa habs_ab hpΦ
  generalize hk : orderOf (a / b : ZMod p) = k at *
  generalize hβ : padicValNat p n = β at *
  have hn₀ : n ≠ 0 := hn.ne_bot
  have hβ₀ : 0 < β := by
    simp [pos_iff_ne_zero, ← hβ, padicValNat.eq_zero_iff, hp.ne_one, hn₀, hpn]
  have hkp : k < p := by
    rw [← hk]
    apply ZMod.orderOf_lt hp.one_lt
  have hk₀ : 0 < k := by
    rw [← hk, orderOf_pos_iff, isOfFinOrder_iff_isUnit]
    exact .div (.mk0 _ hpa') (.mk0 _ hpb')
  have hpk : ¬p ∣ k := by
    contrapose! hkp
    exact Nat.le_of_dvd hk₀ hkp
  cases le_or_gt β 1 with
  | inl hβ₁ =>
    obtain rfl : β = 1 := by omega
    obtain rfl : n = p * k := by rw [Hn, pow_one]
    subst a
    norm_num [zsigmondy_aux hpos hn hp hΦp hkp hpk]
  | inr hβ₁ =>
    refine absurd hΦp <| ne_of_gt ?_
    have Hlt := calc
      (p : ℤ) ≤ p ^ (β - 1) := by
        apply le_self_pow₀
        · exact mod_cast hp.one_lt.le
        · omega
      _ < 1 + b * p ^ (β - 1) := by
        rw [add_comm, Int.lt_add_one_iff]
        apply le_mul_of_one_le_left
        · positivity
        · omega
      _ = b ^ 0 * (p ^ (β - 1)).choose 0 + b ^ 1 * (p ^ (β - 1)).choose 1 := by simp
      _ ≤ ∑ i ∈ .range (p ^ (β - 1)), b ^ i * (p ^ (β - 1)).choose i := by
        apply Finset.add_le_sum (f := fun i ↦ b ^ i * (p ^ (β - 1)).choose i)
        · intro _ _
          positivity
        · rw [Finset.mem_range]
          positivity
        · rw [Finset.mem_range]
          apply Nat.one_lt_pow <;> omega
        · exact zero_ne_one
      _ = a ^ p ^ (β - 1) - b ^ p ^ (β - 1) := by
        simp [Hab₁, add_pow, Finset.sum_range_succ]
    calc
      (p : ℤ) < a ^ p ^ (β - 1) - b ^ p ^ (β - 1) := Hlt
      _ ≤ (a ^ p ^ (β - 1) - b ^ p ^ (β - 1)) ^ φ (k * p) := by
        apply le_self_pow₀
        · exact le_trans (mod_cast hp.one_lt.le) Hlt.le
        · positivity
      _ ≤ MvPolynomial.eval ![a ^ p ^ (β - 1), b ^ p ^ (β - 1)]
            (MvPolynomial.cyclotomic₂ (k * p) ℤ) := by
        apply MvPolynomial.sub_pow_totient_le_eval_cyclotomic₂_int
        · gcongr
        · positivity
      _ = MvPolynomial.eval (![a, b] ^ p ^ (β - 1)) (MvPolynomial.cyclotomic₂ (k * p) ℤ) := by
        congr 2
        ext i; fin_cases i <;> rfl
      _ = MvPolynomial.eval ![a, b] (MvPolynomial.cyclotomic₂ n ℤ) := by
        rw [← MvPolynomial.eval_expand,
          ← MvPolynomial.cyclotomic₂_mul_prime_pow_of_dvd hp (dvd_mul_left _ _),
          mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), Hn, mul_comm]

/-- *Zsigmondy's theorem* for `a ^ n - b ^ n`, stated for integers in terms of `Int.ModEq`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hcopr : IsCoprime a b)
    (h₁ : n = 1 → a ≠ b + 1) (h₂ : n = 2 → ∀ l, a + b ≠ 2 ^ l) (h : (a, b, n) ≠ (2, 1, 6)) :
    ∃ p : ℕ, p.Prime ∧ a ^ n ≡ b ^ n [ZMOD p] ∧ ∀ k ≠ 0, k < n → ¬(a ^ k ≡ b ^ k [ZMOD p]) := by
  cases le_or_gt n 2 with
  | inl hn =>
    interval_cases n
    · use 2
      norm_num
    · have : (a - b).natAbs ≠ 1 := by
        specialize h₁ rfl
        rw [ne_eq, Int.natAbs_eq_iff, Nat.cast_one]
        contrapose! h₁
        omega
      rcases Nat.exists_prime_and_dvd this with ⟨p, hp, hp_dvd⟩
      refine ⟨p, hp, ?_, ?_⟩
      · symm
        simpa [Int.modEq_iff_dvd, Int.ofNat_dvd_left] using hp_dvd
      · intro l hl hl'
        interval_cases l; simp at hl
    · contrapose! h₂
      use rfl
      apply Int.add_eq_two_pow_of_coprime_of_forall_prime_sq_modEq_imp_modEq <;> try assumption
      intro p hp habp
      rcases h₂ p hp habp with ⟨k, hk₀, hk₂, hk⟩
      interval_cases k
      · simp at hk₀
      · simpa using hk
  | inr hn =>
    contrapose! h
    rcases eq_two_one_six_of_zsigmondy hpos hlt hn hcopr h with ⟨rfl, rfl, rfl⟩
    rfl

/-- *Zsigmondy's theorem* for `a ^ n - 1`, stated for integers in terms of `Int.ModEq`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_pow_modEq_one_forall_lt_not_pow_modEq_one {a : ℤ} {n : ℕ}
    (hlt : 1 < a)
    (h₁ : n = 1 → a ≠ 2) (h₂ : n = 2 → ∀ l, a + 1 ≠ 2 ^ l) (h : (a, n) ≠ (2, 6)) :
    ∃ p : ℕ, p.Prime ∧ a ^ n ≡ 1 [ZMOD p] ∧ ∀ k ≠ 0, k < n → ¬(a ^ k ≡ 1 [ZMOD p]) := by
  simpa using exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow one_pos hlt isCoprime_one_right
    (by simpa) (by simpa) (by simpa using h)

/-- *Zsigmondy's theorem* for `a ^ n - b ^ n`, stated for integers in terms of `orderOf` in `ZMod`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_orderOf_div_eq {a b : ℤ} {n : ℕ} (hpos : 0 < b) (hlt : b < a)
    (hcopr : IsCoprime a b) (h₁ : n = 1 → a ≠ b + 1) (h₂ : n = 2 → ∀ l, a + b ≠ 2 ^ l)
    (h : (a, b, n) ≠ (2, 1, 6)) :
    ∃ (p : ℕ) (_ : Fact p.Prime), orderOf (a / b : ZMod p) = n := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · rcases Nat.exists_prime_and_dvd (show a.natAbs ≠ 1 by omega) with ⟨p, hp, hpa⟩
    have := Fact.mk hp
    use p, ⟨hp⟩
    have ha : (a : ZMod p) = 0 := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.ofNat_dvd_left]
    simp [ha]
  rcases Int.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow hpos hlt hcopr h₁ h₂ h
    with ⟨p, hp, hpn, hn_min⟩
  have := Fact.mk hp
  use p, ⟨hp⟩
  obtain ⟨hpa, hpb⟩ := Int.not_dvd_and_not_dvd_of_pow_modEq_pow hn₀ hcopr hpn
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpa hpb
  have hmodEq (k : ℕ) : a ^ k ≡ b ^ k [ZMOD p] ↔ (a / b : ZMod p) ^ k = 1 := by
    rw [div_pow, div_eq_one_iff_eq, ← Int.cast_pow, ← Int.cast_pow, ZMod.intCast_eq_intCast_iff]
    apply pow_ne_zero
    assumption
  simp only [hmodEq] at hpn hn_min
  apply le_antisymm
  · exact orderOf_le_of_pow_eq_one (by positivity) hpn
  · contrapose! hn_min
    refine ⟨_, ?_, hn_min, pow_orderOf_eq_one _⟩
    rw [ne_eq, orderOf_eq_zero_iff_eq_zero]
    exact div_ne_zero hpa hpb

/-- *Zsigmondy's theorem* for `a ^ n - 1`, stated for integers in terms of `orderOf` in `ZMod`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_orderOf_eq {a : ℤ} {n : ℕ} (hlt : 1 < a) (h₁ : n = 1 → a ≠ 2)
    (h₂ : n = 2 → ∀ l, a + 1 ≠ 2 ^ l) (h : (a, n) ≠ (2, 6)) :
    ∃ (p : ℕ) (_ : Fact p.Prime), orderOf (a : ZMod p) = n := by
  simpa using exists_prime_orderOf_div_eq one_pos hlt isCoprime_one_right (by simpa) (by simpa)
    (by simpa using h)

/-- *Zsigmondy's theorem* for `a ^ n - b ^ n`, stated for natural numbers in terms of `Nat.ModEq`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Nat.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow {a b n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hcopr : a.Coprime b)
    (h₁ : n = 1 → a ≠ b + 1) (h₂ : n = 2 → ∀ l, a + b ≠ 2 ^ l) (h : (a, b, n) ≠ (2, 1, 6)) :
    ∃ p : ℕ, p.Prime ∧ a ^ n ≡ b ^ n [MOD p] ∧ ∀ k ≠ 0, k < n → ¬(a ^ k ≡ b ^ k [MOD p]) :=
  mod_cast Int.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow (a := a) (b := b)
    (mod_cast hpos) (mod_cast hlt) (mod_cast hcopr) (mod_cast h₁) (mod_cast h₂)
    (by simpa only [ne_eq, Prod.ext_iff, ← Int.ofNat_inj] using h)

/-- *Zsigmondy's theorem* for `a ^ n - b ^ n`, stated for natural numbers
in terms of `orderOf` in `ZMod`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Nat.exists_prime_orderOf_div_eq {a b n : ℕ} (hpos : 0 < b) (hlt : b < a) (hcopr : a.Coprime b)
    (h₁ : n = 1 → a ≠ b + 1) (h₂ : n = 2 → ∀ l, a + b ≠ 2 ^ l) (h : (a, b, n) ≠ (2, 1, 6)) :
    ∃ (p : ℕ) (_ : Fact p.Prime), orderOf (a / b : ZMod p) = n :=
  mod_cast Int.exists_prime_orderOf_div_eq (a := a) (b := b)
    (mod_cast hpos) (mod_cast hlt) (mod_cast hcopr) (mod_cast h₁) (mod_cast h₂)
    (by simpa only [ne_eq, Prod.ext_iff, ← Int.ofNat_inj] using h)

/-- *Zsigmondy's theorem* for `a ^ n - 1`, stated for natural numbers
in terms of `orderOf` in `ZMod`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Nat.exists_prime_orderOf_eq {a n : ℕ} (hlt : 1 < a) (h₁ : n = 1 → a ≠ 2)
    (h₂ : n = 2 → ∀ l, a + 1 ≠ 2 ^ l) (h : (a, n) ≠ (2, 6)) :
    ∃ (p : ℕ) (_ : Fact p.Prime), orderOf (a : ZMod p) = n := by
  simpa using exists_prime_orderOf_div_eq one_pos hlt (coprime_one_right _) (by simpa) (by simpa)
    (by simpa using h)

/-- *Zsigmondy's theorem* for `a ^ n + b ^ n`, stated for integers in terms of `Int.ModEq`.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_pow_modEq_neg_pow_forall_lt_not_pow_modEq_neg_pow {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hcopr : IsCoprime a b) (h : (a, b, n) ≠ (2, 1, 3)) :
    ∃ p : ℕ, p.Prime ∧ a ^ n ≡ -b ^ n [ZMOD p] ∧ ∀ k ≠ 0, k < n → ¬(a ^ k ≡ -b ^ k [ZMOD p]) := by
  cases le_or_gt n 1 with
  | inl hn₁ =>
    interval_cases n
    · use 2
      norm_num
    · have : (a + b).natAbs ≠ 1 := by
        rw [ne_eq, Int.natAbs_eq_iff, Nat.cast_one]
        by_contra
        omega
      rcases Nat.exists_prime_and_dvd this with ⟨p, hp, hp_dvd⟩
      use p, hp, .symm <| by simpa [Int.modEq_iff_dvd, Int.ofNat_dvd_left] using hp_dvd
      intro k hk₀ hk₁
      interval_cases k; simp at hk₀
  | inr hn₁ =>
    obtain ⟨p, hp, hmodEq, hn_min⟩ :
        ∃ p : ℕ, p.Prime ∧ a ^ (2 * n) ≡ b ^ (2 * n) [ZMOD p] ∧
          ∀ k ≠ 0, k < 2 * n → ¬(a ^ k ≡ b ^ k [ZMOD p]) := by
     apply Int.exists_prime_pow_modEq_pow_forall_lt_not_pow_modEq_pow hpos hlt hcopr
     · intro h
       omega
     · contrapose! hn₁
       omega
     · contrapose! h
       simp at h ⊢
       omega
    refine ⟨p, hp, ?_, ?_⟩
    · rw [pow_mul', pow_mul', Int.sq_modEq_sq (Nat.prime_iff_prime_int.mp hp)] at hmodEq
      apply hmodEq.resolve_left
      contrapose! hn_min
      refine ⟨n, ?_, ?_, hn_min⟩ <;> omega
    · intro k hk₀ hkn
      specialize hn_min (2 * k) (by positivity) (by omega)
      contrapose! hn_min
      rw [pow_mul', pow_mul', ← neg_sq (b ^ k)]
      apply hn_min.pow

/-- *Zsigmondy's theorem* for `a ^ n + b ^ n`, stated for integers in terms of divisibility.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Int.exists_prime_dvd_pow_add_pow_forall_lt_not_dvd_pow_add_pow {a b : ℤ} {n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hcopr : IsCoprime a b) (h : (a, b, n) ≠ (2, 1, 3)) :
    ∃ p : ℕ, p.Prime ∧ ↑p ∣ a ^ n + b ^ n ∧ ∀ k ≠ 0, k < n → ¬(↑p ∣ a ^ k + b ^ k) := by
  have (p : ℤ) (k : ℕ) : a ^ k ≡ -b ^ k [ZMOD p] ↔ p ∣ a ^ k + b ^ k := by
    rw [modEq_comm]
    simp [modEq_iff_dvd]
  simpa [this]
    using Int.exists_prime_pow_modEq_neg_pow_forall_lt_not_pow_modEq_neg_pow hpos hlt hcopr h

/-- *Zsigmondy's theorem* for `a ^ n + b ^ n`, stated for natural numbers in terms of divisibility.

This version does not require `n > 2`. It describes all the exceptions instead. -/
lemma Nat.exists_prime_dvd_pow_add_pow_forall_lt_not_dvd_pow_add_pow {a b n : ℕ}
    (hpos : 0 < b) (hlt : b < a) (hcopr : a.Coprime b) (h : (a, b, n) ≠ (2, 1, 3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ^ n + b ^ n ∧ ∀ k ≠ 0, k < n → ¬(p ∣ a ^ k + b ^ k) :=
  mod_cast Int.exists_prime_dvd_pow_add_pow_forall_lt_not_dvd_pow_add_pow (a := a) (b := b)
    (mod_cast hpos) (mod_cast hlt) (mod_cast hcopr)
    (by simpa only [ne_eq, Prod.ext_iff, ← Int.ofNat_inj] using h)
