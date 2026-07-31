/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard, Seewoo Lee
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.GCD

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

This result is formalised in Lean: `riemannZeta_two_mul_nat`.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli := (-1)^n * bernoulli'`.

The proof of von Staudt-Clausen's theorem follows Rado's JLMS 1934 paper
"A New Proof of a Theorem of v. Staudt".

## Main theorems

* `sum_bernoulli : ∑ k ∈ range n, (n.choose k : ℚ) * bernoulli k =
  if n = 1 then 1 else 0`
* `Bernoulli.vonStaudt_clausen : bernoulli (2 * k) + ∑ p ∈ range (2 * k + 2)
  with p.Prime ∧ (p - 1) ∣ 2 * k, (1 : ℚ) / p ∈ Set.range Int.cast`

## References

* https://en.wikipedia.org/wiki/Bernoulli_number
* [R. Rado, *A New Proof of a Theorem of v. Staudt*][Rado1934]
-/


@[expose] public section


open Nat Finset Finset.Nat PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-! ### Definitions -/


/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli' (n : ℕ) : ℚ :=
  1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

theorem bernoulli'_def' (n : ℕ) :
    bernoulli' n = 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli']

theorem bernoulli'_def (n : ℕ) :
    bernoulli' n = 1 - ∑ k ∈ range n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli'_def', ← Fin.sum_univ_eq_sum_range]

theorem bernoulli'_spec (n : ℕ) :
    (∑ k ∈ range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli' k) = 1 := by
  rw [sum_range_succ_comm, bernoulli'_def n, tsub_self, choose_zero_right, sub_self, zero_add,
    div_one, cast_one, one_mul, sub_add, ← sum_sub_distrib, ← sub_eq_zero, sub_sub_cancel_left,
    neg_eq_zero]
  exact Finset.sum_eq_zero (fun x hx => by rw [choose_symm (le_of_lt (mem_range.1 hx)), sub_self])

theorem bernoulli'_spec' (n : ℕ) :
    (∑ k ∈ antidiagonal n, ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli' k.1) = 1 := by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

/-! ### Examples -/


section Examples

@[simp]
theorem bernoulli'_zero : bernoulli' 0 = 1 := by
  rw [bernoulli'_def]
  simp

@[simp]
theorem bernoulli'_one : bernoulli' 1 = 1 / 2 := by
  rw [bernoulli'_def]
  norm_num

@[simp]
theorem bernoulli'_two : bernoulli' 2 = 1 / 6 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
theorem bernoulli'_three : bernoulli' 3 = 0 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
theorem bernoulli'_four : bernoulli' 4 = -1 / 30 := by
  have : Nat.choose 4 2 = 6 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero, this]

end Examples

@[simp]
theorem sum_bernoulli' (n : ℕ) : (∑ k ∈ range n, (n.choose k : ℚ) * bernoulli' k) = n := by
  cases n with | zero => simp | succ n =>
  suffices
    ((n + 1 : ℚ) * ∑ k ∈ range n, ↑(n.choose k) / (n - k + 1) * bernoulli' k) =
      ∑ x ∈ range n, ↑(n.succ.choose x) * bernoulli' x by
    rw_mod_cast [sum_range_succ, bernoulli'_def, ← this, choose_succ_self_right]
    ring
  simp_rw [mul_sum, ← mul_assoc]
  refine sum_congr rfl fun k hk => ?_
  congr
  have : ((n - k : ℕ) : ℚ) + 1 ≠ 0 := by norm_cast
  simp only [← cast_sub (mem_range.1 hk).le, succ_eq_add_one, field, mul_comm]
  rw_mod_cast [tsub_add_eq_add_tsub (mem_range.1 hk).le, choose_mul_succ_eq]

/-- The exponential generating function for the Bernoulli numbers `bernoulli' n`. -/
def bernoulli'PowerSeries :=
  mk fun n => algebraMap ℚ A (bernoulli' n / n !)

theorem bernoulli'PowerSeries_mul_exp_sub_one :
    bernoulli'PowerSeries A * (exp A - 1) = X * exp A := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  rw [bernoulli'PowerSeries, coeff_mul, mul_comm X, sum_antidiagonal_succ']
  suffices (∑ p ∈ antidiagonal n,
      bernoulli' p.1 / p.1! * ((p.2 + 1) * p.2! : ℚ)⁻¹) = (n ! : ℚ)⁻¹ by
    simpa [map_sum, Nat.factorial] using congr_arg (algebraMap ℚ A) this
  apply eq_inv_of_mul_eq_one_left
  rw [sum_mul]
  convert! bernoulli'_spec' n using 1
  apply sum_congr rfl
  simp_rw [mem_antidiagonal]
  rintro ⟨i, j⟩ rfl
  have := factorial_mul_factorial_dvd_factorial_add i j
  simp [field, add_choose, *]

/-- Odd Bernoulli numbers (greater than 1) are zero. -/
theorem bernoulli'_eq_zero_of_odd {n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli' n = 0 := by
  let B := mk fun n => bernoulli' n / (n ! : ℚ)
  suffices (B - evalNegHom B) * (exp ℚ - 1) = X * (exp ℚ - 1) by
    rcases mul_eq_mul_right_iff.mp this with h | h <;>
      simp only [PowerSeries.ext_iff, evalNegHom, coeff_X] at h
    · apply eq_zero_of_neg_eq
      specialize h n
      split_ifs at h <;> simp_all [B, h_odd.neg_one_pow, factorial_ne_zero]
    · simpa +decide [Nat.factorial] using h 1
  have h : B * (exp ℚ - 1) = X * exp ℚ := by
    simpa [bernoulli'PowerSeries] using bernoulli'PowerSeries_mul_exp_sub_one ℚ
  rw [sub_mul, h, mul_sub X, sub_right_inj, ← neg_sub, mul_neg, neg_eq_iff_eq_neg]
  suffices evalNegHom (B * (exp ℚ - 1)) * exp ℚ = evalNegHom (X * exp ℚ) * exp ℚ by
    simpa [mul_assoc, sub_mul, mul_comm (evalNegHom (exp ℚ)), exp_mul_exp_neg_eq_one]
  congr

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli (n : ℕ) : ℚ :=
  (-1) ^ n * bernoulli' n

theorem bernoulli'_eq_bernoulli (n : ℕ) : bernoulli' n = (-1) ^ n * bernoulli n := by
  simp [bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 := by simp [bernoulli]

@[simp]
theorem bernoulli_one : bernoulli 1 = -1 / 2 := by norm_num [bernoulli]

@[simp]
theorem bernoulli_two : bernoulli 2 = 6⁻¹ := by
  simp [bernoulli]

@[simp]
theorem bernoulli_eq_zero_of_odd {n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0 := by
  rw [bernoulli, bernoulli'_eq_zero_of_odd h_odd hlt, mul_zero]

theorem bernoulli_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n := by
  cases hn.lt_or_gt with
  | inl hlt => simp [lt_one_iff.mp hlt]
  | inr hgt =>
    cases n.even_or_odd with
    | inl heven => rw [bernoulli, heven.neg_one_pow, one_mul]
    | inr hodd => rw [bernoulli'_eq_zero_of_odd hodd hgt, bernoulli_eq_zero_of_odd hodd hgt]

@[simp]
theorem sum_bernoulli (n : ℕ) :
    (∑ k ∈ range n, (n.choose k : ℚ) * bernoulli k) = if n = 1 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  suffices (∑ i ∈ range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2)) = n / 2 by
    simp only [this, sum_range_succ', cast_succ, bernoulli_one, bernoulli_zero, choose_one_right,
      mul_one, choose_zero_right, cast_zero, if_false, zero_add, succ_succ_ne_one]
    ring
  have f := sum_bernoulli' n.succ.succ
  simp_rw [sum_range_succ', cast_succ, ← eq_sub_iff_add_eq] at f
  refine Eq.trans ?_ (Eq.trans f ?_)
  · congr
    funext x
    rw [bernoulli_eq_bernoulli'_of_ne_one (succ_ne_zero x ∘ succ.inj)]
  · simp only [mul_one, bernoulli'_zero, choose_zero_right,
      zero_add, choose_one_right, cast_succ, bernoulli'_one]
    ring

theorem bernoulli_spec' (n : ℕ) :
    (∑ k ∈ antidiagonal n, ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli k.1) =
      if n = 0 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  rw [if_neg (succ_ne_zero _)]
  -- algebra facts
  have h₁ : (1, n) ∈ antidiagonal n.succ := by simp [mem_antidiagonal, add_comm]
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm]
  -- key equation: the corresponding fact for `bernoulli'`
  have H := bernoulli'_spec' n.succ
  -- massage it to match the structure of the goal, then convert piece by piece
  rw [sum_eq_add_sum_sdiff_singleton_of_mem h₁] at H ⊢
  apply add_eq_of_eq_sub'
  convert! eq_sub_of_add_eq' H using 1
  · refine sum_congr rfl fun p h => ?_
    obtain ⟨h', h''⟩ : p ∈ _ ∧ p ≠ _ := by rwa [mem_sdiff, mem_singleton] at h
    simp [bernoulli_eq_bernoulli'_of_ne_one
      ((not_congr (HasAntidiagonal.antidiagonal_congr h' h₁)).mp h'')]
  · simp [field, h₃]
    norm_num

/-- The exponential generating function for the Bernoulli numbers `bernoulli n`. -/
def bernoulliPowerSeries :=
  mk fun n => algebraMap ℚ A (bernoulli n / n !)

theorem bernoulliPowerSeries_mul_exp_sub_one : bernoulliPowerSeries A * (exp A - 1) = X := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  simp only [bernoulliPowerSeries, coeff_mul, coeff_X, sum_antidiagonal_succ', one_div, coeff_mk,
    coeff_one, coeff_exp, map_sub, factorial, if_pos, cast_succ, cast_mul,
    sub_zero, add_eq_zero, if_false, one_ne_zero, and_false, ← map_mul, ← map_sum]
  cases n with | zero => simp | succ n =>
  rw [if_neg n.succ_succ_ne_one]
  have hfact : ∀ m, (m ! : ℚ) ≠ 0 := fun m => mod_cast factorial_ne_zero m
  have hite2 : ite (n.succ = 0) 1 0 = (0 : ℚ) := if_neg n.succ_ne_zero
  simp only [CharP.cast_eq_zero, zero_add, inv_one, map_one, sub_self, mul_zero]
  rw [← map_zero (algebraMap ℚ A), ← zero_div (n.succ ! : ℚ), ← hite2, ← bernoulli_spec', sum_div]
  refine congr_arg (algebraMap ℚ A) (sum_congr rfl fun x h => eq_div_of_mul_eq (hfact n.succ) ?_)
  rw [mem_antidiagonal] at h
  rw [← h, add_choose, cast_div_charZero (factorial_mul_factorial_dvd_factorial_add _ _)]
  simp [field, mul_comm _ (bernoulli x.1), mul_assoc]

section Faulhaber

/-- **Faulhaber's theorem** relating the **sum of p-th powers** to the Bernoulli numbers:
$$\sum_{k=0}^{n-1} k^p = \sum_{i=0}^p B_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
See https://proofwiki.org/wiki/Faulhaber%27s_Formula and [orosi2018faulhaber] for
the proof provided here. -/
theorem sum_range_pow (n p : ℕ) :
    (∑ k ∈ range n, (k : ℚ) ^ p) =
      ∑ i ∈ range (p + 1), bernoulli i * ((p + 1).choose i) * (n : ℚ) ^ (p + 1 - i) / (p + 1) := by
  have hne : ∀ m : ℕ, (m ! : ℚ) ≠ 0 := fun m => mod_cast factorial_ne_zero m
  -- compute the Cauchy product of two power series
  have h_cauchy :
    ((mk fun p => bernoulli p / p !) * mk fun q => coeff (q + 1) (exp ℚ ^ n)) =
      mk fun p => ∑ i ∈ range (p + 1),
          bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)! := by
    ext q : 1
    let f a b := bernoulli a / a ! * coeff (b + 1) (exp ℚ ^ n)
    -- key step: use `PowerSeries.coeff_mul` and then rewrite sums
    simp only [f, coeff_mul, coeff_mk, sum_antidiagonal_eq_sum_range_succ f]
    apply sum_congr rfl
    intro m h
    simp only [exp_pow_eq_rescale_exp, rescale, RingHom.coe_mk]
    -- manipulate factorials and binomial coefficients
    have h : m < q + 1 := by simpa using h
    rw [choose_eq_factorial_div_factorial h.le, eq_comm, div_eq_iff (hne q.succ), succ_eq_add_one,
      mul_assoc _ _ (q.succ ! : ℚ), mul_comm _ (q.succ ! : ℚ), ← mul_assoc, div_mul_eq_mul_div]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, coeff_exp, Algebra.algebraMap_self, one_div,
      map_inv₀, map_natCast, coeff_mk]
    rw [mul_comm ((n : ℚ) ^ (q - m + 1)), ← mul_assoc _ _ ((n : ℚ) ^ (q - m + 1)), ← one_div,
      mul_one_div, div_div, tsub_add_eq_add_tsub (le_of_lt_succ h), cast_div, cast_mul]
    · ring
    · exact factorial_mul_factorial_dvd_factorial h.le
    · simp [factorial_ne_zero]
  -- same as our goal except we pull out `p!` for convenience
  have hps :
    (∑ k ∈ range n, (k : ℚ) ^ p) =
      (∑ i ∈ range (p + 1),
          bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)!) * p ! := by
    suffices
      (mk fun p => ∑ k ∈ range n, (k : ℚ) ^ p * algebraMap ℚ ℚ p !⁻¹) =
        mk fun p =>
          ∑ i ∈ range (p + 1), bernoulli i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1)! by
      rw [← div_eq_iff (hne p), div_eq_mul_inv, sum_mul]
      rw [PowerSeries.ext_iff] at this
      simpa using this p
    -- the power series `exp ℚ - 1` is non-zero, a fact we need in order to use `mul_right_inj'`
    have hexp : exp ℚ - 1 ≠ 0 := by
      simp only [exp, PowerSeries.ext_iff, Ne, not_forall]
      use 1
      simp
    have h_r : exp ℚ ^ n - 1 = X * mk fun p => coeff (p + 1) (exp ℚ ^ n) := by
      have h_const : C (constantCoeff (exp ℚ ^ n)) = 1 := by simp
      rw [← h_const, sub_const_eq_X_mul_shift]
    -- key step: a chain of equalities of power series
    rw [← mul_right_inj' hexp, mul_comm]
    rw [← exp_pow_sum, geom_sum_mul, h_r, ← bernoulliPowerSeries_mul_exp_sub_one,
      bernoulliPowerSeries, mul_right_comm]
    simp only [mul_comm, mul_eq_mul_left_iff, hexp, or_false]
    refine Eq.trans (mul_eq_mul_right_iff.mpr ?_) (Eq.trans h_cauchy ?_)
    · left
      congr
    · simp only [mul_comm, factorial]
  -- massage `hps` into our goal
  rw [hps, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  simp [field, factorial]

/-- Alternate form of **Faulhaber's theorem**, relating the sum of p-th powers to the Bernoulli
numbers:
$$\sum_{k=1}^{n} k^p = \sum_{i=0}^p (-1)^iB_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
Deduced from `sum_range_pow`. -/
theorem sum_Ico_pow (n p : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ p) =
      ∑ i ∈ range (p + 1), bernoulli' i * (p + 1).choose i * (n : ℚ) ^ (p + 1 - i) / (p + 1) := by
  rw [← Nat.cast_succ]
  -- dispose of the trivial case
  cases p with | zero => simp | succ p =>
  let f i := bernoulli i * p.succ.succ.choose i * (n : ℚ) ^ (p.succ.succ - i) / p.succ.succ
  let f' i := bernoulli' i * p.succ.succ.choose i * (n : ℚ) ^ (p.succ.succ - i) / p.succ.succ
  suffices (∑ k ∈ Ico 1 n.succ, (k : ℚ) ^ p.succ) = ∑ i ∈ range p.succ.succ, f' i by convert!
    this
  -- prove some algebraic facts that will make things easier for us later on
  have hle := Nat.le_add_left 1 n
  have hne : (p + 1 + 1 : ℚ) ≠ 0 := by norm_cast
  have h1 : ∀ r : ℚ, r * (p + 1 + 1) * (n : ℚ) ^ p.succ / (p + 1 + 1 : ℚ) = r * (n : ℚ) ^ p.succ :=
      fun r => by rw [mul_div_right_comm, mul_div_cancel_right₀ _ hne]
  have h2 : f 1 + (n : ℚ) ^ p.succ = 1 / 2 * (n : ℚ) ^ p.succ := by
    simp_rw [f, bernoulli_one, choose_one_right, succ_sub_succ_eq_sub, cast_succ, tsub_zero, h1]
    ring
  have :
    (∑ i ∈ range p, bernoulli (i + 2) * (p + 2).choose (i + 2) * (n : ℚ) ^ (p - i) / ↑(p + 2)) =
      ∑ i ∈ range p, bernoulli' (i + 2) * (p + 2).choose (i + 2) * (n : ℚ) ^ (p - i) / ↑(p + 2) :=
    sum_congr rfl fun i _ => by rw [bernoulli_eq_bernoulli'_of_ne_one (succ_succ_ne_one i)]
  calc
    (-- replace sum over `Ico` with sum over `range` and simplify
        ∑ k ∈ Ico 1 n.succ, (k : ℚ) ^ p.succ)
    _ = ∑ k ∈ range n.succ, (k : ℚ) ^ p.succ := by simp [sum_Ico_eq_sub _ hle]
    -- extract the last term of the sum
    _ = (∑ k ∈ range n, (k : ℚ) ^ p.succ) + (n : ℚ) ^ p.succ := by rw [sum_range_succ]
    -- apply the key lemma, `sum_range_pow`
    _ = (∑ i ∈ range p.succ.succ, f i) + (n : ℚ) ^ p.succ := by simp [f, sum_range_pow]
    -- extract the first two terms of the sum
    _ = (∑ i ∈ range p, f i.succ.succ) + f 1 + f 0 + (n : ℚ) ^ p.succ := by
      simp_rw [sum_range_succ']
    _ = (∑ i ∈ range p, f i.succ.succ) + (f 1 + (n : ℚ) ^ p.succ) + f 0 := by ring
    _ = (∑ i ∈ range p, f i.succ.succ) + 1 / 2 * (n : ℚ) ^ p.succ + f 0 := by rw [h2]
    -- convert from `bernoulli` to `bernoulli'`
    _ = (∑ i ∈ range p, f' i.succ.succ) + f' 1 + f' 0 := by
      simpa [f, f', h1, fun i => show i + 2 = i + 1 + 1 from rfl]
    -- rejoin the first two terms of the sum
    _ = ∑ i ∈ range p.succ.succ, f' i := by simp_rw [sum_range_succ']

end Faulhaber

section vonStaudtClausen

/-!
### The von Staudt-Clausen Theorem

Here we formalize Rado's proof of von Staudt-Clausen's theorem, which states that for any $k \ge 0$,
$$B_{2k} + \sum_{p \text{ prime}, (p - 1) \mid 2k} \frac{1}{p} \in \mathbb{Z}.$$
Rado's proof is based on Faulhaber's theorem and induction on $k$.
-/

namespace Bernoulli

/- Indicator function that is `1` if `(p - 1) ∣ k` and `0` otherwise. -/
private noncomputable def vonStaudtIndicator (k p : ℕ) : ℚ :=
  if (p - 1) ∣ k then 1 else 0

/- The primes `q < 2k + 2` with `(q - 1) ∣ 2k` — the primes appearing in the
von Staudt-Clausen correction sum. -/
private abbrev vonStaudtPrimes (k : ℕ) : Finset ℕ :=
  (range (k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ k

/- Over `ZMod p`, the nonzero `l`-th power sum equals the negative indicator of `(p - 1) ∣ l`. -/
private lemma sum_pow_add_indicator_eq_zero {p : ℕ} (l : ℕ) [Fact p.Prime] :
    (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) + (if (p - 1) ∣ l then (1 : ZMod p) else 0) = 0 := by
  have hbij : (∑ v ∈ Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [not_dvd_of_pos_of_lt])))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]
  grind

/- A rational number `x` is `p`-integral if `p` does not divide its denominator, i.e. it lies in
the valuation subring of the `p`-adic valuation. -/
private abbrev pIntegral (p : ℕ) (x : ℚ) [Fact p.Prime] : Prop := x ∈ (Rat.padicValuation p).integer

private lemma pIntegral_iff_not_dvd_den {p : ℕ} [Fact p.Prime] {x : ℚ} :
    pIntegral p x ↔ ¬ p ∣ x.den :=
  Rat.padicValuation_le_one_iff

@[simp]
lemma Rat.padicValuation_natCast (p : ℕ) [Fact p.Prime] (x : ℕ) :
    Rat.padicValuation p x = Int.padicValuation p x :=
  rfl

/- Dividing a `p`-integral rational by a `p`-coprime nat stays `p`-integral. -/
private lemma pIntegral_div_natCast {p : ℕ} [Fact p.Prime] {a : ℚ} {n : ℕ}
    (ha : pIntegral p a) (hn : ¬ p ∣ n) : pIntegral p (a / n) := by
  have hvn : Rat.padicValuation p n = 1 := by
    simpa [Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
  rw [div_eq_mul_inv]
  exact mul_mem ha (by simp [Valuation.mem_integer_iff, hvn])

/- Denominators of the "other primes" part of the indicator sum
stay coprime to a fixed prime `p`. -/
private lemma prod_one_div_prime_den_coprime (k : ℕ) {p : ℕ} [Fact p.Prime] :
    (∏ q ∈ vonStaudtPrimes k with q ≠ p, ((1 : ℚ) / q).den).Coprime p := by
  refine Nat.Coprime.prod_left fun q hq ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
  rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
  exact (Nat.coprime_primes hq_prime Fact.out).mpr hne

/- Splits the prime-indexed correction sum into the `p`-term (`vonStaudtIndicator / p`)
plus the rest. -/
private lemma sum_one_div_prime_eq_indicator_div_add {k p : ℕ} (hk : k > 0) [Fact p.Prime] :
    (∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q) =
    vonStaudtIndicator k p / p + ∑ q ∈ vonStaudtPrimes k with q ≠ p, (1 : ℚ) / q := by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ ↦ rfl]
  by_cases hdvd : (p - 1) ∣ k
  · have hp_mem : p ∈ vonStaudtPrimes k := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by lia) hdvd; lia), Fact.out, hdvd⟩
    rw [← Finset.add_sum_erase _ _ hp_mem]
    simp [vonStaudtIndicator, hdvd]
  · rw [Finset.erase_eq_of_notMem fun h ↦ hdvd (Finset.mem_filter.mp h).2.2]
    simp [vonStaudtIndicator, hdvd]

/- If the `p`-adic valuation of `M` is at most `N`, then `p^N / M` is `p`-integral. -/
private lemma pIntegral_pow_div {p M N : ℕ} [Fact p.Prime] (hM : M ≠ 0)
    (hv : M.factorization p ≤ N) : pIntegral p ((p : ℚ) ^ N / M) := by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  -- Rewrite p^N / M as p^(N-e) / M' where M' = M / p^e is coprime to p
  have hdecomp : p ^ e * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM_eq : (M : ℚ) = ↑(p ^ e) * ↑M' := by rw [← hdecomp]; simp
  have hrw : (p : ℚ) ^ N / M = (p : ℚ) ^ (N - e) / M' := by
    rw [hM_eq, Nat.cast_pow, div_mul_eq_div_div]
    congr 1
    rw [div_eq_iff (pow_ne_zero e hp_ne), ← pow_add, Nat.sub_add_cancel hv]
  have hM'_eq : ((p : ℚ) ^ (N - e) / (M' : ℚ)) = Rat.divInt (p ^ (N - e) : ℤ) (M' : ℤ) := by
    norm_cast
    simp
  rw [hrw]
  exact pIntegral_iff_not_dvd_den.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).1
    (hM'_cop.coprime_dvd_left (by
      rw [hM'_eq]; exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _))).symm)

/- Main valuation estimate behind the contradiction step for even-index summands. -/
private lemma factorization_succ_le_sub_one {p d : ℕ} [Fact p.Prime] (hd : d ≥ 2) :
    (d + 1).factorization p ≤ d - 1 := by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices ∀ n : ℕ, n ≥ 2 → ¬(p = 2 ∧ n = 2) → n + 1 ≤ p ^ (n - 1) from this d hd hcase
    intro n hn hne'
    induction hn with
    | refl => norm_num at hne' ⊢; lia
    | @step m hm IH =>
      by_cases hm2 : p = 2 ∧ m = 2
      · obtain ⟨rfl, rfl⟩ := hm2; norm_num
      · calc m + 1 + 1 ≤ p ^ (m - 1) + 1 := by linarith [IH hm2]
          _ ≤ p ^ (m - 1) * p := by nlinarith [Nat.one_le_pow (m - 1) p (by lia)]
          _ = p ^ m := by rw [show m = m - 1 + 1 by lia]; exact pow_succ ..

/- Multiplicative variant of the binomial coefficient denominator rewrite
as in Rado's summand. -/
private lemma choose_two_mul_succ_mul_div_eq {k m : ℕ} (x : ℚ) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : ℚ) * x / (2 * k + 1) =
    ((2 * k).choose (2 * m) : ℚ) * x / (2 * k - 2 * m + 1) := by
  rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia), mul_right_comm _ x, mul_right_comm _ x]
  refine congrArg (· * x) ?_
  rw [show (2 * (k : ℚ) - 2 * (m : ℚ) + 1) = (↑(2 * k + 1 - 2 * m) : ℚ) by norm_cast; lia]
  exact_mod_cast Nat.choose_mul_succ_eq (2 * k) (2 * m) |>.symm

/- `p`-integrality of the core even-index summand after denominator normalization. -/
private lemma pIntegral_choose_mul_pow_div {k m p : ℕ} (hm_lt : m < k) [Fact p.Prime]
    (hd : 2 * k - 2 * m ≥ 2) :
    pIntegral p (((2 * k).choose (2 * m) : ℚ) * p ^ (2 * k - 2 * m - 1) / (2 * k - 2 * m + 1)) := by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d + 1 ≠ 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m ≤ 2 * k := by lia
  have h_denom_rat : (2 * (k : ℚ) - 2 * m + 1) = ((d + 1 : ℕ) : ℚ) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h_exp, h_denom_rat, mul_div_assoc]
  exact mul_mem (natCast_mem _ ((2 * k).choose (2 * m)))
    (pIntegral_pow_div hd_plus_one_ne_zero (factorization_succ_le_sub_one hd))

/- Uses the induction hypothesis on `B_{2m} + e_{2m}(p)/p`
to prove `p`-integrality of the even term. -/
private lemma pIntegral_bernoulli_even_term {k m p : ℕ} (hm_lt : m < k) [Fact p.Prime]
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  have hp_ne : (p : ℚ) ≠ 0 := mod_cast (Nat.Prime.ne_zero Fact.out)
  set P := (p : ℚ) ^ (2 * k - 2 * m - 1)
  have hpow : (p : ℚ) ^ (2 * k - 2 * m) = P * p := by
    rw [show 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1 by lia, pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      P / (2 * k + 1) := by rw [hpow]; field_simp [hp_ne]; ring
  rw [hdecomp]
  have hcmp := pIntegral_choose_mul_pow_div (p := p) hm_lt (by lia)
  have H x := choose_two_mul_succ_mul_div_eq x hm_lt
  apply sub_mem
  · rw [mul_assoc, mul_div_assoc]
    apply mul_mem ih
    have hpow_mul : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) /
        (2 * k - 2 * m + 1) =
        (p : ℚ) * (((2 * k).choose (2 * m) : ℚ) * P / (2 * k - 2 * m + 1)) := by
      rw [hpow]; ring
    rw [H, hpow_mul]
    exact mul_mem (natCast_mem _ p) hcmp
  · unfold vonStaudtIndicator
    split_ifs
    · grind
    · simp

/- The full remainder sum in Faulhaber's formula is `p`-integral. -/
private lemma pIntegral_faulhaber_sum {k p : ℕ} [Fact p.Prime]
    (ih : ∀ m < k, 0 < m → pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (∑ i ∈ range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * p ^ (2 * k - i) / (2 * k + 1)) := by
  refine (Rat.padicValuation p).map_sum_le fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div (by lia)
      (factorization_succ_le_sub_one (by lia) |>.trans tsub_le_self)
  · rw [zero_add, Nat.choose_one_right, bernoulli_one]
    push_cast
    field_simp
    obtain rfl | hp2 := eq_or_ne p 2
    · push_cast
      rw [show 2 * k - 1 = (2 * k - 2) + 1 by lia, pow_succ, mul_div_cancel_right₀ _ two_ne_zero]
      exact_mod_cast Int.padicValuation_le_one ..
    · rw [Valuation.map_neg]
      refine pIntegral_pow_div two_ne_zero <|
         (factorization_eq_zero_of_lt ?_).trans_le (by lia)
      exact (Prime.odd_iff Fact.out).mp <| Prime.odd_of_ne_two Fact.out hp2
  · rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | hodd
    · have ⟨hm_pos, hm_lt, hi_eq⟩ : 0 < m ∧ m < k ∧ i + 2 = 2 * m := by lia
      simp only [hi_eq]
      exact pIntegral_bernoulli_even_term hm_lt (ih m hm_lt hm_pos)
    · simp [bernoulli_eq_zero_of_odd hodd (by lia)]

private lemma sum_pow_filter_eq_faulhaber {k : ℕ} (p : ℕ) (hk : 0 < k) :
    (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) =
      (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k) := by
  have hfilter : (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) = ∑ v ∈ range p, (v : ℚ) ^ (2 * k) := by
    cases p <;> simp [Finset.sum_range_eq_add_Ico, show 2 * k ≠ 0 by lia]
  rw [hfilter, sum_range_pow, Finset.sum_range_succ, Nat.choose_succ_self_right,
    show 2 * k + 1 - 2 * k = 1 by lia]
  push_cast
  field_simp

private lemma faulhaber_sum_div_prime_eq {k p : ℕ} [Fact p.Prime] :
    (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
      (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1 : ℚ)) / (p : ℚ) =
      ∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
        (p : ℚ) ^ (2 * k - i) / (2 * k + 1 : ℚ) := by
  have hp_ne : (p : ℚ) ≠ 0 := mod_cast (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have := Finset.mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by lia, pow_succ]
  field_simp [hp_ne]

/- Rearranges the Faulhaber identity and power-sum congruence to isolate
`bernoulli (2*k) + vonStaudtIndicator (2*k) p / p`. -/
private lemma bernoulli_add_indicator_eq_sub {k p : ℕ} (hk : k > 0) [Fact p.Prime] :
    ∃ T : ℤ, bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  have hcast : (↑((∑ v ∈ Ico 1 p, (v : ℤ) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 :=
    mod_cast sum_pow_add_indicator_eq_zero (p := p) _
  obtain ⟨T, hT_int⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  use T
  have hT : (∑ v ∈ Ico 1 p, (v : ℚ) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      p * T := by unfold vonStaudtIndicator; exact_mod_cast hT_int
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hAlg : bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) / p := by
    field_simp [hp_ne]; linarith [hT, sum_pow_filter_eq_faulhaber p hk]
  rw [hAlg]; congr 1; simpa using faulhaber_sum_div_prime_eq

/- For fixed prime `p`, the denominator of `B_{2k} + e_{2k}(p)/p` is not divisible by `p`. -/
private lemma pIntegral_bernoulli_add_indicator {p : ℕ} [Fact p.Prime] :
    ∀ {k}, k > 0 → Even k → pIntegral p (bernoulli k + vonStaudtIndicator k p / p) := by
  suffices ∀ k > 0, pIntegral p (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p) by
    grind [even_iff_exists_two_mul]
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    exact sub_mem (intCast_mem _ T) (pIntegral_faulhaber_sum ih)

lemma not_dvd_den_bernoulli_add_ite {p k : ℕ} (hp : p.Prime)
    (hk₀ : k ≠ 0) (hk : Even k) : ¬ p ∣ (bernoulli k + (if p - 1 ∣ k then 1 else 0) / p).den := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← pIntegral_iff_not_dvd_den]
  exact pIntegral_bernoulli_add_indicator hk₀.bot_lt hk

/-- For even `m > 0`, a prime `p` divides the denominator of `bernoulli m` exactly when
`(p - 1) ∣ m`. See `sub_one_dvd_of_dvd_den_bernoulli` -/
theorem dvd_den_bernoulli_iff {p k : ℕ} (hp : p.Prime) (hm : Even k) (hm0 : k ≠ 0) :
    p ∣ (bernoulli k).den ↔ p - 1 ∣ k := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← not_iff_not, ← pIntegral_iff_not_dvd_den]
  have : pIntegral p (bernoulli k + vonStaudtIndicator k p / p) :=
    pIntegral_bernoulli_add_indicator (by lia) hm
  refine ⟨fun h ↦ ?_, by grind [vonStaudtIndicator]⟩
  have h1p : ¬ pIntegral p (1 / p) := by simp [pIntegral_iff_not_dvd_den, hp.ne_zero]
  contrapose! h1p
  simpa [vonStaudtIndicator, h1p] using sub_mem this h

/--
If a prime `p` divides the denominator of a Bernoulli number `bernoulli k` then `p - 1 ∣ k`.
A convenient corollary of the von Staudt-Clausen theorem, see `vonStaudt_clausen`.
See also `dvd_den_bernoulli_iff` for the double implication, with stronger hypotheses.
-/
theorem sub_one_dvd_of_dvd_den_bernoulli {p k : ℕ} (hp : p.Prime) (hk : p ∣ (bernoulli k).den) :
    p - 1 ∣ k := by
  obtain rfl | rfl | he | ⟨ho, hk₁⟩ : k = 0 ∨ k = 1 ∨ (Even k ∧ k ≠ 0) ∨ (Odd k ∧ 1 < k) := by grind
  · simp
  · obtain rfl : p = 2 := by revert hk; rw [← Nat.prime_dvd_prime_iff_eq hp (by decide)]; norm_num
    grind
  · grind [dvd_den_bernoulli_iff]
  · simp [bernoulli_eq_zero_of_odd ho hk₁, hp.ne_one] at hk

/- For `(p - 1) ∤ k`, `bernoulli k` is `p`-integral (contrapositive of
`sub_one_dvd_of_dvd_den_bernoulli`). -/
private theorem pIntegral_bernoulli_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ p - 1 ∣ k) :
    pIntegral p (bernoulli k) :=
  pIntegral_iff_not_dvd_den.2 (mt (sub_one_dvd_of_dvd_den_bernoulli Fact.out) hk)

private theorem pIntegral_mul_bernoulli {p k : ℕ} [Fact p.Prime] :
    pIntegral p (p * bernoulli k) := by
  have hp : p.Prime := Fact.out
  obtain rfl | rfl | he | ⟨ho, hk₁⟩ : k = 0 ∨ k = 1 ∨ (Even k ∧ k ≠ 0) ∨ (Odd k ∧ 1 < k) := by grind
  · simp
  · obtain rfl | hodd := hp.eq_two_or_odd'
    · norm_num
    have : p * bernoulli 1 = (-p) / (2 : ℕ) := by norm_num; ring
    rw [this]
    apply pIntegral_div_natCast (by simp)
    rw [Nat.prime_dvd_prime_iff_eq hp (by decide)]
    grind
  · have hid : p * (bernoulli k + vonStaudtIndicator k p / p) - vonStaudtIndicator k p =
        p * bernoulli k := by
      field [hp.ne_zero]
    rw [← hid]
    apply sub_mem (mul_mem (natCast_mem _ p) (pIntegral_bernoulli_add_indicator (by lia) (by lia)))
    simp [vonStaudtIndicator, apply_ite]
  · simp [bernoulli_eq_zero_of_odd ho hk₁]

theorem not_dvd_mul_bernoulli {p k : ℕ} (hp : p.Prime) :
    ¬ p ∣ (p * bernoulli k).den := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← pIntegral_iff_not_dvd_den]
  exact pIntegral_mul_bernoulli

theorem squarefree_den_bernoulli {k : ℕ} :
    Squarefree (bernoulli k).den := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp h
  suffices p ∣ (p * bernoulli k).den by grind [not_dvd_mul_bernoulli]
  apply Nat.dvd_of_mul_dvd_mul_left hp.pos
  calc
    p * p ∣ (bernoulli k).den := h
    _ = ((1 / p) * (p * bernoulli k)).den := by congr! 1; field [hp.ne_zero]
    _ ∣ (1 / p : ℚ).den * (p * bernoulli k).den := Rat.mul_den_dvd _ _
    _ = _ := by simp [hp.ne_zero]

/- Extends the fixed-prime nondivisibility result to the full prime correction sum. -/
private lemma not_dvd_den_vonStaudt_sum {k p : ℕ} (hk : Even k) [Fact p.Prime] :
    pIntegral p (bernoulli k + ∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q) := by
  obtain rfl | hk₀ : k = 0 ∨ k > 0 := by grind [even_iff_exists_two_mul]
  · simp [vonStaudtPrimes, range_add_one, not_prime_one, not_prime_zero, Finset.filter_insert,
      Finset.filter_singleton]
  rw [sum_one_div_prime_eq_indicator_div_add (p := p) (by lia), ← add_assoc]
  apply add_mem (pIntegral_bernoulli_add_indicator hk₀ hk) (_ : pIntegral _ _)
  rw [pIntegral_iff_not_dvd_den, ← Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact (prod_one_div_prime_den_coprime _).symm.of_dvd_right (Rat.den_sum_dvd_prod_den _ _)

/-- **von Staudt-Clausen theorem:** For any natural number $k$, the sum
$$B_{2k} + \sum_{p - 1 \mid 2k} \frac{1}{p}$$ is an integer.
-/
theorem vonStaudt_clausen {k : ℕ} (hk : Even k) :
    bernoulli k + ∑ p ∈ range (k + 2) with p.Prime ∧ p - 1 ∣ k, (1 / p : ℚ) ∈
      Set.range Int.cast := by
  rw [Set.mem_range]
  refine ⟨_, Rat.coe_int_num_of_den_eq_one <| eq_one_iff_not_exists_prime_dvd.2 fun p hp ↦ ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [← pIntegral_iff_not_dvd_den]
  exact not_dvd_den_vonStaudt_sum hk

/- `p · bernoulli i` is `p`-integral for every `i` (von Staudt: `v_p(B_i) ≥ -1`). -/
private theorem pIntegral_p_mul_bernoulli {p : ℕ} [Fact p.Prime] (i : ℕ) :
    pIntegral p (p * bernoulli i) := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd i with he | ho
  · obtain ⟨l, rfl⟩ := even_iff_exists_two_mul.1 he
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have hid : p * (bernoulli (2 * l) + vonStaudtIndicator (2 * l) p / p)
                 - vonStaudtIndicator (2 * l) p = p * bernoulli (2 * l) := by
        field [hp.ne_zero]
      rw [← hid]
      apply sub_mem (mul_mem (natCast_mem _ p) (pIntegral_bernoulli_add_indicator (by lia) he))
      simp [vonStaudtIndicator, apply_ite]
  · obtain rfl | hne := eq_or_ne i 1
    · rw [bernoulli_one]
      obtain rfl | hp2 := eq_or_ne p 2
      · norm_num
      · have h2 : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        have hph : ((p : ℚ) * (-1 / 2) : ℚ) = -((p : ℚ) / (2 : ℕ)) := by push_cast; ring
        rw [hph]
        exact neg_mem (pIntegral_div_natCast (natCast_mem _ p) h2)
    · obtain ⟨m, rfl⟩ := ho
      rw [bernoulli_eq_zero_of_odd ⟨m, rfl⟩ (by lia), mul_zero]
      exact zero_mem _

/-- `(p : ℚ) · bernoulli i` is `p`-integral: `p` does not divide the denominator of `p · Bᵢ`
(equivalently `v_p(Bᵢ) ≥ -1`). -/
theorem not_dvd_den_p_mul_bernoulli {p : ℕ} [Fact p.Prime] (i : ℕ) :
    ¬ p ∣ ((p : ℚ) * bernoulli i).den :=
  Rat.padicValuation_le_one_iff.mp (pIntegral_p_mul_bernoulli i)

/- The denominator of a `p`-integral rational is a unit mod `p`. -/
private theorem den_ne {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : pIntegral p x) :
    (x.den : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Rat.padicValuation_le_one_iff.mp hx

/- Casting respects addition of two `p`-integral rationals. -/
private theorem cast_add_pIntegral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : pIntegral p a) (hb : pIntegral p b) :
    (((a + b : ℚ)) : ZMod p) = (a : ZMod p) + (b : ZMod p) :=
  Rat.cast_add_of_ne_zero (den_ne ha) (den_ne hb)

/- Casting respects multiplication of two `p`-integral rationals. -/
private theorem cast_mul_pIntegral {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : pIntegral p a) (hb : pIntegral p b) :
    (((a * b : ℚ)) : ZMod p) = (a : ZMod p) * (b : ZMod p) :=
  Rat.cast_mul_of_ne_zero (den_ne ha) (den_ne hb)

/- `w + 4 ≤ 5 ^ (w + 1)`. -/
private theorem five_pow_ge (w : ℕ) : w + 4 ≤ 5 ^ (w + 1) := by
  induction w with
  | zero => norm_num
  | succ n ih =>
    have hps : (5 : ℕ) ^ (n + 1 + 1) = 5 ^ (n + 1) * 5 := pow_succ 5 (n + 1)
    nlinarith [ih, hps]

/- For `q ≥ 5` and `j ≥ 3`, the `q`-adic valuation of `j` undershoots `j` by at least `3`. -/
private theorem factorization_add_three_le {q : ℕ} (hq5 : 5 ≤ q) {j : ℕ} (hj : 3 ≤ j) :
    j.factorization q + 3 ≤ j := by
  have hj0 : j ≠ 0 := by omega
  have hqv : q ^ j.factorization q ≤ j := Nat.ordProj_le q hj0
  have key : ∀ v : ℕ, q ^ v ≤ j → v + 3 ≤ j := by
    intro v hqvj
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · omega
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have hgrow := five_pow_ge w
      have hmono : (5 : ℕ) ^ (w + 1) ≤ q ^ (w + 1) := Nat.pow_le_pow_left hq5 (w + 1)
      omega
  exact key _ hqv

/-- **Faulhaber mod `p²`.** For even `k ≥ 2` with `(p - 1) ∤ k`, the power sum `∑_{a<p} aᵏ`
equals `p·Bₖ` up to a `p²`-multiple of a `p`-integral rational: there is `W` with
`p ∤ W.den` and `∑_{a<p} aᵏ − p·Bₖ = p²·W`. -/
theorem faulhaber_mod_sq {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k)
    (hk1 : ¬ (p - 1) ∣ k) :
    ∃ W : ℚ, ¬ p ∣ W.den ∧
      (∑ a ∈ range p, (a : ℚ) ^ k) - (p : ℚ) * bernoulli k = (p : ℚ) ^ 2 * W := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two (fun h => hk1 (h ▸ one_dvd k))
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hlt5 : p < 5 := by omega
    interval_cases p
    · exact (by decide : ¬ Odd 2) hpodd
    · exact hk1 hk.two_dvd
    · exact absurd hp (by decide)
  have hkm1 : ¬ (p - 1) ∣ (k - 1) := by
    obtain ⟨s, hs⟩ := hpodd
    obtain ⟨r, hr⟩ := hk
    rintro ⟨t, ht⟩
    have hp1 : p - 1 = 2 * s := by omega
    have hev : k - 1 = 2 * (s * t) := by rw [ht, hp1]; ring
    omega
  refine ⟨∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / (k + 1),
    ?_, ?_⟩
  · rw [← Rat.padicValuation_le_one_iff]
    refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
    rw [mem_range] at hi
    have hden2 : ((k + 1 - i : ℕ) : ℚ) ≠ 0 := by rw [Ne, Nat.cast_eq_zero]; omega
    have habs : bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / (k + 1)
        = bernoulli i * (k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ) := by
      have hk1' : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [div_eq_div_iff (by positivity) hden2, hk1']
      have hnat : ((k + 1).choose i : ℚ) * ((k + 1 - i : ℕ) : ℚ)
          = (k.choose i : ℚ) * ((k + 1 : ℕ) : ℚ) := by
        exact_mod_cast (Nat.choose_mul_succ_eq k i).symm
      linear_combination (bernoulli i * (p : ℚ) ^ (k - 1 - i)) * hnat
    rw [habs]
    rcases Nat.lt_or_ge i (k - 1) with hlt | hge
    · have hpeel : (p : ℚ) ^ (k - 1 - i) = (p : ℚ) * (p : ℚ) ^ (k - 2 - i) := by
        rw [show k - 1 - i = 1 + (k - 2 - i) by omega, pow_add, pow_one]
      have hregroup : bernoulli i * (k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 2 - i))
            / ((k + 1 - i : ℕ) : ℚ)
          = ((p : ℚ) * bernoulli i)
            * ((k.choose i : ℚ) * ((p : ℚ) ^ (k - 2 - i) / ((k + 1 - i : ℕ) : ℚ))) := by ring
      rw [hpeel, hregroup]
      refine mul_mem (pIntegral_p_mul_bernoulli i) (mul_mem (natCast_mem _ _) ?_)
      refine pIntegral_pow_div (by omega) ?_
      have h3 : 3 ≤ k + 1 - i := by omega
      have hb := factorization_add_three_le hp5 h3
      omega
    · have hik : i = k - 1 := by omega
      subst hik
      have hz : k - 1 - (k - 1) = 0 := by omega
      have htwo : k + 1 - (k - 1) = 2 := by omega
      rw [hz, pow_zero, mul_one, htwo]
      refine pIntegral_div_natCast
        (mul_mem (pIntegral_bernoulli_of_not_dvd hkm1) (natCast_mem _ _)) ?_
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  · rw [sum_range_pow p k, Finset.sum_range_succ]
    have hfk : bernoulli k * ((k + 1).choose k : ℚ) * (p : ℚ) ^ (k + 1 - k) / (k + 1)
        = (p : ℚ) * bernoulli k := by
      have hone : k + 1 - k = 1 := by omega
      rw [Nat.choose_succ_self_right, hone, pow_one]
      push_cast
      field_simp
    rw [hfk, Finset.mul_sum]
    have hcancel :
        (∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1))
          + (p : ℚ) * bernoulli k - (p : ℚ) * bernoulli k
        = ∑ i ∈ range k,
            bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1) := by
      ring
    rw [hcancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have hsplit : k + 1 - i = (k - 1 - i) + 2 := by omega
    rw [hsplit, pow_add]
    ring

/- The first two binomial terms; `y²` divides the rest. -/
private theorem binom_sub_two_terms_dvd_sq (y r : ℤ) (k : ℕ) :
    (y ^ 2 : ℤ) ∣ (y + r) ^ k - r ^ k - (k : ℤ) * r ^ (k - 1) * y := by
  rw [add_comm y r]
  exact sq_dvd_add_pow_sub_pow_sub r y k

/- `j ↦ (c·j) mod p` permutes `[1, p-1]`, so the power sum is unchanged. -/
private theorem sum_pow_mod_perm {p : ℕ} [Fact p.Prime] {c : ℕ} (hc : ¬ p ∣ c) (k : ℕ) :
    ∑ j ∈ Ico 1 p, ((c * j) % p) ^ k = ∑ j ∈ Ico 1 p, j ^ k := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hc0 : (c : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hc
  set d := ((c : ZMod p)⁻¹).val with hd
  have hd0 : ¬ p ∣ d := by
    rw [← ZMod.natCast_eq_zero_iff, hd, ZMod.natCast_zmod_val]; exact inv_ne_zero hc0
  have hcd : c * d ≡ 1 [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hd, ZMod.natCast_zmod_val, mul_inv_cancel₀ hc0]
  have key : ∀ a b : ℕ, a * b ≡ 1 [MOD p] → ∀ x, a * ((b * x) % p) % p = x % p := by
    intro a b hab x
    calc a * ((b * x) % p) % p
        = (a * (b * x)) % p := ((Nat.mod_modEq _ _).mul_left a)
      _ = ((a * b) * x) % p := by rw [mul_assoc]
      _ = (1 * x) % p := (hab.mul_right x)
      _ = x % p := by rw [one_mul]
  have mem_of : ∀ a : ℕ, ¬ p ∣ a → ∀ j ∈ Ico 1 p, (a * j) % p ∈ Ico 1 p := by
    intro a ha j hj
    rw [mem_Ico] at hj ⊢
    obtain ⟨hj1, hj2⟩ := hj
    have hpj : ¬ p ∣ j := fun h => by have := Nat.le_of_dvd (by lia) h; lia
    have hpaj : ¬ p ∣ (a * j) := fun h => (hp.dvd_mul.1 h).elim ha hpj
    exact ⟨Nat.one_le_iff_ne_zero.2 (fun h0 => hpaj (Nat.dvd_of_mod_eq_zero h0)),
      Nat.mod_lt _ (by lia)⟩
  refine Finset.sum_bij' (fun j _ => (c * j) % p) (fun y _ => (d * y) % p)
    (fun j hj => mem_of c hc j hj) (fun y hy => mem_of d hd0 y hy) ?_ ?_ (fun j _ => rfl)
  · intro j hj
    rw [mem_Ico] at hj
    rw [key d c (by rw [Nat.mul_comm]; exact hcd) j, Nat.mod_eq_of_lt hj.2]
  · intro y hy
    rw [mem_Ico] at hy
    rw [key c d hcd y, Nat.mod_eq_of_lt hy.2]

/- The integer heart of Voronoi's congruence: `p² ∣ (cᵏ−1)·S − k·p·c^{k-1}·V` where `S = ∑ jᵏ`
and `V = ∑ ⌊cj/p⌋·j^{k-1}` over `[1, p-1]`. -/
private theorem voronoi_int {p : ℕ} [Fact p.Prime] {c k : ℕ} (hc : ¬ p ∣ c) :
    (p ^ 2 : ℤ) ∣ ((c : ℤ) ^ k - 1) * (∑ j ∈ Ico 1 p, (j : ℤ) ^ k)
      - (k : ℤ) * p * (c : ℤ) ^ (k - 1) *
        (∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1)) := by
  set S : ℤ := ∑ j ∈ Ico 1 p, (j : ℤ) ^ k with hS
  set A : ℤ := ∑ j ∈ Ico 1 p, ((c * j : ℕ) : ℤ) ^ k with hA
  set R : ℤ := ∑ j ∈ Ico 1 p, (((c * j) % p : ℕ) : ℤ) ^ k with hR
  set Q : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1) with hQ
  set V : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1) with hV
  have e1 : (c : ℤ) ^ k * S = A := by
    rw [hS, hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; rw [mul_pow]
  have e2 : R = S := by
    rw [hR, hS]; exact_mod_cast sum_pow_mod_perm hc k
  have e3 : (p ^ 2 : ℤ) ∣ (A - R - (k : ℤ) * p * Q) := by
    rw [hA, hR, hQ, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    have hyr : ((c * j : ℕ) : ℤ) = (p : ℤ) * ((c * j / p : ℕ) : ℤ) + (((c * j) % p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod (c * j) p).symm
    have hb := binom_sub_two_terms_dvd_sq ((p : ℤ) * ((c * j / p : ℕ) : ℤ))
      (((c * j) % p : ℕ) : ℤ) k
    have hpq : (p ^ 2 : ℤ) ∣ ((p : ℤ) * ((c * j / p : ℕ) : ℤ)) ^ 2 :=
      ⟨((c * j / p : ℕ) : ℤ) ^ 2, by ring⟩
    have hd := dvd_trans hpq hb
    rw [← hyr] at hd
    have heq : ((c * j : ℕ) : ℤ) ^ k - (((c * j) % p : ℕ) : ℤ) ^ k
        - (k : ℤ) * p * (((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1))
        = ((c * j : ℕ) : ℤ) ^ k - (((c * j) % p : ℕ) : ℤ) ^ k
          - (k : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1) * ((p : ℤ) * ((c * j / p : ℕ) : ℤ)) := by
      ring
    rw [heq]
    exact hd
  have e4 : (p : ℤ) ∣ (Q - (c : ℤ) ^ (k - 1) * V) := by
    rw [hQ, hV, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    have hcong : (((c * j) % p : ℕ) : ℤ) ≡ (c : ℤ) * (j : ℤ) [ZMOD p] := by
      have hmul : (c : ℤ) * (j : ℤ) = ((c * j : ℕ) : ℤ) := by push_cast; ring
      rw [hmul]
      exact_mod_cast Nat.mod_modEq (c * j) p
    have hpow : (((c * j) % p : ℕ) : ℤ) ^ (k - 1) ≡ ((c : ℤ) * (j : ℤ)) ^ (k - 1) [ZMOD p] :=
      hcong.pow _
    have hpd : (p : ℤ) ∣
        (((c * j) % p : ℕ) : ℤ) ^ (k - 1) - (c : ℤ) ^ (k - 1) * (j : ℤ) ^ (k - 1) := by
      rw [mul_pow] at hpow
      exact (Int.modEq_iff_dvd.mp hpow.symm)
    have hfactor : ((c * j / p : ℕ) : ℤ) * (((c * j) % p : ℕ) : ℤ) ^ (k - 1)
          - (c : ℤ) ^ (k - 1) * (((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1))
        = ((c * j / p : ℕ) : ℤ) * ((((c * j) % p : ℕ) : ℤ) ^ (k - 1)
          - (c : ℤ) ^ (k - 1) * (j : ℤ) ^ (k - 1)) := by ring
    rw [hfactor]
    exact hpd.mul_left _
  obtain ⟨u, hu⟩ := e3
  obtain ⟨w, hw⟩ := e4
  refine ⟨u + (k : ℤ) * w, ?_⟩
  rw [sub_mul, one_mul, e1, ← e2]
  linear_combination hu + ((k : ℤ) * p) * hw

/-- The floor-weighted power sum `∑_{j=1}^{p-1} ⌊cj/p⌋ · j^{k-1}` over `ZMod p`, appearing in
Voronoi's congruence for Bernoulli numbers. -/
noncomputable def voronoiSum {p : ℕ} (c k : ℕ) : ZMod p :=
  ∑ j ∈ Ico 1 p, (c * j / p : ℕ) * j ^ (k - 1)

/-- **Voronoi's congruence.** For `c` coprime to a prime `p`, even `k ≥ 2` with `(p - 1) ∤ k`,
`(cᵏ − 1) · Bₖ ≡ k · c^{k-1} · voronoiSum c k (mod p)`.  The hypothesis `(p - 1) ∤ k` makes
`bernoulli k` `p`-integral, so its cast to `ZMod p` is the genuine value. -/
theorem voronoi_congr {p : ℕ} [Fact p.Prime] {c k : ℕ} (hc : ¬ p ∣ c) (hk1 : ¬ (p - 1) ∣ k)
    (hk : Even k) (hk2 : 2 ≤ k) :
    ((c : ZMod p) ^ k - 1) * (bernoulli k : ZMod p)
      = (k : ZMod p) * (c : ZMod p) ^ (k - 1) * voronoiSum (p := p) c k := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨C, hC⟩ := voronoi_int (p := p) hc
  obtain ⟨W, hWden, hWeq⟩ := faulhaber_mod_sq (p := p) hk hk2 hk1
  have hWpint : pIntegral p W := Rat.padicValuation_le_one_iff.mpr hWden
  set Sz : ℤ := ∑ j ∈ Ico 1 p, (j : ℤ) ^ k with hSz
  set Vz : ℤ := ∑ j ∈ Ico 1 p, ((c * j / p : ℕ) : ℤ) * (j : ℤ) ^ (k - 1) with hVz
  have hpck : pIntegral p ((c : ℚ) ^ k) := by
    have hck : (c : ℚ) ^ k = ((c ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [hck]
    exact natCast_mem _ _
  have hpc : pIntegral p ((c : ℚ) ^ k - 1) := sub_mem hpck (one_mem _)
  have hpB : pIntegral p (bernoulli k) := pIntegral_bernoulli_of_not_dvd hk1
  have cast_sub_pIntegral : ∀ {a b : ℚ}, pIntegral p a → pIntegral p b →
      (((a - b : ℚ)) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
    intro a b ha hb
    rw [sub_eq_add_neg, cast_add_pIntegral ha (neg_mem hb), Rat.cast_neg, ← sub_eq_add_neg]
  have hSQ : (∑ a ∈ range p, (a : ℚ) ^ k) = (Sz : ℚ) := by
    rw [hSz]
    push_cast
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx; rw [mem_Ico] at hx; rw [mem_range]; lia
    · intro x hx hx2
      rw [mem_range] at hx
      rw [mem_Ico] at hx2
      have hx0 : x = 0 := by lia
      have hk0 : k ≠ 0 := by lia
      rw [hx0]
      simp [zero_pow hk0]
  have hCq : ((c : ℚ) ^ k - 1) * (Sz : ℚ) - (k : ℚ) * p * (c : ℚ) ^ (k - 1) * (Vz : ℚ)
      = (p : ℚ) ^ 2 * (C : ℚ) := by
    exact_mod_cast hC
  have hWq : (Sz : ℚ) - (p : ℚ) * bernoulli k = (p : ℚ) ^ 2 * W := by rw [← hSQ]; exact hWeq
  set M : ℚ := (C : ℚ) - ((c : ℚ) ^ k - 1) * W with hM
  have hMpint : pIntegral p M :=
    sub_mem (intCast_mem _ C) (mul_mem hpc hWpint)
  have hstar : ((c : ℚ) ^ k - 1) * bernoulli k
      = (k : ℚ) * (c : ℚ) ^ (k - 1) * (Vz : ℚ) + (p : ℚ) * M := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hM]
    linear_combination hCq - ((c : ℚ) ^ k - 1) * hWq
  have hVzcast : ((Vz : ℤ) : ZMod p) = voronoiSum (p := p) c k := by
    rw [hVz, voronoiSum, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast]
  have castL : ((((c : ℚ) ^ k - 1) * bernoulli k : ℚ) : ZMod p)
      = ((c : ZMod p) ^ k - 1) * (bernoulli k : ZMod p) := by
    have hck : (c : ℚ) ^ k = ((c ^ k : ℕ) : ℚ) := by push_cast; ring
    rw [cast_mul_pIntegral hpc hpB, cast_sub_pIntegral hpck (one_mem _), Rat.cast_one,
      hck, Rat.cast_natCast]
    push_cast
    ring
  have hck1 : (c : ℚ) ^ (k - 1) = ((c ^ (k - 1) : ℕ) : ℚ) := by push_cast; ring
  have hpck1 : pIntegral p ((c : ℚ) ^ (k - 1)) := by
    rw [hck1]
    exact natCast_mem _ _
  have castR : (((k : ℚ) * (c : ℚ) ^ (k - 1) * (Vz : ℚ) + (p : ℚ) * M : ℚ) : ZMod p)
      = (k : ZMod p) * (c : ZMod p) ^ (k - 1) * voronoiSum (p := p) c k := by
    rw [cast_add_pIntegral
        (mul_mem (mul_mem (natCast_mem _ k) hpck1) (intCast_mem _ Vz))
        (mul_mem (natCast_mem _ p) hMpint),
      cast_mul_pIntegral (mul_mem (natCast_mem _ k) hpck1) (intCast_mem _ Vz),
      cast_mul_pIntegral (natCast_mem _ k) hpck1,
      cast_mul_pIntegral (natCast_mem _ p) hMpint,
      Rat.cast_natCast, Rat.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
      hck1, Rat.cast_natCast, Rat.cast_intCast, hVzcast]
    push_cast
    ring
  rw [← castL, ← castR, hstar]

/- A primitive root mod `p`: `c : ℕ` coprime to `p` whose powers hit `1` exactly on multiples
of `p - 1`. -/
private theorem exists_primitiveRoot {p : ℕ} [Fact p.Prime] :
    ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, (c : ZMod p) ^ k = 1 ↔ (p - 1) ∣ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  refine ⟨(g : ZMod p).val, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]
    exact Units.ne_zero g
  · intro k
    have hcast : ((g : ZMod p).val : ZMod p) = (g : ZMod p) := ZMod.natCast_zmod_val _
    rw [hcast, ← Units.val_pow_eq_pow_val, ← Units.val_one (α := ZMod p),
      Units.val_inj, ← orderOf_dvd_iff_pow_eq_one, hord]

/-- **Kummer's congruence** (weak form, mod `p`).  For even indices `m ≡ n (mod p - 1)` with
`(p - 1) ∤ m`, the denominator-cleared residues satisfy `n · Bₘ ≡ m · Bₙ (mod p)`.  This is
`Bₘ / m ≡ Bₙ / n` with denominators cleared, and it holds even when `p ∣ m` (both sides vanish). -/
theorem kummer_congr {p : ℕ} [Fact p.Prime] {m n : ℕ} (hmn : m ≡ n [MOD p - 1])
    (hm : ¬ (p - 1) ∣ m) (hm1 : m ≠ 1) (hn1 : n ≠ 1) :
    (n : ZMod p) * (bernoulli m : ZMod p) = (m : ZMod p) * (bernoulli n : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two (fun h => hm (h ▸ one_dvd m))
  have h2dvd : 2 ∣ (p - 1) := by obtain ⟨s, hs⟩ := hpodd; omega
  have hpar : m % 2 = n % 2 := Nat.ModEq.of_dvd h2dvd hmn
  have hm2 : 2 ≤ m := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    omega
  have hn2 : 2 ≤ n := by
    have hn0 : n ≠ 0 := by rintro rfl; exact hm (Nat.modEq_zero_iff_dvd.mp hmn)
    omega
  rcases Nat.even_or_odd m with hmeven | hmodd
  · have hneven : Even n := by rw [Nat.even_iff] at hmeven ⊢; omega
    obtain ⟨c, hc, hcord⟩ := exists_primitiveRoot (p := p)
    have hc0 : (c : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hc
    have hn : ¬ (p - 1) ∣ n := fun hdvd =>
      hm (Nat.modEq_zero_iff_dvd.mp (hmn.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
    have hper : ∀ (x : ZMod p) (a b : ℕ), x ≠ 0 → a ≡ b [MOD p - 1] → x ^ a = x ^ b := by
      intro x a b hx hab
      have hx1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
      rcases Nat.le_total b a with hle | hle
      · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hab.symm
        have hsplit : a = b + (p - 1) * t := by lia
        rw [hsplit, pow_add, pow_mul, hx1, one_pow, mul_one]
      · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).mp hab
        have hsplit : b = a + (p - 1) * t := by lia
        rw [hsplit, pow_add, pow_mul, hx1, one_pow, mul_one]
    have hmn1 : m - 1 ≡ n - 1 [MOD p - 1] := by
      have h := hmn
      have hm1' : 1 ≤ m := by lia
      have hn1' : 1 ≤ n := by lia
      rw [← Nat.sub_add_cancel hm1', ← Nat.sub_add_cancel hn1'] at h
      exact Nat.ModEq.add_right_cancel' 1 h
    have hcm : (c : ZMod p) ^ m = (c : ZMod p) ^ n := hper _ _ _ hc0 hmn
    have hcm1 : (c : ZMod p) ^ (m - 1) = (c : ZMod p) ^ (n - 1) := hper _ _ _ hc0 hmn1
    have hvsum : voronoiSum (p := p) c m = voronoiSum (p := p) c n := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj0 : (j : ZMod p) ≠ 0 := by
        rw [mem_Ico] at hj
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun hd => absurd (Nat.le_of_dvd (by lia) hd) (by lia)
      rw [hper _ _ _ hj0 hmn1]
    have hVm := voronoi_congr hc hm hmeven hm2
    have hVn := voronoi_congr hc hn hneven hn2
    rw [hcm, hcm1, hvsum] at hVm
    have hw : (c : ZMod p) ^ n - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact fun h => hn ((hcord n).mp h)
    refine mul_left_cancel₀ hw ?_
    calc ((c : ZMod p) ^ n - 1) * ((n : ZMod p) * (bernoulli m : ZMod p))
          = (n : ZMod p) * (((c : ZMod p) ^ n - 1) * (bernoulli m : ZMod p)) := by ring
      _ = (n : ZMod p) * ((m : ZMod p) * (c : ZMod p) ^ (n - 1) * voronoiSum (p := p) c n) := by
            rw [hVm]
      _ = (m : ZMod p) * ((n : ZMod p) * (c : ZMod p) ^ (n - 1) * voronoiSum (p := p) c n) := by
            ring
      _ = (m : ZMod p) * (((c : ZMod p) ^ n - 1) * (bernoulli n : ZMod p)) := by rw [hVn]
      _ = ((c : ZMod p) ^ n - 1) * ((m : ZMod p) * (bernoulli n : ZMod p)) := by ring
  · have hnodd : Odd n := by rw [Nat.odd_iff] at hmodd ⊢; omega
    rw [bernoulli_eq_zero_of_odd hmodd (by lia), bernoulli_eq_zero_of_odd hnodd (by lia)]
    simp

end Bernoulli

end vonStaudtClausen
