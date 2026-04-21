/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard, Seewoo Lee
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.NumberTheory.Padics.PadicNumbers

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
"A New Proof of a Theorem of v. Staudt"

## Main theorems

* `sum_bernoulli : ∑ k ∈ Finset.range n, (n.choose k : ℚ) * bernoulli k =
  if n = 1 then 1 else 0`
* `bernoulli.vonStaudt_clausen : bernoulli (2 * k) + ∑ p ∈ Finset.range (2 * k + 2)
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
  convert bernoulli'_spec' n using 1
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

@[deprecated (since := "2025-12-09")]
alias bernoulli'_odd_eq_zero := bernoulli'_eq_zero_of_odd

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
  rw [sum_eq_add_sum_diff_singleton_of_mem h₁] at H ⊢
  apply add_eq_of_eq_sub'
  convert eq_sub_of_add_eq' H using 1
  · refine sum_congr rfl fun p h => ?_
    obtain ⟨h', h''⟩ : p ∈ _ ∧ p ≠ _ := by rwa [mem_sdiff, mem_singleton] at h
    simp [bernoulli_eq_bernoulli'_of_ne_one ((not_congr (antidiagonal_congr h' h₁)).mp h'')]
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
  suffices (∑ k ∈ Ico 1 n.succ, (k : ℚ) ^ p.succ) = ∑ i ∈ range p.succ.succ, f' i by convert this
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

namespace bernoulli

/- Indicator function that is `1` if `(p - 1) ∣ k` and `0` otherwise. -/
private noncomputable def vonStaudtIndicator (k p : ℕ) : ℚ :=
  if (p - 1) ∣ k then 1 else 0

/- The primes `q < 2k + 2` with `(q - 1) ∣ 2k` — the primes appearing in the
von Staudt-Clausen correction sum. -/
private abbrev vonStaudtPrimes (k : ℕ) : Finset ℕ :=
  (Finset.range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k

/-- Over `ZMod p`, the nonzero `l`-th power sum equals the negative indicator of `(p - 1) ∣ l`. -/
private lemma sum_pow_add_indicator_eq_zero (p l : ℕ) [Fact p.Prime] :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) +
    (if (p - 1) ∣ l then (1 : ZMod p) else 0) = 0 := by
  have hbij : (∑ v ∈ Finset.range p with v ≠ 0, (v : ZMod p) ^ l) =
      ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv ↦ Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        obtain ⟨hlt, hne⟩ := Finset.mem_filter.mp hv
        exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hlt))))
      (fun u _ ↦ (u : ZMod p).val)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun u _ ↦ by simp [ZMod.val_lt, u.ne_zero])
      (fun v hv ↦ by simp [ZMod.val_cast_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hv).1)])
      (fun u _ ↦ Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ ↦ rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]
  grind

/-- A rational number `x` is `p`-integral if `p` does not divide its denominator. -/
private abbrev pIntegral (p : ℕ) (x : ℚ) [Fact p.Prime] : Prop := Rat.padicValuation p x ≤ 1

private lemma den_sum_dvd_prod_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has]
    exact dvd_trans (Rat.add_den_dvd (f a) (∑ x ∈ s, f x)) (mul_dvd_mul_left _ ih)

private lemma pIntegral_mul (p : ℕ) [Fact p.Prime] (x y : ℚ)
    (hx : pIntegral p x) (hy : pIntegral p y) : pIntegral p (x * y) :=
  ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)

/-- Denominators of the "other primes" part of the indicator sum
stay coprime to a fixed prime `p`. -/
private lemma prod_one_div_prime_den_coprime (k p : ℕ) [Fact p.Prime] :
    (∏ q ∈ vonStaudtPrimes k with q ≠ p, ((1 : ℚ) / q).den).Coprime p := by
  apply Nat.Coprime.prod_left
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  have h1 : q.Prime := hq.1.2.1
  have h2 : ((1 : ℚ) / q).den = q := by simp [h1.ne_zero]
  rw [h2]
  exact (Nat.coprime_primes h1 Fact.out).mpr hq.2

/-- Splits the prime-indexed correction sum into the `p`-term (`vonStaudtIndicator / p`)
plus the rest. -/
private lemma sum_one_div_prime_eq_indicator_div_add (k p : ℕ) (hk : k > 0) [Fact p.Prime] :
    (∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q) =
    vonStaudtIndicator (2 * k) p / p + ∑ q ∈ vonStaudtPrimes k with q ≠ p, (1 : ℚ) / q := by
  by_cases hdvd : (p - 1) ∣ 2 * k
  · -- p is in the filtered set; extract its term
    have hp_mem : p ∈ vonStaudtPrimes k := by
      simp only [vonStaudtPrimes, Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := Nat.le_of_dvd (by lia) hdvd; lia, Fact.out, hdvd⟩
    rw [← Finset.add_sum_erase _ _ hp_mem]
    simp only [vonStaudtIndicator, if_pos hdvd]
    congr 1
    exact Finset.sum_congr (Finset.filter_ne' _ _).symm fun _ _ ↦ rfl
  · -- p is not in the filtered set; filter is redundant since p ∉ vonStaudtPrimes k
    simp only [vonStaudtIndicator, if_neg hdvd, zero_div, zero_add]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    symm
    apply Finset.filter_true_of_mem
    intro q hq
    simp only [vonStaudtPrimes, Finset.mem_filter] at hq
    rintro rfl
    exact hdvd hq.2.2

/-- If the `p`-adic valuation of `M` is at most `N`, then `p^N / M` is `p`-integral. -/
private lemma pIntegral_pow_div (p M N : ℕ) [Fact p.Prime] (hM : M ≠ 0)
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
  exact Rat.padicValuation_le_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).1
    (hM'_cop.coprime_dvd_left (by
      rw [hM'_eq]; exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _))).symm)

/-- The `i = 1` Faulhaber term is `p`-integral (handled separately for `p = 2` and odd `p`). -/
private lemma pIntegral_bernoulli_one_term (k p : ℕ) (hk : k > 0) [Fact p.Prime] :
    pIntegral p (bernoulli 1 * (2 * k) * (p : ℚ) ^ (2 * k - 1) / (2 * k)) := by
  rw [bernoulli_one]
  obtain rfl | hp2 := eq_or_ne p 2
  · have hsub : 2 * k - 1 = (2 * k - 2) + 1 := by lia
    have h : ((-1 / 2 : ℚ) * (2 * k) * (2 : ℚ) ^ (2 * k - 1) / (2 * k)) =
        -(2 : ℤ) ^ (2 * k - 2) := by
      rw [hsub, pow_succ]; push_cast; field_simp
    simpa [h] using Int.padicValuation_le_one _ (-(2 : ℤ) ^ (2 * k - 2))
  · have hk_ne : (2 * k : ℚ) ≠ 0 := by positivity
    have hrw : (-1 / 2 : ℚ) * (2 * k) * (p : ℚ) ^ (2 * k - 1) / (2 * k) =
        (-1 : ℤ) * ((p : ℚ) ^ (2 * k - 1) / 2) := by
      field_simp [hk_ne]; push_cast; ring
    rw [hrw]
    exact pIntegral_mul p _ _ (by exact_mod_cast Int.padicValuation_le_one p (-1))
      (pIntegral_pow_div p 2 (2 * k - 1) two_ne_zero (by
        rw [Nat.factorization_eq_zero_of_not_dvd (fun h ↦ by
          have := Nat.le_of_dvd two_pos h; have := (Fact.out : p.Prime).two_le; lia)]
        exact Nat.zero_le _))

/-- Main valuation estimate behind the contradiction step for even-index summands. -/
private lemma factorization_succ_le_sub_one (p d : ℕ) [Fact p.Prime] (hd : d ≥ 2) :
    (d + 1).factorization p ≤ d - 1 := by
  -- Special case: p = 2, d = 2 (since 3 is not divisible by 2)
  obtain ⟨rfl, rfl⟩ | hne : (p = 2 ∧ d = 2) ∨ ¬(p = 2 ∧ d = 2) := by tauto
  · simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · -- For all other prime p and d ≥ 2, we have d + 1 ≤ p^(d-1)
    apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices ∀ n : ℕ, n ≥ 2 → ¬(p = 2 ∧ n = 2) → n + 1 ≤ p ^ (n - 1) from this d hd hne
    intro n hn hne'
    induction hn with
    | refl => norm_num at hne' ⊢; lia
    | @step m hm IH =>
      by_cases hm2 : p = 2 ∧ m = 2
      · obtain ⟨rfl, rfl⟩ := hm2
        norm_num
      · have hm_eq : m = m - 1 + 1 := by lia
        calc m + 1 + 1 ≤ p ^ (m - 1) + 1 := by linarith [IH hm2]
          _ ≤ p ^ (m - 1) * p := by nlinarith [Nat.one_le_pow (m - 1) p (by lia)]
          _ = p ^ m := by rw [hm_eq]; exact pow_succ ..

/-- Multiplicative variant of the binomial coefficient denominator rewrite
as in Rado's summand. -/
private lemma choose_two_mul_succ_mul_div_eq (k m : ℕ) (x : ℚ) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : ℚ) * x / (2 * k + 1) =
    ((2 * k).choose (2 * m) : ℚ) * x / (2 * k - 2 * m + 1) := by
  have h : ((2 * k + 1).choose (2 * m) : ℚ) / (2 * k + 1) =
      ((2 * k).choose (2 * m) : ℚ) / (2 * k - 2 * m + 1) := by
    have hm_le : 2 * m ≤ 2 * k + 1 := by lia
    rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia)]
    conv_rhs => norm_cast; rw [Nat.choose_mul_succ_eq]
    push_cast [Nat.cast_sub hm_le]; ring
  rw [mul_comm ((2 * k + 1).choose (2 * m) : ℚ) x, mul_div_assoc,
      mul_comm ((2 * k).choose (2 * m) : ℚ) x, mul_div_assoc, h]

/-- `p`-integrality of the core even-index summand after denominator normalization. -/
private lemma pIntegral_choose_mul_pow_div (k m p : ℕ) (hm_lt : m < k) [Fact p.Prime]
    (hd : 2 * k - 2 * m ≥ 2) :
    pIntegral p (((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m - 1) /
      (2 * k - 2 * m + 1)) := by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_ne_zero, hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d ≠ 0 ∧ d + 1 ≠ 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m ≤ 2 * k := by lia
  have h_denom_rat : (2 * (k : ℚ) - 2 * m + 1) = ((d + 1 : ℕ) : ℚ) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h_exp, h_denom_rat, mul_div_assoc]
  exact pIntegral_mul p _ _ (by exact_mod_cast Int.padicValuation_le_one p ((2 * k).choose (2 * m)))
    (pIntegral_pow_div p (d + 1) (d - 1) hd_plus_one_ne_zero (factorization_succ_le_sub_one p d hd))

/-- Uses the induction hypothesis on `B_{2m} + e_{2m}(p)/p`
to prove `p`-integrality of the even term. -/
private lemma pIntegral_bernoulli_even_term (k m p : ℕ) (hm_lt : m < k) [Fact p.Prime]
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  set P := (p : ℚ) ^ (2 * k - 2 * m - 1)
  have hpow : (p : ℚ) ^ (2 * k - 2 * m) = P * p := by
    rw [(by lia : 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1), pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) * (p : ℚ) ^ (2 * k - 2 * m) / (2 * k + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      P / (2 * k + 1) := by rw [hpow]; field_simp [hp_ne]; ring
  rw [hdecomp]
  have hcmp := pIntegral_choose_mul_pow_div k m p hm_lt (by lia)
  apply (Rat.padicValuation p).map_sub_le
  · rw [mul_assoc, mul_div_assoc]
    apply pIntegral_mul _ _ _ ih
    have hpow_mul : ((2 * k).choose (2 * m) : ℚ) * (p : ℚ) ^ (2 * k - 2 * m) /
        (2 * k - 2 * m + 1) =
        (p : ℚ) * (((2 * k).choose (2 * m) : ℚ) * P / (2 * k - 2 * m + 1)) := by
      rw [hpow]; ring
    rw [choose_two_mul_succ_mul_div_eq k m _ hm_lt, hpow_mul]
    exact pIntegral_mul _ _ _ (Int.padicValuation_le_one p p) hcmp
  · unfold vonStaudtIndicator; split_ifs
    · simp only [one_mul]; rw [choose_two_mul_succ_mul_div_eq k m _ hm_lt]; exact hcmp
    · simp only [zero_mul, zero_div, map_zero]; exact bot_le

/-- The full remainder sum in Faulhaber's formula is `p`-integral. -/
private lemma pIntegral_faulhaber_sum (k p : ℕ) (hk : k > 0) [Fact p.Prime]
    (ih : ∀ m, 0 < m → m < k → pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (∑ i ∈ Finset.range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  apply (Rat.padicValuation p).map_sum_le
  intro i hi
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div p (2 * k + 1) (2 * k) (by lia)
      (Nat.factorization_le_of_le_pow <| calc 2 * k + 1 = (2 * k + 1).choose 1 := by simp
        _ ≤ 2 ^ (2 * k) := Nat.choose_succ_le_two_pow _ 1
        _ ≤ p ^ (2 * k) := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le _)
  · simp only [zero_add, Nat.choose_one_right]
    convert pIntegral_bernoulli_one_term k p hk using 1
    push_cast; field_simp
  · rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | hodd
    · have ⟨hm_pos, hm_lt, hi_eq⟩ : 0 < m ∧ m < k ∧ i + 2 = 2 * m := by lia
      simp only [hi_eq]
      exact pIntegral_bernoulli_even_term k m p hm_lt (ih m hm_pos hm_lt)
    · simp only [bernoulli_eq_zero_of_odd hodd (by lia),
        zero_mul, zero_div, map_zero]; exact bot_le

private lemma exists_int_sum_pow_add_indicator_eq (k p : ℕ) [Fact p.Prime] :
    ∃ T : ℤ, (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) +
      vonStaudtIndicator (2 * k) p = p * T := by
  -- Get divisibility in ℤ from the ZMod result
  have ⟨T, hT⟩ : ∃ T : ℤ, (∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0) = p * T := by
    have : (↑((∑ v ∈ Finset.range p with v ≠ 0, (v : ℤ) ^ (2 * k)) +
        (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 := by
      push_cast; exact sum_pow_add_indicator_eq_zero p (2 * k)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  refine ⟨T, ?_⟩
  have : vonStaudtIndicator (2 * k) p =
      ((if (p - 1) ∣ 2 * k then (1 : ℤ) else 0) : ℚ) := by
    unfold vonStaudtIndicator; split_ifs <;> simp
  rw [this]; exact_mod_cast hT

private lemma sum_pow_filter_eq_faulhaber (k p : ℕ) (hk : 0 < k) :
    (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) =
      (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k) := by
  have hfilter : (∑ v ∈ Finset.range p with v ≠ 0, (v : ℚ) ^ (2 * k)) =
      ∑ v ∈ Finset.range p, (v : ℚ) ^ (2 * k) := by
    rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun v _ ↦ by
      by_cases hv : v = 0 <;> simp [hv, (by lia : 2 * k ≠ 0)]
  have hsub : 2 * k + 1 - 2 * k = 1 := by lia
  have hne : (2 * k + 1 : ℚ) ≠ 0 := by positivity
  rw [hfilter, sum_range_pow, Finset.sum_range_succ]
  push_cast
  congr 1
  rw [Nat.choose_succ_self_right, hsub, pow_one]
  push_cast; field_simp [hne]

private lemma faulhaber_sum_div_prime_eq (k p : ℕ) [Fact p.Prime] :
    (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
      (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1 : ℚ)) / (p : ℚ) =
      ∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i : ℚ) *
        (p : ℚ) ^ (2 * k - i) / (2 * k + 1 : ℚ) := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi ↦ by
    have hi_lt := Finset.mem_range.mp hi
    have hsub : 2 * k + 1 - i = (2 * k - i) + 1 := by lia
    rw [hsub, pow_succ]
    field_simp [hp_ne]

/-- Rearranges the Faulhaber identity and power-sum congruence to isolate
`bernoulli (2*k) + vonStaudtIndicator (2*k) p / p`. -/
private lemma bernoulli_add_indicator_eq_sub (k p : ℕ) (hk : k > 0) [Fact p.Prime] :
    ∃ T : ℤ, bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ Finset.range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
  obtain ⟨T, hT⟩ := exists_int_sum_pow_add_indicator_eq k p
  use T
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hAlg : bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i ∈ Finset.range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) / p := by
    field_simp [hp_ne]; linarith [hT, sum_pow_filter_eq_faulhaber k p hk]
  rw [hAlg]; congr 1; simpa using faulhaber_sum_div_prime_eq k p

/-- For fixed prime `p`, the denominator of `B_{2k} + e_{2k}(p)/p` is not divisible by `p`. -/
private lemma bernoulli_add_indicator_den_not_dvd (k p : ℕ) (hk : k > 0) [Fact p.Prime] :
    ¬ p ∣ (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p).den := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub k p hk
    rw [hT]
    have hT_int : pIntegral p (T : ℚ) := Int.padicValuation_le_one p T
    have hR : pIntegral p (∑ i ∈ Finset.range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : ℚ) ^ (2 * k - i) / (2 * k + 1)) := by
      apply pIntegral_faulhaber_sum k p hk
      intro m hm_pos hm_lt
      exact Rat.padicValuation_le_one_iff.2 (ih m hm_lt hm_pos)
    exact Rat.padicValuation_le_one_iff.1 ((Rat.padicValuation p).map_sub_le hT_int hR)

/-- Extends the fixed-prime nondivisibility result to the full prime correction sum. -/
private lemma vonStaudt_sum_den_not_dvd (k p : ℕ) (hk : k > 0) [Fact p.Prime] :
    ¬ p ∣ (bernoulli (2 * k) + ∑ q ∈ vonStaudtPrimes k, (1 : ℚ) / q).den := by
  rw [sum_one_div_prime_eq_indicator_div_add k p hk, ← add_assoc]
  have hcop_ind := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2
    (bernoulli_add_indicator_den_not_dvd k p hk)).symm
  have hcop_rest := Nat.Coprime.of_dvd_left (den_sum_dvd_prod_den _ _)
    (prod_one_div_prime_den_coprime k p)
  have hcop := (Nat.Coprime.of_dvd_left (Rat.add_den_dvd _ _) (hcop_ind.mul_left hcop_rest)).symm
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcop

/-- **von Staudt-Clausen theorem:** For any natural number $k$, the sum
$$B_{2k} + \sum_{p - 1 \mid 2k} \frac{1}{p}$$ is an integer.
-/
theorem vonStaudt_clausen (k : ℕ) :
    bernoulli (2 * k) + ∑ p ∈ Finset.range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
      (1 : ℚ) / p ∈ Set.range Int.cast := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, by decide +kernel⟩
  · rw [Set.mem_range]
    refine ⟨_, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra h
    obtain ⟨p, hp, hdvd⟩ := ne_one_iff_exists_prime_dvd.mp h
    exact absurd hdvd (by let : Fact p.Prime := ⟨hp⟩; exact vonStaudt_sum_den_not_dvd k p hk)

end bernoulli

end vonStaudtClausen
