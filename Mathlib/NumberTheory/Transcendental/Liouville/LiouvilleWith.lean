/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`Liouville` if it is `LiouvilleWith` any real exponent, see `forall_liouvilleWith_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `LiouvilleWith` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/


open Filter Metric Real Set

open scoped Filter Topology

/-- We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `Liouville` if it is `LiouvilleWith` any real
exponent. -/
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

/-- For `p = 1` (hence, for any `p ≤ 1`), the condition `LiouvilleWith p x` is trivial. -/
theorem liouvilleWith_one (x : ℝ) : LiouvilleWith 1 x := by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : ℝ) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn', Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨⌊x * n⌋ + 1, this.ne, ?_⟩
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 this), rpow_one, sub_lt_iff_lt_add',
    add_div_eq_mul_add_div _ _ hn'.ne']
  gcongr
  calc _ ≤ x * n + 1 := by push_cast; gcongr; apply Int.floor_le
    _ < x * n + 2 := by linarith

namespace LiouvilleWith

variable {p q x : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

/-- The constant `C` provided by the definition of `LiouvilleWith` can be made positive.
We also add `1 ≤ n` to the list of assumptions about the denominator. While it is equivalent to
the original statement, the case `n = 0` breaks many arguments. -/
theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ) (_h₀ : 0 < C),
      ∃ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p := by
  rcases h with ⟨C, hC⟩
  refine ⟨max C 1, zero_lt_one.trans_le <| le_max_right _ _, ?_⟩
  refine ((eventually_ge_atTop 1).and_frequently hC).mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

/-- If a number is Liouville with exponent `p`, then it is Liouville with any smaller exponent. -/
theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
  refine ⟨m, hne, hlt.trans_le <| ?_⟩
  gcongr
  exact_mod_cast hn

/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < n ^ (-q) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : ∀ᶠ n : ℕ in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently hC).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  replace hn : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨m, hne, hlt.trans <| (div_lt_iff₀ <| rpow_pos_of_pos hn _).2 ?_⟩
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]

/-- The product of a Liouville number and a nonzero rational number is again a Liouville number. -/
theorem mul_rat (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (x * r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨_hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : ℝ) / ↑(r.den • id n) = m / n * r := by
    simp [← div_mul_div_comm, ← r.cast_def, mul_comm]
  refine ⟨r.num * m, ?_, ?_⟩
  · rw [A]; simp [hne, hr]
  · rw [A, ← sub_mul, abs_mul]
    simp only [smul_eq_mul, id, Nat.cast_mul]
    calc _ < C / ↑n ^ p * |↑r| := by gcongr
      _ = ↑r.den ^ p * (↑|r| * C) / (↑r.den * ↑n) ^ p := ?_
    rw [mul_rpow, mul_div_mul_left, mul_comm, mul_div_assoc]
    · simp only [Rat.cast_abs]
    all_goals positivity

/-- The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem mul_rat_iff (hr : r ≠ 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀ hr, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

/-- The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem rat_mul_iff (hr : r ≠ 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_rat_iff hr]

theorem rat_mul (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (r * x) :=
  (rat_mul_iff hr).2 h

theorem mul_int_iff (hm : m ≠ 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, mul_rat_iff (Int.cast_ne_zero.2 hm)]

theorem mul_int (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (x * m) :=
  (mul_int_iff hm).2 h

theorem int_mul_iff (hm : m ≠ 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_int_iff hm]

theorem int_mul (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (m * x) :=
  (int_mul_iff hm).2 h

theorem mul_nat_iff (hn : n ≠ 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, mul_rat_iff (Nat.cast_ne_zero.2 hn)]

theorem mul_nat (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (x * n) :=
  (mul_nat_iff hn).2 h

theorem nat_mul_iff (hn : n ≠ 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_nat_iff hn]

theorem nat_mul (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (n * x) := by
  rw [mul_comm]; exact h.mul_nat hn

theorem add_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have : (↑(r.den * m + r.num * n : ℤ) / ↑(r.den • id n) : ℝ) = m / n + r := by
    rw [Algebra.id.smul_eq_mul, id]
    nth_rewrite 4 [← Rat.num_div_den r]
    push_cast
    rw [add_div, mul_div_mul_left _ _ (by positivity), mul_div_mul_right _ _ (by positivity)]
  refine ⟨r.den * m + r.num * n, ?_⟩; rw [this, add_sub_add_right_eq_sub]
  refine ⟨by simpa, hlt.trans_le (le_of_eq ?_)⟩
  have : (r.den ^ p : ℝ) ≠ 0 := by positivity
  simp [mul_rpow, Nat.cast_nonneg, mul_div_mul_left, this]

@[simp]
theorem add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x :=
  ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]
theorem rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x := by rw [add_comm, add_rat_iff]

theorem rat_add (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r + x) :=
  add_comm x r ▸ h.add_rat r

@[simp]
theorem add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast m, add_rat_iff]

@[simp]
theorem int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x := by rw [add_comm, add_int_iff]

@[simp]
theorem add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast n, add_rat_iff]

@[simp]
theorem nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x := by rw [add_comm, add_nat_iff]

theorem add_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x + m) :=
  add_int_iff.2 h

theorem int_add (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m + x) :=
  int_add_iff.2 h

theorem add_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x + n) :=
  h.add_int n

theorem nat_add (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n + x) :=
  h.int_add n

protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨m, hne, hlt⟩
  refine ⟨-m, by simp [neg_div, hne], ?_⟩
  convert hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x := by
  rw [sub_eq_add_neg, ← Rat.cast_neg, add_rat_iff]

theorem sub_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, sub_rat_iff]

theorem sub_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, sub_rat_iff]

theorem sub_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem rat_sub (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem int_sub (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem nat_sub (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h

theorem ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : ℤ) : x ≠ m := by
  rintro rfl; rename' m => M
  rcases ((eventually_gt_atTop 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : ℕ, hn : 0 < n, m : ℤ, hne : (M : ℝ) ≠ m / n, hlt : |(M - m / n : ℝ)| < n ^ (-1 : ℝ)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : ℝ) < n := by simpa
  rw [rpow_neg_one, ← one_div, sub_div' hn'.ne', abs_div, Nat.abs_cast]
  gcongr
  norm_cast
  rw [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
  rw [Ne, eq_div_iff hn'.ne'] at hne
  exact mod_cast hne

/-- A number satisfying the Liouville condition with exponent `p > 1` is an irrational number. -/
protected theorem irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · refine (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 ?_
    rw [Rat.cast_inv, mul_inv_cancel₀]
    exacts [Int.cast_one.symm, Rat.cast_ne_zero.mpr h0]

end LiouvilleWith

namespace Liouville

variable {x : ℝ}

/-- If `x` is a Liouville number, then for any `n`, for infinitely many denominators `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`. -/
theorem frequently_exists_num (hx : Liouville x) (n : ℕ) :
    ∃ᶠ b : ℕ in atTop, ∃ a : ℤ, x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ) ^ n := by
  refine Classical.not_not.1 fun H => ?_
  simp only [not_exists, not_frequently, not_and, not_lt,
    eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : ∀ b > (1 : ℕ), ∀ᶠ m : ℕ in atTop, ∀ a : ℤ, 1 / (b : ℝ) ^ m ≤ |x - a / b| := by
    intro b hb
    replace hb : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b : ℝ) ^ m : ℕ → ℝ) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb)
    refine (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono ?_
    exact fun m hm a => hm a
  have : ∀ᶠ m : ℕ in atTop, ∀ b < N, 1 < b → ∀ a : ℤ, 1 / (b : ℝ) ^ m ≤ |x - a / b| :=
    (finite_lt_nat N).eventually_all.2 fun b _hb => eventually_imp_distrib_left.2 (this b)
  rcases (this.and (eventually_ge_atTop n)).exists with ⟨m, hm, hnm⟩
  rcases hx m with ⟨a, b, hb, hne, hlt⟩
  lift b to ℕ using zero_le_one.trans hb.le; norm_cast at hb; push_cast at hne hlt
  rcases le_or_gt N b with h | h
  · refine (hN b h a hne).not_gt (hlt.trans_le ?_)
    gcongr
    exact_mod_cast hb.le
  · exact (hm b h hb _).not_gt hlt

/-- A Liouville number is a Liouville number with any real exponent. -/
protected theorem liouvilleWith (hx : Liouville x) (p : ℝ) : LiouvilleWith p x := by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, ((eventually_gt_atTop 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono ?_⟩
  rintro b ⟨_hb, a, hne, hlt⟩
  refine ⟨a, hne, ?_⟩
  rwa [rpow_natCast]

end Liouville

/-- A number satisfies the Liouville condition with any exponent if and only if it is a Liouville
number. -/
theorem forall_liouvilleWith_iff {x : ℝ} : (∀ p, LiouvilleWith p x) ↔ Liouville x := by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : ℝ)))).exists
    with ⟨b, hb, a, hne, hlt⟩
  exact ⟨a, b, mod_cast hb, hne, by simpa [rpow_neg] using hlt⟩
