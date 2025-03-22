/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Norm
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exponential Function

This file contains the definitions of the real and complex exponential function.

-/

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

theorem isCauSeq_norm_exp (z : ℂ) :
    IsCauSeq abs fun n => ∑ m ∈ range n, ‖z ^ m / m.factorial‖ :=
  let ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (norm_nonneg _) hn
  IsCauSeq.series_ratio_test n (‖z‖ / n) (div_nonneg (norm_nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff₀ hn0, one_mul]) fun m hm => by
      rw [abs_norm, abs_norm, Nat.factorial_succ, pow_succ', mul_comm m.succ, Nat.cast_mul,
        ← div_div, mul_div_assoc, mul_div_right_comm, Complex.norm_mul, Complex.norm_div,
        norm_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)

@[deprecated (since := "2025-02-16")] alias isCauSeq_abs_exp := isCauSeq_norm_exp

noncomputable section

theorem isCauSeq_exp (z : ℂ) : IsCauSeq (‖·‖) fun n => ∑ m ∈ range n, z ^ m / m.factorial :=
  (isCauSeq_norm_exp z).of_abv

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
@[pp_nodot]
def exp' (z : ℂ) : CauSeq ℂ (‖·‖) :=
  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
@[pp_nodot]
def exp (z : ℂ) : ℂ :=
  CauSeq.lim (exp' z)

/-- scoped notation for the complex exponential function -/
scoped notation "cexp" => Complex.exp

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re

/-- scoped notation for the real exponential function -/
scoped notation "rexp" => Real.exp

end

end Real

namespace Complex

variable (x y : ℂ)

@[simp]
theorem exp_zero : exp 0 = 1 := by
  rw [exp]
  refine lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => ?_⟩
  convert (config := .unfoldSameFun) ε0 -- ε0 : ε > 0 but goal is _ < ε
  rcases j with - | j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction j with
    | zero => dsimp [exp']; simp [show Nat.succ 0 = 1 from rfl]
    | succ j ih =>
      rw [← ih (by simp [Nat.succ_le_succ])]
      simp only [sum_range_succ, pow_succ]
      simp

theorem exp_add : exp (x + y) = exp x * exp y := by
  have hj : ∀ j : ℕ, (∑ m ∈ range j, (x + y) ^ m / m.factorial) =
        ∑ i ∈ range j, ∑ k ∈ range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow, div_eq_mul_inv, sum_mul]
    refine Finset.sum_congr rfl fun I hi => ?_
    have h₁ : (m.choose I : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hi))))
    have h₂ := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ <| Finset.mem_range.1 hi)
    rw [← h₂, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
    simp only [mul_left_comm (m.choose I : ℂ), mul_assoc, mul_left_comm (m.choose I : ℂ)⁻¹,
      mul_comm (m.choose I : ℂ)]
    rw [inv_mul_cancel₀ h₁]
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp only [hj]
  exact cauchy_product (isCauSeq_norm_exp x) (isCauSeq_exp y)

/-- the exponential function as a monoid hom from `Multiplicative ℂ` to `ℂ` -/
@[simps]
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℂ) ℂ :=
  { toFun := fun z => exp z.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℂ) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative ℂ) expMonoidHom l

theorem exp_multiset_sum (s : Multiset ℂ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℂ) ℂ _ _ expMonoidHom s

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x) :=
  map_prod (β := Multiplicative ℂ) expMonoidHom f s

lemma exp_nsmul (x : ℂ) (n : ℕ) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative ℂ) ℂ _ _  expMonoidHom _ _

theorem exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ, Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul _ n, one_mul]

@[simp]
theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  zero_ne_one (α := ℂ) <| by rw [← exp_zero, ← add_neg_cancel x, exp_add, h]; simp

theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← mul_right_inj' (exp_ne_zero x), ← exp_add]; simp [mul_inv_cancel₀ (exp_ne_zero x)]

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

theorem exp_int_mul (z : ℂ) (n : ℤ) : Complex.exp (n * z) = Complex.exp z ^ n := by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]

@[simp]
theorem exp_conj : exp (conj x) = conj (exp x) := by
  dsimp [exp]
  rw [← lim_conj]
  refine congr_arg CauSeq.lim (CauSeq.ext fun _ => ?_)
  dsimp [exp', Function.comp_def, cauSeqConj]
  rw [map_sum (starRingEnd _)]
  refine sum_congr rfl fun n _ => ?_
  rw [map_div₀, map_pow, ← ofReal_natCast, conj_ofReal]

@[simp]
theorem ofReal_exp_ofReal_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
  conj_eq_iff_re.1 <| by rw [← exp_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_exp (x : ℝ) : (Real.exp x : ℂ) = exp x :=
  ofReal_exp_ofReal_re _

@[simp]
theorem exp_ofReal_im (x : ℝ) : (exp x).im = 0 := by rw [← ofReal_exp_ofReal_re, ofReal_im]

theorem exp_ofReal_re (x : ℝ) : (exp x).re = Real.exp x :=
  rfl

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem exp_zero : exp 0 = 1 := by simp [Real.exp]

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]

/-- the exponential function as a monoid hom from `Multiplicative ℝ` to `ℝ` -/
@[simps]
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℝ) ℝ :=
  { toFun := fun x => exp x.toAdd,
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℝ) : exp l.sum = (l.map exp).prod :=
  map_list_prod (M := Multiplicative ℝ) expMonoidHom l

theorem exp_multiset_sum (s : Multiset ℝ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℝ) ℝ _ _ expMonoidHom s

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x) :=
  map_prod (β := Multiplicative ℝ) expMonoidHom f s

lemma exp_nsmul (x : ℝ) (n : ℕ) : exp (n • x) = exp x ^ n :=
  @MonoidHom.map_pow (Multiplicative ℝ) ℝ _ _  expMonoidHom _ _

nonrec theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])

@[simp]
nonrec theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  exp_ne_zero x <| by rw [exp, ← ofReal_inj] at h; simp_all

nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹ :=
  ofReal_injective <| by simp [exp_neg]

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]

open IsAbsoluteValue Nat

theorem sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : ∑ i ∈ range n, x ^ i / i ! ≤ exp x :=
  calc
    ∑ i ∈ range n, x ^ i / i ! ≤ lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq ℝ abs) := by
      refine le_lim (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ ↦ ?_
      positivity
    _ = exp x := by rw [exp, Complex.exp, ← cauSeqRe, lim_re]

lemma pow_div_factorial_le_exp (hx : 0 ≤ x) (n : ℕ) : x ^ n / n ! ≤ exp x :=
  calc
    x ^ n / n ! ≤ ∑ k ∈ range (n + 1), x ^ k / k ! :=
        single_le_sum (f := fun k ↦ x ^ k / k !) (fun k _ ↦ by positivity) (self_mem_range_succ n)
    _ ≤ exp x := sum_le_exp_of_nonneg hx _

theorem quadratic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ exp x :=
  calc
    1 + x + x ^ 2 / 2 = ∑ i ∈ range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial, cast_one,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, mul_one, div_one, Nat.mul_one,
          cast_succ, add_right_inj]
        ring_nf
    _ ≤ exp x := sum_le_exp_of_nonneg hx 3

private theorem add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

private theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x := by linarith [add_one_le_exp_of_nonneg hx]

@[bound]
theorem exp_pos (x : ℝ) : 0 < exp x :=
  (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x, Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))

@[bound]
lemma exp_nonneg (x : ℝ) : 0 ≤ exp x := x.exp_pos.le

@[simp]
theorem abs_exp (x : ℝ) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)

lemma exp_abs_le (x : ℝ) : exp |x| ≤ exp x + exp (-x) := by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

@[mono]
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))

@[gcongr]
theorem exp_lt_exp_of_lt {x y : ℝ} (h : x < y) : exp x < exp y := exp_strictMono h

@[mono]
theorem exp_monotone : Monotone exp :=
  exp_strictMono.monotone

@[gcongr, bound]
theorem exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : exp x ≤ exp y := exp_monotone h

@[simp]
theorem exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y :=
  exp_strictMono.lt_iff_lt

@[simp]
theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  exp_strictMono.le_iff_le

theorem exp_injective : Function.Injective exp :=
  exp_strictMono.injective

@[simp]
theorem exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff

@[simp]
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  exp_injective.eq_iff' exp_zero

@[simp]
theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x := by rw [← exp_zero, exp_lt_exp]

@[bound] private alias ⟨_, Bound.one_lt_exp_of_pos⟩ := one_lt_exp_iff

@[simp]
theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 := by rw [← exp_zero, exp_lt_exp]

@[simp]
theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp

@[simp]
theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp

end Real

namespace Complex

theorem sum_div_factorial_le {α : Type*} [LinearOrderedField α] (n j : ℕ) (hn : 0 < n) :
    (∑ m ∈ range j with n ≤ m, (1 / m.factorial : α)) ≤ n.succ / (n.factorial * n) :=
  calc
    (∑ m ∈ range j with n ≤ m, (1 / m.factorial : α)) =
        ∑ m ∈ range (j - n), (1 / ((m + n).factorial : α)) := by
        refine sum_nbij' (· - n) (· + n) ?_ ?_ ?_ ?_ ?_ <;>
          simp +contextual [lt_tsub_iff_right, tsub_add_cancel_of_le]
    _ ≤ ∑ m ∈ range (j - n), ((n.factorial : α) * (n.succ : α) ^ m)⁻¹ := by
      simp_rw [one_div]
      gcongr
      rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le, add_comm]
      exact Nat.factorial_mul_pow_le_factorial
    _ = (n.factorial : α)⁻¹ * ∑ m ∈ range (j - n), (n.succ : α)⁻¹ ^ m := by
      simp [mul_inv, ← mul_sum, ← sum_mul, mul_comm, inv_pow]
    _ = ((n.succ : α) - n.succ * (n.succ : α)⁻¹ ^ (j - n)) / (n.factorial * n) := by
      have h₁ : (n.succ : α) ≠ 1 :=
        @Nat.cast_one α _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.inj (pos_iff_ne_zero.1 hn))
      have h₂ : (n.succ : α) ≠ 0 := by positivity
      have h₃ : (n.factorial * n : α) ≠ 0 := by positivity
      have h₄ : (n.succ - 1 : α) = n := by simp
      rw [geom_sum_inv h₁ h₂, eq_div_iff_mul_eq h₃, mul_comm _ (n.factorial * n : α),
          ← mul_assoc (n.factorial⁻¹ : α), ← mul_inv_rev, h₄, ← mul_assoc (n.factorial * n : α),
          mul_comm (n : α) n.factorial, mul_inv_cancel₀ h₃, one_mul, mul_comm]
    _ ≤ n.succ / (n.factorial * n : α) := by gcongr; apply sub_le_self; positivity

theorem exp_bound {x : ℂ} (hx : ‖x‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  rw [← lim_const (abv := norm) (∑ m ∈ range n, _), exp, sub_eq_add_neg,
    ← lim_neg, lim_add, ← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show
    ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
      ‖x‖ ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹)
  rw [sum_range_sub_sum_range hj]
  calc
    ‖∑ m ∈ range j with n ≤ m, (x ^ m / m.factorial : ℂ)‖
      = ‖∑ m ∈ range j with n ≤ m, (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x‖ ^ n * (1 / m.factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr
      rw [Complex.norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hx
    _ = ‖x‖ ^ n * ∑ m ∈ range j with n ≤ m, (1 / m.factorial : ℝ) := by
      simp [abs_mul, abv_pow abs, abs_div, ← mul_sum]
    _ ≤ ‖x‖ ^ n * (n.succ * (n.factorial * n : ℝ)⁻¹) := by
      gcongr
      exact sum_div_factorial_le _ _ hn

theorem exp_bound' {x : ℂ} {n : ℕ} (hx : ‖x‖ / n.succ ≤ 1 / 2) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ ‖x‖ ^ n / n.factorial * 2 := by
  rw [← lim_const (abv := norm) (∑ m ∈ range n, _),
    exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_norm]
  refine lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤
    ‖x‖ ^ n / n.factorial * 2
  let k := j - n
  have hj : j = n + k := (add_tsub_cancel_of_le hj).symm
  rw [hj, sum_range_add_sub_sum_range]
  calc
    ‖∑ i ∈ range k, x ^ (n + i) / ((n + i).factorial : ℂ)‖ ≤
        ∑ i ∈ range k, ‖x ^ (n + i) / ((n + i).factorial : ℂ)‖ :=
      IsAbsoluteValue.abv_sum _ _ _
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (n + i) / (n + i).factorial := by
      simp [norm_natCast, Complex.norm_pow]
    _ ≤ ∑ i ∈ range k, ‖x‖ ^ (n + i) / ((n.factorial : ℝ) * (n.succ : ℝ) ^ i) := ?_
    _ = ∑ i ∈ range k, ‖x‖ ^ n / n.factorial * (‖x‖ ^ i / (n.succ : ℝ) ^ i) := ?_
    _ ≤ ‖x‖ ^ n / ↑n.factorial * 2 := ?_
  · gcongr
    exact mod_cast Nat.factorial_mul_pow_le_factorial
  · refine Finset.sum_congr rfl fun _ _ => ?_
    simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc]
  · rw [← mul_sum]
    gcongr
    simp_rw [← div_pow]
    rw [geom_sum_eq, div_le_iff_of_neg]
    · trans (-1 : ℝ)
      · linarith
      · simp only [neg_le_sub_iff_le_add, div_pow, Nat.cast_succ, le_add_iff_nonneg_left]
        positivity
    · linarith
    · linarith

theorem norm_exp_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖exp x - 1‖ ≤ 2 * ‖x‖ :=
  calc
    ‖exp x - 1‖ = ‖exp x - ∑ m ∈ range 1, x ^ m / m.factorial‖ := by simp [sum_range_succ]
    _ ≤ ‖x‖ ^ 1 * ((Nat.succ 1 : ℝ) * ((Nat.factorial 1) * (1 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * ‖x‖ := by simp [two_mul, mul_two, mul_add, mul_comm, add_mul, Nat.factorial]

theorem norm_exp_sub_one_sub_id_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 :=
  calc
    ‖exp x - 1 - x‖ = ‖exp x - ∑ m ∈ range 2, x ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ ≤ ‖x‖ ^ 2 * ((Nat.succ 2 : ℝ) * (Nat.factorial 2 * (2 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ ≤ ‖x‖ ^ 2 * 1 := by gcongr; norm_num [Nat.factorial]
    _ = ‖x‖ ^ 2 := by rw [mul_one]

lemma norm_exp_sub_sum_le_exp_norm_sub_sum (x : ℂ) (n : ℕ) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖
      ≤ Real.exp ‖x‖ - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  calc ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖
  _ ≤ (∑ m ∈ range j, ‖x‖ ^ m / m.factorial) - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
    rw [sum_range_sub_sum_range hj, sum_range_sub_sum_range hj]
    refine (IsAbsoluteValue.abv_sum norm ..).trans_eq ?_
    congr with i
    simp [Complex.norm_pow]
  _ ≤ Real.exp ‖x‖ - ∑ m ∈ range n, ‖x‖ ^ m / m.factorial := by
    gcongr
    exact Real.sum_le_exp_of_nonneg (norm_nonneg _) _

lemma norm_exp_le_exp_norm (x : ℂ) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  convert norm_exp_sub_sum_le_exp_norm_sub_sum x 0 using 1 <;> simp

lemma norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) (n : ℕ) :
    ‖exp x - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ ‖x‖ ^ n * Real.exp ‖x‖ := by
  rw [← CauSeq.lim_const (abv := norm) (∑ m ∈ range n, _), Complex.exp, sub_eq_add_neg,
    ← CauSeq.lim_neg, CauSeq.lim_add, ← lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n, fun j hj => ?_⟩)
  simp_rw [← sub_eq_add_neg]
  show ‖(∑ m ∈ range j, x ^ m / m.factorial) - ∑ m ∈ range n, x ^ m / m.factorial‖ ≤ _
  rw [sum_range_sub_sum_range hj]
  calc
    ‖∑ m ∈ range j with n ≤ m, (x ^ m / m.factorial : ℂ)‖
      = ‖∑ m ∈ range j with n ≤ m, (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)‖ := by
      refine congr_arg norm (sum_congr rfl fun m hm => ?_)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x ^ n * (x ^ (m - n) / m.factorial)‖ :=
      IsAbsoluteValue.abv_sum norm ..
    _ ≤ ∑ m ∈ range j with n ≤ m, ‖x‖ ^ n * (‖x‖ ^ (m - n) / (m - n).factorial) := by
      simp_rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, norm_natCast]
      gcongr with i hi
      · rw [Complex.norm_pow]
      · simp
    _ = ‖x‖ ^ n * ∑ m ∈ range j with n ≤ m, (‖x‖ ^ (m - n) / (m - n).factorial) := by
      rw [← mul_sum]
    _ = ‖x‖ ^ n * ∑ m ∈ range (j - n), (‖x‖ ^ m / m.factorial) := by
      congr 1
      refine (sum_bij (fun m hm ↦ m + n) ?_ ?_ ?_ ?_).symm
      · intro a ha
        simp only [mem_filter, mem_range, le_add_iff_nonneg_left, zero_le, and_true]
        simp only [mem_range] at ha
        rwa [← lt_tsub_iff_right]
      · intro a ha b hb hab
        simpa using hab
      · intro b hb
        simp only [mem_range, exists_prop]
        simp only [mem_filter, mem_range] at hb
        refine ⟨b - n, ?_, ?_⟩
        · rw [tsub_lt_tsub_iff_right hb.2]
          exact hb.1
        · rw [tsub_add_cancel_of_le hb.2]
      · simp
    _ ≤ ‖x‖ ^ n * Real.exp ‖x‖ := by
      gcongr
      refine Real.sum_le_exp_of_nonneg ?_ _
      exact norm_nonneg _

@[deprecated (since := "2025-02-16")] alias abs_exp_sub_one_le := norm_exp_sub_one_le
@[deprecated (since := "2025-02-16")] alias abs_exp_sub_one_sub_id_le := norm_exp_sub_one_sub_id_le
@[deprecated (since := "2025-02-16")] alias  abs_exp_sub_sum_le_exp_abs_sub_sum :=
  norm_exp_sub_sum_le_exp_norm_sub_sum
@[deprecated (since := "2025-02-16")] alias abs_exp_le_exp_abs := norm_exp_le_exp_norm
@[deprecated (since := "2025-02-16")] alias abs_exp_sub_sum_le_abs_mul_exp :=
  norm_exp_sub_sum_le_norm_mul_exp

end Complex

namespace Real

open Complex Finset

nonrec theorem exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |exp x - ∑ m ∈ range n, x ^ m / m.factorial| ≤ |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hxc : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  convert exp_bound hxc hn using 2 <;>
  norm_cast

theorem exp_bound' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      x ^ n * (n + 1) / (n.factorial * n) := by
  have h3 : |x| = x := by simpa
  have h4 : |x| ≤ 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t

theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| := by
  have : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_le (x := x) this

theorem abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1 - x| ≤ x ^ 2 := by
  rw [← sq_abs]
  have : ‖(x : ℂ)‖ ≤ 1 := mod_cast hx
  exact_mod_cast Complex.norm_exp_sub_one_sub_id_le this

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `expNear_succ`), with `expNear n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
noncomputable def expNear (n : ℕ) (x r : ℝ) : ℝ :=
  (∑ m ∈ range n, x ^ m / m.factorial) + x ^ n / n.factorial * r

@[simp]
theorem expNear_zero (x r) : expNear 0 x r = r := by simp [expNear]

@[simp]
theorem expNear_succ (n x r) : expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r) := by
  simp [expNear, range_succ, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
      mul_inv, Nat.factorial]
  ac_rfl

theorem expNear_sub (n x r₁ r₂) : expNear n x r₁ -
    expNear n x r₂ = x ^ n / n.factorial * (r₁ - r₂) := by
  simp [expNear, mul_sub]

theorem exp_approx_end (n m : ℕ) (x : ℝ) (e₁ : n + 1 = m) (h : |x| ≤ 1) :
    |exp x - expNear m x 0| ≤ |x| ^ m / m.factorial * ((m + 1) / m) := by
  simp only [expNear, mul_zero, add_zero]
  convert exp_bound (n := m) h ?_ using 1
  · field_simp [mul_comm]
  · omega

theorem exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ) (e₁ : n + 1 = m) (a₂ b₂ : ℝ)
    (e : |1 + x / m * a₂ - a₁| ≤ b₁ - |x| / m * b₂)
    (h : |exp x - expNear m x a₂| ≤ |x| ^ m / m.factorial * b₂) :
    |exp x - expNear n x a₁| ≤ |x| ^ n / n.factorial * b₁ := by
  refine (abs_sub_le _ _ _).trans ((add_le_add_right h _).trans ?_)
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert mul_le_mul_of_nonneg_left (a := |x| ^ n / ↑(Nat.factorial n))
      (le_sub_iff_add_le'.1 e) ?_ using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, ← pow_abs, mul_inv, Nat.factorial]
    ac_rfl
  · simp [div_nonneg, abs_nonneg]

theorem exp_approx_end' {n} {x a b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm)
    (h : |x| ≤ 1) (e : |1 - a| ≤ b - |x| / rm * ((rm + 1) / rm)) :
    |exp x - expNear n x a| ≤ |x| ^ n / n.factorial * b := by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)

theorem exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ} (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm)
    (h : |exp 1 - expNear m 1 ((a₁ - 1) * rm)| ≤ |1| ^ m / m.factorial * (b₁ * rm)) :
    |exp 1 - expNear n 1 a₁| ≤ |1| ^ n / n.factorial * b₁ := by
  subst er
  refine exp_approx_succ _ en _ _ ?_ h
  field_simp [show (m : ℝ) ≠ 0 by norm_cast; omega]

theorem exp_approx_start (x a b : ℝ) (h : |exp x - expNear 0 x a| ≤ |x| ^ 0 / Nat.factorial 0 * b) :
    |exp x - a| ≤ b := by simpa using h

theorem exp_bound_div_one_sub_of_interval' {x : ℝ} (h1 : 0 < x) (h2 : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x) := calc
    0 < x ^ 3 := by positivity
    _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x ≤ _ := exp_bound' h1.le h2.le zero_lt_three
    _ ≤ 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      -- This proof should be restored after the norm_num plugin for big operators is ported.
      -- (It may also need the positivity extensions in https://github.com/leanprover-community/mathlib4/pull/3907.)
      rw [show 3 = 1 + 1 + 1 from rfl]
      repeat rw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
      nlinarith
    _ < 1 / (1 - x) := by rw [lt_div_iff₀] <;> nlinarith

theorem exp_bound_div_one_sub_of_interval {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le

theorem add_one_lt_exp {x : ℝ} (hx : x ≠ 0) : x + 1 < Real.exp x := by
  obtain hx | hx := hx.symm.lt_or_lt
  · exact add_one_lt_exp_of_pos hx
  obtain h' | h' := le_or_lt 1 (-x)
  · linarith [x.exp_pos]
  have hx' : 0 < x + 1 := by linarith
  simpa [add_comm, exp_neg, inv_lt_inv₀ (exp_pos _) hx']
    using exp_bound_div_one_sub_of_interval' (neg_pos.2 hx) h'

theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · exact (add_one_lt_exp hx).le

lemma one_sub_lt_exp_neg {x : ℝ} (hx : x ≠ 0) : 1 - x < exp (-x) :=
  (sub_eq_neg_add _ _).trans_lt <| add_one_lt_exp <| neg_ne_zero.2 hx

lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ exp (-x) :=
  (sub_eq_neg_add _ _).trans_le <| add_one_le_exp _

theorem one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) : (1 - t / n) ^ n ≤ exp (-t) := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  calc
    (1 - t / n) ^ n ≤ rexp (-(t / n)) ^ n := by
      gcongr
      · exact sub_nonneg.2 <| div_le_one_of_le₀ ht' n.cast_nonneg
      · exact one_sub_le_exp_neg _
    _ = rexp (-t) := by rw [← Real.exp_nat_mul, mul_neg, mul_comm, div_mul_cancel₀]; positivity

lemma le_inv_mul_exp (x : ℝ) {c : ℝ} (hc : 0 < c) : x ≤ c⁻¹ * exp (c * x) := by
  rw [le_inv_mul_iff₀ hc]
  calc c * x
  _ ≤ c * x + 1 := le_add_of_nonneg_right zero_le_one
  _ ≤ _ := Real.add_one_le_exp (c * x)

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.exp` is always positive. -/
@[positivity Real.exp _]
def evalExp : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.exp $a) =>
    assertInstancesCommute
    pure (.positive q(Real.exp_pos $a))
  | _, _, _ => throwError "not Real.exp"

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
theorem norm_exp_ofReal (x : ℝ) : ‖exp x‖ = Real.exp x := by
  rw [← ofReal_exp]
  exact Complex.norm_of_nonneg (le_of_lt (Real.exp_pos _))

@[deprecated (since := "2025-02-16")] alias abs_exp_ofReal := norm_exp_ofReal

end Complex
