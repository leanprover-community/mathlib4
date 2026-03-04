/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Qq

/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/

@[expose] public section


noncomputable section

open Real ComplexConjugate Finset Set

/-
## Definitions
-/
namespace Real
variable {x y z : ℝ}

/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re

noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl

theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl

theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]

theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]

theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]
theorem rpow_intCast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]
theorem rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by simpa using rpow_intCast x n

@[simp, norm_cast]
theorem rpow_neg_natCast (x : ℝ) (n : ℕ) : x ^ (-n : ℝ) = x ^ (-n : ℤ) := by
  rw [← rpow_intCast, Int.cast_neg, Int.cast_natCast]

@[simp]
lemma rpow_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (ofNat(n) : ℕ) :=
  rpow_natCast x n

@[simp]
theorem rpow_neg_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] : x ^ (-ofNat(n) : ℝ) = x ^ (-ofNat(n) : ℤ) :=
  rpow_neg_natCast _ _

@[simp]
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]

@[simp] lemma exp_one_pow (n : ℕ) : exp 1 ^ n = exp n := by rw [← rpow_natCast, exp_one_rpow]

theorem rpow_eq_zero_iff_of_nonneg (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]
lemma rpow_eq_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by
  simp [rpow_eq_zero_iff_of_nonneg, *]

lemma rpow_ne_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y ≠ 0 ↔ x ≠ 0 := by
  simp [hx, hy]

open Real

theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) := by
  rw [rpow_def, Complex.cpow_def, if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ←
      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

-- simp is called on three goals at once (leaving one), with different simp sets
set_option linter.flexible false in
theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]
theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

theorem rpow_zero_pos (x : ℝ) : 0 < x ^ (0 : ℝ) := by simp

@[simp]
theorem pi_rpow_zero {α : Type*} (f : α → ℝ) : f ^ (0 : ℝ) = 1 := by ext; simp

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]

theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _

theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]

@[simp]
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]
theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y := by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]

@[bound]
theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) := by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]

lemma rpow_inv_log (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ (log x)⁻¹ = exp 1 := by
  rw [rpow_def_of_pos hx₀, mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

/-- See `Real.rpow_inv_log` for the equality when `x ≠ 1` is strictly positive. -/
lemma rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ ≤ exp 1 := by
  calc
    _ ≤ |x ^ (log x)⁻¹| := le_abs_self _
    _ ≤ |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y := by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

variable {w x y z : ℝ}

theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]

theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

/-- Variant of `Real.rpow_add'` that avoids having to prove `y + z = w` twice. -/
lemma rpow_of_add_eq (hx : 0 ≤ x) (hw : w ≠ 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h, rpow_add' hx]; rwa [h]

theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right-hand side is `1` while the left-hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) := by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 :=
          mul_le_mul (zero_rpow_le_one y) (zero_rpow_le_one z) (zero_rpow_nonneg z) zero_le_one
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]

theorem rpow_sum_of_pos {ι : Type*} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x :=
  map_sum (⟨⟨fun (x : ℝ) => (a ^ x : ℝ), rpow_zero a⟩, rpow_add ha⟩ : ℝ →+ (Additive ℝ)) f s

theorem rpow_sum_of_nonneg {ι : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x := by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

/-- See also `rpow_neg` for a version with `(x ^ y)⁻¹` in the RHS. -/
theorem rpow_neg_eq_inv_rpow (x y : ℝ) : x ^ (-y) = x⁻¹ ^ y := by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

/-- See also `rpow_neg_eq_inv_rpow` for a version with `x⁻¹ ^ y` in the RHS. -/
theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]

theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

protected theorem _root_.HasCompactSupport.rpow_const {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (fun x ↦ f x ^ r) :=
  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

theorem ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]

theorem ofReal_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * I * y) := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, norm_neg, arg_ofReal_of_neg hlt, ← ofReal_neg, arg_ofReal_of_nonneg (neg_nonneg.2 hx),
    ofReal_zero, zero_mul, add_zero]

lemma cpow_ofReal (x : ℂ) (y : ℝ) :
    x ^ (y : ℂ) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul, im_ofReal_mul, log_re, log_im, mul_comm y, mul_comm y, Real.exp_mul,
      Real.exp_log]
    rwa [norm_pos_iff]

lemma cpow_ofReal_re (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).re = ‖x‖ ^ y * Real.cos (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

lemma cpow_ofReal_im (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).im = ‖x‖ ^ y * Real.sin (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

theorem norm_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, norm_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

theorem norm_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw

theorem norm_cpow_le (z w : ℂ) : ‖z ^ w‖ ≤ ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  by_cases! h : z = 0 → w.re = 0 → w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]
theorem norm_cpow_real (x : ℂ) (y : ℝ) : ‖x ^ (y : ℂ)‖ = ‖x‖ ^ y := by
  rw [norm_cpow_of_imp] <;> simp

@[simp]
theorem norm_cpow_inv_nat (x : ℂ) (n : ℕ) : ‖x ^ (n⁻¹ : ℂ)‖ = ‖x‖ ^ (n⁻¹ : ℝ) := by
  rw [← norm_cpow_real]; simp

theorem norm_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : ‖(x : ℂ) ^ y‖ = x ^ y.re := by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), arg_ofReal_of_nonneg hx.le,
    zero_mul, Real.exp_zero, div_one, Complex.norm_of_nonneg hx.le]

theorem norm_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    ‖(x : ℂ) ^ y‖ = x ^ re y := by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

open Filter in
lemma norm_ofReal_cpow_eventually_eq_atTop (c : ℂ) :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) =ᶠ[atTop] fun t ↦ t ^ c.re := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]

lemma norm_natCast_cpow_of_re_ne_zero (n : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

lemma norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

lemma norm_natCast_cpow_pos_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : 0 < ‖(n : ℂ) ^ s‖ :=
  (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem cpow_mul_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℂ) :
    (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z := by
  rw [cpow_mul, ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

end Complex

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is positive (namely 1)
when the exponent is zero. The other cases are done in `evalRpow`. -/
@[positivity (_ : ℝ) ^ (0 : ℝ)]
meta def evalRpowZero : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(Real.rpow_zero_pos $a))
  | _, _, _ => throwError "not Real.rpow"

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : ℝ) ^ (_ : ℝ)]
meta def evalRpow : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ ($b : ℝ)) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa =>
        pure (.positive q(Real.rpow_pos_of_pos $pa $b))
    | .nonnegative pa =>
        pure (.nonnegative q(Real.rpow_nonneg $pa $b))
    | _ => pure .none
  | _, _, _ => throwError "not Real.rpow"

end Mathlib.Meta.Positivity

/-!
## Further algebraic properties of `rpow`
-/


namespace Real

variable {x y z : ℝ} {n : ℕ}

theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.ofReal_inj, Complex.ofReal_cpow (rpow_nonneg hx _),
      Complex.ofReal_cpow hx, Complex.ofReal_mul, Complex.cpow_mul, Complex.ofReal_cpow hx] <;>
    simp only [(Complex.ofReal_mul _ _).symm, (Complex.ofReal_log hx).symm, Complex.ofReal_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_natCast, ← rpow_mul hx, mul_comm y]

lemma rpow_zpow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_intCast, ← rpow_mul hx, mul_comm y]

lemma rpow_add_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_def, rpow_def, Complex.ofReal_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx), Complex.ofReal_intCast,
    Complex.cpow_intCast, ← Complex.ofReal_zpow, mul_comm, Complex.re_ofReal_mul, mul_comm]

lemma rpow_add_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  simpa using rpow_add_intCast hx y n

lemma rpow_sub_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_add_intCast hx y (-n)

lemma rpow_sub_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_sub_intCast hx y n

lemma rpow_add_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_intCast]

lemma rpow_add_natCast' (hx : 0 ≤ x) (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_natCast]

lemma rpow_sub_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_intCast]

lemma rpow_sub_natCast' (hx : 0 ≤ x) (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_natCast]

theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1

theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1

lemma rpow_add_one' (hx : 0 ≤ x) (h : y + 1 ≠ 0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' hx h, rpow_one]

lemma rpow_one_add' (hx : 0 ≤ x) (h : 1 + y ≠ 0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' hx h, rpow_one]

lemma rpow_sub_one' (hx : 0 ≤ x) (h : y - 1 ≠ 0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' hx h, rpow_one]

lemma rpow_one_sub' (hx : 0 ≤ x) (h : 1 - y ≠ 0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' hx h, rpow_one]

theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  simp

theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [rpow_neg_eq_inv_rpow, rpow_one]

-- TODO: fix non-terminal simp (acting on three goals, with different simp sets, leaving two)
set_option linter.flexible false in
theorem mul_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
  iterate 2 rw [Real.rpow_def_of_nonneg]; split_ifs with h_ifs <;> simp_all
  · rw [log_mul ‹_› ‹_›, add_mul, exp_add, rpow_def_of_pos (hy.lt_of_ne' ‹_›)]
  all_goals positivity

theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rw [← rpow_neg_eq_inv_rpow, rpow_neg hx]

theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]

@[push low] /- Lower priority than `log_pow` and `log_zpow`.
This is because otherwise the `pull` tactic will use `log_rpow` in places where it should
use `log_pow` or `log_zpow`. -/
theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x := by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]

theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩

@[simp] lemma rpow_rpow_inv (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul hx, mul_inv_cancel₀ hy, rpow_one]

@[simp] lemma rpow_inv_rpow (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul hx, inv_mul_cancel₀ hy, rpow_one]

theorem pow_rpow_inv_natCast (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, mul_inv_cancel₀ hn0, rpow_one]

theorem rpow_inv_natCast_pow (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, inv_mul_cancel₀ hn0, rpow_one]

lemma rpow_natCast_mul (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_natCast]

lemma rpow_mul_natCast (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_natCast]

lemma rpow_intCast_mul (hx : 0 ≤ x) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_intCast]

lemma rpow_mul_intCast (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_intCast]

/-! Note: lemmas about `(∏ i ∈ s, f i ^ r)` such as `Real.finset_prod_rpow` are proved
in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` instead. -/

/-!
## Order and monotonicity
-/


@[gcongr, bound]
theorem rpow_lt_rpow_left (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz

theorem rpow_left_strictMonoOn {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab ↦ rpow_lt_rpow_left ha hab hr

@[gcongr, bound]
theorem rpow_le_rpow_left {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow_left h h₁' h₂')

theorem rpow_left_monotoneOn {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab ↦ rpow_le_rpow_left ha hab hr

lemma rpow_lt_rpow_left_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z := by
  have := hx.trans hxy
  rw [← inv_lt_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow_left ?_ hxy (neg_pos.2 hz)
  all_goals positivity

lemma rpow_le_rpow_left_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z := by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_le_rpow_left ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity

theorem rpow_lt_rpow_iff_left (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le (fun h ↦ rpow_le_rpow_left hy h (le_of_lt hz)),
    fun h ↦ rpow_lt_rpow_left hx h hz⟩

theorem rpow_le_rpow_iff_left (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff_left hy hx hz

lemma rpow_lt_rpow_iff_left_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le fun h ↦ rpow_le_rpow_left_of_nonpos hx h hz.le,
    fun h ↦ rpow_lt_rpow_left_of_neg hy h hz⟩

lemma rpow_le_rpow_iff_left_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff_left_of_neg hy hx hz

lemma le_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff_left hx _ hz, rpow_inv_rpow] <;> positivity

lemma rpow_inv_le_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff_left _ hy hz, rpow_inv_rpow] <;> positivity

lemma lt_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  lt_iff_lt_of_le_iff_le <| rpow_inv_le_iff_of_pos hy hx hz

lemma rpow_inv_lt_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  lt_iff_lt_of_le_iff_le <| le_rpow_inv_iff_of_pos hy hx hz

theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z := by
  rw [← rpow_le_rpow_iff_left_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x < y ^ z⁻¹ ↔ y < x ^ z := by
  rw [← rpow_lt_rpow_iff_left_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ < y ↔ y ^ z < x := by
  rw [← rpow_lt_rpow_iff_left_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  rw [← rpow_le_rpow_iff_left_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_lt_rpow_right (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]
theorem rpow_le_rpow_right (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx)

@[deprecated (since := "2025-10-28")] alias rpow_lt_rpow_of_exponent_neg :=
  rpow_lt_rpow_left_of_neg

theorem rpow_left_strictAntiOn {r : ℝ} (hr : r < 0) :
    StrictAntiOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab ↦ rpow_lt_rpow_left_of_neg ha hab hr

@[deprecated (since := "2025-10-28")] alias rpow_le_rpow_of_exponent_nonpos :=
  rpow_le_rpow_left_of_nonpos

theorem rpow_left_antitoneOn {r : ℝ} (hr : r ≤ 0) :
    AntitoneOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab ↦ rpow_le_rpow_left_of_nonpos ha hab hr

@[simp]
theorem rpow_le_rpow_iff_right (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z := by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]
theorem rpow_lt_rpow_iff_right (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_ge, rpow_le_rpow_iff_right hx, lt_iff_not_ge]

theorem rpow_lt_rpow_right_of_lt_one (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)

theorem rpow_le_rpow_right_of_le_one (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]
theorem rpow_le_rpow_iff_right_of_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y ≤ x ^ z ↔ z ≤ y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]
theorem rpow_lt_rpow_iff_right_of_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y < x ^ z ↔ z < y := by
  rw [lt_iff_not_ge, rpow_le_rpow_iff_right_of_lt_one hx0 hx1, lt_iff_not_ge]

theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  rw [← one_rpow z]
  exact rpow_lt_rpow_left hx1 hx2 hz

theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  rw [← one_rpow z]
  exact rpow_le_rpow_left hx1 hx2 hz

theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  convert rpow_lt_rpow_right hx hz
  exact (rpow_zero x).symm

theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 := by
  convert rpow_le_rpow_right hx hz
  exact (rpow_zero x).symm

theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  rw [← one_rpow z]
  exact rpow_lt_rpow_left zero_le_one hx hz

theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  rw [← one_rpow z]
  exact rpow_le_rpow_left zero_le_one hx hz

theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
    1 < x ^ z := by
  convert rpow_lt_rpow_right_of_lt_one hx1 hx2 hz
  exact (rpow_zero x).symm

theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert rpow_le_rpow_right_of_le_one hx1 hx2 hz
  exact (rpow_zero x).symm

theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx.le, log_neg_iff hx]

theorem rpow_lt_one_iff (hx : 0 ≤ x) :
    x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]

theorem rpow_lt_one_iff' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ y < 1 ↔ x < 1 := by
  rw [← Real.rpow_lt_rpow_iff_left hx zero_le_one hy, Real.one_rpow]

theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx.le, log_neg_iff hx]

theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' ℝ).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

/-- This is a more general but less convenient version of `rpow_le_rpow_right_of_le_one`.
This version allows `x = 0`, so it explicitly forbids `x = y = 0`, `z ≠ 0`. -/
theorem rpow_le_rpow_right_of_le_one_of_imp (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y)
    (h : x = 0 → y = 0 → z = 0) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_right_of_le_one hx0' hx1 hyz

/-- This version of `rpow_le_rpow_right_of_le_one` allows `x = 0` but requires `0 ≤ z`.
See also `rpow_le_rpow_right_of_le_one_of_imp` for the most general version. -/
theorem rpow_le_rpow_right_of_le_one' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  rpow_le_rpow_right_of_le_one_of_imp hx0 hx1 hyz fun _ hy ↦ le_antisymm (hyz.trans_eq hy) hz

@[deprecated (since := "2026-03-03")] alias strictMonoOn_rpow_Ici_of_exponent_pos :=
  rpow_left_strictMonoOn

@[deprecated (since := "2026-03-03")] alias monotoneOn_rpow_Ici_of_exponent_nonneg :=
  rpow_left_monotoneOn

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow := rpow_lt_rpow_left

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow := rpow_le_rpow_left

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_of_neg := rpow_lt_rpow_left_of_neg

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_of_nonpos := rpow_le_rpow_left_of_nonpos

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_iff := rpow_lt_rpow_iff_left

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_iff := rpow_le_rpow_iff_left

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_iff_of_neg := rpow_lt_rpow_iff_left_of_neg

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_iff_of_neg := rpow_le_rpow_iff_left_of_neg

@[deprecated (since := "2026-03-03")] alias strictAntiOn_rpow_Ioi_of_exponent_neg :=
  rpow_left_strictAntiOn

@[deprecated (since := "2026-03-03")] alias antitoneOn_rpow_Ioi_of_exponent_nonpos :=
  rpow_left_antitoneOn

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_of_exponent_lt := rpow_lt_rpow_right

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_of_exponent_le := rpow_le_rpow_right

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_left_iff := rpow_le_rpow_iff_right

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_left_iff := rpow_lt_rpow_iff_right

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_of_exponent_gt :=
  rpow_lt_rpow_right_of_lt_one

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_of_exponent_ge :=
  rpow_le_rpow_right_of_le_one

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_left_iff_of_base_lt_one :=
  rpow_le_rpow_iff_right_of_lt_one

@[deprecated (since := "2026-03-03")] alias rpow_lt_rpow_left_iff_of_base_lt_one :=
  rpow_lt_rpow_iff_right_of_lt_one

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_of_exponent_ge_of_imp :=
  rpow_le_rpow_right_of_le_one_of_imp

@[deprecated (since := "2026-03-03")] alias rpow_le_rpow_of_exponent_ge' :=
  rpow_le_rpow_right_of_le_one'

lemma rpow_max {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) :
    (max x y) ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow_left hx hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow_left hy hxy hp)]

theorem self_le_rpow_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : y ≤ 1) : x ≤ x ^ y := by
  simpa only [rpow_one]
    using rpow_le_rpow_right_of_le_one_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · one_ne_zero)

theorem self_le_rpow_of_one_le (h₁ : 1 ≤ x) (h₂ : 1 ≤ y) : x ≤ x ^ y := by
  simpa only [rpow_one] using rpow_le_rpow_right h₁ h₂

theorem rpow_le_self_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : 1 ≤ y) : x ^ y ≤ x := by
  simpa only [rpow_one]
    using rpow_le_rpow_right_of_le_one_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · (one_pos.trans_le h₃).ne')

theorem rpow_le_self_of_one_le (h₁ : 1 ≤ x) (h₂ : y ≤ 1) : x ^ y ≤ x := by
  simpa only [rpow_one] using rpow_le_rpow_right h₁ h₂

theorem self_lt_rpow_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_right_of_lt_one h₁ h₂ h₃

theorem self_lt_rpow_of_one_lt (h₁ : 1 < x) (h₂ : 1 < y) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_right h₁ h₂

theorem rpow_lt_self_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_right_of_lt_one h₁ h₂ h₃

theorem rpow_lt_self_of_one_lt (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_right h₁ h₂

theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } := by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← mul_inv_cancel₀ hx, rpow_mul hy, rpow_mul hz, hyz]

lemma rpow_left_inj (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injOn hz).eq_iff hx hy

lemma rpow_inv_eq (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_left_inj _ hy hz, rpow_inv_rpow hx hz]; positivity

lemma eq_rpow_inv (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_left_inj hx _ hz, rpow_inv_rpow hy hz]; positivity

theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ log x ≤ z * log y := by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]

lemma le_pow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy

lemma le_zpow_iff_log_le {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy

lemma le_rpow_of_log_le (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

lemma le_pow_of_log_le (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ le_rpow_of_log_le hy h

lemma le_zpow_of_log_le {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ le_rpow_of_log_le hy h

theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ log x < z * log y := by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]

lemma lt_pow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy

lemma lt_zpow_iff_log_lt {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy

lemma lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

lemma lt_pow_of_log_lt (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h

lemma lt_zpow_of_log_lt {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h

lemma rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z ≤ y ↔ z * log x ≤ log y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma pow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_natCast]

lemma zpow_le_iff_le_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_intCast]

lemma le_log_of_rpow_le (hx : 0 < x) (h : x ^ z ≤ y) : z * log x ≤ log y :=
  log_rpow hx _ ▸ log_le_log (by positivity) h

lemma le_log_of_pow_le (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)

lemma le_log_of_zpow_le {n : ℤ} (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)

lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

lemma pow_le_of_le_log (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ rpow_le_of_le_log hy h

lemma zpow_le_of_le_log {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ rpow_le_of_le_log hy h

lemma rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log y := by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma pow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_natCast]

lemma zpow_lt_iff_lt_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_intCast]

lemma lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) : z * log x < log y :=
  log_rpow hx _ ▸ log_lt_log (by positivity) h

lemma lt_log_of_pow_lt (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)

lemma lt_log_of_zpow_lt {n : ℤ} (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)

lemma rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

lemma pow_lt_of_lt_log (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h

lemma zpow_lt_of_lt_log {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h

theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx.le]

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

/-- `log x` is bounded above by a multiple of every power of `x` with positive exponent. -/
lemma log_le_rpow_div {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : log x ≤ x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

/-- The (real) logarithm of a natural number `n` is bounded by a multiple of every power of `n`
with positive exponent. -/
lemma log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : log n ≤ n ^ ε / ε :=
  log_le_rpow_div n.cast_nonneg hε

lemma strictMono_rpow_of_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMono (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
  exact exp_strictMono.comp <| StrictMono.const_mul strictMono_id <| Real.log_pos hb

lemma monotone_rpow_of_base_ge_one {b : ℝ} (hb : 1 ≤ b) :
    Monotone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

lemma strictAnti_rpow_of_base_lt_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictAnti (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos hb₀]
  exact exp_strictMono.comp_strictAnti <| StrictMono.const_mul_of_neg strictMono_id
      <| Real.log_neg hb₀ hb₁

lemma antitone_rpow_of_base_le_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b ≤ 1) :
    Antitone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

lemma rpow_right_inj (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

/-- Guessing rule for the `bound` tactic: when trying to prove `x ^ y ≤ x ^ z`, we can either assume
`1 ≤ x` or `0 < x ≤ 1`. -/
@[bound] lemma rpow_le_rpow_of_exponent_le_or_ge {x y z : ℝ}
    (h : 1 ≤ x ∧ y ≤ z ∨ 0 < x ∧ x ≤ 1 ∧ z ≤ y) : x ^ y ≤ x ^ z := by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_right x1 yz
  · exact Real.rpow_le_rpow_right_of_le_one x0 x1 zy

end Real

namespace Complex

lemma norm_prime_cpow_le_one_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_left_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_right one_le_two <| (neg_lt_neg hs).le

lemma one_sub_prime_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  refine sub_ne_zero_of_ne fun H ↦ ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H, norm_one] at this
  norm_num at this

lemma norm_natCast_cpow_le_norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) {w z : ℂ}
    (h : w.re ≤ z.re) :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ := by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_right (by exact_mod_cast hn) h

lemma norm_natCast_cpow_le_norm_natCast_cpow_iff {n : ℕ} (hn : 1 < n) {w z : ℂ} :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ ↔ w.re ≤ z.re := by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_iff_right (Nat.one_lt_cast.mpr hn)]

lemma norm_log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ‖log n‖ ≤ n ^ ε / ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log, norm_real, norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

end Complex


/-!
## Square roots of reals
-/


namespace Real

variable {z x y : ℝ}

section Sqrt

theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]

theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = √x ^ r := by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring

end Sqrt

end Real

namespace Complex

lemma cpow_inv_two_re (x : ℂ) : (x ^ (2⁻¹ : ℂ)).re = √((‖x‖ + x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_re, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, cos_half, ← sqrt_mul, ← mul_div_assoc, mul_add, mul_one, norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

lemma cpow_inv_two_im_eq_sqrt {x : ℂ} (hx : 0 ≤ x.im) :
    (x ^ (2⁻¹ : ℂ)).im = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub,
    mul_one, norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

lemma cpow_inv_two_im_eq_neg_sqrt {x : ℂ} (hx : x.im < 0) :
    (x ^ (2⁻¹ : ℂ)).im = -√((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (norm_nonneg _),
    ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

lemma abs_cpow_inv_two_im (x : ℂ) : |(x ^ (2⁻¹ : ℂ)).im| = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
    ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]

open scoped ComplexOrder in
lemma inv_natCast_cpow_ofReal_pos {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    0 < ((n : ℂ) ^ (x : ℂ))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : ℂ) ^ (x : ℂ) = (n : ℝ) ^ (x : ℂ) from rfl, ← ofReal_cpow n.cast_nonneg']
  positivity

end Complex

section Tactics

/-!
## Tactic extensions for real powers
-/
namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

theorem IsNat.rpow_eq_pow {b : ℝ} {n : ℕ} (h : IsNat b n) (a : ℝ) : a ^ b = a ^ n := by
  rw [h.1, Real.rpow_natCast]

theorem IsInt.rpow_eq_inv_pow {b : ℝ} {n : ℕ} (h : IsInt b (.negOfNat n)) (a : ℝ) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1, Real.rpow_intCast, Int.negOfNat_eq, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isNat_rpow_pos {a b : ℝ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isNat_rpow_neg {a b : ℝ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ (Int.negOfNat nb)) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isInt_rpow_pos {a b : ℝ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isInt_rpow_neg {a b : ℝ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ (Int.negOfNat nb)) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isNNRat_rpow_pos {a b : ℝ} {nb : ℕ}
    {num den : ℕ}
    (pb : IsNat b nb) (pe' : IsNNRat (a ^ nb) num den) :
    IsNNRat (a ^ b) num den := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isRat_rpow_pos {a b : ℝ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsNat b nb) (pe' : IsRat (a ^ nb) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isNNRat_rpow_neg {a b : ℝ} {nb : ℕ}
    {num den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNNRat (a ^ (Int.negOfNat nb)) num den) :
    IsNNRat (a ^ b) num den := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isRat_rpow_neg {a b : ℝ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsRat (a ^ (Int.negOfNat nb)) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, Real.rpow_intCast]

/-- Given proofs
- that `a` is a natural number `m`
- that `b` is a nonnegative rational number `n / d`
- that `r ^ d = m ^ n` (written as `r ^ d = k`, `m ^ n = l`, `k = l`)

prove that `a ^ b = r`.
-/
theorem IsNat.rpow_isNNRat {a b : ℝ} {m n d r : ℕ} (ha : IsNat a m) (hb : IsNNRat b n d)
    (k : ℕ) (hr : r ^ d = k) (l : ℕ) (hm : m ^ n = l) (hkl : k = l) : IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d ≠ 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl, div_eq_mul_inv, Real.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
    Nat.cast_pow, Real.pow_rpow_inv_natCast] <;> positivity

theorem IsNNRat.rpow_isNNRat (a b : ℝ) (na da : ℕ) (ha : IsNNRat a na da)
    (nr dr : ℕ) (hnum : IsNat ((na : ℝ) ^ b) nr) (hden : IsNat ((da : ℝ) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : ℝ) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz

theorem rpow_isRat_eq_inv_rpow (a b : ℝ) (n d : ℕ) (hb : IsRat b (Int.negOfNat n) d) :
    a ^ b = (a⁻¹) ^ (n / d : ℝ) := by
  rw [← Real.rpow_neg_eq_inv_rpow, hb.neg_to_eq rfl rfl]

open Lean in
/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatRPowIsNNRat
    (a : Q(ℝ)) (na : Q(ℕ)) (pa : Q(IsNat $a $na))
    (b : Q(ℝ)) (nb db : Q(ℕ)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (ℕ × Σ r : Q(ℕ), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(ℕ) := mkRawNatLit r
  -- avoid evaluating powers in kernel
  let .some ⟨c, pc⟩ ← liftM <| OptionT.run <| evalNatPow er db | failure
  let .some ⟨d, pd⟩ ← liftM <| OptionT.run <| evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a` and `b` are both reals.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers,
except for the case `a < 0`, `b` isn't integer.

TODO: simplify terms like  `(-a : ℝ) ^ (b / 3 : ℝ)` and `(-a : ℝ) ^ (b / 2 : ℝ)` too,
possibly after first considering changing the junk value. -/
@[norm_num (_ : ℝ) ^ (_ : ℝ)]
meta def evalRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(ℝ), ~q(($a : ℝ)^($b : ℝ)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.rpow_eq_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.rpow_eq_inv_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : ℝ))
      assumeInstancesCommute
      return .eqTrans q(rpow_isRat_eq_inv_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

end Tactics
