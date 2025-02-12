/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Data.Complex.Norm

/-!
# Absolute values of complex numbers

-/

open Set ComplexConjugate

namespace Complex

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the Complex norm. -/
noncomputable abbrev abs (z : ℂ) : ℝ := ‖z‖

theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z := rfl

theorem abs_eq_norm (z : ℂ) : abs z = ‖z‖ := rfl

theorem abs_apply {z : ℂ} : Complex.abs z = Real.sqrt (normSq z) :=
  rfl

@[simp, norm_cast]
theorem abs_ofReal (r : ℝ) : Complex.abs r = |r| := norm_real r

protected theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : Complex.abs r = r :=
  Complex.norm_of_nonneg h

-- Porting note: removed `norm_cast` attribute because the RHS can't start with `↑`
@[simp]
theorem abs_natCast (n : ℕ) : Complex.abs n = n := norm_natCast n

@[simp]
theorem abs_ofNat (n : ℕ) [n.AtLeastTwo] :
    Complex.abs ofNat(n) = ofNat(n) :=
  norm_ofNat n

theorem mul_self_abs (z : ℂ) : Complex.abs z * Complex.abs z = normSq z :=
  norm_mul_self_eq_normSq _

protected theorem sq_abs (z : ℂ) : Complex.abs z ^ 2 = normSq z := Complex.sq_norm _

@[simp]
theorem sq_abs_sub_sq_re (z : ℂ) : Complex.abs z ^ 2 - z.re ^ 2 = z.im ^ 2 := sq_norm_sub_sq_re _

@[simp]
theorem sq_abs_sub_sq_im (z : ℂ) : Complex.abs z ^ 2 - z.im ^ 2 = z.re ^ 2 := sq_norm_sub_sq_im _

lemma abs_add_mul_I (x y : ℝ) : Complex.abs (x + y * I) = (x ^ 2 + y ^ 2).sqrt := norm_add_mul_I _ _

lemma abs_eq_sqrt_sq_add_sq (z : ℂ) : Complex.abs z = (z.re ^ 2 + z.im ^ 2).sqrt :=
  norm_eq_sqrt_sq_add_sq _

@[simp]
theorem abs_I : Complex.abs I = 1 := norm_I

protected theorem abs_two : Complex.abs 2 = 2 := abs_ofNat 2

@[simp]
theorem range_abs : range Complex.abs = Ici 0 := Complex.range_norm

@[simp]
theorem abs_conj (z : ℂ) : Complex.abs (conj z) = Complex.abs z := norm_conj _

theorem abs_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (s.prod f) = s.prod fun i ↦ Complex.abs (f i) :=
  Complex.norm_prod s f

protected theorem abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  Complex.norm_pow _ _

theorem abs_zpow (z : ℂ) (n : ℤ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  Complex.norm_zpow _ _

@[bound]
theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ Complex.abs z := abs_re_le_norm _

@[bound]
theorem abs_im_le_abs (z : ℂ) : |z.im| ≤ Complex.abs z := abs_im_le_norm _

theorem re_le_abs (z : ℂ) : z.re ≤ Complex.abs z := re_le_norm _

theorem im_le_abs (z : ℂ) : z.im ≤ Complex.abs z := im_le_norm _

@[simp]
theorem abs_re_lt_abs {z : ℂ} : |z.re| < Complex.abs z ↔ z.im ≠ 0 := abs_re_lt_norm

@[simp]
theorem abs_im_lt_abs {z : ℂ} : |z.im| < Complex.abs z ↔ z.re ≠ 0 := abs_im_lt_norm

@[simp]
lemma abs_re_eq_abs {z : ℂ} : |z.re| = Complex.abs z ↔ z.im = 0 := abs_re_eq_norm

@[simp]
lemma abs_im_eq_abs {z : ℂ} : |z.im| = Complex.abs z ↔ z.re = 0 := abs_im_eq_norm

@[simp]
protected theorem abs_abs (z : ℂ) : |Complex.abs z| = Complex.abs z := abs_norm z

theorem abs_le_abs_re_add_abs_im (z : ℂ) : Complex.abs z ≤ |z.re| + |z.im| :=
  norm_le_abs_re_add_abs_im _

theorem abs_le_sqrt_two_mul_max (z : ℂ) : Complex.abs z ≤ Real.sqrt 2 * max |z.re| |z.im| :=
  norm_le_sqrt_two_mul_max _

theorem abs_re_div_abs_le_one (z : ℂ) : |z.re / Complex.abs z| ≤ 1 :=
  abs_re_div_norm_le_one _

theorem abs_im_div_abs_le_one (z : ℂ) : |z.im / Complex.abs z| ≤ 1 :=
  abs_im_div_norm_le_one _

@[simp, norm_cast] lemma abs_intCast (n : ℤ) : Complex.abs n = |↑n| :=
  norm_intCast _

theorem normSq_eq_abs (x : ℂ) : normSq x = (Complex.abs x) ^ 2 :=
  normSq_eq_norm_sq _

/-! ### Cauchy sequences -/

local notation "abs'" => _root_.abs

theorem isCauSeq_re (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).re := isCauSeq_re' _

theorem isCauSeq_im (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).im := isCauSeq_im' _

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_im f⟩

theorem isCauSeq_abs {f : ℕ → ℂ} (hf : IsCauSeq Complex.abs f) :
    IsCauSeq abs' (Complex.abs ∘ f) := isCauSeq_norm hf

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ Complex.abs) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

theorem equiv_limAux (f : CauSeq ℂ Complex.abs) :
    f ≈ CauSeq.const Complex.abs (limAux f) := equiv_limAux' _

instance instIsComplete : CauSeq.IsComplete ℂ Complex.abs :=
  ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ Complex.abs) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I := lim_eq_lim_im_add_lim_re' _

theorem lim_re (f : CauSeq ℂ Complex.abs) : lim (cauSeqRe f) = (lim f).re := lim_re' _

theorem lim_im (f : CauSeq ℂ Complex.abs) : lim (cauSeqIm f) = (lim f).im := lim_im' _

theorem isCauSeq_conj (f : CauSeq ℂ Complex.abs) :
    IsCauSeq Complex.abs fun n => conj (f n) := isCauSeq_conj' _

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ Complex.abs) : CauSeq ℂ Complex.abs :=
  ⟨_, isCauSeq_conj f⟩

theorem lim_conj (f : CauSeq ℂ Complex.abs) : lim (cauSeqConj f) = conj (lim f) :=
  lim_conj' _

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqAbs (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_abs f.2⟩

theorem lim_abs (f : CauSeq ℂ Complex.abs) : lim (cauSeqAbs f) = Complex.abs (lim f) :=
  lim_norm _

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 :=
  fun h ↦ (zero_re ▸ h ▸ hs).false

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 :=
  ne_zero_of_re_pos <| zero_lt_one.trans hs

lemma re_neg_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : (-s).re ≠ 0 :=
  ne_iff_lt_or_gt.mpr <| Or.inl <| neg_re s ▸ (neg_lt_zero.mpr hs)

lemma re_neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : (-s).re ≠ 0 :=
  re_neg_ne_zero_of_re_pos <| zero_lt_one.trans hs

end Complex
