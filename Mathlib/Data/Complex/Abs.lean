/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

#align_import data.complex.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Absolute values of complex numbers

-/

open Set ComplexConjugate

namespace Complex

/-! ### Absolute value -/

namespace AbsTheory

-- We develop enough theory to bundle `abs` into an `AbsoluteValue` before making things public;
-- this is so there's not two versions of it hanging around.
local notation "abs" z => Real.sqrt (normSq z)

private theorem mul_self_abs (z : ℂ) : ((abs z) * abs z) = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

private theorem abs_nonneg' (z : ℂ) : 0 ≤ abs z :=
  Real.sqrt_nonneg _

theorem abs_conj (z : ℂ) : (abs conj z) = abs z := by simp
#align complex.abs_theory.abs_conj Complex.AbsTheory.abs_conj

private theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ abs z := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (abs_nonneg' _), abs_mul_abs_self, mul_self_abs]
  apply re_sq_le_normSq

private theorem re_le_abs (z : ℂ) : z.re ≤ abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

private theorem abs_mul (z w : ℂ) : (abs z * w) = (abs z) * abs w := by
  rw [normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

private theorem abs_add (z w : ℂ) : (abs z + w) ≤ (abs z) + abs w :=
  (mul_self_le_mul_self_iff (abs_nonneg' (z + w))
      (add_nonneg (abs_nonneg' z) (abs_nonneg' w))).2 <| by
    rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs, add_right_comm, normSq_add,
      add_le_add_iff_left, mul_assoc, mul_le_mul_left (zero_lt_two' ℝ), ←
      Real.sqrt_mul <| normSq_nonneg z, ← normSq_conj w, ← map_mul]
    exact re_le_abs (z * conj w)

/-- The complex absolute value function, defined as the square root of the norm squared. -/
noncomputable def _root_.Complex.abs : AbsoluteValue ℂ ℝ where
  toFun x := abs x
  map_mul' := abs_mul
  nonneg' := abs_nonneg'
  eq_zero' _ := (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero
  add_le' := abs_add
#align complex.abs Complex.abs

end AbsTheory

theorem abs_def : (Complex.abs : ℂ → ℝ) = fun z => (normSq z).sqrt :=
  rfl
#align complex.abs_def Complex.abs_def

theorem abs_apply {z : ℂ} : Complex.abs z = (normSq z).sqrt :=
  rfl
#align complex.abs_apply Complex.abs_apply

@[simp, norm_cast]
theorem abs_ofReal (r : ℝ) : Complex.abs r = |r| := by
  simp [Complex.abs, normSq_ofReal, Real.sqrt_mul_self_eq_abs]
#align complex.abs_of_real Complex.abs_ofReal

nonrec theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : Complex.abs r = r :=
  (Complex.abs_ofReal _).trans (abs_of_nonneg h)
#align complex.abs_of_nonneg Complex.abs_of_nonneg

-- Porting note: removed `norm_cast` attribute because the RHS can't start with `↑`
@[simp]
theorem abs_natCast (n : ℕ) : Complex.abs n = n := Complex.abs_of_nonneg (Nat.cast_nonneg n)
#align complex.abs_of_nat Complex.abs_natCast
#align complex.abs_cast_nat Complex.abs_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem abs_ofNat (n : ℕ) [n.AtLeastTwo] :
    Complex.abs (no_index (OfNat.ofNat n : ℂ)) = OfNat.ofNat n :=
  abs_natCast n

theorem mul_self_abs (z : ℂ) : Complex.abs z * Complex.abs z = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)
#align complex.mul_self_abs Complex.mul_self_abs

theorem sq_abs (z : ℂ) : Complex.abs z ^ 2 = normSq z :=
  Real.sq_sqrt (normSq_nonneg _)
#align complex.sq_abs Complex.sq_abs

@[simp]
theorem sq_abs_sub_sq_re (z : ℂ) : Complex.abs z ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [sq_abs, normSq_apply, ← sq, ← sq, add_sub_cancel_left]
#align complex.sq_abs_sub_sq_re Complex.sq_abs_sub_sq_re

@[simp]
theorem sq_abs_sub_sq_im (z : ℂ) : Complex.abs z ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_abs_sub_sq_re, sub_sub_cancel]
#align complex.sq_abs_sub_sq_im Complex.sq_abs_sub_sq_im

lemma abs_add_mul_I (x y : ℝ) : abs (x + y * I) = (x ^ 2 + y ^ 2).sqrt := by
  rw [← normSq_add_mul_I]; rfl

lemma abs_eq_sqrt_sq_add_sq (z : ℂ) : abs z = (z.re ^ 2 + z.im ^ 2).sqrt := by
  rw [abs_apply, normSq_apply, sq, sq]

@[simp]
theorem abs_I : Complex.abs I = 1 := by simp [Complex.abs]
set_option linter.uppercaseLean3 false in
#align complex.abs_I Complex.abs_I

theorem abs_two : Complex.abs 2 = 2 := abs_ofNat 2
#align complex.abs_two Complex.abs_two

@[simp]
theorem range_abs : range Complex.abs = Ici 0 :=
  Subset.antisymm
    (by simp only [range_subset_iff, Ici, mem_setOf_eq, apply_nonneg, forall_const])
    (fun x hx => ⟨x, Complex.abs_of_nonneg hx⟩)
#align complex.range_abs Complex.range_abs

@[simp]
theorem abs_conj (z : ℂ) : Complex.abs (conj z) = Complex.abs z :=
  AbsTheory.abs_conj z
#align complex.abs_conj Complex.abs_conj

-- Porting note (#10618): @[simp] can prove it now
theorem abs_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (s.prod f) = s.prod fun I => Complex.abs (f I) :=
  map_prod Complex.abs _ _
#align complex.abs_prod Complex.abs_prod

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_pow]` -/
theorem abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_pow Complex.abs z n
#align complex.abs_pow Complex.abs_pow

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zpow₀]` -/
theorem abs_zpow (z : ℂ) (n : ℤ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_zpow₀ Complex.abs z n
#align complex.abs_zpow Complex.abs_zpow

theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
#align complex.abs_re_le_abs Complex.abs_re_le_abs

theorem abs_im_le_abs (z : ℂ) : |z.im| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
#align complex.abs_im_le_abs Complex.abs_im_le_abs

theorem re_le_abs (z : ℂ) : z.re ≤ Complex.abs z :=
  (abs_le.1 (abs_re_le_abs _)).2
#align complex.re_le_abs Complex.re_le_abs

theorem im_le_abs (z : ℂ) : z.im ≤ Complex.abs z :=
  (abs_le.1 (abs_im_le_abs _)).2
#align complex.im_le_abs Complex.im_le_abs

@[simp]
theorem abs_re_lt_abs {z : ℂ} : |z.re| < Complex.abs z ↔ z.im ≠ 0 := by
  rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk, Real.lt_sqrt (abs_nonneg _), normSq_apply,
    _root_.sq_abs, ← sq, lt_add_iff_pos_right, mul_self_pos]
#align complex.abs_re_lt_abs Complex.abs_re_lt_abs

@[simp]
theorem abs_im_lt_abs {z : ℂ} : |z.im| < Complex.abs z ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_abs (z * I)
#align complex.abs_im_lt_abs Complex.abs_im_lt_abs

@[simp]
lemma abs_re_eq_abs {z : ℂ} : |z.re| = abs z ↔ z.im = 0 :=
  not_iff_not.1 <| (abs_re_le_abs z).lt_iff_ne.symm.trans abs_re_lt_abs

@[simp]
lemma abs_im_eq_abs {z : ℂ} : |z.im| = abs z ↔ z.re = 0 :=
  not_iff_not.1 <| (abs_im_le_abs z).lt_iff_ne.symm.trans abs_im_lt_abs

@[simp]
theorem abs_abs (z : ℂ) : |Complex.abs z| = Complex.abs z :=
  _root_.abs_of_nonneg (AbsoluteValue.nonneg _ z)
#align complex.abs_abs Complex.abs_abs

-- Porting note: probably should be golfed
theorem abs_le_abs_re_add_abs_im (z : ℂ) : Complex.abs z ≤ |z.re| + |z.im| := by
  simpa [re_add_im] using Complex.abs.add_le z.re (z.im * I)
#align complex.abs_le_abs_re_add_abs_im Complex.abs_le_abs_re_add_abs_im

-- Porting note: added so `two_pos` in the next proof works
-- TODO: move somewhere else
instance : NeZero (1 : ℝ) :=
 ⟨by apply one_ne_zero⟩

theorem abs_le_sqrt_two_mul_max (z : ℂ) : Complex.abs z ≤ Real.sqrt 2 * max |z.re| |z.im| := by
  cases' z with x y
  simp only [abs_apply, normSq_mk, ← sq]
  by_cases hle : |x| ≤ |y|
  · calc
      Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (y ^ 2 + y ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle) _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_right hle, ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
  · have hle' := le_of_not_le hle
    rw [add_comm]
    calc
      Real.sqrt (y ^ 2 + x ^ 2) ≤ Real.sqrt (x ^ 2 + x ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle') _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_left hle', ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
#align complex.abs_le_sqrt_two_mul_max Complex.abs_le_sqrt_two_mul_max

theorem abs_re_div_abs_le_one (z : ℂ) : |z.re / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_re_le_abs]
#align complex.abs_re_div_abs_le_one Complex.abs_re_div_abs_le_one

theorem abs_im_div_abs_le_one (z : ℂ) : |z.im / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_im_le_abs]
#align complex.abs_im_div_abs_le_one Complex.abs_im_div_abs_le_one

@[simp, norm_cast] lemma abs_intCast (n : ℤ) : abs n = |↑n| := by rw [← ofReal_intCast, abs_ofReal]
#align complex.int_cast_abs Complex.abs_intCast

@[deprecated (since := "2024-02-14")]
lemma int_cast_abs (n : ℤ) : |↑n| = Complex.abs n := (abs_intCast _).symm

theorem normSq_eq_abs (x : ℂ) : normSq x = (Complex.abs x) ^ 2 := by
  simp [abs, sq, abs_def, Real.mul_self_sqrt (normSq_nonneg _)]
#align complex.norm_sq_eq_abs Complex.normSq_eq_abs

@[simp]
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨Real.sqrt x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩
#align complex.range_norm_sq Complex.range_normSq

/-! ### Cauchy sequences -/

local notation "abs'" => _root_.abs

theorem isCauSeq_re (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).re := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)
#align complex.is_cau_seq_re Complex.isCauSeq_re

theorem isCauSeq_im (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).im := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij ↦ by
    simpa only [← ofReal_sub, abs_ofReal, sub_re] using (abs_im_le_abs _).trans_lt $ H _ ij
#align complex.is_cau_seq_im Complex.isCauSeq_im

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_re f⟩
#align complex.cau_seq_re Complex.cauSeqRe

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_im f⟩
#align complex.cau_seq_im Complex.cauSeqIm

theorem isCauSeq_abs {f : ℕ → ℂ} (hf : IsCauSeq Complex.abs f) :
    IsCauSeq abs' (Complex.abs ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt
    (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩
#align complex.is_cau_seq_abs Complex.isCauSeq_abs

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ Complex.abs) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩
#align complex.lim_aux Complex.limAux

theorem equiv_limAux (f : CauSeq ℂ Complex.abs) :
    f ≈ CauSeq.const Complex.abs (limAux f) := fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun i H j ij => by
    cases' H _ ij with H₁ H₂
    apply lt_of_le_of_lt (abs_le_abs_re_add_abs_im _)
    dsimp [limAux] at *
    have := add_lt_add H₁ H₂
    rwa [add_halves] at this
#align complex.equiv_lim_aux Complex.equiv_limAux

instance instIsComplete : CauSeq.IsComplete ℂ Complex.abs :=
  ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ Complex.abs) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const Complex.abs (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal']) (by simp [limAux, cauSeqIm, ofReal'])
#align complex.lim_eq_lim_im_add_lim_re Complex.lim_eq_lim_im_add_lim_re

theorem lim_re (f : CauSeq ℂ Complex.abs) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']
#align complex.lim_re Complex.lim_re

theorem lim_im (f : CauSeq ℂ Complex.abs) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']
#align complex.lim_im Complex.lim_im

theorem isCauSeq_conj (f : CauSeq ℂ Complex.abs) :
    IsCauSeq Complex.abs fun n => conj (f n) := fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    rw [← RingHom.map_sub, abs_conj]; exact hi j hj⟩
#align complex.is_cau_seq_conj Complex.isCauSeq_conj

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ Complex.abs) : CauSeq ℂ Complex.abs :=
  ⟨_, isCauSeq_conj f⟩
#align complex.cau_seq_conj Complex.cauSeqConj

theorem lim_conj (f : CauSeq ℂ Complex.abs) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)
#align complex.lim_conj Complex.lim_conj

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqAbs (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_abs f.2⟩
#align complex.cau_seq_abs Complex.cauSeqAbs

theorem lim_abs (f : CauSeq ℂ Complex.abs) : lim (cauSeqAbs f) = Complex.abs (lim f) :=
  lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩
#align complex.lim_abs Complex.lim_abs

lemma ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 :=
  fun h ↦ ((zero_re ▸ h ▸ hs).trans zero_lt_one).false

lemma re_neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : (-s).re ≠ 0 :=
  ne_iff_lt_or_gt.mpr <| Or.inl <| neg_re s ▸ by linarith
