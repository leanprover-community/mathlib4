/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Abs

/-!
  # Norm on the complex numbers
-/

noncomputable section

namespace Complex
variable {z : ℂ}

open ComplexConjugate Topology Filter

instance : Norm ℂ :=
  ⟨abs⟩

@[simp]
theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z :=
  rfl

lemma norm_I : ‖I‖ = 1 := abs_I

instance instNormedAddCommGroup : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
    { abs with
      map_zero' := map_zero abs
      neg' := abs.map_neg
      eq_zero_of_map_eq_zero' := fun _ => abs.eq_zero.1 }

@[simp] lemma nnnorm_I : ‖I‖₊ = 1 := by simp [nnnorm]

theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl

theorem dist_eq_re_im (z w : ℂ) : dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq]
  rfl

@[simp]
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _

theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h

theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h

theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]

theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]

theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]

theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]

@[simp 1100, norm_cast] lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := abs_ofReal _
@[simp 1100, norm_cast] lemma norm_natCast (n : ℕ) : ‖(n : ℂ)‖ = n := abs_natCast _
@[simp 1100, norm_cast] lemma norm_intCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := abs_intCast n
@[simp 1100, norm_cast] lemma norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := norm_real _

@[simp, norm_cast] lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ := by ext; exact norm_real _
@[simp 1100, norm_cast] lemma nnnorm_natCast (n : ℕ) : ‖(n : ℂ)‖₊ = n := Subtype.ext <| by simp
@[simp 1100, norm_cast] lemma nnnorm_ratCast (q : ℚ) : ‖(q : ℂ)‖₊ = ‖(q : ℝ)‖₊ := nnnorm_real q

@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖ = OfNat.ofNat n := norm_natCast n

@[simp 1100] lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℂ)‖₊ = OfNat.ofNat n := nnnorm_natCast n

@[deprecated (since := "2024-08-25")] alias norm_nat := norm_natCast
@[deprecated (since := "2024-08-25")] alias norm_int := norm_intCast
@[deprecated (since := "2024-08-25")] alias norm_rat := norm_ratCast
@[deprecated (since := "2024-08-25")] alias nnnorm_nat := nnnorm_natCast

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖ = q := Complex.abs_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℂ)‖₊ = q := by simp [nnnorm, -norm_eq_abs]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by
  rw [norm_intCast, ← Int.cast_abs, abs_of_nonneg hn]

lemma normSq_eq_norm_sq (z : ℂ) : normSq z = ‖z‖ ^ 2 := by
  rw [normSq_eq_abs, norm_eq_abs]

end Complex
