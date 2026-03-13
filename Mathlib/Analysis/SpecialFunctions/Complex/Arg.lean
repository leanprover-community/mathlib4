/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returning a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

@[expose] public section

open Filter Metric Set
open scoped ComplexConjugate Real Topology

namespace Complex
variable {a x z : ℂ}

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π

theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / ‖x‖ := by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]

theorem cos_arg {x : ℂ} (hx : x ≠ 0) : Real.cos (arg x) = x.re / ‖x‖ := by
  rw [arg]
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_sq, (norm_pos_iff.mpr hx).le, *]
    field
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field

@[simp]
theorem norm_mul_exp_arg_mul_I (x : ℂ) : ‖x‖ * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

@[simp]
theorem norm_mul_cos_add_sin_mul_I (x : ℂ) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : ℂ) = x := by
  rw [← exp_mul_I, norm_mul_exp_arg_mul_I]

@[simp]
lemma norm_mul_cos_arg (x : ℂ) : ‖x‖ * Real.cos (arg x) = x.re := by
  simpa [-norm_mul_cos_add_sin_mul_I] using congr_arg re (norm_mul_cos_add_sin_mul_I x)

@[simp]
lemma norm_mul_sin_arg (x : ℂ) : ‖x‖ * Real.sin (arg x) = x.im := by
  simpa [-norm_mul_cos_add_sin_mul_I] using congr_arg im (norm_mul_cos_add_sin_mul_I x)

theorem norm_eq_one_iff (z : ℂ) : ‖z‖ = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z := by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem range_exp_mul_I : (Set.range fun x : ℝ => exp (x * I)) = Metric.sphere 0 1 := by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_one_iff, Set.mem_range]

theorem arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ := by
  simp only [arg, norm_mul, norm_cos_add_sin_mul_I, Complex.norm_of_nonneg hr.le, mul_one]
  simp only [re_ofReal_mul, im_ofReal_mul, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left₀ _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ ∈ Set.Icc (-(π / 2)) (π / 2)
  · rw [if_pos]
    exacts [Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h₁
    rcases h₁ with h₁ | h₁
    · replace hθ := hθ.1
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos, ← Real.cos_add_pi]
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
      have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ
      rw [if_neg, if_neg, ← Real.sin_add_pi, Real.arcsin_sin, add_sub_cancel_right] <;> [linarith;
        linarith; exact hsin.not_ge; exact hcos.not_ge]
    · replace hθ := hθ.2
      have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith)
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩
      rw [if_neg, if_pos, ← Real.sin_sub_pi, Real.arcsin_sin, sub_add_cancel] <;> [linarith;
        linarith; exact hsin; exact hcos.not_ge]

theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

theorem arg_exp (z : ℂ) : arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im := by
  convert arg_mul_cos_add_sin_mul_I (Real.exp_pos z.re)
    (θ := toIocMod Real.two_pi_pos (-π) z.im) _ using 1
  · rw [← exp_mul_I, ofReal_exp, toIocMod]
    push_cast
    rw [exp_mul_I_periodic.sub_zsmul_eq, ← exp_add, re_add_im]
  · convert toIocMod_mem_Ioc ..
    ring

lemma arg_exp_mul_I (θ : ℝ) :
    arg (exp (θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  simp [arg_exp]

@[simp]
theorem arg_zero : arg 0 = 0 := by simp [arg]

theorem ext_norm_arg {x y : ℂ} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg) : x = y := by
  rw [← norm_mul_exp_arg_mul_I x, ← norm_mul_exp_arg_mul_I y, h₁, h₂]

theorem ext_norm_arg_iff {x y : ℂ} : x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_norm_arg⟩

theorem arg_mem_Ioc (z : ℂ) : arg z ∈ Set.Ioc (-π) π := by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul, neg_add_cancel_left, ← two_mul, zsmul_eq_mul] at hN
  rw [← norm_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N, ← sin_add_int_mul_two_pi _ N]
  have := arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hz) hN
  push_cast at this
  rwa [this]

@[simp]
theorem toIocMod_arg (z : ℂ) : toIocMod Real.two_pi_pos (-π) z.arg = z.arg := by
  simpa [toIocMod_eq_self, two_mul] using z.arg_mem_Ioc

@[simp]
theorem range_arg : Set.range arg = Set.Ioc (-π) π :=
  (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2

theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1

theorem abs_arg_le_pi (z : ℂ) : |arg z| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩

@[simp]
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im := by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_div_iff₀ (norm_pos_iff.mpr h₀), zero_mul]

@[simp]
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff

theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x := by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  conv_lhs =>
    rw [← norm_mul_cos_add_sin_mul_I x, ← mul_assoc, ← ofReal_mul,
      arg_mul_cos_add_sin_mul_I (mul_pos hr (norm_pos_iff.mpr hx)) x.arg_mem_Ioc]

theorem arg_mul_real {r : ℝ} (hr : 0 < r) (x : ℂ) : arg (x * r) = arg x :=
  mul_comm x r ▸ arg_real_mul x hr

theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    arg x = arg y ↔ (‖y‖ / ‖x‖ : ℂ) * x = y := by
  simp only [ext_norm_arg_iff, norm_mul, norm_div, norm_real, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), true_and]
  rw [← ofReal_div, arg_real_mul]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)

@[simp] lemma arg_one : arg 1 = 0 := by simp [arg, zero_le_one]

/-- This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `arg 0 = 0`. -/
@[simp] lemma arg_div_self (x : ℂ) : arg (x / x) = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp]
theorem arg_neg_one : arg (-1) = π := by simp [arg]

@[simp]
theorem arg_I : arg I = π / 2 := by simp [arg]

@[simp]
theorem arg_neg_I : arg (-I) = -(π / 2) := by simp [arg]

@[simp]
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re := by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
    div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

theorem arg_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 := by simp [arg, hx]

@[simp, norm_cast]
lemma natCast_arg {n : ℕ} : arg n = 0 :=
  ofReal_natCast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

@[simp]
lemma ofNat_arg {n : ℕ} [n.AtLeastTwo] : arg ofNat(n) = 0 :=
  natCast_arg

theorem arg_eq_zero_iff {z : ℂ} : arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [norm_nonneg]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h, rfl : y = 0⟩
    exact arg_ofReal_of_nonneg h

open ComplexOrder in
lemma arg_eq_zero_iff_zero_le {z : ℂ} : arg z = 0 ↔ 0 ≤ z := by
  rw [arg_eq_zero_iff, eq_comm, nonneg_iff]

theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 := by
  by_cases h₀ : z = 0
  · simp [h₀, Real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← ofReal_def]

open ComplexOrder in
lemma arg_eq_pi_iff_lt_zero {z : ℂ} : arg z = π ↔ z < 0 := arg_eq_pi_iff

theorem arg_lt_pi_iff {z : ℂ} : arg z < π ↔ 0 ≤ z.re ∨ z.im ≠ 0 := by
  rw [(arg_le_pi z).lt_iff_ne, not_iff_comm, not_or, not_le, Classical.not_not, arg_eq_pi_iff]

theorem arg_ofReal_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩

theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I, ← arg_real_mul I hy, ofReal_mul', I_re, I_im, mul_zero, mul_one]

theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
    simp

theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / ‖x‖) :=
  if_pos hx

theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
    arg x = Real.arcsin ((-x).im / ‖x‖) + π := by
  simp only [arg, hx_re.not_ge, hx_im, if_true, if_false]

theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / ‖x‖) - π := by
  simp only [arg, hx_re.not_ge, hx_im.not_ge, if_false]

theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) :
    arg z = Real.arccos (z.re / ‖z‖) := by
  rw [← cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / ‖z‖) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' <| h.symm ▸ rfl

theorem arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -Real.arccos (z.re / ‖z‖) := by
  have h₀ : z ≠ 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀, ← Real.cos_neg, Real.arccos_cos, neg_neg]
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]

theorem arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x := by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, norm_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_ge, hi.le, hi.ne, not_le.2 hi, add_comm]
  · simp [hr, hr.not_ge, hi]
  · simp [hr, hr.not_ge, hi.ne.symm, hi.le, not_le.2 hi, sub_eq_neg_add]
  · simp [hr]
  · simp [hr]
  · simp [hr]
  · simp [hr.le, hi.ne]
  · simp [hr.le, hr.le.not_gt]
  · simp [hr.le, hr.le.not_gt]

theorem arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x := by
  rw [← arg_conj, inv_def, mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])

@[simp] lemma abs_arg_inv (x : ℂ) : |x⁻¹.arg| = |x.arg| := by rw [arg_inv]; split_ifs <;> simp [*]

-- TODO: Replace the next two lemmas by general facts about periodic functions
lemma norm_eq_one_iff' : ‖x‖ = 1 ↔ ∃ θ ∈ Set.Ioc (-π) π, exp (θ * I) = x := by
  rw [norm_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq <| toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, exp_mul_I_periodic.sub_zsmul_eq]
  · rintro ⟨θ, _, rfl⟩
    exact ⟨θ, rfl⟩

lemma image_exp_Ioc_eq_sphere : (fun θ : ℝ ↦ exp (θ * I)) '' Set.Ioc (-π) π = sphere 0 1 := by
  ext; simpa using norm_eq_one_iff'.symm

theorem arg_le_pi_div_two_iff {z : ℂ} : arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0 := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him.not_gt]
    rw [iff_false, not_le, arg_of_re_neg_of_im_nonneg hre him, ← sub_lt_iff_lt_add, half_sub,
      Real.neg_pi_div_two_lt_arcsin, neg_im, neg_div, neg_lt_neg_iff, div_lt_one, ←
      abs_of_nonneg him, abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]
  · simp only [him]
    rw [iff_true, arg_of_re_neg_of_im_neg hre him]
    exact (sub_le_self _ Real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)

theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true, arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right Real.pi_pos.le)
  · simp only [him.not_ge]
    rw [iff_false, not_le, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ←
      sub_eq_add_neg, sub_half, Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him,
      abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]

lemma neg_pi_div_two_lt_arg_iff {z : ℂ} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 ≤ im z := by
  rw [lt_iff_le_and_ne, neg_pi_div_two_le_arg_iff, ne_comm, Ne, arg_eq_neg_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · simp [hre.ne, hre.not_ge, hre.not_gt]
  · simp [hre]
  · simp [hre, hre.le, hre.ne']

lemma arg_lt_pi_div_two_iff {z : ℂ} : arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0 := by
  rw [lt_iff_le_and_ne, arg_le_pi_div_two_iff, Ne, arg_eq_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · have : z ≠ 0 := by simp [Complex.ext_iff, hre.ne]
    simp [hre.ne, hre.not_ge, hre.not_gt, this]
  · have : z = 0 ↔ z.im = 0 := by simp [Complex.ext_iff, hre]
    simp [hre, this, or_comm, le_iff_eq_or_lt]
  · simp [hre, hre.le, hre.ne']

@[simp]
theorem abs_arg_le_pi_div_two_iff {z : ℂ} : |arg z| ≤ π / 2 ↔ 0 ≤ re z := by
  rw [abs_le, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, ← or_and_left, ← not_le,
    and_not_self_iff, or_false]

@[simp]
theorem abs_arg_lt_pi_div_two_iff {z : ℂ} : |arg z| < π / 2 ↔ 0 < re z ∨ z = 0 := by
  rw [abs_lt, arg_lt_pi_div_two_iff, neg_pi_div_two_lt_arg_iff, ← or_and_left]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · simp_rw [hz, or_false, ← not_lt, not_and_self_iff, or_false]

@[simp]
theorem arg_conj_coe_angle (x : ℂ) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_conj, h]

@[simp]
theorem arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_inv, h]

theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π := by
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]

theorem arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π := by
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]

theorem arg_neg_eq_arg_sub_pi_iff {x : ℂ} :
    arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_gt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr]
    · simp [hr, Real.pi_ne_zero]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr.not_gt, ← add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos]

theorem arg_neg_eq_arg_add_pi_iff {x : ℂ} :
    arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_gt, ← two_mul, Real.pi_ne_zero]
    · simp [hr, Real.pi_ne_zero.symm]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr]
  · simp [hi, hi.ne.symm, hi.not_gt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg, ←
      add_eq_zero_iff_neg_eq, Real.pi_ne_zero]

theorem arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : Real.Angle) = arg x + π := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
        Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
    · exact False.elim (hx (ext hr hi))
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr),
        Real.Angle.coe_zero, zero_add]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]

theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [arg_real_mul _ hr, ← exp_mul_I, arg_exp_mul_I]

theorem arg_cos_add_sin_mul_I_eq_toIocMod (θ : ℝ) :
    arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]

theorem arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr, toIocMod_sub_self, toIocDiv_eq_neg_floor,
    zsmul_eq_mul]
  ring_nf

theorem arg_cos_add_sin_mul_I_sub (θ : ℝ) :
    arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on with | _ θ
  simp [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]

theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

theorem arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x * y) : Real.Angle) = arg x + arg y := by
  convert arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (arg x + arg y : Real.Angle) using 3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofReal_mul]
  rw [mul_assoc, mul_comm (exp _), ← mul_assoc (‖y‖ : ℂ), norm_mul_exp_arg_mul_I, mul_comm y, ←
    mul_assoc, norm_mul_exp_arg_mul_I]

theorem arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]

theorem arg_pow_coe_angle (x : ℂ) (n : ℕ) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  obtain rfl | x0 := eq_or_ne x 0
  · by_cases n0 : n = 0 <;> simp [n0]
  · induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]

theorem arg_zpow_coe_angle (x : ℂ) (n : ℤ) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  match n with
  | Int.ofNat m => simp [arg_pow_coe_angle]
  | Int.negSucc m => simp [arg_pow_coe_angle]

@[simp]
theorem arg_coe_angle_toReal_eq_arg (z : ℂ) : (arg z : Real.Angle).toReal = arg z := by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _

theorem arg_coe_angle_eq_iff_eq_toReal {z : ℂ} {θ : Real.Angle} :
    (arg z : Real.Angle) = θ ↔ arg z = θ.toReal := by
  rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

@[simp]
theorem arg_coe_angle_eq_iff {x y : ℂ} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

lemma arg_mul_eq_add_arg_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    (x * y).arg = x.arg + y.arg ↔ arg x + arg y ∈ Set.Ioc (-π) π := by
  rw [← arg_coe_angle_toReal_eq_arg, arg_mul_coe_angle hx₀ hy₀, ← Real.Angle.coe_add,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

alias ⟨_, arg_mul⟩ := arg_mul_eq_add_arg_iff

section slitPlane

open ComplexOrder in
/-- An alternative description of the slit plane as consisting of nonzero complex numbers
whose argument is not π. -/
lemma mem_slitPlane_iff_arg {z : ℂ} : z ∈ slitPlane ↔ z.arg ≠ π ∧ z ≠ 0 := by
  simp only [mem_slitPlane_iff_not_le_zero, le_iff_lt_or_eq, ne_eq, arg_eq_pi_iff_lt_zero, not_or]

lemma slitPlane_arg_ne_pi {z : ℂ} (hz : z ∈ slitPlane) : z.arg ≠ Real.pi :=
  (mem_slitPlane_iff_arg.mp hz).1

theorem exp_mem_slitPlane {z : ℂ} : exp z ∈ slitPlane ↔ toIocMod Real.two_pi_pos (-π) z.im ≠ π := by
  simp [mem_slitPlane_iff_arg, arg_exp]

end slitPlane

section Continuity

theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / ‖x‖) :=
  ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le

theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_zero continuous_im)

theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) - π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0 from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_im continuous_zero)

theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos

theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg

theorem continuousAt_arg (h : x ∈ slitPlane) : ContinuousAt arg x := by
  have h₀ : ‖x‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact slitPlane_ne_zero h
  rw [mem_slitPlane_iff, ← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (Real.continuous_arccos.continuousAt.comp
            (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (Real.continuous_arccos.continuousAt.comp
          (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]

@[fun_prop]
theorem continuousOn_arg : ContinuousOn arg slitPlane :=
  fun _ h ↦ continuousAt_arg h |>.continuousWithinAt

theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) := by
  suffices H : Tendsto (fun x : ℂ => Real.arcsin ((-x).im / ‖x‖) - π)
      (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) by
    refine H.congr' ?_
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_ge, if_neg him.not_ge]
  convert (Real.continuousAt_arcsin.comp_continuousWithinAt
    ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
      continuous_norm.continuousWithinAt _)).sub_const π using 1
  · simp [him]
  · lift z to ℝ using him
    simpa using hre.ne

theorem continuousWithinAt_arg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : ℂ | 0 ≤ z.im } z := by
  have : arg =ᶠ[𝓝[{ z : ℂ | 0 ≤ z.im }] z] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : ℂ | 0 ≤ z.im }),
      mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_ge, if_pos him]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ this ?_
  · refine
      (Real.continuousAt_arcsin.comp_continuousWithinAt
            ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
              continuous_norm.continuousWithinAt ?_)).add
        tendsto_const_nhds
    lift z to ℝ using him
    simpa using hre.ne
  · rw [arg, if_neg hre.not_ge, if_pos him.ge]

theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 π) := by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto

theorem continuousAt_arg_coe_angle (h : x ≠ 0) : ContinuousAt ((↑) ∘ arg : ℂ → Real.Angle) x := by
  by_cases hs : x ∈ slitPlane
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
  · rw [← Function.comp_id (((↑) : ℝ → Real.Angle) ∘ arg),
      (funext_iff.2 fun _ => (neg_neg _).symm : (id : ℂ → ℂ) = Neg.neg ∘ Neg.neg), ←
      Function.comp_assoc]
    refine ContinuousAt.comp ?_ continuous_neg.continuousAt
    suffices ContinuousAt (Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π) (-x) by
      rwa [continuousAt_update_of_ne (neg_ne_zero.2 h)] at this
    have ha :
      Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π = fun z =>
        (arg z : Real.Angle) + π := by
      rw [Function.update_eq_iff]
      exact ⟨by simp, fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    replace hs := mem_slitPlane_iff.mpr.mt hs
    push Not at hs
    refine
      (Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg (Or.inl ?_))).add
        continuousAt_const
    rw [neg_re, neg_pos]
    exact hs.1.lt_of_ne fun h0 => h (Complex.ext_iff.2 ⟨h0, hs.2⟩)

end Continuity

end Complex
