/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `GaussianInt.toComplex` into the complex numbers is also defined in this file.

## See also

See `NumberTheory.Zsqrtd.QuadraticReciprocity` for:
* `prime_iff_mod_four_eq_three_of_nat_prime`:
  A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notation

This file uses the local notation `ℤ[i]` for `GaussianInt`

## Implementation notes

Gaussian integers are implemented using the more general definition `Zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `Zsqrtd` can easily be used.
-/


open Zsqrtd Complex

open scoped ComplexConjugate

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
abbrev GaussianInt : Type :=
  Zsqrtd (-1)

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

instance : Repr ℤ[i] :=
  ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance instCommRing : CommRing ℤ[i] :=
  Zsqrtd.commRing

section

attribute [-instance] Complex.instField -- Avoid making things noncomputable unnecessarily.

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift ⟨I, by simp⟩

end

instance : Coe ℤ[i] ℂ :=
  ⟨toComplex⟩

theorem toComplex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I :=
  rfl

theorem toComplex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [toComplex_def]

theorem toComplex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [toComplex_def]

@[simp]
theorem intCast_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [toComplex_def]

@[deprecated (since := "2025-08-31")] alias to_real_re := intCast_re

@[simp]
theorem intCast_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [toComplex_def]

@[deprecated (since := "2025-08-31")] alias to_real_im := intCast_im

@[simp]
theorem re_toComplex (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [toComplex_def]

@[deprecated (since := "2025-08-31")] alias toComplex_re := re_toComplex

@[simp]
theorem im_toComplex (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [toComplex_def]

@[deprecated (since := "2025-08-31")] alias toComplex_im := im_toComplex

theorem toComplex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y :=
  toComplex.map_add _ _

theorem toComplex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y :=
  toComplex.map_mul _ _

theorem toComplex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  toComplex.map_one

theorem toComplex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  toComplex.map_zero

theorem toComplex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  toComplex.map_neg _

theorem toComplex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  toComplex.map_sub _ _

@[simp]
theorem toComplex_star (x : ℤ[i]) : ((star x : ℤ[i]) : ℂ) = conj (x : ℂ) := by
  rw [toComplex_def₂, toComplex_def₂]
  exact congr_arg₂ _ rfl (Int.cast_neg _)

@[simp]
theorem toComplex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y := by
  cases x; cases y; simp [toComplex_def₂]

lemma toComplex_injective : Function.Injective GaussianInt.toComplex :=
  fun ⦃_ _⦄ ↦ toComplex_inj.mp

@[simp]
theorem toComplex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 := by
  rw [← toComplex_zero, toComplex_inj]

@[simp]
theorem intCast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = Complex.normSq (x : ℂ) := by
  rw [Zsqrtd.norm, normSq]; simp

@[simp]
theorem intCast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = Complex.normSq (x : ℂ) := by
  cases x; rw [Zsqrtd.norm, normSq]; simp

theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  Zsqrtd.norm_nonneg (by simp) _

@[simp]
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 := by rw [← @Int.cast_inj ℝ _ _ _]; simp

theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm, norm_eq_zero]; simp [norm_nonneg]

theorem abs_natCast_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natCast_natAbs_norm {α : Type*} [AddGroupWithOne α] (x : ℤ[i]) :
    (x.norm.natAbs : α) = x.norm := by
  simp

theorem natAbs_norm_eq (x : ℤ[i]) :
    x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs := by
  zify
  rw [abs_norm (by simp)]
  simp [Zsqrtd.norm]

instance : Div ℤ[i] :=
  ⟨fun x y =>
    let n := (norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

theorem div_def (x y : ℤ[i]) :
    x / y = ⟨round ((x * star y).re / norm y : ℚ), round ((x * star y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]

theorem toComplex_re_div (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re := by
  rw [div_def, ← @Rat.round_cast ℝ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

@[deprecated (since := "2025-08-31")] alias toComplex_div_re := toComplex_re_div

theorem toComplex_im_div (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im := by
  rw [div_def, ← @Rat.round_cast ℝ _ _, ← @Rat.round_cast ℝ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

@[deprecated (since := "2025-08-31")] alias toComplex_div_im := toComplex_im_div

theorem normSq_le_normSq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
    (him : |x.im| ≤ |y.im|) : Complex.normSq x ≤ Complex.normSq y := by
  rw [normSq_apply, normSq_apply, ← _root_.abs_mul_self, _root_.abs_mul, ←
      _root_.abs_mul_self y.re, _root_.abs_mul y.re, ← _root_.abs_mul_self x.im,
      _root_.abs_mul x.im, ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]
  gcongr

theorem normSq_div_sub_div_lt_one (x y : ℤ[i]) :
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)) < 1 :=
  calc
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ))
    _ = Complex.normSq
      ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re + ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) *
        I : ℂ) :=
      congr_arg _ <| by apply Complex.ext <;> simp
    _ ≤ Complex.normSq (1 / 2 + 1 / 2 * I) := by
      have : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_nonneg (by simp)
      exact normSq_le_normSq_of_re_le_of_im_le
        (by rw [toComplex_re_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).re)
        (by rw [toComplex_im_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 := by simp [normSq]; norm_num

instance : Mod ℤ[i] :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have : (y : ℂ) ≠ 0 := by rwa [Ne, ← toComplex_zero, toComplex_inj]
  (@Int.cast_lt ℝ _ _ _ _).1 <|
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : ℤ[i]) : ℂ) := by simp [mod_def]
      _ = Complex.normSq (y : ℂ) * Complex.normSq (x / y - (x / y : ℤ[i]) : ℂ) := by
        rw [← normSq_mul, mul_sub, mul_div_cancel₀ _ this]
      _ < Complex.normSq (y : ℂ) * 1 :=
        (mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one _ _) (normSq_pos.2 this))
      _ = Zsqrtd.norm y := by simp

theorem natAbs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 <| by simp [norm_mod_lt x hy]

theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))

instance instNontrivial : Nontrivial ℤ[i] :=
  ⟨⟨0, 1, by decide⟩⟩

instance : EuclideanDomain ℤ[i] :=
  { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ℤ[i])) : ∃ a b, a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2 <| by
      rw [norm_natCast, Int.natAbs_mul, mul_eq_one]
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.natCast_inj, Int.natCast_pow, sq, ← @norm_natCast (-1), hpab]; simp).1
  ⟨a.re.natAbs, a.im.natAbs, by simpa [natAbs_norm_eq, sq] using hnap⟩

end GaussianInt
