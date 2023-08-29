/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import number_theory.zsqrtd.gaussian_int from "leanprover-community/mathlib"@"5b2fe80501ff327b9109fb09b7cc8c325cd0d7d9"

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

## Notations

This file uses the local notation `ℤ[i]` for `GaussianInt`

## Implementation notes

Gaussian integers are implemented using the more general definition `Zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `Zsqrtd` can easily be used.
-/


open Zsqrtd Complex

open scoped ComplexConjugate

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
@[reducible]
def GaussianInt : Type :=
  Zsqrtd (-1)
#align gaussian_int GaussianInt

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

instance : Repr ℤ[i] :=
  ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance instCommRing : CommRing ℤ[i] :=
  Zsqrtd.commRing
#align gaussian_int.comm_ring GaussianInt.instCommRing

section

attribute [-instance] Complex.instField -- Avoid making things noncomputable unnecessarily.

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift ⟨I, by simp⟩
                     -- 🎉 no goals
#align gaussian_int.to_complex GaussianInt.toComplex

end

instance : Coe ℤ[i] ℂ :=
  ⟨toComplex⟩

theorem toComplex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I :=
  rfl
#align gaussian_int.to_complex_def GaussianInt.toComplex_def

theorem toComplex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [toComplex_def]
                                                                           -- 🎉 no goals
#align gaussian_int.to_complex_def' GaussianInt.toComplex_def'

theorem toComplex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [toComplex_def]
  -- ⊢ (↑toComplex x).re = { re := ↑x.re, im := ↑x.im }.re
                        -- 🎉 no goals
                        -- 🎉 no goals
#align gaussian_int.to_complex_def₂ GaussianInt.toComplex_def₂

@[simp]
theorem to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [toComplex_def]
                                                                    -- 🎉 no goals
#align gaussian_int.to_real_re GaussianInt.to_real_re

@[simp]
theorem to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [toComplex_def]
                                                                    -- 🎉 no goals
#align gaussian_int.to_real_im GaussianInt.to_real_im

@[simp]
theorem toComplex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [toComplex_def]
                                                                    -- 🎉 no goals
#align gaussian_int.to_complex_re GaussianInt.toComplex_re

@[simp]
theorem toComplex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [toComplex_def]
                                                                    -- 🎉 no goals
#align gaussian_int.to_complex_im GaussianInt.toComplex_im

-- Porting note: @[simp] can prove this
theorem toComplex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y :=
  toComplex.map_add _ _
#align gaussian_int.to_complex_add GaussianInt.toComplex_add

-- Porting note: @[simp] can prove this
theorem toComplex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y :=
  toComplex.map_mul _ _
#align gaussian_int.to_complex_mul GaussianInt.toComplex_mul

-- Porting note: @[simp] can prove this
theorem toComplex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  toComplex.map_one
#align gaussian_int.to_complex_one GaussianInt.toComplex_one

-- Porting note: @[simp] can prove this
theorem toComplex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  toComplex.map_zero
#align gaussian_int.to_complex_zero GaussianInt.toComplex_zero

-- Porting note: @[simp] can prove this
theorem toComplex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  toComplex.map_neg _
#align gaussian_int.to_complex_neg GaussianInt.toComplex_neg

-- Porting note: @[simp] can prove this
theorem toComplex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  toComplex.map_sub _ _
#align gaussian_int.to_complex_sub GaussianInt.toComplex_sub

@[simp]
theorem toComplex_star (x : ℤ[i]) : ((star x : ℤ[i]) : ℂ) = conj (x : ℂ) := by
  rw [toComplex_def₂, toComplex_def₂]
  -- ⊢ { re := ↑(star x).re, im := ↑(star x).im } = ↑(starRingEnd ((fun x => ℂ) x)) …
  exact congr_arg₂ _ rfl (Int.cast_neg _)
  -- 🎉 no goals
#align gaussian_int.to_complex_star GaussianInt.toComplex_star

@[simp]
theorem toComplex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y := by
  cases x; cases y; simp [toComplex_def₂]
  -- ⊢ ↑toComplex { re := re✝, im := im✝ } = ↑toComplex y ↔ { re := re✝, im := im✝  …
           -- ⊢ ↑toComplex { re := re✝¹, im := im✝¹ } = ↑toComplex { re := re✝, im := im✝ }  …
                    -- 🎉 no goals
#align gaussian_int.to_complex_inj GaussianInt.toComplex_inj

@[simp]
theorem toComplex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 := by
  rw [← toComplex_zero, toComplex_inj]
  -- 🎉 no goals
#align gaussian_int.to_complex_eq_zero GaussianInt.toComplex_eq_zero

@[simp]
theorem int_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = Complex.normSq (x : ℂ) := by
  rw [Zsqrtd.norm, normSq]; simp
  -- ⊢ ↑(x.re * x.re - -1 * x.im * x.im) = ↑{ toZeroHom := { toFun := fun z => z.re …
                            -- 🎉 no goals
#align gaussian_int.nat_cast_real_norm GaussianInt.int_cast_real_norm

@[simp]
theorem int_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = Complex.normSq (x : ℂ) := by
  cases x; rw [Zsqrtd.norm, normSq]; simp
  -- ⊢ ↑(norm { re := re✝, im := im✝ }) = ↑(↑normSq (↑toComplex { re := re✝, im :=  …
           -- ⊢ ↑({ re := re✝, im := im✝ }.re * { re := re✝, im := im✝ }.re - -1 * { re := r …
                                     -- 🎉 no goals
#align gaussian_int.nat_cast_complex_norm GaussianInt.int_cast_complex_norm

theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  Zsqrtd.norm_nonneg (by norm_num) _
                         -- 🎉 no goals
#align gaussian_int.norm_nonneg GaussianInt.norm_nonneg

@[simp]
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 := by rw [← @Int.cast_inj ℝ _ _ _]; simp
                                                           -- ⊢ ↑(norm x) = ↑0 ↔ x = 0
                                                                                         -- 🎉 no goals
#align gaussian_int.norm_eq_zero GaussianInt.norm_eq_zero

theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne.def, eq_comm, norm_eq_zero]; simp [norm_nonneg]
  -- ⊢ 0 ≤ norm x ∧ ¬x = 0 ↔ x ≠ 0
                                                        -- 🎉 no goals
#align gaussian_int.norm_pos GaussianInt.norm_pos

theorem abs_coe_nat_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)
#align gaussian_int.abs_coe_nat_norm GaussianInt.abs_coe_nat_norm

@[simp]
theorem nat_cast_natAbs_norm {α : Type*} [Ring α] (x : ℤ[i]) : (x.norm.natAbs : α) = x.norm := by
  rw [← Int.cast_ofNat, abs_coe_nat_norm]
  -- 🎉 no goals
#align gaussian_int.nat_cast_nat_abs_norm GaussianInt.nat_cast_natAbs_norm

theorem natAbs_norm_eq (x : ℤ[i]) :
    x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs :=
  Int.ofNat.inj <| by simp; simp [Zsqrtd.norm]
                      -- ⊢ norm x = x.re * x.re + x.im * x.im
                            -- 🎉 no goals
#align gaussian_int.nat_abs_norm_eq GaussianInt.natAbs_norm_eq

instance : Div ℤ[i] :=
  ⟨fun x y =>
    let n := (norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

theorem div_def (x y : ℤ[i]) :
    x / y = ⟨round ((x * star y).re / norm y : ℚ), round ((x * star y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]
                            -- 🎉 no goals
#align gaussian_int.div_def GaussianInt.div_def

theorem toComplex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re := by
  rw [div_def, ← @Rat.round_cast ℝ _ _]
  -- ⊢ (↑toComplex { re := round ↑(↑(x * star y).re / ↑(norm y)), im := round (↑(x  …
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]
  -- 🎉 no goals
#align gaussian_int.to_complex_div_re GaussianInt.toComplex_div_re

theorem toComplex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im := by
  rw [div_def, ← @Rat.round_cast ℝ _ _, ← @Rat.round_cast ℝ _ _]
  -- ⊢ (↑toComplex { re := round ↑(↑(x * star y).re / ↑(norm y)), im := round ↑(↑(x …
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]
  -- 🎉 no goals
#align gaussian_int.to_complex_div_im GaussianInt.toComplex_div_im

theorem normSq_le_normSq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
    (him : |x.im| ≤ |y.im|) : Complex.normSq x ≤ Complex.normSq y := by
  rw [normSq_apply, normSq_apply, ← _root_.abs_mul_self, _root_.abs_mul, ←
      _root_.abs_mul_self y.re, _root_.abs_mul y.re, ← _root_.abs_mul_self x.im,
      _root_.abs_mul x.im, ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]
  exact
      add_le_add (mul_self_le_mul_self (abs_nonneg _) hre) (mul_self_le_mul_self (abs_nonneg _) him)
#align gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le GaussianInt.normSq_le_normSq_of_re_le_of_im_le

theorem normSq_div_sub_div_lt_one (x y : ℤ[i]) :
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)) < 1 :=
  calc
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ))
    _ = Complex.normSq
      ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re + ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) *
        I : ℂ) :=
      congr_arg _ <| by apply Complex.ext <;> simp
                        -- ⊢ (↑toComplex x / ↑toComplex y - ↑toComplex (x / y)).re = (↑(↑toComplex x / ↑t …
                                              -- 🎉 no goals
                                              -- 🎉 no goals
    _ ≤ Complex.normSq (1 / 2 + 1 / 2 * I) := by
      have : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_nonneg (by norm_num)
      -- ⊢ ↑normSq (↑(↑toComplex x / ↑toComplex y).re - ↑(↑toComplex (x / y)).re + (↑(↑ …
      exact normSq_le_normSq_of_re_le_of_im_le
        (by rw [toComplex_div_re]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).re)
        (by rw [toComplex_div_im]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 := by simp [normSq]; norm_num
                -- ⊢ 2⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ < 1
                               -- 🎉 no goals
#align gaussian_int.norm_sq_div_sub_div_lt_one GaussianInt.normSq_div_sub_div_lt_one

instance : Mod ℤ[i] :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) :=
  rfl
#align gaussian_int.mod_def GaussianInt.mod_def

theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have : (y : ℂ) ≠ 0 := by rwa [Ne.def, ← toComplex_zero, toComplex_inj]
                           -- 🎉 no goals
  (@Int.cast_lt ℝ _ _ _ _).1 <|
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : ℤ[i]) : ℂ) := by simp [mod_def]
                                                                                 -- 🎉 no goals
      _ = Complex.normSq (y : ℂ) * Complex.normSq (x / y - (x / y : ℤ[i]) : ℂ) := by
        rw [← normSq_mul, mul_sub, mul_div_cancel' _ this]
        -- 🎉 no goals
      _ < Complex.normSq (y : ℂ) * 1 :=
        (mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one _ _) (normSq_pos.2 this))
      _ = Zsqrtd.norm y := by simp
                              -- 🎉 no goals
#align gaussian_int.norm_mod_lt GaussianInt.norm_mod_lt

theorem natAbs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 (by simp [-Int.ofNat_lt, norm_mod_lt x hy])
                     -- 🎉 no goals
#align gaussian_int.nat_abs_norm_mod_lt GaussianInt.natAbs_norm_mod_lt

theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  -- ⊢ Int.natAbs (norm x) ≤ Int.natAbs (norm x) * Int.natAbs (norm y)
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_coe_nat_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))
#align gaussian_int.norm_le_norm_mul_left GaussianInt.norm_le_norm_mul_left

instance instNontrivial : Nontrivial ℤ[i] :=
  ⟨⟨0, 1, by decide⟩⟩
             -- 🎉 no goals
#align gaussian_int.nontrivial GaussianInt.instNontrivial

instance : EuclideanDomain ℤ[i] :=
  { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
                        -- ⊢ { re := 0, im := 0 } = 0
                                        -- 🎉 no goals
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
                                                   -- 🎉 no goals
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ℤ[i])) : ∃ a b, a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2 <| by
      rw [norm_nat_cast, Int.natAbs_mul, mul_eq_one]
      -- ⊢ ¬(Int.natAbs ↑p = 1 ∧ Int.natAbs ↑p = 1)
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
      -- 🎉 no goals
  have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    -- Porting note: was
    -- simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
    simpa only [true_and, not_false_iff, exists_prop, irreducible_iff, hpu, not_forall, not_or]
      using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.coe_nat_inj', Int.coe_nat_pow, sq, ← @norm_nat_cast (-1), hpab]; simp).1
        -- ⊢ ↑(Int.natAbs (norm a) * Int.natAbs (norm b)) = norm (a * b)
                                                                                   -- 🎉 no goals
  ⟨a.re.natAbs, a.im.natAbs, by simpa [natAbs_norm_eq, sq] using hnap⟩
                                -- 🎉 no goals
#align gaussian_int.sq_add_sq_of_nat_prime_of_not_irreducible GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible

end GaussianInt
