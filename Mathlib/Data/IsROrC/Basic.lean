/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap

#align_import data.is_R_or_C.basic from "leanprover-community/mathlib"@"baa88307f3e699fa7054ef04ec79fa4f056169cb"

/-!
# `IsROrC`: a typeclass for ℝ or ℂ

This file defines the typeclass `IsROrC` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Applications include defining inner products and Hilbert spaces for both the real and
complex case. One typically produces the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `Mathlib/Analysis/Complex/Basic.lean`.

## Implementation notes

The coercion from reals into an `IsROrC` field is done by registering `IsROrC.ofReal` as
a `CoeTC`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `Coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `Mathlib/Data/Nat/Cast/Defs.lean`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `Mathlib/Analysis/Complex/Basic.lean` (which causes linter errors).

A few lemmas requiring heavier imports are in `Mathlib/Data/IsROrC/Lemmas.lean`.
-/

set_option autoImplicit true


open BigOperators

section

local notation "𝓚" => algebraMap ℝ _

open ComplexConjugate

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class IsROrC (K : semiOutParam (Type*)) extends DenselyNormedField K, StarRing K,
    NormedAlgebra ℝ K, CompleteSpace K where
  re : K →+ ℝ
  im : K →+ ℝ
  /-- Imaginary unit in `K`. Meant to be set to `0` for `K = ℝ`. -/
  I : K
  I_re_ax : re I = 0
  I_mul_I_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : ∀ z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
  ofReal_re_ax : ∀ r : ℝ, re (𝓚 r) = r
  ofReal_im_ax : ∀ r : ℝ, im (𝓚 r) = 0
  mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w
  mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w
  conj_re_ax : ∀ z : K, re (conj z) = re z
  conj_im_ax : ∀ z : K, im (conj z) = -im z
  conj_I_ax : conj I = -I
  norm_sq_eq_def_ax : ∀ z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
  mul_im_I_ax : ∀ z : K, im z * im I = im z
  /-- only an instance in the `ComplexOrder` locale -/
  [toPartialOrder : PartialOrder K]
  le_iff_re_im : z ≤ w ↔ re z ≤ re w ∧ im z = im w
#align is_R_or_C IsROrC

scoped[ComplexOrder] attribute [instance 100] IsROrC.toPartialOrder

end

variable {K E : Type*} [IsROrC K]

namespace IsROrC

open ComplexConjugate

/-- Coercion from `ℝ` to an `IsROrC` field. -/
@[coe] abbrev ofReal : ℝ → K := Algebra.cast

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `Mathlib/Data/Nat/Cast/Basic.lean` for more details. -/
noncomputable instance (priority := 900) algebraMapCoe : CoeTC ℝ K :=
  ⟨ofReal⟩
#align is_R_or_C.algebra_map_coe IsROrC.algebraMapCoe

theorem ofReal_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x
#align is_R_or_C.of_real_alg IsROrC.ofReal_alg

theorem real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z
#align is_R_or_C.real_smul_eq_coe_mul IsROrC.real_smul_eq_coe_mul

theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [IsROrC.ofReal_alg, smul_one_smul]
                                                -- 🎉 no goals
#align is_R_or_C.real_smul_eq_coe_smul IsROrC.real_smul_eq_coe_smul

theorem algebraMap_eq_ofReal : ⇑(algebraMap ℝ K) = ofReal :=
  rfl
#align is_R_or_C.algebra_map_eq_of_real IsROrC.algebraMap_eq_ofReal

@[simp, isROrC_simps]
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  IsROrC.re_add_im_ax z
#align is_R_or_C.re_add_im IsROrC.re_add_im

@[simp, norm_cast, isROrC_simps]
theorem ofReal_re : ∀ r : ℝ, re (r : K) = r :=
  IsROrC.ofReal_re_ax
#align is_R_or_C.of_real_re IsROrC.ofReal_re

@[simp, norm_cast, isROrC_simps]
theorem ofReal_im : ∀ r : ℝ, im (r : K) = 0 :=
  IsROrC.ofReal_im_ax
#align is_R_or_C.of_real_im IsROrC.ofReal_im

@[simp, isROrC_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  IsROrC.mul_re_ax
#align is_R_or_C.mul_re IsROrC.mul_re

@[simp, isROrC_simps]
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  IsROrC.mul_im_ax
#align is_R_or_C.mul_im IsROrC.mul_im

theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩
#align is_R_or_C.ext_iff IsROrC.ext_iff

theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩
#align is_R_or_C.ext IsROrC.ext

@[norm_cast]
theorem ofReal_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero
#align is_R_or_C.of_real_zero IsROrC.ofReal_zero

@[isROrC_simps]
theorem zero_re' : re (0 : K) = (0 : ℝ) :=
  map_zero re
#align is_R_or_C.zero_re' IsROrC.zero_re'

@[norm_cast]
theorem ofReal_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)
#align is_R_or_C.of_real_one IsROrC.ofReal_one

@[simp, isROrC_simps]
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]
                                      -- 🎉 no goals
#align is_R_or_C.one_re IsROrC.one_re

@[simp, isROrC_simps]
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]
                                      -- 🎉 no goals
#align is_R_or_C.one_im IsROrC.one_im

theorem ofReal_injective : Function.Injective ((↑) : ℝ → K) :=
  (algebraMap ℝ K).injective
#align is_R_or_C.of_real_injective IsROrC.ofReal_injective

@[norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj
#align is_R_or_C.of_real_inj IsROrC.ofReal_inj

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem bit0_re (z : K) : re (bit0 z) = bit0 (re z) :=
  map_bit0 _ _
#align is_R_or_C.bit0_re IsROrC.bit0_re

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps]
theorem bit1_re (z : K) : re (bit1 z) = bit1 (re z) := by simp only [bit1, map_add, bit0_re, one_re]
                                                          -- 🎉 no goals
#align is_R_or_C.bit1_re IsROrC.bit1_re

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem bit0_im (z : K) : im (bit0 z) = bit0 (im z) :=
  map_bit0 _ _
#align is_R_or_C.bit0_im IsROrC.bit0_im

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps]
theorem bit1_im (z : K) : im (bit1 z) = bit0 (im z) := by
  simp only [bit1, map_add, bit0_im, one_im, add_zero]
  -- 🎉 no goals
#align is_R_or_C.bit1_im IsROrC.bit1_im

theorem ofReal_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.lift_map_eq_zero_iff x
#align is_R_or_C.of_real_eq_zero IsROrC.ofReal_eq_zero

theorem ofReal_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  ofReal_eq_zero.not
#align is_R_or_C.of_real_ne_zero IsROrC.ofReal_ne_zero

@[simp, isROrC_simps, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _
#align is_R_or_C.of_real_add IsROrC.ofReal_add

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps, norm_cast]
theorem ofReal_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) :=
  ofReal_add _ _
#align is_R_or_C.of_real_bit0 IsROrC.ofReal_bit0

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps, norm_cast]
theorem ofReal_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
  map_bit1 (algebraMap ℝ K) r
#align is_R_or_C.of_real_bit1 IsROrC.ofReal_bit1

@[simp, norm_cast, isROrC_simps]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r
#align is_R_or_C.of_real_neg IsROrC.ofReal_neg

@[simp, norm_cast, isROrC_simps]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s
#align is_R_or_C.of_real_sub IsROrC.ofReal_sub

@[simp, isROrC_simps, norm_cast]
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _
#align is_R_or_C.of_real_sum IsROrC.ofReal_sum

@[simp, isROrC_simps, norm_cast]
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.sum fun a b => g a b : ℝ) : K) = f.sum fun a b => (g a b : K) :=
  map_finsupp_sum (algebraMap ℝ K) f g
#align is_R_or_C.of_real_finsupp_sum IsROrC.ofReal_finsupp_sum

@[simp, norm_cast, isROrC_simps]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _
#align is_R_or_C.of_real_mul IsROrC.ofReal_mul

@[simp, norm_cast, isROrC_simps]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_pow (algebraMap ℝ K) r n
#align is_R_or_C.of_real_pow IsROrC.ofReal_pow

@[simp, isROrC_simps, norm_cast]
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
  map_prod (algebraMap ℝ K) _ _
#align is_R_or_C.of_real_prod IsROrC.ofReal_prod

@[simp, isROrC_simps, norm_cast]
theorem ofReal_finsupp_prod {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.prod fun a b => g a b : ℝ) : K) = f.prod fun a b => (g a b : K) :=
  map_finsupp_prod _ f g
#align is_R_or_C.of_real_finsupp_prod IsROrC.ofReal_finsupp_prod

@[simp, norm_cast, isROrC_simps]
theorem real_smul_ofReal (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _
#align is_R_or_C.real_smul_of_real IsROrC.real_smul_ofReal

@[isROrC_simps]
theorem ofReal_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]
  -- 🎉 no goals
#align is_R_or_C.of_real_mul_re IsROrC.ofReal_mul_re

@[isROrC_simps]
theorem ofReal_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]
  -- 🎉 no goals
#align is_R_or_C.of_real_mul_im IsROrC.ofReal_mul_im

@[isROrC_simps]
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, ofReal_mul_re]
  -- 🎉 no goals
#align is_R_or_C.smul_re IsROrC.smul_re

@[isROrC_simps]
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, ofReal_mul_im]
  -- 🎉 no goals
#align is_R_or_C.smul_im IsROrC.smul_im

@[simp, norm_cast, isROrC_simps]
theorem norm_ofReal (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r
#align is_R_or_C.norm_of_real IsROrC.norm_ofReal

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero.  -/
instance (priority := 100) charZero_isROrC : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).injective).1 inferInstance
set_option linter.uppercaseLean3 false in
#align is_R_or_C.char_zero_R_or_C IsROrC.charZero_isROrC

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, isROrC_simps]
theorem I_re : re (I : K) = 0 :=
  I_re_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_re IsROrC.I_re

@[simp, isROrC_simps]
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_im IsROrC.I_im

@[simp, isROrC_simps]
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]
                                                       -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_im' IsROrC.I_im'

@[isROrC_simps] -- porting note: was `simp`
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_re IsROrC.I_mul_re

theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_I IsROrC.I_mul_I

@[simp, isROrC_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  IsROrC.conj_re_ax z
#align is_R_or_C.conj_re IsROrC.conj_re

@[simp, isROrC_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  IsROrC.conj_im_ax z
#align is_R_or_C.conj_im IsROrC.conj_im

@[simp, isROrC_simps]
theorem conj_I : conj (I : K) = -I :=
  IsROrC.conj_I_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_I IsROrC.conj_I

@[simp, isROrC_simps]
theorem conj_ofReal (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  -- ⊢ ↑re (↑(starRingEnd K) ↑r) = ↑re ↑r ∧ ↑im (↑(starRingEnd K) ↑r) = ↑im ↑r
  simp only [ofReal_im, conj_im, eq_self_iff_true, conj_re, and_self_iff, neg_zero]
  -- 🎉 no goals
#align is_R_or_C.conj_of_real IsROrC.conj_ofReal

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) :=
  map_bit0 _ _
#align is_R_or_C.conj_bit0 IsROrC.conj_bit0

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) :=
  map_bit1 _ _
#align is_R_or_C.conj_bit1 IsROrC.conj_bit1

@[isROrC_simps] -- porting note: was a `simp` but `simp` can prove it
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]
                                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_neg_I IsROrC.conj_neg_I

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_ofReal, conj_ofReal, mul_neg, sub_eq_add_neg]
    -- 🎉 no goals
#align is_R_or_C.conj_eq_re_sub_im IsROrC.conj_eq_re_sub_im

theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
                                                           -- 🎉 no goals
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]
                           -- 🎉 no goals
#align is_R_or_C.sub_conj IsROrC.sub_conj

@[isROrC_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, ofReal_mul, ofReal_mul,
    real_smul_eq_coe_mul r (_ - _), mul_sub, mul_assoc]
#align is_R_or_C.conj_smul IsROrC.conj_smul

theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
                                                           -- 🎉 no goals
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]
                       -- 🎉 no goals
#align is_R_or_C.add_conj IsROrC.add_conj

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left (re z : K) two_ne_zero]
  -- 🎉 no goals
#align is_R_or_C.re_eq_add_conj IsROrC.re_eq_add_conj

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← ofReal_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]
#align is_R_or_C.im_eq_conj_sub IsROrC.im_eq_conj_sub

open List in
/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
theorem is_real_TFAE (z : K) : TFAE [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0] := by
  tfae_have 1 → 4
  -- ⊢ ↑(starRingEnd K) z = z → ↑im z = 0
  · intro h
    -- ⊢ ↑im z = 0
    rw [← @ofReal_inj K, im_eq_conj_sub, h, sub_self, mul_zero, zero_div,
      ofReal_zero]
  tfae_have 4 → 3
  -- ⊢ ↑im z = 0 → ↑(↑re z) = z
  · intro h
    -- ⊢ ↑(↑re z) = z
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
    -- 🎉 no goals
  tfae_have 3 → 2; exact fun h => ⟨_, h⟩
  -- ⊢ ↑(↑re z) = z → ∃ r, ↑r = z
                   -- ⊢ TFAE [↑(starRingEnd K) z = z, ∃ r, ↑r = z, ↑(↑re z) = z, ↑im z = 0]
  tfae_have 2 → 1; exact fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  -- ⊢ (∃ r, ↑r = z) → ↑(starRingEnd K) z = z
                   -- ⊢ TFAE [↑(starRingEnd K) z = z, ∃ r, ↑r = z, ↑(↑re z) = z, ↑im z = 0]
  tfae_finish
  -- 🎉 no goals
#align is_R_or_C.is_real_tfae IsROrC.is_real_TFAE

theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  ((is_real_TFAE z).out 0 1).trans <| by simp only [eq_comm]
                                         -- 🎉 no goals
#align is_R_or_C.conj_eq_iff_real IsROrC.conj_eq_iff_real

theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2
#align is_R_or_C.conj_eq_iff_re IsROrC.conj_eq_iff_re

theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3
#align is_R_or_C.conj_eq_iff_im IsROrC.conj_eq_iff_im

@[simp]
theorem star_def : (Star.star : K → K) = conj :=
  rfl
#align is_R_or_C.star_def IsROrC.star_def

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv
#align is_R_or_C.conj_to_ring_equiv IsROrC.conjToRingEquiv

variable {K}

/-- The norm squared function. -/
def normSq : K →*₀ ℝ where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
                  -- 🎉 no goals
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
                 -- 🎉 no goals
  map_mul' z w := by
    simp only [mul_im, mul_re]
    -- ⊢ (↑re z * ↑re w - ↑im z * ↑im w) * (↑re z * ↑re w - ↑im z * ↑im w) + (↑re z * …
    ring
    -- 🎉 no goals
#align is_R_or_C.norm_sq IsROrC.normSq

theorem normSq_apply (z : K) : normSq z = re z * re z + im z * im z :=
  rfl
#align is_R_or_C.norm_sq_apply IsROrC.normSq_apply

theorem norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z
#align is_R_or_C.norm_sq_eq_def IsROrC.norm_sq_eq_def

theorem normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2 :=
  norm_sq_eq_def.symm
#align is_R_or_C.norm_sq_eq_def' IsROrC.normSq_eq_def'

@[isROrC_simps]
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero
#align is_R_or_C.norm_sq_zero IsROrC.normSq_zero

@[isROrC_simps]
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one
#align is_R_or_C.norm_sq_one IsROrC.normSq_one

theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
#align is_R_or_C.norm_sq_nonneg IsROrC.normSq_nonneg

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _
#align is_R_or_C.norm_sq_eq_zero IsROrC.normSq_eq_zero

@[simp, isROrC_simps]
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm]; simp [normSq_nonneg]
  -- ⊢ 0 ≤ ↑normSq z ∧ ¬↑normSq z = 0 ↔ z ≠ 0
                                      -- 🎉 no goals
#align is_R_or_C.norm_sq_pos IsROrC.normSq_pos

@[simp, isROrC_simps]
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]
                                                          -- 🎉 no goals
#align is_R_or_C.norm_sq_neg IsROrC.normSq_neg

@[simp, isROrC_simps]
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, isROrC_simps]
  -- 🎉 no goals
#align is_R_or_C.norm_sq_conj IsROrC.normSq_conj

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w
#align is_R_or_C.norm_sq_mul IsROrC.normSq_mul

theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, isROrC_simps]
  -- ⊢ (↑re z + ↑re w) * (↑re z + ↑re w) + (↑im z + ↑im w) * (↑im z + ↑im w) = ↑re  …
  ring
  -- 🎉 no goals
#align is_R_or_C.norm_sq_add IsROrC.normSq_add

theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
#align is_R_or_C.re_sq_le_norm_sq IsROrC.re_sq_le_normSq

theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
#align is_R_or_C.im_sq_le_norm_sq IsROrC.im_sq_le_normSq

theorem mul_conj (z : K) : z * conj z = (normSq z : K) := by
  apply ext <;> simp only [normSq_apply, isROrC_simps, map_add, mul_zero] <;> ring
  -- ⊢ ↑re (z * ↑(starRingEnd K) z) = ↑re ↑(↑normSq z)
                -- ⊢ ↑re z * ↑re z - ↑im z * -↑im z = ↑re z * ↑re z - 0 + (↑im z * ↑im z - 0)
                -- ⊢ ↑re z * -↑im z + ↑im z * ↑re z = 0 + 0 * ↑re z + (0 + 0 * ↑im z)
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align is_R_or_C.mul_conj IsROrC.mul_conj

theorem conj_mul (x : K) : conj x * x = (normSq x : K) := by rw [mul_comm, mul_conj]
                                                             -- 🎉 no goals
#align is_R_or_C.conj_mul IsROrC.conj_mul

theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]
  -- 🎉 no goals
#align is_R_or_C.norm_sq_sub IsROrC.normSq_sub

theorem sqrt_normSq_eq_norm {z : K} : Real.sqrt (normSq z) = ‖z‖ := by
  rw [normSq_eq_def', Real.sqrt_sq (norm_nonneg _)]
  -- 🎉 no goals
#align is_R_or_C.sqrt_norm_sq_eq_norm IsROrC.sqrt_normSq_eq_norm

/-! ### Inversion -/

@[simp, norm_cast, isROrC_simps]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r
#align is_R_or_C.of_real_inv IsROrC.ofReal_inv

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  -- ⊢ 0⁻¹ = ↑(starRingEnd K) 0 * ↑(‖0‖ ^ 2)⁻¹
  · simp
    -- 🎉 no goals
  · apply inv_eq_of_mul_eq_one_right
    -- ⊢ z * (↑(starRingEnd K) z * ↑(‖z‖ ^ 2)⁻¹) = 1
    rw [← mul_assoc, mul_conj, ofReal_inv, ← normSq_eq_def', mul_inv_cancel]
    -- ⊢ ↑(↑normSq z) ≠ 0
    rwa [ofReal_ne_zero, Ne.def, normSq_eq_zero]
    -- 🎉 no goals
#align is_R_or_C.inv_def IsROrC.inv_def

@[simp, isROrC_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, ofReal_mul_re, conj_re, div_eq_inv_mul]
  -- 🎉 no goals
#align is_R_or_C.inv_re IsROrC.inv_re

@[simp, isROrC_simps]
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, ofReal_mul_im, conj_im, div_eq_inv_mul]
  -- 🎉 no goals
#align is_R_or_C.inv_im IsROrC.inv_im

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg, map_neg,
    isROrC_simps]
#align is_R_or_C.div_re IsROrC.div_re

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg, map_neg,
    isROrC_simps]
#align is_R_or_C.div_im IsROrC.div_im

@[isROrC_simps] -- porting note: was `simp`
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _
#align is_R_or_C.conj_inv IsROrC.conj_inv

@[simp, norm_cast, isROrC_simps]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s
#align is_R_or_C.of_real_div IsROrC.ofReal_div

theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, ofReal_mul_re]
  -- 🎉 no goals
#align is_R_or_C.div_re_of_real IsROrC.div_re_ofReal

@[simp, norm_cast, isROrC_simps]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n
#align is_R_or_C.of_real_zpow IsROrC.ofReal_zpow

theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_I_of_nonzero IsROrC.I_mul_I_of_nonzero

@[simp, isROrC_simps]
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  -- ⊢ I⁻¹ = -I
  · simp [h]
    -- 🎉 no goals
  · field_simp [I_mul_I_of_nonzero h]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_R_or_C.inv_I IsROrC.inv_I

@[simp, isROrC_simps]
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]
                                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align is_R_or_C.div_I IsROrC.div_I

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z
#align is_R_or_C.norm_sq_inv IsROrC.normSq_inv

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w
#align is_R_or_C.norm_sq_div IsROrC.normSq_div

@[isROrC_simps] -- porting note: was `simp`
theorem norm_conj {z : K} : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]
                                                 -- 🎉 no goals
#align is_R_or_C.norm_conj IsROrC.norm_conj

instance (priority := 100) : CstarRing K where
  norm_star_mul_self {x} := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) norm_conj

/-! ### Cast lemmas -/

@[simp, isROrC_simps, norm_cast]
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n
#align is_R_or_C.of_real_nat_cast IsROrC.ofReal_natCast

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem natCast_re (n : ℕ) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]
                                                  -- 🎉 no goals
#align is_R_or_C.nat_cast_re IsROrC.natCast_re

@[simp, isROrC_simps, norm_cast]
theorem natCast_im (n : ℕ) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]
                                                  -- 🎉 no goals
#align is_R_or_C.nat_cast_im IsROrC.natCast_im

@[simp, isROrC_simps]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : re (no_index (OfNat.ofNat n) : K) = OfNat.ofNat n :=
  natCast_re n

@[simp, isROrC_simps]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : im (no_index (OfNat.ofNat n) : K) = 0 :=
  natCast_im n

@[simp, isROrC_simps, norm_cast]
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℝ) : K) = OfNat.ofNat n :=
  ofReal_natCast n

theorem ofNat_mul_re (n : ℕ) [n.AtLeastTwo] (z : K) :
    re (OfNat.ofNat n * z) = OfNat.ofNat n * re z := by
  rw [← ofReal_ofNat, ofReal_mul_re]
  -- 🎉 no goals

theorem ofNat_mul_im (n : ℕ) [n.AtLeastTwo] (z : K) :
    im (OfNat.ofNat n * z) = OfNat.ofNat n * im z := by
  rw [← ofReal_ofNat, ofReal_mul_im]
  -- 🎉 no goals

@[simp, isROrC_simps, norm_cast]
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast _ n
#align is_R_or_C.of_real_int_cast IsROrC.ofReal_intCast

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem intCast_re (n : ℤ) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]
                                                  -- 🎉 no goals
#align is_R_or_C.int_cast_re IsROrC.intCast_re

@[simp, isROrC_simps, norm_cast]
theorem intCast_im (n : ℤ) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]
                                                  -- 🎉 no goals
#align is_R_or_C.int_cast_im IsROrC.intCast_im

@[simp, isROrC_simps, norm_cast]
theorem ofReal_ratCast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast _ n
#align is_R_or_C.of_real_rat_cast IsROrC.ofReal_ratCast

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem ratCast_re (q : ℚ) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]
                                                  -- 🎉 no goals
#align is_R_or_C.rat_cast_re IsROrC.ratCast_re

@[simp, isROrC_simps, norm_cast]
theorem ratCast_im (q : ℚ) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]
                                                  -- 🎉 no goals
#align is_R_or_C.rat_cast_im IsROrC.ratCast_im

/-! ### Norm -/

theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)
#align is_R_or_C.norm_of_nonneg IsROrC.norm_of_nonneg

@[simp, isROrC_simps, norm_cast]
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  -- ⊢ ‖↑↑n‖ = ↑n
  exact norm_of_nonneg (Nat.cast_nonneg n)
  -- 🎉 no goals
#align is_R_or_C.norm_nat_cast IsROrC.norm_natCast

@[simp, isROrC_simps]
theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(no_index (OfNat.ofNat n) : K)‖ = OfNat.ofNat n :=
  norm_natCast n

theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]
                                                           -- 🎉 no goals
#align is_R_or_C.mul_self_norm IsROrC.mul_self_norm

attribute [isROrC_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

-- porting note: removed @[simp, isROrC_simps], b/c generalized to `norm_ofNat`
theorem norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2
#align is_R_or_C.norm_two IsROrC.norm_two

theorem abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  -- ⊢ ↑re z * ↑re z ≤ ↑normSq z
  apply re_sq_le_normSq
  -- 🎉 no goals
#align is_R_or_C.abs_re_le_norm IsROrC.abs_re_le_norm

theorem abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  -- ⊢ ↑im z * ↑im z ≤ ↑normSq z
  apply im_sq_le_normSq
  -- 🎉 no goals
#align is_R_or_C.abs_im_le_norm IsROrC.abs_im_le_norm

theorem norm_re_le_norm (z : K) : ‖re z‖ ≤ ‖z‖ :=
  abs_re_le_norm z
#align is_R_or_C.norm_re_le_norm IsROrC.norm_re_le_norm

theorem norm_im_le_norm (z : K) : ‖im z‖ ≤ ‖z‖ :=
  abs_im_le_norm z
#align is_R_or_C.norm_im_le_norm IsROrC.norm_im_le_norm

theorem re_le_norm (z : K) : re z ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm z)).2
#align is_R_or_C.re_le_norm IsROrC.re_le_norm

theorem im_le_norm (z : K) : im z ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2
#align is_R_or_C.im_le_norm IsROrC.im_le_norm

theorem im_eq_zero_of_le {a : K} (h : ‖a‖ ≤ re a) : im a = 0 := by
  simpa only [mul_self_norm a, normSq_apply, self_eq_add_right, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)
#align is_R_or_C.im_eq_zero_of_le IsROrC.im_eq_zero_of_le

theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re, conj_eq_iff_im, im_eq_zero_of_le h]
  -- 🎉 no goals
#align is_R_or_C.re_eq_self_of_le IsROrC.re_eq_self_of_le

open IsAbsoluteValue

theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  -- ⊢ |↑re z| / ‖z‖ ≤ 1
  exact div_le_one_of_le (abs_re_le_norm _) (norm_nonneg _)
  -- 🎉 no goals
#align is_R_or_C.abs_re_div_norm_le_one IsROrC.abs_re_div_norm_le_one

theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  -- ⊢ |↑im z| / ‖z‖ ≤ 1
  exact div_le_one_of_le (abs_im_le_norm _) (norm_nonneg _)
  -- 🎉 no goals
#align is_R_or_C.abs_im_div_norm_le_one IsROrC.abs_im_div_norm_le_one

theorem norm_I_of_ne_zero (hI : (I : K) ≠ 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
    I_mul_I_of_nonzero hI, norm_neg, norm_one]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.norm_I_of_ne_zero IsROrC.norm_I_of_ne_zero

theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, ofReal_re, norm_ofReal, abs_of_nonneg (normSq_nonneg _)]
  -- 🎉 no goals
#align is_R_or_C.re_eq_norm_of_mul_conj IsROrC.re_eq_norm_of_mul_conj

theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, ← ofReal_ofNat, ← ofReal_mul, norm_ofReal, sq_abs, ofReal_re]
  -- 🎉 no goals
#align is_R_or_C.norm_sq_re_add_conj IsROrC.norm_sq_re_add_conj

theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]
  -- 🎉 no goals
#align is_R_or_C.norm_sq_re_conj_add IsROrC.norm_sq_re_conj_add

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)
                       -- 🎉 no goals
#align is_R_or_C.is_cau_seq_re IsROrC.isCauSeq_re

theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)
                       -- 🎉 no goals
#align is_R_or_C.is_cau_seq_im IsROrC.isCauSeq_im

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩
#align is_R_or_C.cau_seq_re IsROrC.cauSeqRe

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩
#align is_R_or_C.cau_seq_im IsROrC.cauSeqIm

theorem isCauSeq_norm {f : ℕ → K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
#align is_R_or_C.is_cau_seq_norm IsROrC.isCauSeq_norm

end IsROrC

section Instances

noncomputable instance Real.isROrC : IsROrC ℝ where
  re := AddMonoidHom.id ℝ
  im := 0
  I := 0
  I_re_ax := by simp only [AddMonoidHom.map_zero]
                -- 🎉 no goals
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.id.map_eq_id, RingHom.id_apply, AddMonoidHom.id_apply]
    -- 🎉 no goals
  ofReal_re_ax f := rfl
  ofReal_im_ax r := rfl
  mul_re_ax z w := by simp only [sub_zero, mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
                      -- 🎉 no goals
  mul_im_ax z w := by simp only [add_zero, zero_mul, mul_zero, AddMonoidHom.zero_apply]
                      -- 🎉 no goals
  conj_re_ax z := by simp only [starRingEnd_apply, star_id_of_comm]
                     -- 🎉 no goals
  conj_im_ax z := by simp only [neg_zero, AddMonoidHom.zero_apply]
                     -- 🎉 no goals
  conj_I_ax := by simp only [RingHom.map_zero, neg_zero]
                  -- 🎉 no goals
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax z := by simp only [mul_zero, AddMonoidHom.zero_apply]
                      -- 🎉 no goals
  le_iff_re_im := (and_iff_left rfl).symm
#align real.is_R_or_C Real.isROrC

end Instances

namespace IsROrC

section Order

open scoped ComplexOrder

theorem lt_iff_re_im {z w : K} : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @IsROrC.le_iff_re_im K]
  -- ⊢ (↑re z ≤ ↑re w ∧ ↑im z = ↑im w) ∧ z ≠ w ↔ (↑re z ≤ ↑re w ∧ ↑re z ≠ ↑re w) ∧  …
  constructor
  -- ⊢ (↑re z ≤ ↑re w ∧ ↑im z = ↑im w) ∧ z ≠ w → (↑re z ≤ ↑re w ∧ ↑re z ≠ ↑re w) ∧  …
  · rintro ⟨⟨hr, hi⟩, heq⟩
    -- ⊢ (↑re z ≤ ↑re w ∧ ↑re z ≠ ↑re w) ∧ ↑im z = ↑im w
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
    -- 🎉 no goals
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    -- ⊢ (↑re z ≤ ↑re w ∧ ↑im z = ↑im w) ∧ z ≠ w
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩
    -- 🎉 no goals

theorem nonneg_iff {z : K} : 0 ≤ z ↔ 0 ≤ re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)
  -- 🎉 no goals

theorem pos_iff {z : K} : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)
  -- 🎉 no goals

theorem nonpos_iff {z : K} : z ≤ 0 ↔ re z ≤ 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)
  -- 🎉 no goals

theorem neg_iff {z : K} : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)
  -- 🎉 no goals

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered rings.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)

Note this is only an instance with `open scoped ComplexOrder`. -/
def toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.ofNonnegIff'
    (h_add := fun {x y} hxy z => by
      rw [IsROrC.le_iff_re_im] at *
      -- ⊢ ↑re (z + x) ≤ ↑re (z + y) ∧ ↑im (z + x) = ↑im (z + y)
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
      -- 🎉 no goals
    (h_nonneg_iff := fun x => by
      rw [IsROrC.le_iff_re_im, map_zero, map_zero, IsROrC.star_def, eq_comm]
      -- ⊢ 0 ≤ ↑re x ∧ ↑im x = 0 ↔ ∃ s, x = ↑(starRingEnd K) s * s
      constructor
      -- ⊢ 0 ≤ ↑re x ∧ ↑im x = 0 → ∃ s, x = ↑(starRingEnd K) s * s
      · rintro ⟨hr, hi⟩
        -- ⊢ ∃ s, x = ↑(starRingEnd K) s * s
        refine ⟨Real.sqrt (IsROrC.re x), ?_⟩
        -- ⊢ x = ↑(starRingEnd K) ↑(Real.sqrt (↑re x)) * ↑(Real.sqrt (↑re x))
        have := (IsROrC.is_real_TFAE x).out 2 3
        -- ⊢ x = ↑(starRingEnd K) ↑(Real.sqrt (↑re x)) * ↑(Real.sqrt (↑re x))
        rw [IsROrC.conj_ofReal, ← IsROrC.ofReal_mul, Real.mul_self_sqrt hr, eq_comm, this, hi]
        -- 🎉 no goals
      · rintro ⟨s, rfl⟩
        -- ⊢ 0 ≤ ↑re (↑(starRingEnd K) s * s) ∧ ↑im (↑(starRingEnd K) s * s) = 0
        simp only [IsROrC.star_def, IsROrC.conj_mul]
        -- ⊢ 0 ≤ ↑re ↑(↑normSq s) ∧ ↑im ↑(↑normSq s) = 0
        rw [IsROrC.ofReal_re, IsROrC.ofReal_im, eq_self, and_true]
        -- ⊢ 0 ≤ ↑normSq s
        apply IsROrC.normSq_nonneg)
        -- 🎉 no goals

scoped[ComplexOrder] attribute [instance] IsROrC.toStarOrderedRing

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
def toStrictOrderedCommRing : StrictOrderedCommRing K where
  zero_le_one := by simp [@IsROrC.le_iff_re_im K]
                    -- 🎉 no goals
  add_le_add_left _ _ := add_le_add_left
  mul_pos z w hz hw := by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    -- ⊢ 0 < ↑re (z * w) ∧ ↑im 0 = ↑im (z * w)
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]
    -- 🎉 no goals
  mul_comm := by intros; apply ext <;> ring_nf
                 -- ⊢ a✝ * b✝ = b✝ * a✝
                         -- ⊢ ↑re (a✝ * b✝) = ↑re (b✝ * a✝)
                                       -- 🎉 no goals
                                       -- 🎉 no goals

scoped[ComplexOrder] attribute [instance] IsROrC.toStrictOrderedCommRing

theorem toOrderedSMul : OrderedSMul ℝ K :=
  OrderedSMul.mk' fun a b r hab hr => by
    replace hab := hab.le
    -- ⊢ r • a ≤ r • b
    rw [IsROrC.le_iff_re_im] at hab
    -- ⊢ r • a ≤ r • b
    rw [IsROrC.le_iff_re_im, smul_re, smul_re, smul_im, smul_im]
    -- ⊢ r * ↑re a ≤ r * ↑re b ∧ r * ↑im a = r * ↑im b
    exact hab.imp (fun h => mul_le_mul_of_nonneg_left h hr.le) (congr_arg _)
    -- 🎉 no goals

scoped[ComplexOrder] attribute [instance] IsROrC.toOrderedSMul

end Order

open ComplexConjugate

section CleanupLemmas

local notation "reR" => @IsROrC.re ℝ _
local notation "imR" => @IsROrC.im ℝ _
local notation "IR" => @IsROrC.I ℝ _
local notation "normSqR" => @IsROrC.normSq ℝ _

@[simp, isROrC_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl
#align is_R_or_C.re_to_real IsROrC.re_to_real

@[simp, isROrC_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl
#align is_R_or_C.im_to_real IsROrC.im_to_real

@[simp, isROrC_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl
#align is_R_or_C.conj_to_real IsROrC.conj_to_real

@[simp, isROrC_simps]
theorem I_to_real : IR = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_to_real IsROrC.I_to_real

@[simp, isROrC_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [IsROrC.normSq]
                                                        -- 🎉 no goals
#align is_R_or_C.norm_sq_to_real IsROrC.normSq_to_real

@[simp]
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl
#align is_R_or_C.coe_real_eq_id IsROrC.ofReal_real_eq_id

end CleanupLemmas

section LinearMaps

/-- The real part in an `IsROrC` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }
#align is_R_or_C.re_lm IsROrC.reLm

@[simp, isROrC_simps]
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_lm_coe IsROrC.reLm_coe

/-- The real part in an `IsROrC` field, as a continuous linear map. -/
noncomputable def reClm : K →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    -- ⊢ ‖↑reLm x‖ ≤ ‖x‖
    exact abs_re_le_norm x
    -- 🎉 no goals
#align is_R_or_C.re_clm IsROrC.reClm

@[simp, isROrC_simps, norm_cast]
theorem reClm_coe : ((reClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl
#align is_R_or_C.re_clm_coe IsROrC.reClm_coe

@[simp, isROrC_simps]
theorem reClm_apply : ((reClm : K →L[ℝ] ℝ) : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_clm_apply IsROrC.reClm_apply

@[continuity]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reClm.continuous
#align is_R_or_C.continuous_re IsROrC.continuous_re

/-- The imaginary part in an `IsROrC` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }
#align is_R_or_C.im_lm IsROrC.imLm

@[simp, isROrC_simps]
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_lm_coe IsROrC.imLm_coe

/-- The imaginary part in an `IsROrC` field, as a continuous linear map. -/
noncomputable def imClm : K →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    -- ⊢ ‖↑imLm x‖ ≤ ‖x‖
    exact abs_im_le_norm x
    -- 🎉 no goals
#align is_R_or_C.im_clm IsROrC.imClm

@[simp, isROrC_simps, norm_cast]
theorem imClm_coe : ((imClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl
#align is_R_or_C.im_clm_coe IsROrC.imClm_coe

@[simp, isROrC_simps]
theorem imClm_apply : ((imClm : K →L[ℝ] ℝ) : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_clm_apply IsROrC.imClm_apply

@[continuity]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imClm.continuous
#align is_R_or_C.continuous_im IsROrC.continuous_im

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }
#align is_R_or_C.conj_ae IsROrC.conjAe

@[simp, isROrC_simps]
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl
#align is_R_or_C.conj_ae_coe IsROrC.conjAe_coe

/-- Conjugate as a linear isometry -/
noncomputable def conjLie : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun _ => norm_conj⟩
#align is_R_or_C.conj_lie IsROrC.conjLie

@[simp, isROrC_simps]
theorem conjLie_apply : (conjLie : K → K) = conj :=
  rfl
#align is_R_or_C.conj_lie_apply IsROrC.conjLie_apply

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCle : K ≃L[ℝ] K :=
  @conjLie K _
#align is_R_or_C.conj_cle IsROrC.conjCle

@[simp, isROrC_simps]
theorem conjCle_coe : (@conjCle K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl
#align is_R_or_C.conj_cle_coe IsROrC.conjCle_coe

@[simp, isROrC_simps]
theorem conjCle_apply : (conjCle : K → K) = conj :=
  rfl
#align is_R_or_C.conj_cle_apply IsROrC.conjCle_apply

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLie.continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star
#align is_R_or_C.continuous_conj IsROrC.continuous_conj

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K
#align is_R_or_C.of_real_am IsROrC.ofRealAm

@[simp, isROrC_simps]
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_am_coe IsROrC.ofRealAm_coe

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLi : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal
#align is_R_or_C.of_real_li IsROrC.ofRealLi

@[simp, isROrC_simps]
theorem ofRealLi_apply : (ofRealLi : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_li_apply IsROrC.ofRealLi_apply

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealClm : ℝ →L[ℝ] K :=
  ofRealLi.toContinuousLinearMap
#align is_R_or_C.of_real_clm IsROrC.ofRealClm

@[simp, isROrC_simps]
theorem ofRealClm_coe : (@ofRealClm K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl
#align is_R_or_C.of_real_clm_coe IsROrC.ofRealClm_coe

@[simp, isROrC_simps]
theorem ofRealClm_apply : (ofRealClm : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_clm_apply IsROrC.ofRealClm_apply

@[continuity]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLi.continuous
#align is_R_or_C.continuous_of_real IsROrC.continuous_ofReal

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)
#align is_R_or_C.continuous_norm_sq IsROrC.continuous_normSq

end LinearMaps

end IsROrC
