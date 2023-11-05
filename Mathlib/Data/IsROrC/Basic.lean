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
  -- note we cannot put this in the `extends` clause
  [toDecidableEq : DecidableEq K]

scoped[ComplexOrder] attribute [instance 100] IsROrC.toPartialOrder
attribute [instance 100] IsROrC.toDecidableEq

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

theorem ofReal_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x

theorem real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z

theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [IsROrC.ofReal_alg, smul_one_smul]

theorem algebraMap_eq_ofReal : ⇑(algebraMap ℝ K) = ofReal :=
  rfl

@[simp, isROrC_simps]
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  IsROrC.re_add_im_ax z

@[simp, norm_cast, isROrC_simps]
theorem ofReal_re : ∀ r : ℝ, re (r : K) = r :=
  IsROrC.ofReal_re_ax

@[simp, norm_cast, isROrC_simps]
theorem ofReal_im : ∀ r : ℝ, im (r : K) = 0 :=
  IsROrC.ofReal_im_ax

@[simp, isROrC_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  IsROrC.mul_re_ax

@[simp, isROrC_simps]
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  IsROrC.mul_im_ax

theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩

@[norm_cast]
theorem ofReal_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero

@[isROrC_simps]
theorem zero_re' : re (0 : K) = (0 : ℝ) :=
  map_zero re

@[norm_cast]
theorem ofReal_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)

@[simp, isROrC_simps]
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]

@[simp, isROrC_simps]
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]

theorem ofReal_injective : Function.Injective ((↑) : ℝ → K) :=
  (algebraMap ℝ K).injective

@[norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem bit0_re (z : K) : re (bit0 z) = bit0 (re z) :=
  map_bit0 _ _

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps]
theorem bit1_re (z : K) : re (bit1 z) = bit1 (re z) := by simp only [bit1, map_add, bit0_re, one_re]

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem bit0_im (z : K) : im (bit0 z) = bit0 (im z) :=
  map_bit0 _ _

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps]
theorem bit1_im (z : K) : im (bit1 z) = bit0 (im z) := by
  simp only [bit1, map_add, bit0_im, one_im, add_zero]

theorem ofReal_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.lift_map_eq_zero_iff x

theorem ofReal_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  ofReal_eq_zero.not

@[simp, isROrC_simps, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps, norm_cast]
theorem ofReal_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) :=
  ofReal_add _ _

set_option linter.deprecated false in
@[deprecated, simp, isROrC_simps, norm_cast]
theorem ofReal_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
  map_bit1 (algebraMap ℝ K) r

@[simp, norm_cast, isROrC_simps]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r

@[simp, norm_cast, isROrC_simps]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s

@[simp, isROrC_simps, norm_cast]
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _

@[simp, isROrC_simps, norm_cast]
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.sum fun a b => g a b : ℝ) : K) = f.sum fun a b => (g a b : K) :=
  map_finsupp_sum (algebraMap ℝ K) f g

@[simp, norm_cast, isROrC_simps]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _

@[simp, norm_cast, isROrC_simps]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_pow (algebraMap ℝ K) r n

@[simp, isROrC_simps, norm_cast]
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
  map_prod (algebraMap ℝ K) _ _

@[simp, isROrC_simps, norm_cast]
theorem ofReal_finsupp_prod {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.prod fun a b => g a b : ℝ) : K) = f.prod fun a b => (g a b : K) :=
  map_finsupp_prod _ f g

@[simp, norm_cast, isROrC_simps]
theorem real_smul_ofReal (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _

@[isROrC_simps]
theorem ofReal_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[isROrC_simps]
theorem ofReal_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[isROrC_simps]
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, ofReal_mul_re]

@[isROrC_simps]
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, ofReal_mul_im]

@[simp, norm_cast, isROrC_simps]
theorem norm_ofReal (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero.  -/
instance (priority := 100) charZero_isROrC : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).injective).1 inferInstance

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, isROrC_simps]
theorem I_re : re (I : K) = 0 :=
  I_re_ax

@[simp, isROrC_simps]
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z

@[simp, isROrC_simps]
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]

@[isROrC_simps] -- porting note: was `simp`
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax

@[simp, isROrC_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  IsROrC.conj_re_ax z

@[simp, isROrC_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  IsROrC.conj_im_ax z

@[simp, isROrC_simps]
theorem conj_I : conj (I : K) = -I :=
  IsROrC.conj_I_ax

@[simp, isROrC_simps]
theorem conj_ofReal (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, eq_self_iff_true, conj_re, and_self_iff, neg_zero]

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) :=
  map_bit0 _ _

set_option linter.deprecated false in
@[deprecated, isROrC_simps] -- porting note: was `simp` but `simp` can prove it
theorem conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) :=
  map_bit1 _ _

@[isROrC_simps] -- porting note: was a `simp` but `simp` can prove it
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_ofReal, conj_ofReal, mul_neg, sub_eq_add_neg]

theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[isROrC_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, ofReal_mul, ofReal_mul,
    real_smul_eq_coe_mul r (_ - _), mul_sub, mul_assoc]

theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left (re z : K) two_ne_zero]

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← ofReal_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]

open List in
/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
theorem is_real_TFAE (z : K) : TFAE [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0] := by
  tfae_have 1 → 4
  · intro h
    rw [← @ofReal_inj K, im_eq_conj_sub, h, sub_self, mul_zero, zero_div,
      ofReal_zero]
  tfae_have 4 → 3
  · intro h
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 → 2; exact fun h => ⟨_, h⟩
  tfae_have 2 → 1; exact fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  tfae_finish

theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  ((is_real_TFAE z).out 0 1).trans <| by simp only [eq_comm]

theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2

theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3

@[simp]
theorem star_def : (Star.star : K → K) = conj :=
  rfl

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv

variable {K}

/-- The norm squared function. -/
def normSq : K →*₀ ℝ where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring

theorem normSq_apply (z : K) : normSq z = re z * re z + im z * im z :=
  rfl

theorem norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z

theorem normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2 :=
  norm_sq_eq_def.symm

@[isROrC_simps]
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero

@[isROrC_simps]
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one

theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _

@[simp, isROrC_simps]
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm]; simp [normSq_nonneg]

@[simp, isROrC_simps]
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]

@[simp, isROrC_simps]
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, isROrC_simps]

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w

theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, isROrC_simps]
  ring

theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = (normSq z : K) := by
  apply ext <;> simp only [normSq_apply, isROrC_simps, map_add, mul_zero] <;> ring

theorem conj_mul (x : K) : conj x * x = (normSq x : K) := by rw [mul_comm, mul_conj]

theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]

theorem sqrt_normSq_eq_norm {z : K} : Real.sqrt (normSq z) = ‖z‖ := by
  rw [normSq_eq_def', Real.sqrt_sq (norm_nonneg _)]

/-! ### Inversion -/

@[simp, norm_cast, isROrC_simps]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, ofReal_inv, ← normSq_eq_def', mul_inv_cancel]
    rwa [ofReal_ne_zero, Ne.def, normSq_eq_zero]

@[simp, isROrC_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, ofReal_mul_re, conj_re, div_eq_inv_mul]

@[simp, isROrC_simps]
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, ofReal_mul_im, conj_im, div_eq_inv_mul]

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg, map_neg,
    isROrC_simps]

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg, map_neg,
    isROrC_simps]

@[isROrC_simps] -- porting note: was `simp`
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _

@[simp, norm_cast, isROrC_simps]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s

theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, ofReal_mul_re]

@[simp, norm_cast, isROrC_simps]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n

theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left

@[simp, isROrC_simps]
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp [I_mul_I_of_nonzero h]

@[simp, isROrC_simps]
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

@[isROrC_simps] -- porting note: was `simp`
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

@[isROrC_simps] -- porting note: was `simp`
theorem norm_conj {z : K} : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]

instance (priority := 100) : CstarRing K where
  norm_star_mul_self {x} := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) norm_conj

/-! ### Cast lemmas -/

@[simp, isROrC_simps, norm_cast]
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem natCast_re (n : ℕ) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]

@[simp, isROrC_simps, norm_cast]
theorem natCast_im (n : ℕ) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]

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

theorem ofNat_mul_im (n : ℕ) [n.AtLeastTwo] (z : K) :
    im (OfNat.ofNat n * z) = OfNat.ofNat n * im z := by
  rw [← ofReal_ofNat, ofReal_mul_im]

@[simp, isROrC_simps, norm_cast]
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast _ n

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem intCast_re (n : ℤ) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]

@[simp, isROrC_simps, norm_cast]
theorem intCast_im (n : ℤ) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]

@[simp, isROrC_simps, norm_cast]
theorem ofReal_ratCast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast _ n

@[simp, isROrC_simps] -- porting note: removed `norm_cast`
theorem ratCast_re (q : ℚ) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]

@[simp, isROrC_simps, norm_cast]
theorem ratCast_im (q : ℚ) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]

/-! ### Norm -/

theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)

@[simp, isROrC_simps, norm_cast]
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)

@[simp, isROrC_simps]
theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(no_index (OfNat.ofNat n) : K)‖ = OfNat.ofNat n :=
  norm_natCast n

theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]

attribute [isROrC_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

-- porting note: removed @[simp, isROrC_simps], b/c generalized to `norm_ofNat`
theorem norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2

theorem abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply re_sq_le_normSq

theorem abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply im_sq_le_normSq

theorem norm_re_le_norm (z : K) : ‖re z‖ ≤ ‖z‖ :=
  abs_re_le_norm z

theorem norm_im_le_norm (z : K) : ‖im z‖ ≤ ‖z‖ :=
  abs_im_le_norm z

theorem re_le_norm (z : K) : re z ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm z)).2

theorem im_le_norm (z : K) : im z ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2

theorem im_eq_zero_of_le {a : K} (h : ‖a‖ ≤ re a) : im a = 0 := by
  simpa only [mul_self_norm a, normSq_apply, self_eq_add_right, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)

theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re, conj_eq_iff_im, im_eq_zero_of_le h]

open IsAbsoluteValue

theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_re_le_norm _) (norm_nonneg _)

theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_im_le_norm _) (norm_nonneg _)

theorem norm_I_of_ne_zero (hI : (I : K) ≠ 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
    I_mul_I_of_nonzero hI, norm_neg, norm_one]

theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, ofReal_re, norm_ofReal, abs_of_nonneg (normSq_nonneg _)]

theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, ← ofReal_ofNat, ← ofReal_mul, norm_ofReal, sq_abs, ofReal_re]

theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩

theorem isCauSeq_norm {f : ℕ → K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩

end IsROrC

section Instances

noncomputable instance Real.isROrC : IsROrC ℝ where
  re := AddMonoidHom.id ℝ
  im := 0
  I := 0
  I_re_ax := by simp only [AddMonoidHom.map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.id.map_eq_id, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax f := rfl
  ofReal_im_ax r := rfl
  mul_re_ax z w := by simp only [sub_zero, mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_ax z w := by simp only [add_zero, zero_mul, mul_zero, AddMonoidHom.zero_apply]
  conj_re_ax z := by simp only [starRingEnd_apply, star_id_of_comm]
  conj_im_ax z := by simp only [neg_zero, AddMonoidHom.zero_apply]
  conj_I_ax := by simp only [RingHom.map_zero, neg_zero]
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax z := by simp only [mul_zero, AddMonoidHom.zero_apply]
  le_iff_re_im := (and_iff_left rfl).symm

end Instances

namespace IsROrC

section Order

open scoped ComplexOrder

theorem lt_iff_re_im {z w : K} : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @IsROrC.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

theorem nonneg_iff {z : K} : 0 ≤ z ↔ 0 ≤ re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

theorem pos_iff {z : K} : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

theorem nonpos_iff {z : K} : z ≤ 0 ↔ re z ≤ 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

theorem neg_iff {z : K} : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered rings.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)

Note this is only an instance with `open scoped ComplexOrder`. -/
def toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.ofNonnegIff'
    (h_add := fun {x y} hxy z => by
      rw [IsROrC.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [IsROrC.le_iff_re_im, map_zero, map_zero, IsROrC.star_def, eq_comm]
      constructor
      · rintro ⟨hr, hi⟩
        refine ⟨Real.sqrt (IsROrC.re x), ?_⟩
        have := (IsROrC.is_real_TFAE x).out 2 3
        rw [IsROrC.conj_ofReal, ← IsROrC.ofReal_mul, Real.mul_self_sqrt hr, eq_comm, this, hi]
      · rintro ⟨s, rfl⟩
        simp only [IsROrC.star_def, IsROrC.conj_mul]
        rw [IsROrC.ofReal_re, IsROrC.ofReal_im, eq_self, and_true]
        apply IsROrC.normSq_nonneg)

scoped[ComplexOrder] attribute [instance] IsROrC.toStarOrderedRing

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
def toStrictOrderedCommRing : StrictOrderedCommRing K where
  zero_le_one := by simp [@IsROrC.le_iff_re_im K]
  add_le_add_left _ _ := add_le_add_left
  mul_pos z w hz hw := by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]
  mul_comm := by intros; apply ext <;> ring_nf

scoped[ComplexOrder] attribute [instance] IsROrC.toStrictOrderedCommRing

theorem toOrderedSMul : OrderedSMul ℝ K :=
  OrderedSMul.mk' fun a b r hab hr => by
    replace hab := hab.le
    rw [IsROrC.le_iff_re_im] at hab
    rw [IsROrC.le_iff_re_im, smul_re, smul_re, smul_im, smul_im]
    exact hab.imp (fun h => mul_le_mul_of_nonneg_left h hr.le) (congr_arg _)

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

@[simp, isROrC_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl

@[simp, isROrC_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl

@[simp, isROrC_simps]
theorem I_to_real : IR = 0 :=
  rfl

@[simp, isROrC_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [IsROrC.normSq]

@[simp]
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl

end CleanupLemmas

section LinearMaps

/-- The real part in an `IsROrC` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }

@[simp, isROrC_simps]
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl

/-- The real part in an `IsROrC` field, as a continuous linear map. -/
noncomputable def reClm : K →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, isROrC_simps, norm_cast]
theorem reClm_coe : ((reClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp, isROrC_simps]
theorem reClm_apply : ((reClm : K →L[ℝ] ℝ) : K → ℝ) = re :=
  rfl

@[continuity]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reClm.continuous

/-- The imaginary part in an `IsROrC` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }

@[simp, isROrC_simps]
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl

/-- The imaginary part in an `IsROrC` field, as a continuous linear map. -/
noncomputable def imClm : K →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, isROrC_simps, norm_cast]
theorem imClm_coe : ((imClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp, isROrC_simps]
theorem imClm_apply : ((imClm : K →L[ℝ] ℝ) : K → ℝ) = im :=
  rfl

@[continuity]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imClm.continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, isROrC_simps]
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl

/-- Conjugate as a linear isometry -/
noncomputable def conjLie : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun _ => norm_conj⟩

@[simp, isROrC_simps]
theorem conjLie_apply : (conjLie : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCle : K ≃L[ℝ] K :=
  @conjLie K _

@[simp, isROrC_simps]
theorem conjCle_coe : (@conjCle K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, isROrC_simps]
theorem conjCle_apply : (conjCle : K → K) = conj :=
  rfl

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLie.continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K

@[simp, isROrC_simps]
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = ofReal :=
  rfl

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLi : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, isROrC_simps]
theorem ofRealLi_apply : (ofRealLi : ℝ → K) = ofReal :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealClm : ℝ →L[ℝ] K :=
  ofRealLi.toContinuousLinearMap

@[simp, isROrC_simps]
theorem ofRealClm_coe : (@ofRealClm K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, isROrC_simps]
theorem ofRealClm_apply : (ofRealClm : ℝ → K) = ofReal :=
  rfl

@[continuity]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLi.continuous

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

end LinearMaps

end IsROrC
