/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Analysis.NormedSpace.Basic

#align_import data.is_R_or_C.basic from "leanprover-community/mathlib"@"baa88307f3e699fa7054ef04ec79fa4f056169cb"

/-!
# `RCLike`: a typeclass for ℝ or ℂ

This file defines the typeclass `RCLike` intended to have only two instances:
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

The coercion from reals into an `RCLike` field is done by registering `RCLike.ofReal` as
a `CoeTC`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `Coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `Mathlib/Data/Nat/Cast/Defs.lean`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `Mathlib/Analysis/Complex/Basic.lean` (which causes linter errors).

A few lemmas requiring heavier imports are in `Mathlib/Data/RCLike/Lemmas.lean`.
-/

section

local notation "𝓚" => algebraMap ℝ _

open ComplexConjugate

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class RCLike (K : semiOutParam Type*) extends DenselyNormedField K, StarRing K,
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
  le_iff_re_im {z w : K} : z ≤ w ↔ re z ≤ re w ∧ im z = im w
  -- note we cannot put this in the `extends` clause
  [toDecidableEq : DecidableEq K]
#align is_R_or_C RCLike

scoped[ComplexOrder] attribute [instance 100] RCLike.toPartialOrder
attribute [instance 100] RCLike.toDecidableEq

end

variable {K E : Type*} [RCLike K]

namespace RCLike

open ComplexConjugate

/-- Coercion from `ℝ` to an `RCLike` field. -/
@[coe] abbrev ofReal : ℝ → K := Algebra.cast

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `Mathlib/Data/Nat/Cast/Basic.lean` for more details. -/
noncomputable instance (priority := 900) algebraMapCoe : CoeTC ℝ K :=
  ⟨ofReal⟩
#align is_R_or_C.algebra_map_coe RCLike.algebraMapCoe

theorem ofReal_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x
#align is_R_or_C.of_real_alg RCLike.ofReal_alg

theorem real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z
#align is_R_or_C.real_smul_eq_coe_mul RCLike.real_smul_eq_coe_mul

theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [RCLike.ofReal_alg, smul_one_smul]
#align is_R_or_C.real_smul_eq_coe_smul RCLike.real_smul_eq_coe_smul

theorem algebraMap_eq_ofReal : ⇑(algebraMap ℝ K) = ofReal :=
  rfl
#align is_R_or_C.algebra_map_eq_of_real RCLike.algebraMap_eq_ofReal

@[simp, rclike_simps]
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  RCLike.re_add_im_ax z
#align is_R_or_C.re_add_im RCLike.re_add_im

@[simp, norm_cast, rclike_simps]
theorem ofReal_re : ∀ r : ℝ, re (r : K) = r :=
  RCLike.ofReal_re_ax
#align is_R_or_C.of_real_re RCLike.ofReal_re

@[simp, norm_cast, rclike_simps]
theorem ofReal_im : ∀ r : ℝ, im (r : K) = 0 :=
  RCLike.ofReal_im_ax
#align is_R_or_C.of_real_im RCLike.ofReal_im

@[simp, rclike_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  RCLike.mul_re_ax
#align is_R_or_C.mul_re RCLike.mul_re

@[simp, rclike_simps]
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  RCLike.mul_im_ax
#align is_R_or_C.mul_im RCLike.mul_im

theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩
#align is_R_or_C.ext_iff RCLike.ext_iff

theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩
#align is_R_or_C.ext RCLike.ext

@[norm_cast]
theorem ofReal_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero
#align is_R_or_C.of_real_zero RCLike.ofReal_zero

@[rclike_simps]
theorem zero_re' : re (0 : K) = (0 : ℝ) :=
  map_zero re
#align is_R_or_C.zero_re' RCLike.zero_re'

@[norm_cast]
theorem ofReal_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)
#align is_R_or_C.of_real_one RCLike.ofReal_one

@[simp, rclike_simps]
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]
#align is_R_or_C.one_re RCLike.one_re

@[simp, rclike_simps]
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]
#align is_R_or_C.one_im RCLike.one_im

theorem ofReal_injective : Function.Injective ((↑) : ℝ → K) :=
  (algebraMap ℝ K).injective
#align is_R_or_C.of_real_injective RCLike.ofReal_injective

@[norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj
#align is_R_or_C.of_real_inj RCLike.ofReal_inj

-- replaced by `RCLike.ofNat_re`
#noalign is_R_or_C.bit0_re
#noalign is_R_or_C.bit1_re
-- replaced by `RCLike.ofNat_im`
#noalign is_R_or_C.bit0_im
#noalign is_R_or_C.bit1_im

theorem ofReal_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.lift_map_eq_zero_iff x
#align is_R_or_C.of_real_eq_zero RCLike.ofReal_eq_zero

theorem ofReal_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  ofReal_eq_zero.not
#align is_R_or_C.of_real_ne_zero RCLike.ofReal_ne_zero

@[simp, rclike_simps, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _
#align is_R_or_C.of_real_add RCLike.ofReal_add

-- replaced by `RCLike.ofReal_ofNat`
#noalign is_R_or_C.of_real_bit0
#noalign is_R_or_C.of_real_bit1

@[simp, norm_cast, rclike_simps]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r
#align is_R_or_C.of_real_neg RCLike.ofReal_neg

@[simp, norm_cast, rclike_simps]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s
#align is_R_or_C.of_real_sub RCLike.ofReal_sub

@[simp, rclike_simps, norm_cast]
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : K) = ∑ i ∈ s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _
#align is_R_or_C.of_real_sum RCLike.ofReal_sum

@[simp, rclike_simps, norm_cast]
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.sum fun a b => g a b : ℝ) : K) = f.sum fun a b => (g a b : K) :=
  map_finsupp_sum (algebraMap ℝ K) f g
#align is_R_or_C.of_real_finsupp_sum RCLike.ofReal_finsupp_sum

@[simp, norm_cast, rclike_simps]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _
#align is_R_or_C.of_real_mul RCLike.ofReal_mul

@[simp, norm_cast, rclike_simps]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_pow (algebraMap ℝ K) r n
#align is_R_or_C.of_real_pow RCLike.ofReal_pow

@[simp, rclike_simps, norm_cast]
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ i ∈ s, f i : ℝ) : K) = ∏ i ∈ s, (f i : K) :=
  map_prod (algebraMap ℝ K) _ _
#align is_R_or_C.of_real_prod RCLike.ofReal_prod

@[simp, rclike_simps, norm_cast]
theorem ofReal_finsupp_prod {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.prod fun a b => g a b : ℝ) : K) = f.prod fun a b => (g a b : K) :=
  map_finsupp_prod _ f g
#align is_R_or_C.of_real_finsupp_prod RCLike.ofReal_finsupp_prod

@[simp, norm_cast, rclike_simps]
theorem real_smul_ofReal (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _
#align is_R_or_C.real_smul_of_real RCLike.real_smul_ofReal

@[rclike_simps]
theorem re_ofReal_mul (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]
#align is_R_or_C.of_real_mul_re RCLike.re_ofReal_mul

@[rclike_simps]
theorem im_ofReal_mul (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]
#align is_R_or_C.of_real_mul_im RCLike.im_ofReal_mul

@[rclike_simps]
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, re_ofReal_mul]
#align is_R_or_C.smul_re RCLike.smul_re

@[rclike_simps]
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, im_ofReal_mul]
#align is_R_or_C.smul_im RCLike.smul_im

@[simp, norm_cast, rclike_simps]
theorem norm_ofReal (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r
#align is_R_or_C.norm_of_real RCLike.norm_ofReal

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero.  -/
instance (priority := 100) charZero_rclike : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).injective).1 inferInstance
set_option linter.uppercaseLean3 false in
#align is_R_or_C.char_zero_R_or_C RCLike.charZero_rclike

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, rclike_simps]
theorem I_re : re (I : K) = 0 :=
  I_re_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_re RCLike.I_re

@[simp, rclike_simps]
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_im RCLike.I_im

@[simp, rclike_simps]
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_im' RCLike.I_im'

@[rclike_simps] -- porting note (#10618): was `simp`
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_re RCLike.I_mul_re

theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_I RCLike.I_mul_I

variable (𝕜) in
lemma I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1 :=
  I_mul_I (K := K) |>.imp_right fun h ↦ by simpa [h] using (I_mul_re (I : K)).symm

@[simp, rclike_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  RCLike.conj_re_ax z
#align is_R_or_C.conj_re RCLike.conj_re

@[simp, rclike_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  RCLike.conj_im_ax z
#align is_R_or_C.conj_im RCLike.conj_im

@[simp, rclike_simps]
theorem conj_I : conj (I : K) = -I :=
  RCLike.conj_I_ax
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_I RCLike.conj_I

@[simp, rclike_simps]
theorem conj_ofReal (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, eq_self_iff_true, conj_re, and_self_iff, neg_zero]
#align is_R_or_C.conj_of_real RCLike.conj_ofReal

-- replaced by `RCLike.conj_ofNat`
#noalign is_R_or_C.conj_bit0
#noalign is_R_or_C.conj_bit1

theorem conj_nat_cast (n : ℕ) : conj (n : K) = n := map_natCast _ _

-- See note [no_index around OfNat.ofNat]
theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (no_index (OfNat.ofNat n : K)) = OfNat.ofNat n :=
  map_ofNat _ _

@[rclike_simps] -- Porting note (#10618): was a `simp` but `simp` can prove it
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_neg_I RCLike.conj_neg_I

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_ofReal, conj_ofReal, mul_neg, sub_eq_add_neg]
#align is_R_or_C.conj_eq_re_sub_im RCLike.conj_eq_re_sub_im

theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]
#align is_R_or_C.sub_conj RCLike.sub_conj

@[rclike_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, ofReal_mul, ofReal_mul,
    real_smul_eq_coe_mul r (_ - _), mul_sub, mul_assoc]
#align is_R_or_C.conj_smul RCLike.conj_smul

theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]
#align is_R_or_C.add_conj RCLike.add_conj

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left₀ (re z : K) two_ne_zero]
#align is_R_or_C.re_eq_add_conj RCLike.re_eq_add_conj

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← ofReal_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]
#align is_R_or_C.im_eq_conj_sub RCLike.im_eq_conj_sub

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
  tfae_have 3 → 2
  · exact fun h => ⟨_, h⟩
  tfae_have 2 → 1
  · exact fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  tfae_finish
#align is_R_or_C.is_real_tfae RCLike.is_real_TFAE

theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  ((is_real_TFAE z).out 0 1).trans <| by simp only [eq_comm]
#align is_R_or_C.conj_eq_iff_real RCLike.conj_eq_iff_real

theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2
#align is_R_or_C.conj_eq_iff_re RCLike.conj_eq_iff_re

theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3
#align is_R_or_C.conj_eq_iff_im RCLike.conj_eq_iff_im

@[simp]
theorem star_def : (Star.star : K → K) = conj :=
  rfl
#align is_R_or_C.star_def RCLike.star_def

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv
#align is_R_or_C.conj_to_ring_equiv RCLike.conjToRingEquiv

variable {K} {z : K}

/-- The norm squared function. -/
def normSq : K →*₀ ℝ where
  toFun z := re z * re z + im z * im z
  map_zero' := by simp only [add_zero, mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring
#align is_R_or_C.norm_sq RCLike.normSq

theorem normSq_apply (z : K) : normSq z = re z * re z + im z * im z :=
  rfl
#align is_R_or_C.norm_sq_apply RCLike.normSq_apply

theorem norm_sq_eq_def {z : K} : ‖z‖ ^ 2 = re z * re z + im z * im z :=
  norm_sq_eq_def_ax z
#align is_R_or_C.norm_sq_eq_def RCLike.norm_sq_eq_def

theorem normSq_eq_def' (z : K) : normSq z = ‖z‖ ^ 2 :=
  norm_sq_eq_def.symm
#align is_R_or_C.norm_sq_eq_def' RCLike.normSq_eq_def'

@[rclike_simps]
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero
#align is_R_or_C.norm_sq_zero RCLike.normSq_zero

@[rclike_simps]
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one
#align is_R_or_C.norm_sq_one RCLike.normSq_one

theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
#align is_R_or_C.norm_sq_nonneg RCLike.normSq_nonneg

@[rclike_simps] -- porting note (#10618): was `simp`
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _
#align is_R_or_C.norm_sq_eq_zero RCLike.normSq_eq_zero

@[simp, rclike_simps]
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm]; simp [normSq_nonneg]
#align is_R_or_C.norm_sq_pos RCLike.normSq_pos

@[simp, rclike_simps]
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]
#align is_R_or_C.norm_sq_neg RCLike.normSq_neg

@[simp, rclike_simps]
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]
#align is_R_or_C.norm_sq_conj RCLike.normSq_conj

@[rclike_simps] -- porting note (#10618): was `simp`
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w
#align is_R_or_C.norm_sq_mul RCLike.normSq_mul

theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, rclike_simps]
  ring
#align is_R_or_C.norm_sq_add RCLike.normSq_add

theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
#align is_R_or_C.re_sq_le_norm_sq RCLike.re_sq_le_normSq

theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
#align is_R_or_C.im_sq_le_norm_sq RCLike.im_sq_le_normSq

theorem mul_conj (z : K) : z * conj z = ‖z‖ ^ 2 := by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]

#align is_R_or_C.mul_conj RCLike.mul_conj

theorem conj_mul (z : K) : conj z * z = ‖z‖ ^ 2 := by rw [mul_comm, mul_conj]
#align is_R_or_C.conj_mul RCLike.conj_mul

lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z :=
  inv_eq_of_mul_eq_one_left $ by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]

theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]
#align is_R_or_C.norm_sq_sub RCLike.normSq_sub

theorem sqrt_normSq_eq_norm {z : K} : √(normSq z) = ‖z‖ := by
  rw [normSq_eq_def', Real.sqrt_sq (norm_nonneg _)]
#align is_R_or_C.sqrt_norm_sq_eq_norm RCLike.sqrt_normSq_eq_norm

/-! ### Inversion -/

@[simp, norm_cast, rclike_simps]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r
#align is_R_or_C.of_real_inv RCLike.ofReal_inv

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, ofReal_inv, ofReal_pow, mul_inv_cancel]
    simpa
#align is_R_or_C.inv_def RCLike.inv_def

@[simp, rclike_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, re_ofReal_mul, conj_re, div_eq_inv_mul]
#align is_R_or_C.inv_re RCLike.inv_re

@[simp, rclike_simps]
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, im_ofReal_mul, conj_im, div_eq_inv_mul]
#align is_R_or_C.inv_im RCLike.inv_im

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg, map_neg,
    rclike_simps]
#align is_R_or_C.div_re RCLike.div_re

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg, map_neg,
    rclike_simps]
#align is_R_or_C.div_im RCLike.div_im

@[rclike_simps] -- porting note (#10618): was `simp`
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _
#align is_R_or_C.conj_inv RCLike.conj_inv

lemma conj_div (x y : K) : conj (x / y) = conj x / conj y := map_div' conj conj_inv _ _

--TODO: Do we rather want the map as an explicit definition?
lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

lemma exists_norm_mul_eq_self (x : K) : ∃ c, ‖c‖ = 1 ∧ c * ‖x‖ = x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

@[simp, norm_cast, rclike_simps]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s
#align is_R_or_C.of_real_div RCLike.ofReal_div

theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, re_ofReal_mul]
#align is_R_or_C.div_re_of_real RCLike.div_re_ofReal

@[simp, norm_cast, rclike_simps]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n
#align is_R_or_C.of_real_zpow RCLike.ofReal_zpow

theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_mul_I_of_nonzero RCLike.I_mul_I_of_nonzero

@[simp, rclike_simps]
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp [I_mul_I_of_nonzero h]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.inv_I RCLike.inv_I

@[simp, rclike_simps]
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.div_I RCLike.div_I

@[rclike_simps] -- porting note (#10618): was `simp`
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z
#align is_R_or_C.norm_sq_inv RCLike.normSq_inv

@[rclike_simps] -- porting note (#10618): was `simp`
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w
#align is_R_or_C.norm_sq_div RCLike.normSq_div

@[rclike_simps] -- porting note (#10618): was `simp`
theorem norm_conj {z : K} : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]
#align is_R_or_C.norm_conj RCLike.norm_conj

instance (priority := 100) : CstarRing K where
  norm_star_mul_self {x} := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) norm_conj

/-! ### Cast lemmas -/

@[simp, rclike_simps, norm_cast]
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n
#align is_R_or_C.of_real_nat_cast RCLike.ofReal_natCast

@[simp, rclike_simps] -- Porting note: removed `norm_cast`
theorem natCast_re (n : ℕ) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]
#align is_R_or_C.nat_cast_re RCLike.natCast_re

@[simp, rclike_simps, norm_cast]
theorem natCast_im (n : ℕ) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]
#align is_R_or_C.nat_cast_im RCLike.natCast_im

-- See note [no_index around OfNat.ofNat]
@[simp, rclike_simps]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : re (no_index (OfNat.ofNat n) : K) = OfNat.ofNat n :=
  natCast_re n

-- See note [no_index around OfNat.ofNat]
@[simp, rclike_simps]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : im (no_index (OfNat.ofNat n) : K) = 0 :=
  natCast_im n

-- See note [no_index around OfNat.ofNat]
@[simp, rclike_simps, norm_cast]
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℝ) : K) = OfNat.ofNat n :=
  ofReal_natCast n

theorem ofNat_mul_re (n : ℕ) [n.AtLeastTwo] (z : K) :
    re (OfNat.ofNat n * z) = OfNat.ofNat n * re z := by
  rw [← ofReal_ofNat, re_ofReal_mul]

theorem ofNat_mul_im (n : ℕ) [n.AtLeastTwo] (z : K) :
    im (OfNat.ofNat n * z) = OfNat.ofNat n * im z := by
  rw [← ofReal_ofNat, im_ofReal_mul]

@[simp, rclike_simps, norm_cast]
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast _ n
#align is_R_or_C.of_real_int_cast RCLike.ofReal_intCast

@[simp, rclike_simps] -- Porting note: removed `norm_cast`
theorem intCast_re (n : ℤ) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]
#align is_R_or_C.int_cast_re RCLike.intCast_re

@[simp, rclike_simps, norm_cast]
theorem intCast_im (n : ℤ) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]
#align is_R_or_C.int_cast_im RCLike.intCast_im

@[simp, rclike_simps, norm_cast]
theorem ofReal_ratCast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast _ n
#align is_R_or_C.of_real_rat_cast RCLike.ofReal_ratCast

@[simp, rclike_simps] -- Porting note: removed `norm_cast`
theorem ratCast_re (q : ℚ) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]
#align is_R_or_C.rat_cast_re RCLike.ratCast_re

@[simp, rclike_simps, norm_cast]
theorem ratCast_im (q : ℚ) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]
#align is_R_or_C.rat_cast_im RCLike.ratCast_im

/-! ### Norm -/

theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)
#align is_R_or_C.norm_of_nonneg RCLike.norm_of_nonneg

@[simp, rclike_simps, norm_cast]
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)
#align is_R_or_C.norm_nat_cast RCLike.norm_natCast

@[simp, rclike_simps]
theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(no_index (OfNat.ofNat n) : K)‖ = OfNat.ofNat n :=
  norm_natCast n

variable (K) in
lemma norm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ := by
  rw [nsmul_eq_smul_cast K, norm_smul, RCLike.norm_natCast, nsmul_eq_mul]

theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]
#align is_R_or_C.mul_self_norm RCLike.mul_self_norm

attribute [rclike_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

-- Porting note: removed @[simp, rclike_simps], b/c generalized to `norm_ofNat`
theorem norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2
#align is_R_or_C.norm_two RCLike.norm_two

theorem abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply re_sq_le_normSq
#align is_R_or_C.abs_re_le_norm RCLike.abs_re_le_norm

theorem abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (abs_nonneg _) (norm_nonneg _), abs_mul_abs_self, mul_self_norm]
  apply im_sq_le_normSq
#align is_R_or_C.abs_im_le_norm RCLike.abs_im_le_norm

theorem norm_re_le_norm (z : K) : ‖re z‖ ≤ ‖z‖ :=
  abs_re_le_norm z
#align is_R_or_C.norm_re_le_norm RCLike.norm_re_le_norm

theorem norm_im_le_norm (z : K) : ‖im z‖ ≤ ‖z‖ :=
  abs_im_le_norm z
#align is_R_or_C.norm_im_le_norm RCLike.norm_im_le_norm

theorem re_le_norm (z : K) : re z ≤ ‖z‖ :=
  (abs_le.1 (abs_re_le_norm z)).2
#align is_R_or_C.re_le_norm RCLike.re_le_norm

theorem im_le_norm (z : K) : im z ≤ ‖z‖ :=
  (abs_le.1 (abs_im_le_norm _)).2
#align is_R_or_C.im_le_norm RCLike.im_le_norm

theorem im_eq_zero_of_le {a : K} (h : ‖a‖ ≤ re a) : im a = 0 := by
  simpa only [mul_self_norm a, normSq_apply, self_eq_add_right, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)
#align is_R_or_C.im_eq_zero_of_le RCLike.im_eq_zero_of_le

theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re, conj_eq_iff_im, im_eq_zero_of_le h]
#align is_R_or_C.re_eq_self_of_le RCLike.re_eq_self_of_le

open IsAbsoluteValue

theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_re_le_norm _) (norm_nonneg _)
#align is_R_or_C.abs_re_div_norm_le_one RCLike.abs_re_div_norm_le_one

theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_im_le_norm _) (norm_nonneg _)
#align is_R_or_C.abs_im_div_norm_le_one RCLike.abs_im_div_norm_le_one

theorem norm_I_of_ne_zero (hI : (I : K) ≠ 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
    I_mul_I_of_nonzero hI, norm_neg, norm_one]
set_option linter.uppercaseLean3 false in
#align is_R_or_C.norm_I_of_ne_zero RCLike.norm_I_of_ne_zero

theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, ← ofReal_pow]; simp [-ofReal_pow]
#align is_R_or_C.re_eq_norm_of_mul_conj RCLike.re_eq_norm_of_mul_conj

theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, ← ofReal_ofNat, ← ofReal_mul, norm_ofReal, sq_abs, ofReal_re]
#align is_R_or_C.norm_sq_re_add_conj RCLike.norm_sq_re_add_conj

theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]
#align is_R_or_C.norm_sq_re_conj_add RCLike.norm_sq_re_conj_add

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)
#align is_R_or_C.is_cau_seq_re RCLike.isCauSeq_re

theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)
#align is_R_or_C.is_cau_seq_im RCLike.isCauSeq_im

/-- The real part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩
#align is_R_or_C.cau_seq_re RCLike.cauSeqRe

/-- The imaginary part of a K Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq K norm) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_im f⟩
#align is_R_or_C.cau_seq_im RCLike.cauSeqIm

theorem isCauSeq_norm {f : ℕ → K} (hf : IsCauSeq norm f) : IsCauSeq abs (norm ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt (abs_norm_sub_norm_le _ _) (hi j hj)⟩
#align is_R_or_C.is_cau_seq_norm RCLike.isCauSeq_norm

end RCLike

section Instances

noncomputable instance Real.RCLike : RCLike ℝ where
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
  conj_im_ax _ := by simp only [neg_zero, AddMonoidHom.zero_apply]
  conj_I_ax := by simp only [RingHom.map_zero, neg_zero]
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax _ := by simp only [mul_zero, AddMonoidHom.zero_apply]
  le_iff_re_im := (and_iff_left rfl).symm
#align real.is_R_or_C Real.RCLike

end Instances

namespace RCLike

section Order

open scoped ComplexOrder
variable {z w : K}

theorem lt_iff_re_im : z < w ↔ re z < re w ∧ im z = im w := by
  simp_rw [lt_iff_le_and_ne, @RCLike.le_iff_re_im K]
  constructor
  · rintro ⟨⟨hr, hi⟩, heq⟩
    exact ⟨⟨hr, mt (fun hreq => ext hreq hi) heq⟩, hi⟩
  · rintro ⟨⟨hr, hrn⟩, hi⟩
    exact ⟨⟨hr, hi⟩, ne_of_apply_ne _ hrn⟩

theorem nonneg_iff : 0 ≤ z ↔ 0 ≤ re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using le_iff_re_im (z := 0) (w := z)

theorem pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0 := by
  simpa only [map_zero, eq_comm] using lt_iff_re_im (z := 0) (w := z)

theorem nonpos_iff : z ≤ 0 ↔ re z ≤ 0 ∧ im z = 0 := by
  simpa only [map_zero] using le_iff_re_im (z := z) (w := 0)

theorem neg_iff : z < 0 ↔ re z < 0 ∧ im z = 0 := by
  simpa only [map_zero] using lt_iff_re_im (z := z) (w := 0)

lemma nonneg_iff_exists_ofReal : 0 ≤ z ↔ ∃ x ≥ (0 : ℝ), x = z := by
  simp_rw [nonneg_iff (K := K), ext_iff (K := K)]; aesop

lemma pos_iff_exists_ofReal : 0 < z ↔ ∃ x > (0 : ℝ), x = z := by
  simp_rw [pos_iff (K := K), ext_iff (K := K)]; aesop

lemma nonpos_iff_exists_ofReal : z ≤ 0 ↔ ∃ x ≤ (0 : ℝ), x = z := by
  simp_rw [nonpos_iff (K := K), ext_iff (K := K)]; aesop

lemma neg_iff_exists_ofReal : z < 0 ↔ ∃ x < (0 : ℝ), x = z := by
  simp_rw [neg_iff (K := K), ext_iff (K := K)]; aesop

@[simp, norm_cast]
lemma ofReal_le_ofReal {x y : ℝ} : (x : K) ≤ (y : K) ↔ x ≤ y := by
  rw [le_iff_re_im]
  simp

@[simp, norm_cast]
lemma ofReal_lt_ofReal {x y : ℝ} : (x : K) < (y : K) ↔ x < y := by
  rw [lt_iff_re_im]
  simp

@[simp, norm_cast]
lemma ofReal_nonneg {x : ℝ} : 0 ≤ (x : K) ↔ 0 ≤ x := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
lemma ofReal_nonpos {x : ℝ} : (x : K) ≤ 0 ↔ x ≤ 0 := by
  rw [← ofReal_zero, ofReal_le_ofReal]

@[simp, norm_cast]
lemma ofReal_pos {x : ℝ} : 0 < (x : K) ↔ 0 < x := by
  rw [← ofReal_zero, ofReal_lt_ofReal]

@[simp, norm_cast]
lemma ofReal_lt_zero {x : ℝ} : (x : K) < 0 ↔ x < 0 := by
  rw [← ofReal_zero, ofReal_lt_ofReal]

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are star ordered rings.
(That is, a star ring in which the nonnegative elements are those of the form `star z * z`.)

Note this is only an instance with `open scoped ComplexOrder`. -/
lemma toStarOrderedRing : StarOrderedRing K :=
  StarOrderedRing.of_nonneg_iff'
    (h_add := fun {x y} hxy z => by
      rw [RCLike.le_iff_re_im] at *
      simpa [map_add, add_le_add_iff_left, add_right_inj] using hxy)
    (h_nonneg_iff := fun x => by
      rw [nonneg_iff]
      refine ⟨fun h ↦ ⟨√(re x), by simp [ext_iff (K := K), h.1, h.2]⟩, ?_⟩
      rintro ⟨s, rfl⟩
      simp [mul_comm, mul_self_nonneg, add_nonneg])

scoped[ComplexOrder] attribute [instance] RCLike.toStarOrderedRing

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
def toStrictOrderedCommRing : StrictOrderedCommRing K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]
  add_le_add_left _ _ := add_le_add_left
  mul_pos z w hz hw := by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]
  mul_comm := by intros; apply ext <;> ring_nf

scoped[ComplexOrder] attribute [instance] RCLike.toStrictOrderedCommRing

theorem toOrderedSMul : OrderedSMul ℝ K :=
  OrderedSMul.mk' fun a b r hab hr => by
    replace hab := hab.le
    rw [RCLike.le_iff_re_im] at hab
    rw [RCLike.le_iff_re_im, smul_re, smul_re, smul_im, smul_im]
    exact hab.imp (fun h => mul_le_mul_of_nonneg_left h hr.le) (congr_arg _)

scoped[ComplexOrder] attribute [instance] RCLike.toOrderedSMul

end Order

open ComplexConjugate

section CleanupLemmas

local notation "reR" => @RCLike.re ℝ _
local notation "imR" => @RCLike.im ℝ _
local notation "IR" => @RCLike.I ℝ _
local notation "normSqR" => @RCLike.normSq ℝ _

@[simp, rclike_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl
#align is_R_or_C.re_to_real RCLike.re_to_real

@[simp, rclike_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl
#align is_R_or_C.im_to_real RCLike.im_to_real

@[rclike_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl
#align is_R_or_C.conj_to_real RCLike.conj_to_real

@[simp, rclike_simps]
theorem I_to_real : IR = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align is_R_or_C.I_to_real RCLike.I_to_real

@[simp, rclike_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [RCLike.normSq]
#align is_R_or_C.norm_sq_to_real RCLike.normSq_to_real

@[simp]
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl
#align is_R_or_C.coe_real_eq_id RCLike.ofReal_real_eq_id

end CleanupLemmas

section LinearMaps

/-- The real part in an `RCLike` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }
#align is_R_or_C.re_lm RCLike.reLm

@[simp, rclike_simps]
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_lm_coe RCLike.reLm_coe

/-- The real part in an `RCLike` field, as a continuous linear map. -/
noncomputable def reCLM : K →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x
#align is_R_or_C.re_clm RCLike.reCLM

@[simp, rclike_simps, norm_cast]
theorem reCLM_coe : ((reCLM : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl
#align is_R_or_C.re_clm_coe RCLike.reCLM_coe

@[simp, rclike_simps]
theorem reCLM_apply : ((reCLM : K →L[ℝ] ℝ) : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_clm_apply RCLike.reCLM_apply

@[continuity, fun_prop]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reCLM.continuous
#align is_R_or_C.continuous_re RCLike.continuous_re

/-- The imaginary part in an `RCLike` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }
#align is_R_or_C.im_lm RCLike.imLm

@[simp, rclike_simps]
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_lm_coe RCLike.imLm_coe

/-- The imaginary part in an `RCLike` field, as a continuous linear map. -/
noncomputable def imCLM : K →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x
#align is_R_or_C.im_clm RCLike.imCLM

@[simp, rclike_simps, norm_cast]
theorem imCLM_coe : ((imCLM : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl
#align is_R_or_C.im_clm_coe RCLike.imCLM_coe

@[simp, rclike_simps]
theorem imCLM_apply : ((imCLM : K →L[ℝ] ℝ) : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_clm_apply RCLike.imCLM_apply

@[continuity, fun_prop]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imCLM.continuous
#align is_R_or_C.continuous_im RCLike.continuous_im

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }
#align is_R_or_C.conj_ae RCLike.conjAe

@[simp, rclike_simps]
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl
#align is_R_or_C.conj_ae_coe RCLike.conjAe_coe

/-- Conjugate as a linear isometry -/
noncomputable def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun _ => norm_conj⟩
#align is_R_or_C.conj_lie RCLike.conjLIE

@[simp, rclike_simps]
theorem conjLIE_apply : (conjLIE : K → K) = conj :=
  rfl
#align is_R_or_C.conj_lie_apply RCLike.conjLIE_apply

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _
#align is_R_or_C.conj_cle RCLike.conjCLE

@[simp, rclike_simps]
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl
#align is_R_or_C.conj_cle_coe RCLike.conjCLE_coe

@[simp, rclike_simps]
theorem conjCLE_apply : (conjCLE : K → K) = conj :=
  rfl
#align is_R_or_C.conj_cle_apply RCLike.conjCLE_apply

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star
#align is_R_or_C.continuous_conj RCLike.continuous_conj

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K
#align is_R_or_C.of_real_am RCLike.ofRealAm

@[simp, rclike_simps]
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_am_coe RCLike.ofRealAm_coe

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal
#align is_R_or_C.of_real_li RCLike.ofRealLI

@[simp, rclike_simps]
theorem ofRealLI_apply : (ofRealLI : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_li_apply RCLike.ofRealLI_apply

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap
#align is_R_or_C.of_real_clm RCLike.ofRealCLM

@[simp, rclike_simps]
theorem ofRealCLM_coe : (@ofRealCLM K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl
#align is_R_or_C.of_real_clm_coe RCLike.ofRealCLM_coe

@[simp, rclike_simps]
theorem ofRealCLM_apply : (ofRealCLM : ℝ → K) = ofReal :=
  rfl
#align is_R_or_C.of_real_clm_apply RCLike.ofRealCLM_apply

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLI.continuous
#align is_R_or_C.continuous_of_real RCLike.continuous_ofReal

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)
#align is_R_or_C.continuous_norm_sq RCLike.continuous_normSq

end LinearMaps

/-!
### ℝ-dependent results

Here we gather results that depend on whether `K` is `ℝ`.
-/
section CaseSpecific

lemma im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0 := by
  rw [← re_add_im z, h]
  simp

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when `RCLike.I = 0`. -/
@[simps]
def realRingEquiv (h : I = (0 : K)) : K ≃+* ℝ where
  toFun := re
  invFun := (↑)
  left_inv x := by nth_rw 2 [← re_add_im x]; simp [h]
  right_inv := ofReal_re
  map_add' := map_add re
  map_mul' := by simp [im_eq_zero h]

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when
`RCLike.I = 0`. -/
@[simps]
noncomputable def realLinearIsometryEquiv (h : I = (0 : K)) : K ≃ₗᵢ[ℝ] ℝ where
  map_smul' := smul_re
  norm_map' z := by rw [← re_add_im z]; simp [- re_add_im, h]
  __ := realRingEquiv h

end CaseSpecific

end RCLike
