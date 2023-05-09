/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module data.is_R_or_C.basic
! leanprover-community/mathlib commit 3f655f5297b030a87d641ad4e825af8d9679eb0b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Analysis.NormedSpace.ContinuousLinearMap

/-!
# `is_R_or_C`: a typeclass for ℝ or ℂ

This file defines the typeclass `is_R_or_C` intended to have only two instances:
ℝ and ℂ. It is meant for definitions and theorems which hold for both the real and the complex case,
and in particular when the real case follows directly from the complex case by setting `re` to `id`,
`im` to zero and so on. Its API follows closely that of ℂ.

Applications include defining inner products and Hilbert spaces for both the real and
complex case. One typically produces the definitions and proof for an arbitrary field of this
typeclass, which basically amounts to doing the complex case, and the two cases then fall out
immediately from the two instances of the class.

The instance for `ℝ` is registered in this file.
The instance for `ℂ` is declared in `analysis.complex.basic`.

## Implementation notes

The coercion from reals into an `is_R_or_C` field is done by registering `algebra_map ℝ K` as
a `has_coe_t`. For this to work, we must proceed carefully to avoid problems involving circular
coercions in the case `K=ℝ`; in particular, we cannot use the plain `has_coe` and must set
priorities carefully. This problem was already solved for `ℕ`, and we copy the solution detailed
in `data/nat/cast`. See also Note [coercion into rings] for more details.

In addition, several lemmas need to be set at priority 900 to make sure that they do not override
their counterparts in `complex.lean` (which causes linter errors).

A few lemmas requiring heavier imports are in `data.is_R_or_C.lemmas`.
-/


open BigOperators

section

-- mathport name: expr𝓚
local notation "𝓚" => algebraMap ℝ _

open ComplexConjugate

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class IsROrC (K : Type _) extends DenselyNormedField K, StarRing K, NormedAlgebra ℝ K,
  CompleteSpace K where
  re : K →+ ℝ
  im : K →+ ℝ
  i : K
  -- Meant to be set to 0 for K=ℝ
  i_re_ax : re I = 0
  i_mul_i_ax : I = 0 ∨ I * I = -1
  re_add_im_ax : ∀ z : K, 𝓚 (re z) + 𝓚 (im z) * I = z
  of_real_re_ax : ∀ r : ℝ, re (𝓚 r) = r
  of_real_im_ax : ∀ r : ℝ, im (𝓚 r) = 0
  mul_re_ax : ∀ z w : K, re (z * w) = re z * re w - im z * im w
  mul_im_ax : ∀ z w : K, im (z * w) = re z * im w + im z * re w
  conj_re_ax : ∀ z : K, re (conj z) = re z
  conj_im_ax : ∀ z : K, im (conj z) = -im z
  conj_i_ax : conj I = -I
  norm_sq_eq_def_ax : ∀ z : K, ‖z‖ ^ 2 = re z * re z + im z * im z
  mul_im_i_ax : ∀ z : K, im z * im I = im z
#align is_R_or_C IsROrC

end

/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment "/--" "Simp attribute for lemmas about `is_R_or_C` -/")]
     "register_simp_attr"
     `is_R_or_C_simps)-/-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp attribute for lemmas about `is_R_or_C` -/ register_simp_attr is_R_or_C_simps

variable {K E : Type _} [IsROrC K]

namespace IsROrC

open ComplexConjugate

/- The priority must be set at 900 to ensure that coercions are tried in the right order.
See Note [coercion into rings], or `data/nat/cast.lean` for more details. -/
noncomputable instance (priority := 900) algebraMapCoe : CoeTC ℝ K :=
  ⟨algebraMap ℝ K⟩
#align is_R_or_C.algebra_map_coe IsROrC.algebraMapCoe

theorem of_real_alg (x : ℝ) : (x : K) = x • (1 : K) :=
  Algebra.algebraMap_eq_smul_one x
#align is_R_or_C.of_real_alg IsROrC.of_real_alg

theorem real_smul_eq_coe_mul (r : ℝ) (z : K) : r • z = (r : K) * z :=
  Algebra.smul_def r z
#align is_R_or_C.real_smul_eq_coe_mul IsROrC.real_smul_eq_coe_mul

theorem real_smul_eq_coe_smul [AddCommGroup E] [Module K E] [Module ℝ E] [IsScalarTower ℝ K E]
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [IsROrC.of_real_alg, smul_one_smul]
#align is_R_or_C.real_smul_eq_coe_smul IsROrC.real_smul_eq_coe_smul

theorem algebraMap_eq_of_real : ⇑(algebraMap ℝ K) = coe :=
  rfl
#align is_R_or_C.algebra_map_eq_of_real IsROrC.algebraMap_eq_of_real

@[simp, is_R_or_C_simps]
theorem re_add_im (z : K) : (re z : K) + im z * i = z :=
  IsROrC.re_add_im_ax z
#align is_R_or_C.re_add_im IsROrC.re_add_im

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_re : ∀ r : ℝ, re (r : K) = r :=
  IsROrC.of_real_re_ax
#align is_R_or_C.of_real_re IsROrC.of_real_re

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_im : ∀ r : ℝ, im (r : K) = 0 :=
  IsROrC.of_real_im_ax
#align is_R_or_C.of_real_im IsROrC.of_real_im

@[simp, is_R_or_C_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  IsROrC.mul_re_ax
#align is_R_or_C.mul_re IsROrC.mul_re

@[simp, is_R_or_C_simps]
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
theorem of_real_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero
#align is_R_or_C.of_real_zero IsROrC.of_real_zero

@[is_R_or_C_simps]
theorem zero_re' : re (0 : K) = (0 : ℝ) :=
  map_zero re
#align is_R_or_C.zero_re' IsROrC.zero_re'

@[norm_cast]
theorem of_real_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)
#align is_R_or_C.of_real_one IsROrC.of_real_one

@[simp, is_R_or_C_simps]
theorem one_re : re (1 : K) = 1 := by rw [← of_real_one, of_real_re]
#align is_R_or_C.one_re IsROrC.one_re

@[simp, is_R_or_C_simps]
theorem one_im : im (1 : K) = 0 := by rw [← of_real_one, of_real_im]
#align is_R_or_C.one_im IsROrC.one_im

theorem of_real_injective : Function.Injective (coe : ℝ → K) :=
  (algebraMap ℝ K).Injective
#align is_R_or_C.of_real_injective IsROrC.of_real_injective

@[norm_cast]
theorem of_real_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj
#align is_R_or_C.of_real_inj IsROrC.of_real_inj

@[simp, is_R_or_C_simps]
theorem bit0_re (z : K) : re (bit0 z) = bit0 (re z) :=
  map_bit0 _ _
#align is_R_or_C.bit0_re IsROrC.bit0_re

@[simp, is_R_or_C_simps]
theorem bit1_re (z : K) : re (bit1 z) = bit1 (re z) := by simp only [bit1, map_add, bit0_re, one_re]
#align is_R_or_C.bit1_re IsROrC.bit1_re

@[simp, is_R_or_C_simps]
theorem bit0_im (z : K) : im (bit0 z) = bit0 (im z) :=
  map_bit0 _ _
#align is_R_or_C.bit0_im IsROrC.bit0_im

@[simp, is_R_or_C_simps]
theorem bit1_im (z : K) : im (bit1 z) = bit0 (im z) := by
  simp only [bit1, map_add, bit0_im, one_im, add_zero]
#align is_R_or_C.bit1_im IsROrC.bit1_im

theorem of_real_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.lift_map_eq_zero_iff x
#align is_R_or_C.of_real_eq_zero IsROrC.of_real_eq_zero

theorem of_real_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  of_real_eq_zero.Not
#align is_R_or_C.of_real_ne_zero IsROrC.of_real_ne_zero

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _
#align is_R_or_C.of_real_add IsROrC.of_real_add

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : K) = bit0 (r : K) :=
  of_real_add _ _
#align is_R_or_C.of_real_bit0 IsROrC.of_real_bit0

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : K) = bit1 (r : K) :=
  map_bit1 (algebraMap ℝ K) r
#align is_R_or_C.of_real_bit1 IsROrC.of_real_bit1

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r
#align is_R_or_C.of_real_neg IsROrC.of_real_neg

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s
#align is_R_or_C.of_real_sub IsROrC.of_real_sub

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_sum {α : Type _} (s : Finset α) (f : α → ℝ) :
    ((∑ i in s, f i : ℝ) : K) = ∑ i in s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _
#align is_R_or_C.of_real_sum IsROrC.of_real_sum

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_finsupp_sum {α M : Type _} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.Sum fun a b => g a b : ℝ) : K) = f.Sum fun a b => (g a b : K) :=
  map_finsupp_sum (algebraMap ℝ K) f g
#align is_R_or_C.of_real_finsupp_sum IsROrC.of_real_finsupp_sum

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _
#align is_R_or_C.of_real_mul IsROrC.of_real_mul

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = r ^ n :=
  map_pow (algebraMap ℝ K) r n
#align is_R_or_C.of_real_pow IsROrC.of_real_pow

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_prod {α : Type _} (s : Finset α) (f : α → ℝ) :
    ((∏ i in s, f i : ℝ) : K) = ∏ i in s, (f i : K) :=
  RingHom.map_prod _ _ _
#align is_R_or_C.of_real_prod IsROrC.of_real_prod

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_finsupp_prod {α M : Type _} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.Prod fun a b => g a b : ℝ) : K) = f.Prod fun a b => (g a b : K) :=
  RingHom.map_finsupp_prod _ f g
#align is_R_or_C.of_real_finsupp_prod IsROrC.of_real_finsupp_prod

@[simp, norm_cast, is_R_or_C_simps]
theorem real_smul_of_real (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _
#align is_R_or_C.real_smul_of_real IsROrC.real_smul_of_real

@[is_R_or_C_simps]
theorem of_real_mul_re (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, of_real_im, MulZeroClass.zero_mul, of_real_re, sub_zero]
#align is_R_or_C.of_real_mul_re IsROrC.of_real_mul_re

@[is_R_or_C_simps]
theorem of_real_mul_im (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, of_real_im, MulZeroClass.zero_mul, of_real_re, mul_im]
#align is_R_or_C.of_real_mul_im IsROrC.of_real_mul_im

@[is_R_or_C_simps]
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, of_real_mul_re]
#align is_R_or_C.smul_re IsROrC.smul_re

@[is_R_or_C_simps]
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, of_real_mul_im]
#align is_R_or_C.smul_im IsROrC.smul_im

@[simp, norm_cast, is_R_or_C_simps]
theorem norm_of_real (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r
#align is_R_or_C.norm_of_real IsROrC.norm_of_real

/-! ### Characteristic zero -/


-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero.  -/
instance (priority := 100) charZero_R_or_C : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).Injective).1 inferInstance
#align is_R_or_C.char_zero_R_or_C IsROrC.charZero_R_or_C

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
@[simp, is_R_or_C_simps]
theorem i_re : re (i : K) = 0 :=
  i_re_ax
#align is_R_or_C.I_re IsROrC.i_re

@[simp, is_R_or_C_simps]
theorem i_im (z : K) : im z * im (i : K) = im z :=
  mul_im_i_ax z
#align is_R_or_C.I_im IsROrC.i_im

@[simp, is_R_or_C_simps]
theorem i_im' (z : K) : im (i : K) * im z = im z := by rw [mul_comm, I_im _]
#align is_R_or_C.I_im' IsROrC.i_im'

@[simp, is_R_or_C_simps]
theorem i_mul_re (z : K) : re (i * z) = -im z := by
  simp only [I_re, zero_sub, I_im', MulZeroClass.zero_mul, mul_re]
#align is_R_or_C.I_mul_re IsROrC.i_mul_re

theorem i_mul_i : (i : K) = 0 ∨ (i : K) * i = -1 :=
  i_mul_i_ax
#align is_R_or_C.I_mul_I IsROrC.i_mul_i

@[simp, is_R_or_C_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  IsROrC.conj_re_ax z
#align is_R_or_C.conj_re IsROrC.conj_re

@[simp, is_R_or_C_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  IsROrC.conj_im_ax z
#align is_R_or_C.conj_im IsROrC.conj_im

@[simp, is_R_or_C_simps]
theorem conj_i : conj (i : K) = -i :=
  IsROrC.conj_i_ax
#align is_R_or_C.conj_I IsROrC.conj_i

@[simp, is_R_or_C_simps]
theorem conj_of_real (r : ℝ) : conj (r : K) = (r : K) :=
  by
  rw [ext_iff]
  simp only [of_real_im, conj_im, eq_self_iff_true, conj_re, and_self_iff, neg_zero]
#align is_R_or_C.conj_of_real IsROrC.conj_of_real

@[simp, is_R_or_C_simps]
theorem conj_bit0 (z : K) : conj (bit0 z) = bit0 (conj z) :=
  map_bit0 _ _
#align is_R_or_C.conj_bit0 IsROrC.conj_bit0

@[simp, is_R_or_C_simps]
theorem conj_bit1 (z : K) : conj (bit1 z) = bit1 (conj z) :=
  map_bit1 _ _
#align is_R_or_C.conj_bit1 IsROrC.conj_bit1

@[simp, is_R_or_C_simps]
theorem conj_neg_i : conj (-i) = (i : K) := by rw [map_neg, conj_I, neg_neg]
#align is_R_or_C.conj_neg_I IsROrC.conj_neg_i

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * i :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_of_real, conj_of_real, mul_neg, sub_eq_add_neg]
#align is_R_or_C.conj_eq_re_sub_im IsROrC.conj_eq_re_sub_im

theorem sub_conj (z : K) : z - conj z = 2 * im z * i :=
  by
  nth_rw 1 [← re_add_im z]
  rw [conj_eq_re_sub_im, add_sub_sub_cancel, ← two_mul, mul_assoc]
#align is_R_or_C.sub_conj IsROrC.sub_conj

@[is_R_or_C_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, of_real_mul, of_real_mul,
    real_smul_eq_coe_mul, mul_sub, mul_assoc]
#align is_R_or_C.conj_smul IsROrC.conj_smul

theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * i + (re z - im z * i) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]
    
#align is_R_or_C.add_conj IsROrC.add_conj

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left (re z : K) two_ne_zero]
#align is_R_or_C.re_eq_add_conj IsROrC.re_eq_add_conj

theorem im_eq_conj_sub (z : K) : ↑(im z) = i * (conj z - z) / 2 := by
  rw [← neg_inj, ← of_real_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]
#align is_R_or_C.im_eq_conj_sub IsROrC.im_eq_conj_sub

/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
theorem is_real_tFAE (z : K) : TFAE [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0] :=
  by
  tfae_have 1 → 4
  · intro h
    rw [← @of_real_inj K, im_eq_conj_sub, h, sub_self, MulZeroClass.mul_zero, zero_div,
      of_real_zero]
  tfae_have 4 → 3
  · intro h
    conv_rhs => rw [← re_add_im z, h, of_real_zero, MulZeroClass.zero_mul, add_zero]
  tfae_have 3 → 2; exact fun h => ⟨_, h⟩
  tfae_have 2 → 1; exact fun ⟨r, hr⟩ => hr ▸ conj_of_real _
  tfae_finish
#align is_R_or_C.is_real_tfae IsROrC.is_real_tFAE

theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  ((is_real_tFAE z).out 0 1).trans <| by simp only [eq_comm]
#align is_R_or_C.conj_eq_iff_real IsROrC.conj_eq_iff_real

theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_tFAE z).out 0 2
#align is_R_or_C.conj_eq_iff_re IsROrC.conj_eq_iff_re

theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_tFAE z).out 0 3
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
  map_zero' := by simp only [add_zero, MulZeroClass.mul_zero, map_zero]
  map_one' := by simp only [one_im, add_zero, mul_one, one_re, MulZeroClass.mul_zero]
  map_mul' z w := by
    simp only [mul_im, mul_re]
    ring
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

@[is_R_or_C_simps]
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero
#align is_R_or_C.norm_sq_zero IsROrC.normSq_zero

@[is_R_or_C_simps]
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one
#align is_R_or_C.norm_sq_one IsROrC.normSq_one

theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
#align is_R_or_C.norm_sq_nonneg IsROrC.normSq_nonneg

@[simp, is_R_or_C_simps]
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  by
  rw [norm_sq_eq_def']
  simp [sq]
#align is_R_or_C.norm_sq_eq_zero IsROrC.normSq_eq_zero

@[simp, is_R_or_C_simps]
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm] <;> simp [norm_sq_nonneg]
#align is_R_or_C.norm_sq_pos IsROrC.normSq_pos

@[simp, is_R_or_C_simps]
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [norm_sq_eq_def', norm_neg]
#align is_R_or_C.norm_sq_neg IsROrC.normSq_neg

@[simp, is_R_or_C_simps]
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [norm_sq_apply, neg_mul, mul_neg, neg_neg, is_R_or_C_simps]
#align is_R_or_C.norm_sq_conj IsROrC.normSq_conj

@[simp, is_R_or_C_simps]
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w
#align is_R_or_C.norm_sq_mul IsROrC.normSq_mul

theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) :=
  by
  simp only [norm_sq_apply, map_add, mul_neg, sub_neg_eq_add, is_R_or_C_simps]
  ring
#align is_R_or_C.norm_sq_add IsROrC.normSq_add

theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
#align is_R_or_C.re_sq_le_norm_sq IsROrC.re_sq_le_normSq

theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
#align is_R_or_C.im_sq_le_norm_sq IsROrC.im_sq_le_normSq

theorem mul_conj (z : K) : z * conj z = (normSq z : K) := by
  simp only [map_add, add_zero, ext_iff, add_left_inj, mul_eq_mul_left_iff, MulZeroClass.zero_mul,
    add_comm, true_or_iff, eq_self_iff_true, mul_neg, add_right_neg, zero_add, norm_sq_apply,
    mul_comm, and_self_iff, neg_neg, MulZeroClass.mul_zero, sub_eq_neg_add, neg_zero,
    is_R_or_C_simps]
#align is_R_or_C.mul_conj IsROrC.mul_conj

theorem conj_mul (x : K) : conj x * x = (normSq x : K) := by rw [mul_comm, mul_conj]
#align is_R_or_C.conj_mul IsROrC.conj_mul

theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [norm_sq_add, sub_eq_add_neg, RingEquiv.map_neg, mul_neg, norm_sq_neg, map_neg]
#align is_R_or_C.norm_sq_sub IsROrC.normSq_sub

theorem sqrt_normSq_eq_norm {z : K} : Real.sqrt (normSq z) = ‖z‖ := by
  rw [norm_sq_eq_def', Real.sqrt_sq (norm_nonneg _)]
#align is_R_or_C.sqrt_norm_sq_eq_norm IsROrC.sqrt_normSq_eq_norm

/-! ### Inversion -/


@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = r⁻¹ :=
  map_inv₀ (algebraMap ℝ K) r
#align is_R_or_C.of_real_inv IsROrC.of_real_inv

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) :=
  by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, of_real_inv, ← norm_sq_eq_def', mul_inv_cancel]
    rwa [of_real_ne_zero, Ne.def, norm_sq_eq_zero]
#align is_R_or_C.inv_def IsROrC.inv_def

@[simp, is_R_or_C_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, norm_sq_eq_def', mul_comm, of_real_mul_re, conj_re, div_eq_inv_mul]
#align is_R_or_C.inv_re IsROrC.inv_re

@[simp, is_R_or_C_simps]
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, norm_sq_eq_def', mul_comm, of_real_mul_im, conj_im, div_eq_inv_mul]
#align is_R_or_C.inv_im IsROrC.inv_im

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg, map_neg,
    is_R_or_C_simps]
#align is_R_or_C.div_re IsROrC.div_re

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg, map_neg,
    is_R_or_C_simps]
#align is_R_or_C.div_im IsROrC.div_im

@[simp, is_R_or_C_simps]
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _
#align is_R_or_C.conj_inv IsROrC.conj_inv

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s
#align is_R_or_C.of_real_div IsROrC.of_real_div

theorem div_re_of_real {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← of_real_inv, of_real_mul_re]
#align is_R_or_C.div_re_of_real IsROrC.div_re_of_real

@[simp, norm_cast, is_R_or_C_simps]
theorem of_real_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = r ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n
#align is_R_or_C.of_real_zpow IsROrC.of_real_zpow

theorem i_mul_i_of_nonzero : (i : K) ≠ 0 → (i : K) * i = -1 :=
  i_mul_i_ax.resolve_left
#align is_R_or_C.I_mul_I_of_nonzero IsROrC.i_mul_i_of_nonzero

@[simp, is_R_or_C_simps]
theorem inv_i : (i : K)⁻¹ = -i := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp [I_mul_I_of_nonzero h]
#align is_R_or_C.inv_I IsROrC.inv_i

@[simp, is_R_or_C_simps]
theorem div_i (z : K) : z / i = -(z * i) := by rw [div_eq_mul_inv, inv_I, mul_neg]
#align is_R_or_C.div_I IsROrC.div_i

@[simp, is_R_or_C_simps]
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ (@normSq K _) z
#align is_R_or_C.norm_sq_inv IsROrC.normSq_inv

@[simp, is_R_or_C_simps]
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ (@normSq K _) z w
#align is_R_or_C.norm_sq_div IsROrC.normSq_div

@[simp, is_R_or_C_simps]
theorem norm_conj {z : K} : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_norm_sq_eq_norm, norm_sq_conj]
#align is_R_or_C.norm_conj IsROrC.norm_conj

instance (priority := 100) : CstarRing K
    where norm_star_mul_self x := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) norm_conj

/-! ### Cast lemmas -/


@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n
#align is_R_or_C.of_real_nat_cast IsROrC.of_real_nat_cast

@[simp, is_R_or_C_simps, norm_cast]
theorem nat_cast_re (n : ℕ) : re (n : K) = n := by rw [← of_real_nat_cast, of_real_re]
#align is_R_or_C.nat_cast_re IsROrC.nat_cast_re

@[simp, is_R_or_C_simps, norm_cast]
theorem nat_cast_im (n : ℕ) : im (n : K) = 0 := by rw [← of_real_nat_cast, of_real_im]
#align is_R_or_C.nat_cast_im IsROrC.nat_cast_im

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast (algebraMap ℝ K) n
#align is_R_or_C.of_real_int_cast IsROrC.of_real_int_cast

@[simp, is_R_or_C_simps, norm_cast]
theorem int_cast_re (n : ℤ) : re (n : K) = n := by rw [← of_real_int_cast, of_real_re]
#align is_R_or_C.int_cast_re IsROrC.int_cast_re

@[simp, is_R_or_C_simps, norm_cast]
theorem int_cast_im (n : ℤ) : im (n : K) = 0 := by rw [← of_real_int_cast, of_real_im]
#align is_R_or_C.int_cast_im IsROrC.int_cast_im

@[simp, is_R_or_C_simps, norm_cast]
theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast (algebraMap ℝ K) n
#align is_R_or_C.of_real_rat_cast IsROrC.of_real_rat_cast

@[simp, is_R_or_C_simps, norm_cast]
theorem rat_cast_re (q : ℚ) : re (q : K) = q := by rw [← of_real_rat_cast, of_real_re]
#align is_R_or_C.rat_cast_re IsROrC.rat_cast_re

@[simp, is_R_or_C_simps, norm_cast]
theorem rat_cast_im (q : ℚ) : im (q : K) = 0 := by rw [← of_real_rat_cast, of_real_im]
#align is_R_or_C.rat_cast_im IsROrC.rat_cast_im

/-! ### Norm -/


theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_of_real _).trans (abs_of_nonneg h)
#align is_R_or_C.norm_of_nonneg IsROrC.norm_of_nonneg

@[simp, is_R_or_C_simps, norm_cast]
theorem norm_nat_cast (n : ℕ) : ‖(n : K)‖ = n :=
  by
  rw [← of_real_nat_cast]
  exact norm_of_nonneg (Nat.cast_nonneg n)
#align is_R_or_C.norm_nat_cast IsROrC.norm_nat_cast

theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [norm_sq_eq_def', sq]
#align is_R_or_C.mul_self_norm IsROrC.mul_self_norm

attribute [is_R_or_C_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

@[simp, is_R_or_C_simps]
theorem norm_two : ‖(2 : K)‖ = 2 := by rw [← Nat.cast_two, norm_nat_cast, Nat.cast_two]
#align is_R_or_C.norm_two IsROrC.norm_two

theorem abs_re_le_norm (z : K) : |re z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (re z)) (norm_nonneg _), abs_mul_abs_self,
      mul_self_norm] <;>
    apply re_sq_le_norm_sq
#align is_R_or_C.abs_re_le_norm IsROrC.abs_re_le_norm

theorem abs_im_le_norm (z : K) : |im z| ≤ ‖z‖ := by
  rw [mul_self_le_mul_self_iff (_root_.abs_nonneg (im z)) (norm_nonneg _), abs_mul_abs_self,
      mul_self_norm] <;>
    apply im_sq_le_norm_sq
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
  simpa only [mul_self_norm a, norm_sq_apply, self_eq_add_right, mul_self_eq_zero] using
    congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)
#align is_R_or_C.im_eq_zero_of_le IsROrC.im_eq_zero_of_le

theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [(is_real_tfae a).out 2 3, im_eq_zero_of_le h]
#align is_R_or_C.re_eq_self_of_le IsROrC.re_eq_self_of_le

open IsAbsoluteValue

theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 :=
  by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_re_le_norm _) (norm_nonneg _)
#align is_R_or_C.abs_re_div_norm_le_one IsROrC.abs_re_div_norm_le_one

theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 :=
  by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le (abs_im_le_norm _) (norm_nonneg _)
#align is_R_or_C.abs_im_div_norm_le_one IsROrC.abs_im_div_norm_le_one

theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, of_real_re, norm_of_real, abs_of_nonneg (norm_sq_nonneg _)]
#align is_R_or_C.re_eq_norm_of_mul_conj IsROrC.re_eq_norm_of_mul_conj

theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, norm_mul, norm_two, norm_of_real, two_mul (re x : K), map_add, of_real_re, ←
    two_mul, mul_pow, mul_pow, sq_abs]
#align is_R_or_C.norm_sq_re_add_conj IsROrC.norm_sq_re_add_conj

theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]
#align is_R_or_C.norm_sq_re_conj_add IsROrC.norm_sq_re_conj_add

/-! ### Cauchy sequences -/


theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun ε ε0 =>
  (f.Cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)
#align is_R_or_C.is_cau_seq_re IsROrC.isCauSeq_re

theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun ε ε0 =>
  (f.Cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_im_le_norm (f j - f i)) (H _ ij)
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

noncomputable instance Real.isROrC : IsROrC ℝ :=
  { Real.denselyNormedField,
    Real.metricSpace with
    re := AddMonoidHom.id ℝ
    im := 0
    i := 0
    i_re_ax := by simp only [AddMonoidHom.map_zero]
    i_mul_i_ax := Or.intro_left _ rfl
    re_add_im_ax := fun z => by
      simp only [add_zero, MulZeroClass.mul_zero, Algebra.id.map_eq_id, RingHom.id_apply,
        AddMonoidHom.id_apply]
    of_real_re_ax := fun r => by simp only [AddMonoidHom.id_apply, Algebra.id.map_eq_self]
    of_real_im_ax := fun r => by simp only [AddMonoidHom.zero_apply]
    mul_re_ax := fun z w => by
      simp only [sub_zero, MulZeroClass.mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
    mul_im_ax := fun z w => by
      simp only [add_zero, MulZeroClass.zero_mul, MulZeroClass.mul_zero, AddMonoidHom.zero_apply]
    conj_re_ax := fun z => by simp only [starRingEnd_apply, star_id_of_comm]
    conj_im_ax := fun z => by simp only [neg_zero, AddMonoidHom.zero_apply]
    conj_i_ax := by simp only [RingHom.map_zero, neg_zero]
    norm_sq_eq_def_ax := fun z => by
      simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero, MulZeroClass.mul_zero,
        AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
    mul_im_i_ax := fun z => by simp only [MulZeroClass.mul_zero, AddMonoidHom.zero_apply] }
#align real.is_R_or_C Real.isROrC

end Instances

namespace IsROrC

open ComplexConjugate

section CleanupLemmas

-- mathport name: exprreR
local notation "reR" => @IsROrC.re ℝ _

-- mathport name: exprimR
local notation "imR" => @IsROrC.im ℝ _

-- mathport name: exprIR
local notation "IR" => @IsROrC.i ℝ _

-- mathport name: exprnorm_sqR
local notation "norm_sqR" => @IsROrC.normSq ℝ _

@[simp, is_R_or_C_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl
#align is_R_or_C.re_to_real IsROrC.re_to_real

@[simp, is_R_or_C_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl
#align is_R_or_C.im_to_real IsROrC.im_to_real

@[simp, is_R_or_C_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl
#align is_R_or_C.conj_to_real IsROrC.conj_to_real

@[simp, is_R_or_C_simps]
theorem i_to_real : IR = 0 :=
  rfl
#align is_R_or_C.I_to_real IsROrC.i_to_real

@[simp, is_R_or_C_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [IsROrC.normSq]
#align is_R_or_C.norm_sq_to_real IsROrC.normSq_to_real

@[simp]
theorem coe_real_eq_id : @coe ℝ ℝ _ = id :=
  rfl
#align is_R_or_C.coe_real_eq_id IsROrC.coe_real_eq_id

end CleanupLemmas

section LinearMaps

/-- The real part in a `is_R_or_C` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }
#align is_R_or_C.re_lm IsROrC.reLm

@[simp, is_R_or_C_simps]
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_lm_coe IsROrC.reLm_coe

/-- The real part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def reClm : K →L[ℝ] ℝ :=
  LinearMap.mkContinuous reLm 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x
#align is_R_or_C.re_clm IsROrC.reClm

@[simp, is_R_or_C_simps, norm_cast]
theorem reClm_coe : ((reClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl
#align is_R_or_C.re_clm_coe IsROrC.reClm_coe

@[simp, is_R_or_C_simps]
theorem reClm_apply : ((reClm : K →L[ℝ] ℝ) : K → ℝ) = re :=
  rfl
#align is_R_or_C.re_clm_apply IsROrC.reClm_apply

@[continuity]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reClm.Continuous
#align is_R_or_C.continuous_re IsROrC.continuous_re

/-- The imaginary part in a `is_R_or_C` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }
#align is_R_or_C.im_lm IsROrC.imLm

@[simp, is_R_or_C_simps]
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_lm_coe IsROrC.imLm_coe

/-- The imaginary part in a `is_R_or_C` field, as a continuous linear map. -/
noncomputable def imClm : K →L[ℝ] ℝ :=
  LinearMap.mkContinuous imLm 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x
#align is_R_or_C.im_clm IsROrC.imClm

@[simp, is_R_or_C_simps, norm_cast]
theorem imClm_coe : ((imClm : K →L[ℝ] ℝ) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl
#align is_R_or_C.im_clm_coe IsROrC.imClm_coe

@[simp, is_R_or_C_simps]
theorem imClm_apply : ((imClm : K →L[ℝ] ℝ) : K → ℝ) = im :=
  rfl
#align is_R_or_C.im_clm_apply IsROrC.imClm_apply

@[continuity]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imClm.Continuous
#align is_R_or_C.continuous_im IsROrC.continuous_im

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_of_real }
#align is_R_or_C.conj_ae IsROrC.conjAe

@[simp, is_R_or_C_simps]
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl
#align is_R_or_C.conj_ae_coe IsROrC.conjAe_coe

/-- Conjugate as a linear isometry -/
noncomputable def conjLie : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, fun _ => norm_conj⟩
#align is_R_or_C.conj_lie IsROrC.conjLie

@[simp, is_R_or_C_simps]
theorem conjLie_apply : (conjLie : K → K) = conj :=
  rfl
#align is_R_or_C.conj_lie_apply IsROrC.conjLie_apply

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCle : K ≃L[ℝ] K :=
  @conjLie K _
#align is_R_or_C.conj_cle IsROrC.conjCle

@[simp, is_R_or_C_simps]
theorem conjCle_coe : (@conjCle K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl
#align is_R_or_C.conj_cle_coe IsROrC.conjCle_coe

@[simp, is_R_or_C_simps]
theorem conjCle_apply : (conjCle : K → K) = conj :=
  rfl
#align is_R_or_C.conj_cle_apply IsROrC.conjCle_apply

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLie.Continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star
#align is_R_or_C.continuous_conj IsROrC.continuous_conj

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K
#align is_R_or_C.of_real_am IsROrC.ofRealAm

@[simp, is_R_or_C_simps]
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = coe :=
  rfl
#align is_R_or_C.of_real_am_coe IsROrC.ofRealAm_coe

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLi : ℝ →ₗᵢ[ℝ] K
    where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_of_real
#align is_R_or_C.of_real_li IsROrC.ofRealLi

@[simp, is_R_or_C_simps]
theorem ofRealLi_apply : (ofRealLi : ℝ → K) = coe :=
  rfl
#align is_R_or_C.of_real_li_apply IsROrC.ofRealLi_apply

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealClm : ℝ →L[ℝ] K :=
  ofRealLi.toContinuousLinearMap
#align is_R_or_C.of_real_clm IsROrC.ofRealClm

@[simp, is_R_or_C_simps]
theorem ofRealClm_coe : (@ofRealClm K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl
#align is_R_or_C.of_real_clm_coe IsROrC.ofRealClm_coe

@[simp, is_R_or_C_simps]
theorem ofRealClm_apply : (ofRealClm : ℝ → K) = coe :=
  rfl
#align is_R_or_C.of_real_clm_apply IsROrC.ofRealClm_apply

@[continuity]
theorem continuous_of_real : Continuous (coe : ℝ → K) :=
  ofRealLi.Continuous
#align is_R_or_C.continuous_of_real IsROrC.continuous_of_real

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)
#align is_R_or_C.continuous_norm_sq IsROrC.continuous_normSq

end LinearMaps

end IsROrC

