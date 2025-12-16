/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.BigOperators.Balance
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

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

A few lemmas requiring heavier imports are in `Mathlib/Analysis/RCLike/Lemmas.lean`.
-/

@[expose] public section

open Fintype
open scoped BigOperators ComplexConjugate

section

local notation "𝓚" => algebraMap ℝ _

/--
This typeclass captures properties shared by ℝ and ℂ, with an API that closely matches that of ℂ.
-/
class RCLike (K : semiOutParam Type*) extends DenselyNormedField K, StarRing K,
    NormedAlgebra ℝ K, CompleteSpace K where
  /-- The real part as an additive monoid homomorphism -/
  re : K →+ ℝ
  /-- The imaginary part as an additive monoid homomorphism -/
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
  /-- only an instance in the `ComplexOrder` scope -/
  [toPartialOrder : PartialOrder K]
  le_iff_re_im {z w : K} : z ≤ w ↔ re z ≤ re w ∧ im z = im w
  -- note we cannot put this in the `extends` clause
  [toDecidableEq : DecidableEq K]

scoped[ComplexOrder] attribute [instance 100] RCLike.toPartialOrder
attribute [instance 100] RCLike.toDecidableEq

end

variable {K E : Type*} [RCLike K]

namespace RCLike

/-- Coercion from `ℝ` to an `RCLike` field. -/
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
    (r : ℝ) (x : E) : r • x = (r : K) • x := by rw [RCLike.ofReal_alg, smul_one_smul]

theorem algebraMap_eq_ofReal : ⇑(algebraMap ℝ K) = ofReal :=
  rfl

@[simp, rclike_simps]
theorem re_add_im (z : K) : (re z : K) + im z * I = z :=
  RCLike.re_add_im_ax z

@[simp, norm_cast, rclike_simps]
theorem ofReal_re : ∀ r : ℝ, re (r : K) = r :=
  RCLike.ofReal_re_ax

@[simp, norm_cast, rclike_simps]
theorem ofReal_im : ∀ r : ℝ, im (r : K) = 0 :=
  RCLike.ofReal_im_ax

@[simp, rclike_simps]
theorem mul_re : ∀ z w : K, re (z * w) = re z * re w - im z * im w :=
  RCLike.mul_re_ax

@[simp, rclike_simps]
theorem mul_im : ∀ z w : K, im (z * w) = re z * im w + im z * re w :=
  RCLike.mul_im_ax

theorem ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ => re_add_im z ▸ re_add_im w ▸ h₁ ▸ h₂ ▸ rfl⟩

theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
  ext_iff.2 ⟨hre, him⟩

@[norm_cast]
theorem ofReal_zero : ((0 : ℝ) : K) = 0 :=
  algebraMap.coe_zero

@[rclike_simps]
theorem zero_re : re (0 : K) = (0 : ℝ) :=
  map_zero re

@[deprecated (since := "2025-05-29")]
alias zero_re' := zero_re

@[rclike_simps]
theorem zero_im : im (0 : K) = (0 : ℝ) :=
  map_zero im

@[norm_cast]
theorem ofReal_one : ((1 : ℝ) : K) = 1 :=
  map_one (algebraMap ℝ K)

@[simp, rclike_simps]
theorem one_re : re (1 : K) = 1 := by rw [← ofReal_one, ofReal_re]

@[simp, rclike_simps]
theorem one_im : im (1 : K) = 0 := by rw [← ofReal_one, ofReal_im]

theorem ofReal_injective : Function.Injective ((↑) : ℝ → K) :=
  (algebraMap ℝ K).injective

@[norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : K) = (w : K) ↔ z = w :=
  algebraMap.coe_inj _ _

theorem ofReal_eq_zero {x : ℝ} : (x : K) = 0 ↔ x = 0 :=
  algebraMap.coe_eq_zero_iff _ _ _

theorem ofReal_ne_zero {x : ℝ} : (x : K) ≠ 0 ↔ x ≠ 0 :=
  ofReal_eq_zero.not

@[rclike_simps, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : K) = r + s :=
  algebraMap.coe_add _ _

@[rclike_simps, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : K) = -r :=
  algebraMap.coe_neg r

@[rclike_simps, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : K) = r - s :=
  map_sub (algebraMap ℝ K) r s

@[rclike_simps, norm_cast]
theorem ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : K) = ∑ i ∈ s, (f i : K) :=
  map_sum (algebraMap ℝ K) _ _

@[simp, rclike_simps, norm_cast]
theorem ofReal_finsupp_sum {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.sum fun a b => g a b : ℝ) : K) = f.sum fun a b => (g a b : K) :=
  map_finsuppSum (algebraMap ℝ K) f g

@[rclike_simps, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : K) = r * s :=
  algebraMap.coe_mul _ _

@[rclike_simps, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_pow (algebraMap ℝ K) r n

@[rclike_simps, norm_cast]
theorem ofReal_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∏ i ∈ s, f i : ℝ) : K) = ∏ i ∈ s, (f i : K) :=
  map_prod (algebraMap ℝ K) _ _

@[simp, rclike_simps, norm_cast]
theorem ofReal_finsuppProd {α M : Type*} [Zero M] (f : α →₀ M) (g : α → M → ℝ) :
    ((f.prod fun a b => g a b : ℝ) : K) = f.prod fun a b => (g a b : K) :=
  map_finsuppProd _ f g

@[simp, norm_cast, rclike_simps]
theorem real_smul_ofReal (r x : ℝ) : r • (x : K) = (r : K) * (x : K) :=
  real_smul_eq_coe_mul _ _

@[rclike_simps]
theorem re_ofReal_mul (r : ℝ) (z : K) : re (↑r * z) = r * re z := by
  simp only [mul_re, ofReal_im, zero_mul, ofReal_re, sub_zero]

@[rclike_simps]
theorem im_ofReal_mul (r : ℝ) (z : K) : im (↑r * z) = r * im z := by
  simp only [add_zero, ofReal_im, zero_mul, ofReal_re, mul_im]

@[rclike_simps]
theorem smul_re (r : ℝ) (z : K) : re (r • z) = r * re z := by
  rw [real_smul_eq_coe_mul, re_ofReal_mul]

@[rclike_simps]
theorem smul_im (r : ℝ) (z : K) : im (r • z) = r * im z := by
  rw [real_smul_eq_coe_mul, im_ofReal_mul]

@[rclike_simps, norm_cast]
theorem norm_ofReal (r : ℝ) : ‖(r : K)‖ = |r| :=
  norm_algebraMap' K r

@[simp]
theorem re_ofReal_pow (a : ℝ) (n : ℕ) : re ((a : K) ^ n) = a ^ n := by
  rw [← ofReal_pow, @ofReal_re]

@[simp]
theorem im_ofReal_pow (a : ℝ) (n : ℕ) : im ((a : K) ^ n) = 0 := by
  rw [← @ofReal_pow, @ofReal_im_ax]

/-! ### Characteristic zero -/

-- see Note [lower instance priority]
/-- ℝ and ℂ are both of characteristic zero. -/
instance (priority := 100) charZero_rclike : CharZero K :=
  (RingHom.charZero_iff (algebraMap ℝ K).injective).1 inferInstance

@[rclike_simps, norm_cast]
lemma ofReal_expect {α : Type*} (s : Finset α) (f : α → ℝ) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : K) :=
  map_expect (algebraMap ..) ..

@[norm_cast]
lemma ofReal_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) :
    ((balance f i : ℝ) : K) = balance ((↑) ∘ f) i := map_balance (algebraMap ..) ..

@[simp] lemma ofReal_comp_balance {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ofReal ∘ balance f = balance (ofReal ∘ f : ι → K) := funext <| ofReal_balance _

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
@[simp, rclike_simps]
theorem I_re : re (I : K) = 0 :=
  I_re_ax

@[simp, rclike_simps]
theorem I_im (z : K) : im z * im (I : K) = im z :=
  mul_im_I_ax z

@[simp, rclike_simps]
theorem I_im' (z : K) : im (I : K) * im z = im z := by rw [mul_comm, I_im]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
theorem I_mul_re (z : K) : re (I * z) = -im z := by
  simp only [I_re, zero_sub, I_im', zero_mul, mul_re]

theorem I_mul_I : (I : K) = 0 ∨ (I : K) * I = -1 :=
  I_mul_I_ax

variable (𝕜) in
lemma I_eq_zero_or_im_I_eq_one : (I : K) = 0 ∨ im (I : K) = 1 :=
  I_mul_I (K := K) |>.imp_right fun h ↦ by simpa [h] using (I_mul_re (I : K)).symm

@[simp, rclike_simps]
theorem conj_re (z : K) : re (conj z) = re z :=
  RCLike.conj_re_ax z

@[simp, rclike_simps]
theorem conj_im (z : K) : im (conj z) = -im z :=
  RCLike.conj_im_ax z

@[simp, rclike_simps]
theorem conj_I : conj (I : K) = -I :=
  RCLike.conj_I_ax

@[simp, rclike_simps]
theorem conj_ofReal (r : ℝ) : conj (r : K) = (r : K) := by
  rw [ext_iff]
  simp only [ofReal_im, conj_im, conj_re, and_self_iff, neg_zero]

theorem conj_nat_cast (n : ℕ) : conj (n : K) = n := map_natCast _ _

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : K) = ofNat(n) :=
  map_ofNat _ _

@[rclike_simps, simp]
theorem conj_neg_I : conj (-I) = (I : K) := by rw [map_neg, conj_I, neg_neg]

theorem conj_eq_re_sub_im (z : K) : conj z = re z - im z * I :=
  (congr_arg conj (re_add_im z).symm).trans <| by
    rw [map_add, map_mul, conj_I, conj_ofReal, conj_ofReal, mul_neg, sub_eq_add_neg]

theorem sub_conj (z : K) : z - conj z = 2 * im z * I :=
  calc
    z - conj z = re z + im z * I - (re z - im z * I) := by rw [re_add_im, ← conj_eq_re_sub_im]
    _ = 2 * im z * I := by rw [add_sub_sub_cancel, ← two_mul, mul_assoc]

@[rclike_simps]
theorem conj_smul (r : ℝ) (z : K) : conj (r • z) = r • conj z := by
  rw [conj_eq_re_sub_im, conj_eq_re_sub_im, smul_re, smul_im, ofReal_mul, ofReal_mul,
    real_smul_eq_coe_mul r (_ - _), mul_sub, mul_assoc]

theorem add_conj (z : K) : z + conj z = 2 * re z :=
  calc
    z + conj z = re z + im z * I + (re z - im z * I) := by rw [re_add_im, conj_eq_re_sub_im]
    _ = 2 * re z := by rw [add_add_sub_cancel, two_mul]

theorem re_eq_add_conj (z : K) : ↑(re z) = (z + conj z) / 2 := by
  rw [add_conj, mul_div_cancel_left₀ (re z : K) two_ne_zero]

theorem im_eq_conj_sub (z : K) : ↑(im z) = I * (conj z - z) / 2 := by
  rw [← neg_inj, ← ofReal_neg, ← I_mul_re, re_eq_add_conj, map_mul, conj_I, ← neg_div, ← mul_neg,
    neg_sub, mul_sub, neg_mul, sub_eq_add_neg]

open List in
/-- There are several equivalent ways to say that a number `z` is in fact a real number. -/
theorem is_real_TFAE (z : K) :
    TFAE [conj z = z, ∃ r : ℝ, (r : K) = z, ↑(re z) = z, im z = 0, IsSelfAdjoint z] := by
  tfae_have 1 → 4
  | h => by
    rw [← @ofReal_inj K, im_eq_conj_sub, h, sub_self, mul_zero, zero_div,
      ofReal_zero]
  tfae_have 4 → 3
  | h => by
    conv_rhs => rw [← re_add_im z, h, ofReal_zero, zero_mul, add_zero]
  tfae_have 3 → 2 := fun h => ⟨_, h⟩
  tfae_have 2 → 1 := fun ⟨r, hr⟩ => hr ▸ conj_ofReal _
  tfae_have 1 → 5 := fun _ => by rwa [isSelfAdjoint_iff]
  tfae_have 5 → 1 := fun hz => by rwa [isSelfAdjoint_iff] at hz
  tfae_finish

theorem conj_eq_iff_real {z : K} : conj z = z ↔ ∃ r : ℝ, z = (r : K) :=
  calc
    _ ↔ ∃ r : ℝ, (r : K) = z := (is_real_TFAE z).out 0 1
    _ ↔ _                    := by simp only [eq_comm]

theorem conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) = z :=
  (is_real_TFAE z).out 0 2

theorem conj_eq_iff_im {z : K} : conj z = z ↔ im z = 0 :=
  (is_real_TFAE z).out 0 3

@[simp]
theorem star_def : (Star.star : K → K) = conj :=
  rfl

lemma im_eq_zero_iff_isSelfAdjoint {x : K} : im x = 0 ↔ IsSelfAdjoint x :=
  is_real_TFAE x |>.out 3 4

lemma re_eq_ofReal_of_isSelfAdjoint {x : K} {y : ℝ} (hx : IsSelfAdjoint x) :
    re x = y ↔ x = y := by
  simp [RCLike.ext_iff (K := K), hx, im_eq_zero_iff_isSelfAdjoint]

lemma ofReal_eq_re_of_isSelfAdjoint {x : K} {y : ℝ} (hx : IsSelfAdjoint x) :
    y = re x ↔ y = x := by
  simpa [eq_comm] using re_eq_ofReal_of_isSelfAdjoint hx

variable (K)

/-- Conjugation as a ring equivalence. This is used to convert the inner product into a
sesquilinear product. -/
abbrev conjToRingEquiv : K ≃+* Kᵐᵒᵖ :=
  starRingEquiv

variable {K} {z : K}

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

@[rclike_simps]
theorem normSq_zero : normSq (0 : K) = 0 :=
  normSq.map_zero

@[rclike_simps]
theorem normSq_one : normSq (1 : K) = 1 :=
  normSq.map_one

theorem normSq_nonneg (z : K) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
theorem normSq_eq_zero {z : K} : normSq z = 0 ↔ z = 0 :=
  map_eq_zero _

@[simp, rclike_simps]
theorem normSq_pos {z : K} : 0 < normSq z ↔ z ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm]; simp [normSq_nonneg]

@[simp, rclike_simps]
theorem normSq_neg (z : K) : normSq (-z) = normSq z := by simp only [normSq_eq_def', norm_neg]

@[simp, rclike_simps]
theorem normSq_conj (z : K) : normSq (conj z) = normSq z := by
  simp only [normSq_apply, neg_mul, mul_neg, neg_neg, rclike_simps]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
theorem normSq_mul (z w : K) : normSq (z * w) = normSq z * normSq w :=
  map_mul _ z w

theorem normSq_add (z w : K) : normSq (z + w) = normSq z + normSq w + 2 * re (z * conj w) := by
  simp only [normSq_apply, map_add, rclike_simps]
  ring

theorem re_sq_le_normSq (z : K) : re z * re z ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : K) : im z * im z ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : K) : z * conj z = ‖z‖ ^ 2 := by
  apply ext <;> simp [← ofReal_pow, norm_sq_eq_def, mul_comm]

theorem conj_mul (z : K) : conj z * z = ‖z‖ ^ 2 := by rw [mul_comm, mul_conj]

lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z :=
  inv_eq_of_mul_eq_one_left <| by simp_rw [conj_mul, hz, algebraMap.coe_one, one_pow]

theorem normSq_sub (z w : K) : normSq (z - w) = normSq z + normSq w - 2 * re (z * conj w) := by
  simp only [normSq_add, sub_eq_add_neg, map_neg, mul_neg, normSq_neg, map_neg]

theorem sqrt_normSq_eq_norm {z : K} : √(normSq z) = ‖z‖ := by
  rw [normSq_eq_def', Real.sqrt_sq (norm_nonneg _)]

/-! ### Inversion -/

@[rclike_simps, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : K) = (r : K)⁻¹ :=
  map_inv₀ _ r

theorem inv_def (z : K) : z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
  · apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, mul_conj, ofReal_inv, ofReal_pow, mul_inv_cancel₀]
    simpa

@[simp, rclike_simps]
theorem inv_re (z : K) : re z⁻¹ = re z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, re_ofReal_mul, conj_re, div_eq_inv_mul]

@[simp, rclike_simps]
theorem inv_im (z : K) : im z⁻¹ = -im z / normSq z := by
  rw [inv_def, normSq_eq_def', mul_comm, im_ofReal_mul, conj_im, div_eq_inv_mul]

theorem div_re (z w : K) : re (z / w) = re z * re w / normSq w + im z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, neg_mul, mul_neg, neg_neg,
    rclike_simps]

theorem div_im (z w : K) : im (z / w) = im z * re w / normSq w - re z * im w / normSq w := by
  simp only [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm, neg_mul, mul_neg,
    rclike_simps]

-- Not `@[simp]` since `simp` can prove this
@[rclike_simps]
theorem conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

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

@[rclike_simps, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : K) = r / s :=
  map_div₀ (algebraMap ℝ K) r s

theorem div_re_ofReal {z : K} {r : ℝ} : re (z / r) = re z / r := by
  rw [div_eq_inv_mul, div_eq_inv_mul, ← ofReal_inv, re_ofReal_mul]

@[rclike_simps, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : K) = (r : K) ^ n :=
  map_zpow₀ (algebraMap ℝ K) r n

theorem I_mul_I_of_nonzero : (I : K) ≠ 0 → (I : K) * I = -1 :=
  I_mul_I_ax.resolve_left

@[simp, rclike_simps]
theorem inv_I : (I : K)⁻¹ = -I := by
  by_cases h : (I : K) = 0
  · simp [h]
  · field_simp
    linear_combination I_mul_I_of_nonzero h

@[simp, rclike_simps]
theorem div_I (z : K) : z / I = -(z * I) := by rw [div_eq_mul_inv, inv_I, mul_neg]

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
theorem normSq_inv (z : K) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

-- Not `@[simp]` since `simp` can prove this.
@[rclike_simps]
theorem normSq_div (z w : K) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

@[simp 1100, rclike_simps]
theorem norm_conj (z : K) : ‖conj z‖ = ‖z‖ := by simp only [← sqrt_normSq_eq_norm, normSq_conj]

@[simp 1100, rclike_simps] lemma nnnorm_conj (z : K) : ‖conj z‖₊ = ‖z‖₊ := by simp [nnnorm]

@[simp 1100, rclike_simps] lemma enorm_conj (z : K) : ‖conj z‖ₑ = ‖z‖ₑ := by simp [enorm]

instance (priority := 100) : CStarRing K where
  norm_mul_self_le x := le_of_eq <| ((norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_conj _)).symm

instance : StarModule ℝ K where
  star_smul r a := by
    apply RCLike.ext <;> simp [RCLike.smul_re, RCLike.smul_im]

/-! ### Cast lemmas -/

@[rclike_simps, norm_cast]
theorem ofReal_natCast (n : ℕ) : ((n : ℝ) : K) = n :=
  map_natCast (algebraMap ℝ K) n

@[rclike_simps, norm_cast]
lemma ofReal_nnratCast (q : ℚ≥0) : ((q : ℝ) : K) = q := map_nnratCast (algebraMap ℝ K) _

@[simp, rclike_simps]
theorem natCast_re (n : ℕ) : re (n : K) = n := by rw [← ofReal_natCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
theorem natCast_im (n : ℕ) : im (n : K) = 0 := by rw [← ofReal_natCast, ofReal_im]
@[simp, rclike_simps]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : re (ofNat(n) : K) = ofNat(n) :=
  natCast_re n
@[simp, rclike_simps]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : im (ofNat(n) : K) = 0 :=
  natCast_im n

@[rclike_simps, norm_cast]
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℝ) : K) = ofNat(n) :=
  ofReal_natCast n

theorem ofNat_mul_re (n : ℕ) [n.AtLeastTwo] (z : K) :
    re (ofNat(n) * z) = ofNat(n) * re z := by
  rw [← ofReal_ofNat, re_ofReal_mul]

theorem ofNat_mul_im (n : ℕ) [n.AtLeastTwo] (z : K) :
    im (ofNat(n) * z) = ofNat(n) * im z := by
  rw [← ofReal_ofNat, im_ofReal_mul]

@[rclike_simps, norm_cast]
theorem ofReal_intCast (n : ℤ) : ((n : ℝ) : K) = n :=
  map_intCast _ n

@[simp, rclike_simps]
theorem intCast_re (n : ℤ) : re (n : K) = n := by rw [← ofReal_intCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
theorem intCast_im (n : ℤ) : im (n : K) = 0 := by rw [← ofReal_intCast, ofReal_im]

@[rclike_simps, norm_cast]
theorem ofReal_ratCast (n : ℚ) : ((n : ℝ) : K) = n :=
  map_ratCast _ n

@[simp, rclike_simps]
theorem ratCast_re (q : ℚ) : re (q : K) = q := by rw [← ofReal_ratCast, ofReal_re]

@[simp, rclike_simps, norm_cast]
theorem ratCast_im (q : ℚ) : im (q : K) = 0 := by rw [← ofReal_ratCast, ofReal_im]

/-! ### Norm -/

theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
  (norm_ofReal _).trans (abs_of_nonneg h)

@[simp 1100, rclike_simps, norm_cast]
theorem norm_natCast (n : ℕ) : ‖(n : K)‖ = n := by
  rw [← ofReal_natCast]
  exact norm_of_nonneg (Nat.cast_nonneg n)

@[simp, rclike_simps, norm_cast] lemma nnnorm_natCast (n : ℕ) : ‖(n : K)‖₊ = n := by simp [nnnorm]

@[simp, rclike_simps]
theorem norm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖ = ofNat(n) :=
  norm_natCast n

@[simp, rclike_simps]
lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(ofNat(n) : K)‖₊ = ofNat(n) :=
  nnnorm_natCast n

lemma norm_two : ‖(2 : K)‖ = 2 := norm_ofNat 2
lemma nnnorm_two : ‖(2 : K)‖₊ = 2 := nnnorm_ofNat 2

@[simp, rclike_simps, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : K)‖ = q := by
  rw [← ofReal_nnratCast]; exact norm_of_nonneg q.cast_nonneg

@[simp, rclike_simps, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : K)‖₊ = q := by simp [nnnorm]

variable (K) in
lemma norm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ := by
  simpa [Nat.cast_smul_eq_nsmul] using norm_smul (n : K) x

variable (K) in
lemma nnnorm_nsmul [NormedAddCommGroup E] [NormedSpace K E] (n : ℕ) (x : E) :
    ‖n • x‖₊ = n • ‖x‖₊ := by simpa [Nat.cast_smul_eq_nsmul] using nnnorm_smul (n : K) x

section NormedField
variable [NormedField E] [CharZero E] [NormedSpace K E]
include K

variable (K) in
lemma norm_nnqsmul (q : ℚ≥0) (x : E) : ‖q • x‖ = q • ‖x‖ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using norm_smul (q : K) x

variable (K) in
lemma nnnorm_nnqsmul (q : ℚ≥0) (x : E) : ‖q • x‖₊ = q • ‖x‖₊ := by
  simpa [NNRat.cast_smul_eq_nnqsmul] using nnnorm_smul (q : K) x

@[bound]
lemma norm_expect_le {ι : Type*} {s : Finset ι} {f : ι → E} : ‖𝔼 i ∈ s, f i‖ ≤ 𝔼 i ∈ s, ‖f i‖ :=
  Finset.le_expect_of_subadditive norm_zero norm_add_le fun _ _ ↦ by rw [norm_nnqsmul K]

end NormedField

theorem mul_self_norm (z : K) : ‖z‖ * ‖z‖ = normSq z := by rw [normSq_eq_def', sq]

attribute [rclike_simps] norm_zero norm_one norm_eq_zero abs_norm norm_inv norm_div

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
  simpa only [mul_self_norm a, normSq_apply, left_eq_add, mul_self_eq_zero]
    using congr_arg (fun z => z * z) ((re_le_norm a).antisymm h)

theorem re_eq_self_of_le {a : K} (h : ‖a‖ ≤ re a) : (re a : K) = a := by
  rw [← conj_eq_iff_re, conj_eq_iff_im, im_eq_zero_of_le h]

open IsAbsoluteValue

theorem abs_re_div_norm_le_one (z : K) : |re z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (abs_re_le_norm _) (norm_nonneg _)

theorem abs_im_div_norm_le_one (z : K) : |im z / ‖z‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (abs_im_le_norm _) (norm_nonneg _)

theorem norm_I_of_ne_zero (hI : (I : K) ≠ 0) : ‖(I : K)‖ = 1 := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg I) zero_le_one, one_mul, ← norm_mul,
    I_mul_I_of_nonzero hI, norm_neg, norm_one]

theorem re_eq_norm_of_mul_conj (x : K) : re (x * conj x) = ‖x * conj x‖ := by
  rw [mul_conj, ← ofReal_pow]; simp [-map_pow]

theorem norm_sq_re_add_conj (x : K) : ‖x + conj x‖ ^ 2 = re (x + conj x) ^ 2 := by
  rw [add_conj, ← ofReal_ofNat, ← ofReal_mul, norm_ofReal, sq_abs, ofReal_re]

theorem norm_sq_re_conj_add (x : K) : ‖conj x + x‖ ^ 2 = re (conj x + x) ^ 2 := by
  rw [add_comm, norm_sq_re_add_conj]

instance : NormSMulClass ℤ K where
  norm_smul r x := by
    rw [zsmul_eq_mul, norm_mul, ← ofReal_intCast, norm_ofReal, Int.norm_eq_abs]

/-! ### Cauchy sequences -/

theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

theorem isCauSeq_im (f : CauSeq K norm) : IsCauSeq abs fun n => im (f n) := fun _ ε0 =>
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

end RCLike

section Instances

noncomputable instance Real.instRCLike : RCLike ℝ where
  re := AddMonoidHom.id ℝ
  im := 0
  I := 0
  I_re_ax := by simp only [map_zero]
  I_mul_I_ax := Or.intro_left _ rfl
  re_add_im_ax z := by
    simp only [add_zero, mul_zero, Algebra.algebraMap_self, RingHom.id_apply, AddMonoidHom.id_apply]
  ofReal_re_ax _ := rfl
  ofReal_im_ax _ := rfl
  mul_re_ax z w := by simp only [sub_zero, mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_ax z w := by simp only [add_zero, zero_mul, mul_zero, AddMonoidHom.zero_apply]
  conj_re_ax z := by simp only [starRingEnd_apply, star_id_of_comm]
  conj_im_ax _ := by simp only [neg_zero, AddMonoidHom.zero_apply]
  conj_I_ax := by simp only [map_zero, neg_zero]
  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
    mul_zero, AddMonoidHom.zero_apply, AddMonoidHom.id_apply]
  mul_im_I_ax _ := by simp only [mul_zero, AddMonoidHom.zero_apply]
  le_iff_re_im := (and_iff_left rfl).symm

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

lemma norm_le_re_iff_eq_norm {z : K} :
    ‖z‖ ≤ re z ↔ z = ‖z‖ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ‖z‖ = re z := (le_antisymm (re_le_norm z) h).symm
    rw [h', re_eq_self_of_le h]
  · rw [h]
    simp

lemma re_le_neg_norm_iff_eq_neg_norm {z : K} :
    re z ≤ -‖z‖ ↔ z = -‖z‖ := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_re_iff_eq_norm (z := -z)

lemma norm_of_nonneg' {x : K} (hx : 0 ≤ x) : ‖x‖ = x := by
  rw [eq_comm, ← norm_le_re_iff_eq_norm, ← sqrt_normSq_eq_norm, normSq_apply]
  simp [nonneg_iff.mp hx]

lemma re_nonneg_of_nonneg {x : K} (hx : IsSelfAdjoint x) : 0 ≤ re x ↔ 0 ≤ x := by
  simp [nonneg_iff (K := K), conj_eq_iff_im.mp hx]

@[gcongr]
lemma re_le_re {x y : K} (h : x ≤ y) : re x ≤ re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

lemma re_monotone : Monotone (re : K → ℝ) :=
  fun _ _ => re_le_re

protected lemma inv_pos_of_pos (hz : 0 < z) : 0 < z⁻¹ := by
  rw [pos_iff_exists_ofReal] at hz
  obtain ⟨x, hx, hx'⟩ := hz
  rw [← hx', ← ofReal_inv, ofReal_pos]
  exact inv_pos_of_pos hx

protected lemma inv_pos : 0 < z⁻¹ ↔ 0 < z := by
  refine ⟨fun h => ?_, fun h => RCLike.inv_pos_of_pos h⟩
  rw [← inv_inv z]
  exact RCLike.inv_pos_of_pos h

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

lemma toZeroLEOneClass : ZeroLEOneClass K where
  zero_le_one := by simp [@RCLike.le_iff_re_im K]

scoped[ComplexOrder] attribute [instance] RCLike.toZeroLEOneClass

lemma toIsOrderedAddMonoid : IsOrderedAddMonoid K where
  add_le_add_left _ _ := add_le_add_left

scoped[ComplexOrder] attribute [instance] RCLike.toIsOrderedAddMonoid

/-- With `z ≤ w` iff `w - z` is real and nonnegative, `ℝ` and `ℂ` are strictly ordered rings.

Note this is only an instance with `open scoped ComplexOrder`. -/
lemma toIsStrictOrderedRing : IsStrictOrderedRing K :=
  .of_mul_pos fun z w hz hw ↦ by
    rw [lt_iff_re_im, map_zero] at hz hw ⊢
    simp [mul_re, mul_im, ← hz.2, ← hw.2, mul_pos hz.1 hw.1]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedRing

lemma toPosMulReflectLT : PosMulReflectLT K where
  elim := by
    rintro ⟨x, hx⟩ y z hyz
    dsimp at *
    rw [RCLike.le_iff_re_im, map_zero, map_zero, eq_comm] at hx
    obtain ⟨r, rfl⟩ := ((is_real_TFAE x).out 3 1).1 hx.2
    simp only [RCLike.lt_iff_re_im (K := K), mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      mul_im, add_zero, mul_eq_mul_left_iff] at hyz ⊢
    refine ⟨lt_of_mul_lt_mul_of_nonneg_left hyz.1 <| by simpa using hx, hyz.2.resolve_right ?_⟩
    rintro rfl
    simp at hyz

scoped[ComplexOrder] attribute [instance] RCLike.toPosMulReflectLT

theorem toIsStrictOrderedModule : IsStrictOrderedModule ℝ K where
  smul_lt_smul_of_pos_left r hr a b hab := by
    simpa [RCLike.lt_iff_re_im (K := K), smul_re, smul_im, hr, hr.ne'] using hab
  smul_lt_smul_of_pos_right a ha r₁ r₂ hr := by
    obtain ⟨hare, haim⟩ := RCLike.lt_iff_re_im.1 ha
    simp_all [RCLike.lt_iff_re_im (K := K), smul_re, smul_im]

scoped[ComplexOrder] attribute [instance] RCLike.toIsStrictOrderedModule

theorem ofReal_mul_pos_iff (x : ℝ) (z : K) :
    0 < x * z ↔ (x < 0 ∧ z < 0) ∨ (0 < x ∧ 0 < z) := by
  simp only [pos_iff (K := K), neg_iff (K := K), re_ofReal_mul, im_ofReal_mul]
  obtain hx | hx | hx := lt_trichotomy x 0
  · simp only [mul_pos_iff, not_lt_of_gt hx, false_and, hx, true_and, false_or, mul_eq_zero, hx.ne,
      or_false]
  · simp only [hx, zero_mul, lt_self_iff_false, false_and, false_or]
  · simp only [mul_pos_iff, hx, true_and, not_lt_of_gt hx, false_and, or_false, mul_eq_zero,
      hx.ne', false_or]

theorem ofReal_mul_neg_iff (x : ℝ) (z : K) :
    x * z < 0 ↔ (x < 0 ∧ 0 < z) ∨ (0 < x ∧ z < 0) := by
  simpa only [mul_neg, neg_pos, neg_neg_iff_pos] using ofReal_mul_pos_iff x (-z)

lemma instPosMulReflectLE : PosMulReflectLE K where
  elim a b c h := by
    obtain ⟨a', ha1, ha2⟩ := pos_iff_exists_ofReal.mp a.2
    rw [← sub_nonneg]
    #adaptation_note /-- 2025-03-29 need beta reduce for https://github.com/leanprover/lean4/issues/7717 -/
    beta_reduce at h
    rw [← ha2, ← sub_nonneg, ← mul_sub, le_iff_lt_or_eq] at h
    rcases h with h | h
    · rw [ofReal_mul_pos_iff] at h
      exact le_of_lt <| h.rec (False.elim <| not_lt_of_gt ·.1 ha1) (·.2)
    · exact ((mul_eq_zero_iff_left <| ofReal_ne_zero.mpr ha1.ne').mp h.symm).ge

scoped[ComplexOrder] attribute [instance] RCLike.instPosMulReflectLE

end Order

section CleanupLemmas

local notation "reR" => @RCLike.re ℝ _
local notation "imR" => @RCLike.im ℝ _
local notation "IR" => @RCLike.I ℝ _
local notation "normSqR" => @RCLike.normSq ℝ _

@[simp, rclike_simps]
theorem re_to_real {x : ℝ} : reR x = x :=
  rfl

@[simp, rclike_simps]
theorem im_to_real {x : ℝ} : imR x = 0 :=
  rfl

@[rclike_simps]
theorem conj_to_real {x : ℝ} : conj x = x :=
  rfl

@[simp, rclike_simps]
theorem I_to_real : IR = 0 :=
  rfl

@[simp, rclike_simps]
theorem normSq_to_real {x : ℝ} : normSq x = x * x := by simp [RCLike.normSq]

@[simp]
theorem ofReal_real_eq_id : @ofReal ℝ _ = id :=
  rfl

end CleanupLemmas

section LinearMaps

/-- The real part in an `RCLike` field, as a linear map. -/
def reLm : K →ₗ[ℝ] ℝ :=
  { re with map_smul' := smul_re }

@[simp, rclike_simps]
theorem reLm_coe : (reLm : K → ℝ) = re :=
  rfl

/-- The real part in an `RCLike` field, as a continuous linear map. -/
noncomputable def reCLM : StrongDual ℝ K :=
  reLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_re_le_norm x

@[simp, rclike_simps, norm_cast]
theorem reCLM_coe : ((reCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp, rclike_simps]
theorem reCLM_apply : ((reCLM : StrongDual ℝ K) : K → ℝ) = re :=
  rfl

@[continuity, fun_prop]
theorem continuous_re : Continuous (re : K → ℝ) :=
  reCLM.continuous

/-- The imaginary part in an `RCLike` field, as a linear map. -/
def imLm : K →ₗ[ℝ] ℝ :=
  { im with map_smul' := smul_im }

@[simp, rclike_simps]
theorem imLm_coe : (imLm : K → ℝ) = im :=
  rfl

/-- The imaginary part in an `RCLike` field, as a continuous linear map. -/
noncomputable def imCLM : StrongDual ℝ K :=
  imLm.mkContinuous 1 fun x => by
    rw [one_mul]
    exact abs_im_le_norm x

@[simp, rclike_simps, norm_cast]
theorem imCLM_coe : ((imCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp, rclike_simps]
theorem imCLM_apply : ((imCLM : StrongDual ℝ K) : K → ℝ) = im :=
  rfl

@[continuity, fun_prop]
theorem continuous_im : Continuous (im : K → ℝ) :=
  imCLM.continuous

/-- Conjugate as an `ℝ`-algebra equivalence -/
def conjAe : K ≃ₐ[ℝ] K :=
  { conj with
    invFun := conj
    left_inv := conj_conj
    right_inv := conj_conj
    commutes' := conj_ofReal }

@[simp, rclike_simps]
theorem conjAe_coe : (conjAe : K → K) = conj :=
  rfl

/-- Conjugate as a linear isometry -/
noncomputable def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]
theorem conjLIE_apply : (conjLIE : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _

@[simp, rclike_simps]
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, rclike_simps]
theorem conjCLE_apply : (conjCLE : K → K) = conj :=
  rfl

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The `ℝ → K` coercion, as a linear map -/
noncomputable def ofRealAm : ℝ →ₐ[ℝ] K :=
  Algebra.ofId ℝ K

@[simp, rclike_simps]
theorem ofRealAm_coe : (ofRealAm : ℝ → K) = ofReal :=
  rfl

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]
theorem ofRealLI_apply : (ofRealLI : ℝ → K) = ofReal :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]
theorem ofRealCLM_coe : (@ofRealCLM K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, rclike_simps]
theorem ofRealCLM_apply : (ofRealCLM : ℝ → K) = ofReal :=
  rfl

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLI.continuous

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

theorem lipschitzWith_ofReal : LipschitzWith 1 (ofReal : ℝ → K) :=
  ofRealLI.lipschitz

lemma lipschitzWith_re : LipschitzWith 1 (re (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖re x - re y‖ₑ
  _ = ‖re (x - y)‖ₑ := by rw [map_sub re x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_re_le_norm (x - y)

lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_eq_enorm_sub]
  calc ‖im x - im y‖ₑ
  _ = ‖im (x - y)‖ₑ := by rw [map_sub im x y]
  _ ≤ ‖x - y‖ₑ := by rw [enorm_le_iff_norm_le]; exact norm_im_le_norm (x - y)

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

lemma norm_le_im_iff_eq_I_mul_norm {z : K} :
    ‖z‖ ≤ im z ↔ z = I * ‖z‖ := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := K)
  · simp [h, im_eq_zero]
  · have : (I : K) ≠ 0 := fun _ ↦ by simp_all
    rw [← mul_right_inj' (neg_ne_zero.mpr this)]
    convert norm_le_re_iff_eq_norm (z := -I * z) using 2
    all_goals simp [neg_mul, ← mul_assoc, I_mul_I_of_nonzero this, norm_I_of_ne_zero this]

lemma im_le_neg_norm_iff_eq_neg_I_mul_norm {z : K} :
    im z ≤ -‖z‖ ↔ z = -(I * ‖z‖) := by
  simpa [neg_eq_iff_eq_neg, le_neg] using norm_le_im_iff_eq_I_mul_norm (z := -z)

end RCLike

namespace AddChar
variable {G : Type*} [Finite G]

lemma inv_apply_eq_conj [AddLeftCancelMonoid G] (ψ : AddChar G K) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  RCLike.inv_eq_conj <| norm_apply _ _

lemma map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G K) (x : G) : ψ (-x) = conj (ψ x) := by
  rw [map_neg_eq_inv, inv_apply_eq_conj]

end AddChar

section

/-- A mixin over a normed field, saying that the norm field structure is the same as `ℝ` or `ℂ`.
To endow such a field with a compatible `RCLike` structure in a proof, use
`letI := IsRCLikeNormedField.rclike 𝕜`. -/
class IsRCLikeNormedField (𝕜 : Type*) [hk : NormedField 𝕜] : Prop where
  out : ∃ h : RCLike 𝕜, hk = h.toNormedField

instance (priority := 100) (𝕜 : Type*) [h : RCLike 𝕜] : IsRCLikeNormedField 𝕜 := ⟨⟨h, rfl⟩⟩

/-- A copy of an `RCLike` field in which the `NormedField` field is adjusted to be become defeq
to a propeq one. -/
noncomputable def RCLike.copy_of_normedField {𝕜 : Type*} (h : RCLike 𝕜) (hk : NormedField 𝕜)
    (h'' : hk = h.toNormedField) : RCLike 𝕜 where
  __ := hk
  toPartialOrder := h.toPartialOrder
  toDecidableEq := h.toDecidableEq
  complete := by subst h''; exact h.complete
  lt_norm_lt := by subst h''; exact h.lt_norm_lt
  -- star fields
  star := (@StarMul.toInvolutiveStar _ (_) (@StarRing.toStarMul _ (_) h.toStarRing)).star
  star_involutive := by subst h''; exact h.star_involutive
  star_mul := by subst h''; exact h.star_mul
  star_add := by subst h''; exact h.star_add
  -- algebra fields
  smul := (@Algebra.toSMul _ _ _ (_) (@NormedAlgebra.toAlgebra _ _ _ (_) h.toNormedAlgebra)).smul
  algebraMap :=
  { toFun := @Algebra.algebraMap _ _ _ (_) (@NormedAlgebra.toAlgebra _ _ _ (_) h.toNormedAlgebra)
    map_one' := by subst h''; exact h.algebraMap.map_one'
    map_mul' := by subst h''; exact h.algebraMap.map_mul'
    map_zero' := by subst h''; exact h.algebraMap.map_zero'
    map_add' := by subst h''; exact h.algebraMap.map_add' }
  commutes' := by subst h''; exact h.commutes'
  smul_def' := by subst h''; exact h.smul_def'
  norm_smul_le := by subst h''; exact h.norm_smul_le
  -- RCLike fields
  re := by subst h''; exact h.re
  im := by subst h''; exact h.im
  I := h.I
  I_re_ax := by subst h''; exact h.I_re_ax
  I_mul_I_ax := by subst h''; exact h.I_mul_I_ax
  re_add_im_ax := by subst h''; exact h.re_add_im_ax
  ofReal_re_ax := by subst h''; exact h.ofReal_re_ax
  ofReal_im_ax := by subst h''; exact h.ofReal_im_ax
  mul_re_ax := by subst h''; exact h.mul_re_ax
  mul_im_ax := by subst h''; exact h.mul_im_ax
  conj_re_ax := by subst h''; exact h.conj_re_ax
  conj_im_ax := by subst h''; exact h.conj_im_ax
  conj_I_ax := by subst h''; exact h.conj_I_ax
  norm_sq_eq_def_ax := by subst h''; exact h.norm_sq_eq_def_ax
  mul_im_I_ax := by subst h''; exact h.mul_im_I_ax
  le_iff_re_im := by subst h''; exact h.le_iff_re_im

/-- Given a normed field `𝕜` satisfying `IsRCLikeNormedField 𝕜`, build an associated `RCLike 𝕜`
structure on `𝕜` which is definitionally compatible with the given normed field structure. -/
noncomputable def IsRCLikeNormedField.rclike (𝕜 : Type*)
    [hk : NormedField 𝕜] [h : IsRCLikeNormedField 𝕜] : RCLike 𝕜 := by
  choose p hp using h.out
  exact p.copy_of_normedField hk hp

end
