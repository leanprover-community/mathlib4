/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Indicator functions and support of a function in groups with zero
-/

open Set

variable {ι κ G₀ M₀ R : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s t : Set ι} {f g : ι → M₀} {i : ι}

lemma indicator_mul (s : Set ι) (f g : ι → M₀) :
    indicator s (fun i ↦ f i * g i) = fun i ↦ indicator s f i * indicator s g i := by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
#align set.indicator_mul Set.indicator_mul

lemma indicator_mul_left (s : Set ι) (f g : ι → M₀) :
    indicator s (fun j ↦ f j * g j) i = indicator s f i * g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [zero_mul]
#align set.indicator_mul_left Set.indicator_mul_left

lemma indicator_mul_right (s : Set ι) (f g : ι → M₀) :
    indicator s (fun j ↦ f j * g j) i = f i * indicator s g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]
#align set.indicator_mul_right Set.indicator_mul_right

lemma inter_indicator_mul (f g : ι → M₀) (i : ι) :
    (s ∩ t).indicator (fun j ↦ f j * g j) i = s.indicator f i * t.indicator g i := by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp
#align set.inter_indicator_mul Set.inter_indicator_mul

end MulZeroClass

section MulZeroOneClass
variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

lemma inter_indicator_one : (s ∩ t).indicator (1 : ι → M₀) = s.indicator 1 * t.indicator 1 :=
  funext fun _ ↦ by simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr
#align set.inter_indicator_one Set.inter_indicator_one

lemma indicator_prod_one {t : Set κ} {j : κ} :
    (s ×ˢ t).indicator (1 : ι × κ → M₀) (i, j) = s.indicator 1 i * t.indicator 1 j := by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto
#align set.indicator_prod_one Set.indicator_prod_one

variable (M₀) [Nontrivial M₀]

lemma indicator_eq_zero_iff_not_mem : indicator s 1 i = (0 : M₀) ↔ i ∉ s := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_zero_iff_not_mem Set.indicator_eq_zero_iff_not_mem

lemma indicator_eq_one_iff_mem : indicator s 1 i = (1 : M₀) ↔ i ∈ s := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_one_iff_mem Set.indicator_eq_one_iff_mem

lemma indicator_one_inj (h : indicator s (1 : ι → M₀) = indicator t 1) : s = t := by
  ext; simp_rw [← indicator_eq_one_iff_mem M₀, h]
#align set.indicator_one_inj Set.indicator_one_inj

end MulZeroOneClass
end Set

namespace Function
section ZeroOne
variable (R) [Zero R] [One R] [NeZero (1 : R)]

@[simp] lemma support_one : support (1 : ι → R) = univ := support_const one_ne_zero
#align function.support_one Function.support_one

@[simp] lemma mulSupport_zero : mulSupport (0 : ι → R) = univ := mulSupport_const zero_ne_one
#align function.mul_support_zero Function.mulSupport_zero

end ZeroOne

section MulZeroClass
variable [MulZeroClass M₀]

--@[simp] Porting note: removing simp, bad lemma LHS not in normal form
lemma support_mul_subset_left (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support f :=
  fun x hfg hf ↦ hfg <| by simp only [hf, zero_mul]
#align function.support_mul_subset_left Function.support_mul_subset_left

--@[simp] Porting note: removing simp, bad lemma LHS not in normal form
lemma support_mul_subset_right (f g : ι → M₀) : support (fun x ↦ f x * g x) ⊆ support g :=
  fun x hfg hg => hfg <| by simp only [hg, mul_zero]
#align function.support_mul_subset_right Function.support_mul_subset_right

variable [NoZeroDivisors M₀]

@[simp] lemma support_mul (f g : ι → M₀) : support (fun x ↦ f x * g x) = support f ∩ support g :=
  ext fun x ↦ by simp [not_or]
#align function.support_mul Function.support_mul

@[simp] lemma support_mul' (f g : ι → M₀) : support (f * g) = support f ∩ support g :=
  support_mul _ _

end MulZeroClass

section MonoidWithZero
variable [MonoidWithZero M₀] [NoZeroDivisors M₀] {n : ℕ}

@[simp] lemma support_pow (f : ι → M₀) (hn : n ≠ 0) : support (fun a ↦ f a ^ n) = support f := by
  ext; exact (pow_eq_zero_iff hn).not

@[simp] lemma support_pow' (f : ι → M₀) (hn : n ≠ 0) : support (f ^ n) = support f :=
  support_pow _ hn

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

@[simp] lemma support_inv (f : ι → G₀) : support (fun a ↦ (f a)⁻¹) = support f :=
  Set.ext fun _ ↦ not_congr inv_eq_zero
#align function.support_inv Function.support_inv

@[simp] lemma support_inv' (f : ι → G₀) : support f⁻¹ = support f := support_inv _

@[simp] lemma support_div (f g : ι → G₀) : support (fun a ↦ f a / g a) = support f ∩ support g := by
  simp [div_eq_mul_inv]
#align function.support_div Function.support_div

@[simp] lemma support_div' (f g : ι → G₀) : support (f / g) = support f ∩ support g :=
  support_div _ _

end GroupWithZero

variable [One R]

lemma mulSupport_one_add [AddLeftCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ 1 + f x) = support f :=
  Set.ext fun _ ↦ not_congr add_right_eq_self
#align function.mul_support_one_add Function.mulSupport_one_add

lemma mulSupport_one_add' [AddLeftCancelMonoid R] (f : ι → R) : mulSupport (1 + f) = support f :=
  mulSupport_one_add f
#align function.mul_support_one_add' Function.mulSupport_one_add'

lemma mulSupport_add_one [AddRightCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ f x + 1) = support f := Set.ext fun _ ↦ not_congr add_left_eq_self
#align function.mul_support_add_one Function.mulSupport_add_one

lemma mulSupport_add_one' [AddRightCancelMonoid R] (f : ι → R) : mulSupport (f + 1) = support f :=
  mulSupport_add_one f
#align function.mul_support_add_one' Function.mulSupport_add_one'

lemma mulSupport_one_sub' [AddGroup R] (f : ι → R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg, mulSupport_one_add', support_neg']
#align function.mul_support_one_sub' Function.mulSupport_one_sub'

lemma mulSupport_one_sub [AddGroup R] (f : ι → R) :
    mulSupport (fun x ↦ 1 - f x) = support f := mulSupport_one_sub' f
#align function.mul_support_one_sub Function.mulSupport_one_sub
