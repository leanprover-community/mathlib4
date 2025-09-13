/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Notation.Support

/-!
# Support of a function

In this file we prove basic properties of `Function.support f = {x | f x ≠ 0}`, and similarly for
`Function.mulSupport f = {x | f x ≠ 1}`.
-/

assert_not_exists CompleteLattice MonoidWithZero

open Set

variable {α M G : Type*}

namespace Function

@[to_additive]
theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x ↦ f x * g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]
theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[to_additive (attr := simp)]
theorem mulSupport_fun_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one

@[to_additive (attr := simp)]
theorem mulSupport_inv : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_fun_inv f

@[deprecated (since := "2025-07-31")] alias support_neg' := support_neg
@[deprecated (since := "2025-07-31")] alias mulSupport_inv' := mulSupport_inv

@[to_additive]
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]
theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g

end DivisionMonoid

end Function
