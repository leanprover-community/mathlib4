/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.Filter.Germ.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Ordered monoid instances on the space of germs of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `IsOrderedCancelMonoid` and `IsOrderedCancelAddMonoid`.

## Tags

filter, germ
-/

public section

namespace Filter.Product

variable {α : Type*} {ε : α → Type*} {l : Filter α}

@[to_additive]
instance instIsOrderedMonoid [∀ i, CommMonoid (ε i)] [∀ i, Preorder (ε i)]
    [∀ i, IsOrderedMonoid (ε i)] : IsOrderedMonoid (Product l ε) where
  mul_le_mul_left a b hab c := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_mul, coe_le, Pi.mul_apply] at hab ⊢
    filter_upwards [hab] with x habx
    exact mul_le_mul_left habx (c x)

@[to_additive]
instance instIsOrderedCancelMonoid [∀ i, CommMonoid (ε i)] [∀ i, Preorder (ε i)]
    [∀ i, IsOrderedCancelMonoid (ε i)] : IsOrderedCancelMonoid (Product l ε) where
  le_of_mul_le_mul_left a b c habc := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_mul, coe_le, Pi.mul_apply] at habc ⊢
    filter_upwards [habc] with x habcx
    exact le_of_mul_le_mul_left' habcx

@[to_additive]
instance instCanonicallyOrderedMul [∀ i, Mul (ε i)] [∀ i, LE (ε i)]
    [∀ i, CanonicallyOrderedMul (ε i)] : CanonicallyOrderedMul (Product l ε) where
  le_mul_self a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_mul]
  le_self_mul a b := by induction a, b using inductionOn₂ with | ofFun a b => simp [← coe_mul]

end Filter.Product
