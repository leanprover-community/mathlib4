/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Order.IsBotOne

/-!
# Order on associates of a monoid

This file puts the divisibility preorder on `Associates M` and shows that it has `1` as a bottom
element.
-/

public section

assert_not_exists IsOrderedMonoid Multiset Ring

variable {M : Type*}

namespace Associates
variable [CommMonoid M] {a b c d : Associates M} {x y : M}

instance instPreorder : Preorder (Associates M) where
  le := Dvd.dvd
  le_refl := dvd_refl
  le_trans _ _ _ := dvd_trans

lemma dvd_eq_le : ((· ∣ ·) : Associates M → Associates M → Prop) = (· ≤ ·) := rfl

lemma isUnit_iff_eq_bot : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, bot_eq_one]

lemma mul_mono (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_left_comm]⟩

instance : IsBotOneClass (Associates M) where
  isBot_one a := Dvd.intro _ (one_mul a)

instance instOrderBot : OrderBot (Associates M) where
  bot_le _ := one_le

@[deprecated _root_.one_le +typeChanged (since := "2026-05-07")]
protected lemma one_le : 1 ≤ a :=
  one_le

lemma le_mul_right : a ≤ a * b := ⟨b, rfl⟩
lemma le_mul_left : a ≤ b * a := by rw [mul_comm]; exact le_mul_right

lemma dvd_of_mk_le_mk : Associates.mk x ≤ Associates.mk y → x ∣ y := mk_dvd_mk.mp

lemma mk_le_mk_of_dvd : x ∣ y → Associates.mk x ≤ Associates.mk y := mk_dvd_mk.mpr
lemma mk_le_mk_iff_dvd : Associates.mk x ≤ Associates.mk y ↔ x ∣ y := mk_dvd_mk

end Associates
