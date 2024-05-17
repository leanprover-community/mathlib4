/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Logic.Basic
import Mathlib.Init.ZeroOne
import Mathlib.Init.Order.Defs

#align_import algebra.ne_zero from "leanprover-community/mathlib"@"f340f229b1f461aa1c8ee11e0a172d0a3b301a4a"

/-!
# `NeZero` typeclass

We create a typeclass `NeZero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `NeZero`: `n ≠ 0` as a typeclass.
-/

variable {R : Type*} [Zero R]

/-- A type-class version of `n ≠ 0`.  -/
class NeZero (n : R) : Prop where
  /-- The proposition that `n` is not zero. -/
  out : n ≠ 0
#align ne_zero NeZero

theorem NeZero.ne (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out
#align ne_zero.ne NeZero.ne

theorem NeZero.ne' (n : R) [h : NeZero n] : 0 ≠ n :=
  h.out.symm
#align ne_zero.ne' NeZero.ne'

theorem neZero_iff {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h ↦ h.out, NeZero.mk⟩
#align ne_zero_iff neZero_iff

@[simp] lemma neZero_zero_iff_false {α : Type*} [Zero α] : NeZero (0 : α) ↔ False :=
  ⟨fun h ↦ h.ne rfl, fun h ↦ h.elim⟩

theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]
#align not_ne_zero not_neZero

theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk
#align eq_zero_or_ne_zero eq_zero_or_neZero

section
variable {α : Type*} [Zero α]

@[simp] lemma zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := NeZero.ne' (1 : α)
#align zero_ne_one zero_ne_one

@[simp] lemma one_ne_zero [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := NeZero.ne (1 : α)
#align one_ne_zero one_ne_zero

lemma ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 := h ▸ one_ne_zero
#align ne_zero_of_eq_one ne_zero_of_eq_one

@[field_simps]
lemma two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := NeZero.ne (2 : α)
#align two_ne_zero two_ne_zero

@[field_simps]
lemma three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := NeZero.ne (3 : α)
#align three_ne_zero three_ne_zero

@[field_simps]
lemma four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := NeZero.ne (4 : α)
#align four_ne_zero four_ne_zero

variable (α)

lemma zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := zero_ne_one
#align zero_ne_one' zero_ne_one'

lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := one_ne_zero
#align one_ne_zero' one_ne_zero'

lemma two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := two_ne_zero
#align two_ne_zero' two_ne_zero'

lemma three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := three_ne_zero
#align three_ne_zero' three_ne_zero'

lemma four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := four_ne_zero
#align four_ne_zero' four_ne_zero'

end

namespace NeZero

variable {M : Type*} {x : M}

instance succ {n : ℕ} : NeZero (n + 1) := ⟨n.succ_ne_zero⟩

theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩
#align ne_zero.of_pos NeZero.of_pos

end NeZero

lemma Nat.pos_of_neZero (n : ℕ) [NeZero n] : 0 < n := Nat.pos_of_ne_zero (NeZero.ne _)
