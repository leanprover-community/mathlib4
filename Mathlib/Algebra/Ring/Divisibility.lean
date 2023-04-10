/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
Ported by: Matej Penciak

! This file was ported from Lean 3 source module algebra.ring.divisibility
! leanprover-community/mathlib commit 47a1a73351de8dd6c8d3d32b569c8e434b03ca47
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Convert

/-!
# Lemmas about divisibility in rings
-/


variable {α β : Type _}

section DistribSemigroup

variable [Add α] [Semigroup α]

theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])
#align dvd_add dvd_add

end DistribSemigroup

set_option linter.deprecated false in
@[simp]
theorem two_dvd_bit0 [Semiring α] {a : α} : 2 ∣ bit0 a :=
  ⟨a, bit0_eq_two_mul _⟩
#align two_dvd_bit0 two_dvd_bit0

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)
#align has_dvd.dvd.linear_comb Dvd.dvd.linear_comb

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b c : α}

theorem dvd_neg_of_dvd (h : a ∣ b) : a ∣ -b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by simp [hc]⟩
#align dvd_neg_of_dvd dvd_neg_of_dvd

theorem dvd_of_dvd_neg (h : a ∣ -b) : a ∣ b := by
  let t := dvd_neg_of_dvd h
  rwa [neg_neg] at t
#align dvd_of_dvd_neg dvd_of_dvd_neg

/-- An element a of a semigroup with a distributive negation divides the negation of an element b
iff a divides b. -/
@[simp]
theorem dvd_neg (a b : α) : a ∣ -b ↔ a ∣ b :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩
#align dvd_neg dvd_neg

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by simp [hc]⟩
#align neg_dvd_of_dvd neg_dvd_of_dvd

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b := by
  let t := neg_dvd_of_dvd h
  rwa [neg_neg] at t
#align dvd_of_neg_dvd dvd_of_neg_dvd

/-- The negation of an element a of a semigroup with a distributive negation divides
another element b iff a divides b. -/
@[simp]
theorem neg_dvd (a b : α) : -a ∣ b ↔ a ∣ b :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩
#align neg_dvd neg_dvd

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  rw [sub_eq_add_neg]
  exact dvd_add h₁ (dvd_neg_of_dvd h₂)
#align dvd_sub dvd_sub

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  ⟨fun h₂ => dvd_add h₂ h, fun H => by have t := dvd_sub H h ; rwa [add_sub_cancel] at t⟩
#align dvd_add_iff_left dvd_add_iff_left

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c := by
  rw [add_comm] ; exact dvd_add_iff_left h
#align dvd_add_iff_right dvd_add_iff_right

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  (dvd_add_iff_left h).symm
#align dvd_add_left dvd_add_left

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  (dvd_add_iff_right h).symm
#align dvd_add_right dvd_add_right

theorem dvd_iff_dvd_of_dvd_sub {a b c : α} (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  constructor
  · intro h'
    convert dvd_sub h' h
    exact Eq.symm (sub_sub_self b c)
  · intro h'
    convert dvd_add h h'
    exact eq_add_of_sub_eq rfl
#align dvd_iff_dvd_of_dvd_sub dvd_iff_dvd_of_dvd_sub

--porting note: Needed to give an explicit argument to `dvd_neg`
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg a, neg_sub]
#align dvd_sub_comm dvd_sub_comm

end NonUnitalRing

section Ring

variable [Ring α] {a b c : α}

set_option linter.deprecated false in
theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 :=
  (dvd_add_iff_right (@two_dvd_bit0 _ _ a)).symm
#align two_dvd_bit1 two_dvd_bit1

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)
#align dvd_add_self_left dvd_add_self_left

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)
#align dvd_add_self_right dvd_add_self_right

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y) using 1
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]
#align dvd_mul_sub_mul dvd_mul_sub_mul

end NonUnitalCommRing
