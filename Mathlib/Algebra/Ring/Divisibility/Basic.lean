/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.Defs

#align_import algebra.ring.divisibility from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib.Algebra.Ring.Divisibility.Lemmas` which is not subject to this import constraint.
-/


variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β] (f : F)

theorem map_dvd_iff {a b} : f a ∣ f b ↔ a ∣ b :=
  let f := MulEquivClass.toMulEquiv f
  ⟨fun h ↦ by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

theorem MulEquiv.decompositionMonoid [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by
    rw [← map_dvd_iff f, map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨symm f a₁, symm f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, ← map_mul, eq_symm_apply]
    iterate 2 erw [(f : α ≃* β).apply_symm_apply]
    exact h

end Semigroup

section DistribSemigroup

variable [Add α] [Semigroup α]

theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])
#align dvd_add dvd_add

alias Dvd.dvd.add := dvd_add
#align has_dvd.dvd.add Dvd.dvd.add

end DistribSemigroup

set_option linter.deprecated false in
@[simp]
theorem two_dvd_bit0 [Semiring α] {a : α} : 2 ∣ bit0 a :=
  ⟨a, bit0_eq_two_mul _⟩
#align two_dvd_bit0 two_dvd_bit0

section Semiring
variable [Semiring α] {a b c : α} {m n : ℕ}

lemma min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b :=
  ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)
#align min_pow_dvd_add min_pow_dvd_add

end Semiring

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)
#align has_dvd.dvd.linear_comb Dvd.dvd.linear_comb

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b c : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp]
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]
#align dvd_neg dvd_neg

/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp]
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]
#align neg_dvd neg_dvd

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd
#align has_dvd.dvd.of_neg_left Dvd.dvd.of_neg_left
#align has_dvd.dvd.neg_left Dvd.dvd.neg_left

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg
#align has_dvd.dvd.of_neg_right Dvd.dvd.of_neg_right
#align has_dvd.dvd.neg_right Dvd.dvd.neg_right

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right
#align dvd_sub dvd_sub

alias Dvd.dvd.sub := dvd_sub
#align has_dvd.dvd.sub Dvd.dvd.sub

/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩
#align dvd_add_left dvd_add_left

/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h
#align dvd_add_right dvd_add_right

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  -- Porting note: Needed to give `α` explicitly
  simpa only [← sub_eq_add_neg] using dvd_add_left ((dvd_neg (α := α)).2 h)
#align dvd_sub_left dvd_sub_left

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  -- Porting note: Needed to give `α` explicitly
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg (α := α)]
#align dvd_sub_right dvd_sub_right

theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]
#align dvd_iff_dvd_of_dvd_sub dvd_iff_dvd_of_dvd_sub

-- Porting note: Needed to give `α` explicitly
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg (α := α), neg_sub]
#align dvd_sub_comm dvd_sub_comm

end NonUnitalRing

section Ring

variable [Ring α] {a b c : α}

set_option linter.deprecated false in
theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 :=
  dvd_add_right two_dvd_bit0
#align two_dvd_bit1 two_dvd_bit1

/-- An element a divides the sum a + b if and only if a divides b. -/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)
#align dvd_add_self_left dvd_add_self_left

/-- An element a divides the sum b + a if and only if a divides b. -/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)
#align dvd_add_self_right dvd_add_self_right

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  dvd_sub_right dvd_rfl
#align dvd_sub_self_left dvd_sub_self_left

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  dvd_sub_left dvd_rfl
#align dvd_sub_self_right dvd_sub_self_right

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
