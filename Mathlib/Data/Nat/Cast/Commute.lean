/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

variable {α β : Type*}

namespace Nat

section Commute

variable [NonAssocSemiring α]

theorem cast_commute (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)
#align nat.cast_commute Nat.cast_commute

theorem _root_.Commute.ofNat_left (n : ℕ) [n.AtLeastTwo] (x : α) : Commute (OfNat.ofNat n) x :=
  n.cast_commute x

theorem cast_comm (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq
#align nat.cast_comm Nat.cast_comm

theorem commute_cast (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm
#align nat.commute_cast Nat.commute_cast

theorem _root_.Commute.ofNat_right (x : α) (n : ℕ) [n.AtLeastTwo] : Commute x (OfNat.ofNat n) :=
  n.commute_cast x

end Commute
end Nat

namespace SemiconjBy
variable [Semiring α] {a x y : α}

@[simp]
lemma natCast_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h
#align semiconj_by.cast_nat_mul_right SemiconjBy.natCast_mul_right

@[simp]
lemma natCast_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h
#align semiconj_by.cast_nat_mul_left SemiconjBy.natCast_mul_left

@[simp]
lemma natCast_mul_natCast_mul (h : SemiconjBy a x y) (m n : ℕ) :
    SemiconjBy (m * a) (n * x) (n * y) :=
  (h.natCast_mul_left m).natCast_mul_right n
#align semiconj_by.cast_nat_mul_cast_nat_mul SemiconjBy.natCast_mul_natCast_mul

end SemiconjBy

namespace Commute
variable [Semiring α] {a b : α}

@[simp] lemma natCast_mul_right (h : Commute a b) (n : ℕ) : Commute a (n * b) :=
  SemiconjBy.natCast_mul_right h n
#align commute.cast_nat_mul_right Commute.natCast_mul_right

@[simp] lemma natCast_mul_left (h : Commute a b) (n : ℕ) : Commute (n * a) b :=
  SemiconjBy.natCast_mul_left h n
#align commute.cast_nat_mul_left Commute.natCast_mul_left

@[simp] lemma natCast_mul_natCast_mul (h : Commute a b) (m n : ℕ) : Commute (m * a) (n * b) :=
  SemiconjBy.natCast_mul_natCast_mul h m n
#align commute.cast_nat_mul_cast_nat_mul Commute.natCast_mul_natCast_mul

variable (a) (m n : ℕ)

-- Porting note (#10618): `simp` can prove this using `Commute.refl`, `Commute.natCast_mul_right`
-- @[simp]
lemma self_natCast_mul : Commute a (n * a) := (Commute.refl a).natCast_mul_right n
#align commute.self_cast_nat_mul Commute.self_natCast_mul

-- Porting note (#10618): `simp` can prove this using `Commute.refl`, `Commute.natCast_mul_left`
-- @[simp]
lemma natCast_mul_self : Commute (n * a) a := (Commute.refl a).natCast_mul_left n
#align commute.cast_nat_mul_self Commute.natCast_mul_self

-- Porting note (#10618): `simp` can prove this using `Commute.refl`, `Commute.natCast_mul_left`,
-- `Commute.natCast_mul_right`
-- @[simp]
lemma self_natCast_mul_natCast_mul : Commute (m * a) (n * a) :=
  (Commute.refl a).natCast_mul_natCast_mul m n
#align commute.self_cast_nat_mul_cast_nat_mul Commute.self_natCast_mul_natCast_mul

@[deprecated (since := "2024-05-27")] alias cast_nat_mul_right := natCast_mul_right
@[deprecated (since := "2024-05-27")] alias cast_nat_mul_left := natCast_mul_left
@[deprecated (since := "2024-05-27")] alias cast_nat_mul_cast_nat_mul := natCast_mul_natCast_mul
@[deprecated (since := "2024-05-27")] alias self_cast_nat_mul := self_natCast_mul
@[deprecated (since := "2024-05-27")] alias cast_nat_mul_self := natCast_mul_self
@[deprecated (since := "2024-05-27")]
alias self_cast_nat_mul_cast_nat_mul := self_natCast_mul_natCast_mul

end Commute
