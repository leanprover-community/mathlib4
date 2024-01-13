/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Basic
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

theorem commute_add_cast (r s : α) (n : ℕ) (h : Commute r s) :
    Commute r (s + n) :=
  h.add_right (commute_cast r n)

theorem add_cast_commute (r s : α) (n : ℕ) (h : Commute r s) :
    Commute (r + n) s :=
  h.add_left (cast_commute n s)

theorem add_cast_commute_add_cast (r s : α) (k n : ℕ) (h : Commute r s):
    Commute (r + k) (s + n) :=
  (h.add_left (cast_commute k s)).add_right (commute_cast (r+k) n)

end Commute
end Nat

namespace SemiconjBy
variable [Semiring α] {a x y : α}

@[simp]
lemma cast_nat_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h
#align semiconj_by.cast_nat_mul_right SemiconjBy.cast_nat_mul_right

@[simp]
lemma cast_nat_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h
#align semiconj_by.cast_nat_mul_left SemiconjBy.cast_nat_mul_left

@[simp]
lemma cast_nat_mul_cast_nat_mul (h : SemiconjBy a x y) (m n : ℕ) :
    SemiconjBy (m * a) (n * x) (n * y) :=
  (h.cast_nat_mul_left m).cast_nat_mul_right n
#align semiconj_by.cast_nat_mul_cast_nat_mul SemiconjBy.cast_nat_mul_cast_nat_mul

end SemiconjBy

namespace Commute
variable [Semiring α] {a b : α}

@[simp] lemma cast_nat_mul_right (h : Commute a b) (n : ℕ) : Commute a (n * b) :=
  SemiconjBy.cast_nat_mul_right h n
#align commute.cast_nat_mul_right Commute.cast_nat_mul_right

@[simp] lemma cast_nat_mul_left (h : Commute a b) (n : ℕ) : Commute (n * a) b :=
  SemiconjBy.cast_nat_mul_left h n
#align commute.cast_nat_mul_left Commute.cast_nat_mul_left

@[simp] lemma cast_nat_mul_cast_nat_mul (h : Commute a b) (m n : ℕ) : Commute (m * a) (n * b) :=
  SemiconjBy.cast_nat_mul_cast_nat_mul h m n
#align commute.cast_nat_mul_cast_nat_mul Commute.cast_nat_mul_cast_nat_mul

variable (a) (m n : ℕ)

-- Porting note: `simp` can prove this using `Commute.refl`, `Commute.cast_nat_mul_right`
-- @[simp]
lemma self_cast_nat_mul : Commute a (n * a) := (Commute.refl a).cast_nat_mul_right n
#align commute.self_cast_nat_mul Commute.self_cast_nat_mul

-- Porting note: `simp` can prove this using `Commute.refl`, `Commute.cast_nat_mul_left`
-- @[simp]
lemma cast_nat_mul_self : Commute (n * a) a := (Commute.refl a).cast_nat_mul_left n
#align commute.cast_nat_mul_self Commute.cast_nat_mul_self

-- Porting note: `simp` can prove this using `Commute.refl`, `Commute.cast_nat_mul_left`,
-- `Commute.cast_nat_mul_right`
-- @[simp]
lemma self_cast_nat_mul_cast_nat_mul : Commute (m * a) (n * a) :=
  (Commute.refl a).cast_nat_mul_cast_nat_mul m n
#align commute.self_cast_nat_mul_cast_nat_mul Commute.self_cast_nat_mul_cast_nat_mul

end Commute
