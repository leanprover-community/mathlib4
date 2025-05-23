/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute

/-!
# Cast of natural numbers: lemmas about `Commute`

-/

variable {α : Type*}

namespace Nat

section Commute

variable [NonAssocSemiring α]

theorem cast_commute (n : ℕ) (x : α) : Commute (n : α) x := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Commute.zero_left x
  | succ n ihn => rw [Nat.cast_succ]; exact ihn.add_left (Commute.one_left x)

theorem _root_.Commute.ofNat_left (n : ℕ) [n.AtLeastTwo] (x : α) : Commute (OfNat.ofNat n) x :=
  n.cast_commute x

theorem cast_comm (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).eq

theorem commute_cast (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm

theorem _root_.Commute.ofNat_right (x : α) (n : ℕ) [n.AtLeastTwo] : Commute x (OfNat.ofNat n) :=
  n.commute_cast x

end Commute
end Nat

namespace SemiconjBy
variable [Semiring α] {a x y : α}

@[simp]
lemma natCast_mul_right (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Nat.commute_cast _ _) h

@[simp]
lemma natCast_mul_left (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Nat.cast_commute _ _) h

lemma natCast_mul_natCast_mul (h : SemiconjBy a x y) (m n : ℕ) :
    SemiconjBy (m * a) (n * x) (n * y) := by
  simp [h]

end SemiconjBy

namespace Commute
variable [Semiring α] {a b : α}

@[simp] lemma natCast_mul_right (h : Commute a b) (n : ℕ) : Commute a (n * b) :=
  SemiconjBy.natCast_mul_right h n

@[simp] lemma natCast_mul_left (h : Commute a b) (n : ℕ) : Commute (n * a) b :=
  SemiconjBy.natCast_mul_left h n

lemma natCast_mul_natCast_mul (h : Commute a b) (m n : ℕ) : Commute (m * a) (n * b) := by
  simp [h]

variable (a) (m n : ℕ)

lemma self_natCast_mul : Commute a (n * a) := (Commute.refl a).natCast_mul_right n

lemma natCast_mul_self : Commute (n * a) a := (Commute.refl a).natCast_mul_left n

lemma self_natCast_mul_natCast_mul : Commute (m * a) (n * a) :=
  (Commute.refl a).natCast_mul_natCast_mul m n

end Commute
