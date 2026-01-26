import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Torsion-free rings

A characteristic zero domain is torsion-free.
-/

public section

namespace IsDomain

-- This instance is potentially expensive, and is known to slow down grind.
-- Please keep it as a scoped instance.
scoped instance (R : Type*) [Semiring R] [IsDomain R] [CharZero R] :
    IsAddTorsionFree R where
  nsmul_right_injective n h a b w := by
    simp only [nsmul_eq_mul, mul_eq_mul_left_iff, Nat.cast_eq_zero] at w
    grind

end IsDomain

namespace MonoidHom
variable {R M : Type*} [Ring R] [Monoid M] [IsMulTorsionFree M] (f : R →* M)

lemma map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff_left (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]

@[simp] lemma map_neg (x : R) : f (-x) = f x := by rw [← neg_one_mul, map_mul, map_neg_one, one_mul]

lemma map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [← map_neg, neg_sub]

end MonoidHom
