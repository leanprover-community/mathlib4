import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Basic

section AddCommSemigroup_lemmas

variable {A : Type u} [AddCommSemigroup A]

theorem add_add_add_comm (a b c d : A) : (a + b) +(c + d) = (a + c) + (b + d) :=
by simp [add_left_comm, add_assoc]

end AddCommSemigroup_lemmas

section CommSemigroup_lemmas

variable {M : Type u} [CommSemigroup M]

theorem mul_mul_mul_comm (a b c d : M) : (a * b) * (c * d) = (a * c) * (b * d) :=
by simp [mul_assoc, mul_left_comm]

end CommSemigroup_lemmas
