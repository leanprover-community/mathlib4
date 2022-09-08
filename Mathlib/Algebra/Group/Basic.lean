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

section AddLeftCancelMonoid_lemmas
-- too lazy to do mul versions and right versions

variable {A : Type u} [AddMonoid A] [IsAddLeftCancel A] {a b : A}

lemma add_right_eq_self : a + b = a ↔ b = 0 :=
by rw [←add_left_cancel_iff (c := 0), add_zero]

lemma self_eq_add_right : a = a + b ↔ b = 0 :=
by rw [←add_left_cancel_iff (c := 0), add_zero, eq_comm]

end AddLeftCancelMonoid_lemmas
