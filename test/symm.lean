import Mathlib.Tactic.Relation.Symm
import Std.Tactic.ShowTerm
import Mathlib.Algebra.Hom.Group
import Mathlib.Logic.Equiv.Basic
-- testing that the attribute is recognized
@[symm] def eq_symm {α : Type} (a b : α) : a = b → b = a := Eq.symm

example (a b : Nat) : a = b → b = a := by intros; symm; assumption
example (a b : Nat) : a = b → True → b = a := by intro h _; symm at h; assumption

def sameParity : Nat → Nat → Prop
| n, m => n % 2 = m % 2

@[symm] def sameParity_symm (n m : Nat) : sameParity n m → sameParity m n := Eq.symm

example (a b : Nat) : sameParity a b → sameParity b a := by intros; symm; assumption


def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

structure MulEquiv (M N : Type u) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

#check @MulEquiv

infixl:25 " ≃* " => MulEquiv

@[symm]
-- with the "flip check" this is not recognized as a symm lemma:
-- the flipped final hypothesis
-- MulEquiv.{u_1} ?_uniq.10884 ?_uniq.10883 ?_uniq.10885 ?_uniq.10886
-- is not definitionally equal to the final hypothesis
-- MulEquiv.{u_1} ?_uniq.10883 ?_uniq.10884 ?_uniq.10885 ?_uniq.10886
def foo_symm {M N : Type _} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  { h.toEquiv.symm with map_mul' := (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul }
