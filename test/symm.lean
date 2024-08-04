import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit true
-- testing that the attribute is recognized
@[symm] def eq_symm {α : Type} (a b : α) : a = b → b = a := Eq.symm

example (a b : Nat) : a = b → b = a := by intros; symm; assumption
example (a b : Nat) : a = b → True → b = a := by intro h _; symm at h; assumption

def sameParity : Nat → Nat → Prop
  | n, m => n % 2 = m % 2

@[symm] def sameParity_symm (n m : Nat) : sameParity n m → sameParity m n := Eq.symm

example (a b : Nat) : sameParity a b → sameParity b a := by intros; symm; assumption

example (a b c : Nat) (ab : a = b) (bc : b = c) : c = a := by
  symm_saturate
  -- Run twice to check that we don't add repeated copies.
  -- Unfortunately `guard_hyp_nums` doesn't seem to work so I haven't made an assertion.
  symm_saturate
  apply Eq.trans <;> assumption

def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

structure MulEquiv (M N : Type u) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

/--
info: MulEquiv : (M N : Type u_1) → [inst : Mul M] → [inst : Mul N] → Type u_1
-/
#guard_msgs in
#check @MulEquiv

infixl:25 " ≃* " => MulEquiv

@[symm]
def foo_symm {M N : Type _} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  { h.toEquiv.symm with map_mul' := (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul }

def MyEq (n m : Nat) := ∃ k, n + k = m ∧ m + k = n

@[symm] lemma MyEq.symm {n m : Nat} (h : MyEq n m) : MyEq m n := by
  rcases h with ⟨k, h1, h2⟩
  exact ⟨k, h2, h1⟩

example {n m : Nat} (h : MyEq n m) : MyEq m n := by
  symm
  assumption
