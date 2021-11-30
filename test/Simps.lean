import Mathlib.Tactic.Simps

/-!
We currently only have a no-operation implementation of `@[simps]`,
so there isn't much to test here.
-/

structure X :=
(a : Nat)
(h : a = 3)

@[simps]
def x : X :=
⟨3, rfl⟩
