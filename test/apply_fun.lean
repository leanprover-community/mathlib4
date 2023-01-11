import Mathlib.Init.Data.Nat.Notation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Init.Function
-- import Mathlib.Data.Matrix.Basic

open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective $ g ∘ f) : Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h

example (x : Int) (h : x = 1) : 1 = 1 := by
  apply_fun (fun p => p) at h
  rfl

example (a b : Int) (h : a = b) : a + 1 = b + 1 := by
  -- Make sure that we infer the type of the function only after we see the hypothesis:
  apply_fun (fun n => n+1) at h
  -- check that `h` was β-reduced (in Lean3 this required additional work)
  guard_hyp h : a + 1 = b + 1
  exact h

-- Verify failure when applying a dependently typed function.
example (P : Nat → Type) (Q : (n : Nat) -> P n) (a b : Nat) (h : a = b) : True := by
  fail_if_success apply_fun Q at h
  trivial

-- TODO restore and port these tests from mathlib3

example (f : ℕ → ℕ) (a b : ℕ) (monof : Monotone f) (h : a ≤ b) : f a ≤ f b := by
  apply_fun f at h using monof
  assumption

example (f : ℕ → ℕ) (a b : ℕ) (monof : Monotone f) (h : a ≤ b) : f a ≤ f b := by
  apply_fun f at h
  · assumption
  · assumption

example (n m : ℕ) (f : ℕ → ℕ) (h : f n ≠ f m) : n ≠ m := by
  apply_fun f
  exact h

example (n m : ℕ) (f : ℕ → ℕ) (w : Function.Injective f) (h : f n = f m) : n = m := by
  apply_fun f
  assumption

example (n m : ℕ) (f : ℕ → ℕ) (w : Function.Injective f) (h : f n = f m) : n = m := by
  apply_fun f using w
  assumption

example (n m : ℕ) (f : ℕ → ℕ) (w : Function.Injective f ∧ true) (h : f n = f m) : n = m := by
  apply_fun f using w.1
  assumption

example (a b : List α) (P : a = b) : True := by
  apply_fun List.length at P
  trivial

-- -- monotonicity will be proved by `mono` in the next example
-- example (a b : ℕ) (h : a ≤ b) : a + 1 ≤ b + 1 :=
-- begin
--   apply_fun (λ n, n+1) at h,
--   exact h
-- end

-- example {n : Type} [fintype n] {X : Type} [semiring X]
--   (f : matrix n n X → matrix n n X) (A B : matrix n n X) (h : A * B = 0) : f (A * B) = f 0 :=
-- begin
--   apply_fun f at h,
--   -- check that our β-reduction didn't mess things up:
--   -- (previously `apply_fun` was producing `f (A.mul B) = f 0`)
--   guard_hyp' h : f (A * B) = f 0,
--   exact h,
-- end

-- -- Verify that `apply_fun` works with `fin.cast_succ`, even though it has an implicit argument.
-- example (n : ℕ) (a b : fin n) (H : a ≤ b) : a.cast_succ ≤ b.cast_succ :=
-- begin
--   apply_fun fin.cast_succ at H,
--   exact H,
-- end

-- example (n m : ℕ) (f : ℕ ≃ ℕ) (h : f n = f m) : n = m :=
-- begin
--   apply_fun f,
--   assumption,
-- end

-- example (n m : ℕ) (f : ℕ ≃o ℕ) (h : f n ≤ f m) : n ≤ m :=
-- begin
--   apply_fun f,
--   assumption,
-- end

-- example (n m : ℕ) (f : ℕ ≃o ℕ) (h : f n < f m) : n < m :=
-- begin
--   apply_fun f,
--   assumption,
-- end
