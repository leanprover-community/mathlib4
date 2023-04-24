import Mathlib.Init.Data.Nat.Notation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ApplyFun
import Mathlib.Init.Function
import Mathlib.Data.Fintype.Card
-- import Mathlib.Data.Matrix.Basic

open Function

example (f : ℕ → ℕ) (h : f x = f y) : x = y := by
  apply_fun f
  · guard_target = f x = f y
    assumption
  · guard_target = Injective f
    sorry

example (f : ℕ → ℕ → ℕ) (h : f 1 x = f 1 y) (hinj : ∀ n, Injective (f n)) : x = y := by
  apply_fun f ?foo
  guard_target = f ?foo x = f ?foo y
  case foo => exact 1
  · exact h
  · apply hinj

-- Uses `refine`-style rules for placeholders:
example (f : ℕ → ℕ → ℕ) : x = y := by
  fail_if_success apply_fun f _
  sorry

example (f : ℕ → ℕ → ℕ) (h : f 1 x = f 1 y) (hinj : Injective (f 1)) : x = y := by
  apply_fun f _ using hinj
  -- Solves for the hole using unification since it makes use of the `using` clause.
  guard_target = f 1 x = f 1 y
  assumption

-- A test to show a perhaps unexpected consequence of how injectivity is auto-proved:
example (f : ℕ → ℕ → ℕ) (h : f 1 x = f 1 y) (hinj : Injective (f 1)) : x = y := by
  apply_fun f _
  -- Solves for the hole using unification since `hinj` is pulled in by `assumption`.
  guard_target = f 1 x = f 1 y
  assumption

-- A test to show a perhaps unexpected consequence of how injectivity is auto-proved:
example (f : ℕ → ℕ) (h : f x = f y) (hinj : Injective f) : x = y := by
  apply_fun _
  guard_target = f x = f y
  assumption

-- Make sure named holes generate new goals for `≠`
example (f : ℕ → ℕ → ℕ) (h : f 1 x ≠ f 1 y) : x ≠ y := by
  apply_fun f ?foo
  guard_target = f ?foo x ≠ f ?foo y
  case foo => exact 1
  assumption

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective $ g ∘ f) : Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h

example (x : Int) (h : x = 1) : 1 = 1 := by
  apply_fun (fun p => p) at h
  rfl

example (a b : Int) (h : a = b) : a + 1 = b + 1 := by
  -- Make sure that we infer the type of the function only after we see the hypothesis:
  apply_fun (fun n => n + 1) at h
  -- check that `h` was β-reduced
  guard_hyp h :ₛ a + 1 = b + 1
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

example (n m : ℕ) (f : ℕ ≃ ℕ) (h : f n ≠ f m) : n ≠ m := by
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

example (f : ℕ ≃ ℕ) (h : f x = f y) : x = y := by
  apply_fun f
  assumption

example (f : ℕ ≃ ℕ) (h : f x = f y) : x = y := by
  apply_fun f using f.injective
  assumption

example {x y : ℕ} (h : Equiv.refl ℕ x = Equiv.refl ℕ y) : x = y := by
  apply_fun Equiv.refl ℕ
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

example : ∀ m n : ℕ, m = n → (m < 2) = (n < 2) := by
  refine fun m n h => ?_
  apply_fun (· < 2) at h
  exact h

example : ∀ m n : ℕ, m = n → (m < 2) = (n < 2) := by
  intro m n h
  apply_fun (· < 2) at h
  exact h

example (f : ℕ ≃ ℕ) (a b : ℕ) (h : a = b) : True := by
  apply_fun f at h
  guard_hyp h : f a = f b
  trivial

example (f : ℤ ≃ ℤ) (a b : ℕ) (h : a = b) : True := by
  apply_fun f at h
  guard_hyp h : f a = f b
  trivial

example (f : ℤ ≃ ℤ) (a b : α) (h : a = b) : True := by
  fail_if_success apply_fun f at h
  trivial

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : True := by
  apply_fun f at h
  guard_hyp h : f a = f b
  trivial

example (f : {i : Nat} → Fin i → ℕ) (a b : Fin 37) (h : a = b) : True := by
  apply_fun f at h
  guard_hyp h : f a = f b
  trivial

example (f : (p : Prop) → [Decidable p] → Nat) (p q : Prop) (h : p = q)
    (h' : {n m : Nat} → n = m → True) : True := by
  classical
  apply_fun f at h
  apply h'
  exact h

example (f : (p : Prop) → [Decidable p] → Nat) (p q : Prop) (h : p = q)
    (h' : {n m : Nat} → n = m → True) : True := by
  classical
  apply_fun (fun x [Decidable x] => f x) at h
  apply h'
  exact h

example (a b : ℕ) (h : a = b) : True := by
  apply_fun (fun i => i + ?_) at h
  · trivial
  · exact 37

-- Check that it can solve congruence (needs Subsingleton.elim for the fintype instances)
example (α β : Type u) [Fintype α] [Fintype β] (h : α = β) : True := by
  apply_fun Fintype.card at h
  guard_hyp h : Fintype.card α = Fintype.card β
  trivial
