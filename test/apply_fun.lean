import Mathlib.Tactic.ApplyFun
import Mathlib.Init.Function
-- import Mathlib.Data.Matrix.Basic

open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f := by
  intros x x' h
  apply_fun g at h
  exact H h

-- TODO restore and port these tests from mathlib3

-- example (x : ℤ) (h : x = 1) : 1 = 1 :=
-- begin
--   revert h,
--   refine (λ h, _),
--   apply_fun (λ p, p) at h,
--   refl,
-- end

-- example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f) (h : a ≤ b) : f a ≤ f b :=
-- begin
--   apply_fun f at h,
--   assumption,
--   assumption
-- end

-- example (a b : ℤ) (h : a = b) : a + 1 = b + 1 :=
-- begin
--   apply_fun (λ n, n+1) at h,
--   -- check that `h` was β-reduced
--   guard_hyp' h : a + 1 = b + 1,
--   exact h
-- end

-- example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f) (h : a ≤ b) : f a ≤ f b :=
-- begin
--   apply_fun f at h using monof,
--   assumption
-- end

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

-- example (n m : ℕ) (f : ℕ → ℕ) (h : f n ≠ f m) : n ≠ m :=
-- begin
--   apply_fun f,
--   exact h,
-- end

-- example (n m : ℕ) (f : ℕ → ℕ) (w : function.injective f) (h : f n = f m) : n = m :=
-- begin
--   apply_fun f,
--   assumption,
-- end

-- example (n m : ℕ) (f : ℕ → ℕ) (w : function.injective f ∧ true) (h : f n = f m) : n = m :=
-- begin
--   apply_fun f using w.1,
--   assumption,
-- end

-- example (n m : ℕ) (f : ℕ → ℕ) (w : function.injective f ∧ true) (h : f n = f m) : n = m :=
-- begin
--   apply_fun f,
--   assumption,
--   exact w.1,
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
