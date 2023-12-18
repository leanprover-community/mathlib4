import Mathlib.Data.Nat.Basic
def foo (x : ℕ) (h : x < 5) : ℕ := x
def bar (x : ℕ) (h : x ≥ 6) : ℕ :=
  if h₀ : x < 4 then
    foo x (by have h₁ : 4 ≤ 5 := by simp
              revert h₀
              revert h₁
              apply le.trans_lt')
  else 0
