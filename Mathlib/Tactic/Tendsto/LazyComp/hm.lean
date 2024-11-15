import Mathlib.Data.Vector.Defs

structure VectorN where
  n : ℕ
  v : Mathlib.Vector ℕ n

example (vn : VectorN) (h : vn.n = 0): vn.v.length = 0 := by
  generalize vn.n = k at *


-- to make `n` explicit argument
def length (n : ℕ) (v : Mathlib.Vector ℕ n) : ℕ := n

def n : ℕ := 1
def m : ℕ := 2

example (v : Mathlib.Vector ℕ (n + m)) : v.length = 3 := by
  unfold Mathlib.Vector.length
  rfl
  