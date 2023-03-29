import Mathlib.Tactic.GPT.Sagredo.Dialog
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Tactic.Ring

open List

example (α : Type) (L M : List α) : (L ++ M ++ L).length = (M ++ L ++ L).length := by
  sagredo
