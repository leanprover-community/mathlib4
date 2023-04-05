import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Tactic.Ring

open List

theorem list_length_concat (α : Type) (L M : List α) : List.length (L ++ M ++ L) = List.length (M ++ L ++ L) := by
  rw [List.length_append, List.length_append, List.length_append, List.length_append]
  rw [Nat.add_assoc, Nat.add_comm (List.length M) (List.length L), Nat.add_assoc]
  rw [Nat.add_comm (List.length L) (List.length M)]
