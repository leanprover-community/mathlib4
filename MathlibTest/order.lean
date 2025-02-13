import Mathlib.Tactic.Order.LinearOrder
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Int.Order.Basic

example (a b c d e : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

example (a b c d e : Nat) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : b ≠ d) :
    a < e := by
  order

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  order

example (a b : Int) (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) : a = b := by
  order

example {α : Type} [LinearOrder α] (a b : α) (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) : a = b := by
  order

example {α : Type} [PartialOrder α] (a b c d e : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : b ≠ d) :
    a < e := by
  order
