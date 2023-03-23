import Mathlib.Tactic.ChatGPT.Dialog
import Mathlib.Data.List.Basic

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l := by
  gpt
