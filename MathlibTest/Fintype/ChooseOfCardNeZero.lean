import Mathlib.Data.Fintype.Choose

noncomputable section

example (α : Type*) [Fintype α] (h : Fintype.card α ≠ 0) : α :=
  Fintype.chooseOfCardNeZero α h
