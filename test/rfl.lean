import Mathlib.Tactic.Relation.Rfl

@[refl] def eqRefl {α : Type} (a : α) : a = a := Eq.refl a

example (a : ℕ) : a = a := by rfl

open Setoid

variable {α : Sort u} [Setoid α]

@[refl] def iseqv_refl (a : α) : a ≈ a :=
  iseqv.refl a

example (a : α) : a ≈ a := by rfl
