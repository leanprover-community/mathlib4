import Mathlib

example {α : Type} [Fintype α] {β : α → Type} [∀ a, Fintype (β a)] : Fintype (Σ a, β a) := inferInstance
