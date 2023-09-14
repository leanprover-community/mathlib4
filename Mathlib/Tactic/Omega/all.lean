import Mathlib

set_option autoImplicit true

instance (x : Option α) : Decidable (x = none) := by
  cases x <;> (simp; infer_instance)

example (L : List (Option α)) : Decidable (∃ x ∈ L, x = none) := inferInstance

theorem List.mem_iff_exists_mem_eq {a : α} {L : List α} : a ∈ L ↔ ∃ x ∈ L, x = a := by
  simp

instance (L : List (Option α)) : Decidable (none ∈ L) := by
  rw [List.mem_iff_exists_mem_eq]
  infer_instance
