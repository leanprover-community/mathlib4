import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.Simproc.VecPerm

open Mathlib.Tactic.FinVec

variable {α : Type*} (a b c d : α)

example : ![a, b, c] ∘ Equiv.swap 0 1 = ![b, a, c] := by
  simp -- this is dealt with using `Matrix.cons_cons_comp_swap_zero_one`

example : ![a, b, c] ∘ Equiv.swap 0 2 = ![c, b, a] := by
  simp [vecPerm, Equiv.swap_apply_def]

example : ![a, b, c] ∘ c[0, 1] = ![b, a, c] := by
  simp -- this is dealt with using `Matrix.cons_cons_comp_swap_zero_one`

example : ![a, b, c] ∘ c[2, 0, 1] = ![b, c, a] := by
  simp [vecPerm, Equiv.swap_apply_def]

example : ![a, b, c, d] ∘ c[2, 3, 0, 1] = ![b, c, d, a] := by
  simp [vecPerm, Equiv.swap_apply_def]

example : ![a, b, c, d] ∘ ![1, 3, 1, 3] = ![b, d, b, d] := by
  simp [vecPerm]

set_option linter.unusedSimpArgs false

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (u v w x : Fin 4) : ![a, b, c, d] ∘ ![u, v, w, x] = ![b, d, b, d] := by
  simp [vecPerm]
  guard_target = ![a, b, c, d] ∘ ![u, v, w, x] = ![b, d, b, d]
  sorry

/--
error: `simp` made no progress
-/
#guard_msgs in
example {n : Nat} (p q r : Fin n → Fin n) : p ∘ q = r := by
  simp [vecPerm]
