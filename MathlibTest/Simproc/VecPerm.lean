import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.Simproc.VecPerm

open FinVec

variable {α : Type*} (a b c d : α)

example : ![a, b, c] ∘ Equiv.swap 0 1 = ![b, a, c] := by
  simp only [vecPerm]

example : ![a, b, c] ∘ Equiv.swap 0 2 = ![c, b, a] := by
  simp only [vecPerm]

example : ![a, b, c] ∘ c[0, 1] = ![b, a, c] := by
  simp only [vecPerm]

example : ![a, b, c] ∘ c[2, 0, 1] = ![b, c, a] := by
  simp only [vecPerm]

example : ![a, b, c, d] ∘ c[2, 3, 0, 1] = ![b, c, d, a] := by
  simp only [vecPerm]

example : ![a, b, c, d] ∘ ![1, 3, 1, 3] = ![b, d, b, d] := by
  simp only [vecPerm]
