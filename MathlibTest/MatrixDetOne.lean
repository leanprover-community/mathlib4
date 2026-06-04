import Mathlib.LinearAlgebra.Determinant

/--
Check that using Matrix.det_one for an explicit matrix doesn't cause a
(kernel) deep recursion detected
error, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/kernel.20deep.20recursion.20detected
-/

example : (1 : Matrix (Fin 8) (Fin 8) ℚ).det = 1 := by
  rw [Matrix.det_one]

example : (1 : Matrix (Fin 8) (Fin 8) ℚ).det = 1 := Matrix.det_one

example : (1 : Matrix (Fin 8) (Fin 8) ℚ).det = 1 := by
  have := Matrix.det_one (n := Fin 8) (R := ℚ)
  exact this

/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : (1 : Matrix (Fin 8) (Fin 8) ℚ).det = 1 := by
  unfold Matrix.det Matrix.detRowAlternating MultilinearMap.alternatization
  sorry
