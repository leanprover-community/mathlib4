import Mathlib.Tactic.Simproc.Matrix

open Matrix

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu, transpose_of% 2 3, hv]

example (a b c d e f : Fin 37) : !![a, b, c; d, e, f]ᵀ = !![a, d; b, e; c, f] := by
  rw [transpose_of% 2 3]

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  rw [hu]
  simp only [matrix_transpose]
  rw [hv]

example (u : Matrix (Fin 2) (Fin 3) ℤ) (v : Matrix (Fin 3) (Fin 2) ℤ)
    (hu : u = !![1, 2, 3; 4, 5, 6]) (hv : v = !![1, 4; 2, 5; 3, 6]) :
    uᵀ = v := by
  simp [*]

/-- info: Try this: simp only [matrix_transpose] -/
#guard_msgs in
example : !![1, 2, 3; 4, 5, 6]ᵀ = !![1, 4; 2, 5; 3, 6] := by
  simp?

/-- error: simp made no progress -/
#guard_msgs in
example : !![1, 2, 3; 4, 5, 6]ᵀ = !![1, 4; 2, 5; 3, 6] := by
  simp [-matrix_transpose]

/-- error: simp made no progress -/
#guard_msgs in
example {n : ℕ} (u : Fin (OfNat.ofNat n) → Fin 3 → ℚ) : (of u)ᵀ = 0 := by
  simp only [matrix_transpose]
