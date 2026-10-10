module

import Mathlib.Tactic.Simproc.IsIndecomposable

import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

open Matrix CartanMatrix

/-! ## Literals over `ℤ` -/

-- No edge from `0` to `1`, so the search from `0` fails.
example : ¬(!![2, 0; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

-- No edge from `1` to `0`, so the search from `0` succeeds and the search back to `0` fails.
example : ¬(!![2, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp [reduceIsIndecomposable]

example : (!![0] : Matrix (Fin 1) (Fin 1) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (0 : Matrix (Fin 0) (Fin 0) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

/-! ## Matrices given by definitions -/

-- an existing definition, after rewriting it to a literal
example : (E 8).IsIndecomposable := by
  rw [E_eight_eq]
  simp only [reduceIsIndecomposable]

example : ¬(D 2).IsIndecomposable := by
  rw [D_two]
  simp [reduceIsIndecomposable]

/-! ## Other entry types -/

example : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℕ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

example : (!![1/2, 1/3; 1/5, 0] : Matrix (Fin 2) (Fin 2) ℚ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

/-! ## Terms the simproc skips -/

-- Equality on `ℝ` is classical, so the kernel cannot decide it.
/-- error: `simp` made no progress -/
#guard_msgs in
example : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- a matrix given by a function; this will be handled in a future PR
/-- error: `simp` made no progress -/
#guard_msgs in
example : (of fun i j : Fin 2 ↦ if i = j then (2 : ℤ) else -1).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- a free variable
/-- error: `simp` made no progress -/
#guard_msgs in
example (x : ℤ) : (!![x, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- an index type other than `Fin n`
/-- error: `simp` made no progress -/
#guard_msgs in
example : (fromBlocks !![1] !![1] !![1] !![1] :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- a dimension that is not a numeral
/-- error: `simp` made no progress -/
#guard_msgs in
example : (1 : Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℤ).IsIndecomposable := by
  simp only [reduceIsIndecomposable]

-- entries without `DecidableEq`
/-- error: `simp` made no progress -/
#guard_msgs in
example : (!![fun _ : ℕ ↦ (0 : ℤ)] : Matrix (Fin 1) (Fin 1) (ℕ → ℤ)).IsIndecomposable := by
  simp only [reduceIsIndecomposable]
