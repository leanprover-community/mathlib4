import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

import Mathlib.LinearAlgebra.UnitaryGroup

noncomputable def one  : Matrix (Fin 3) (Fin 3) Real := 1

theorem one_orthogonal : one ∈ Matrix.orthogonalGroup (Fin 3) Real := by
  exact Submonoid.instCompleteLatticeSubmonoid.proof_16 (Matrix.orthogonalGroup (Fin 3) ℝ) one rfl



noncomputable def matrix_a'_SO := Matrix.specialOrthogonalGroup.mkOfDetEqOne (Fin 3) Real one (by simp [one]) (by simp [one])
