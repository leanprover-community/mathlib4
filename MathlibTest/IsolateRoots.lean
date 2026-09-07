module

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IsolateRoots

open Polynomial

noncomputable section

-- Distinct roots, including the square-free-core transport.
noncomputable def repeated : Hex.IsolatedRealRoots ((X - 1) ^ 2 * (X - 3) : ℚ[X]) 2 :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : ℚ[X])

example : Fintype.card (((X - 1) ^ 2 * (X - 3) : ℚ[X]).rootSet ℝ) = 2 :=
  repeated.card_rootSet (by apply Monic.ne_zero; monicity <;> norm_num)

-- Integer and real coefficient rings use the same cardinality API.
noncomputable def integer : Hex.IsolatedRealRoots (X ^ 4 - 2 : ℤ[X]) 2 :=
  isolate_roots (X ^ 4 - 2 : ℤ[X])

example : Fintype.card ((X ^ 4 - 2 : ℤ[X]).rootSet ℝ) = 2 :=
  integer.card_rootSet (by apply Monic.ne_zero; monicity; norm_num)

noncomputable def real : Hex.IsolatedRealRoots (X ^ 2 + 1 : ℝ[X]) 0 :=
  isolate_roots (X ^ 2 + 1 : ℝ[X])

example : Fintype.card ((X ^ 2 + 1 : ℝ[X]).rootSet ℝ) = 0 :=
  real.card_rootSet (by apply Monic.ne_zero; monicity; norm_num)

-- Constants have no roots; an incorrect requested count is rejected.
example : Hex.IsolatedRealRoots (7 : ℚ[X]) 0 := isolate_roots (7 : ℚ[X])

#check_failure (isolate_roots (X ^ 2 - 2 : ℚ[X]) :
  Hex.IsolatedRealRoots (X ^ 2 - 2 : ℚ[X]) 3)
