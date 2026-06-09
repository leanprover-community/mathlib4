/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

noncomputable section

open Finset Function Module
open scoped Affine

namespace Affine

variable {n : ℕ}
variable (k : Type*) {V : Type*} (P : Type*)

namespace Simplex

section ofBasis

def mkOfAffineBasis [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
  (b : AffineBasis (Fin (n + 1)) k P) : Simplex k P n := mk b b.ind

def mkOfBasis [Field k] [AddCommGroup V] [Module k V] (b : Basis (Fin n) k V) : Simplex k V n :=
  mk (Fin.cons 0 b) <| by
    rw [affineIndependent_iff_finrank_vectorSpan_eq k (Fin.cons 0 b) ?_]
    -- have : False := by trivial
    try
      have : False := by trivial
    have : True := by try try?
    sorry

example : 1 + 1 = 2 := by
  have : True := by try try?
  norm_num

end ofBasis

end Simplex

namespace piLp

section stdAffineSimplex

end stdAffineSimplex

end piLp
