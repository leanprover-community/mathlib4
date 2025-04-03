/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/


variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {R : Type*} [Semiring R] [InvariantBasisNumber R]

open Matrix

theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M * N = 1)
    (h' : N * M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)
