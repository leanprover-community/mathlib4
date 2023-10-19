/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.Data.Matrix.Basic

/-!
# Elementary Matrix
-/

namespace Matrix

universe u v

open Matrix

variable {n : Type u} [DecidableEq n] {R : Type v}

/-- A matrix with only one nonzero element.-/
def Single [AddMonoid R] (i j : n) (c : R) : Matrix n n R := of fun (k1 : n) (k2 : n) =>
  if k1 = i ∧ k2 = j then c
  else 0

/-- A matrix of elementary row/column operation.
Multiplying this matrix on the left is equivalent to
adding `c` times the j-th row to the i-th row.
Multiplying this matrix on the right is equivalent to
adding `c` times the i-th column to the j-th column.
-/
def Elementary [AddMonoidWithOne R] (i j : n) (c : R) : Matrix n n R := 1 + Single i j c
