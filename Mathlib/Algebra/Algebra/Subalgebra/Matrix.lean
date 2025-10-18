/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Matrix subalgebras

In this file we define the subalgebra of square matrices with entries in some subalgebra.

## Main definitions

* `Subalgebra.matrix`: the subalgebra of square matrices with entries in some subalgebra.
-/

open Matrix
open Algebra

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A version of `Set.matrix` for `Subalgebra`s.
Given a `Subalgebra` `S`, `S.matrix` is the `Subalgebra` of square matrices `m`
all of whose entries `m i j` belong to `S`. -/
@[simps!]
def matrix (S : Subalgebra R A) : Subalgebra R (Matrix n n A) where
  __ := S.toSubsemiring.matrix
  algebraMap_mem' _ :=
    (diagonal_mem_matrix_iff (Subalgebra.zero_mem _)).mpr (fun _ => Subalgebra.algebraMap_mem _ _)

end Subalgebra
