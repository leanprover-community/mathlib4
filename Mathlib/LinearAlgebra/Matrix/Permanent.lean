/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Basic

/-!
# Permanent of a matrix

This file defines the permanent of a matrix, `Matrix.perm`.

## Main definitions

 - `Matrix.perm`: the permanent of a square matrix, as a sum over permutations

-/

universe u v

open Equiv

namespace Matrix

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type v} [CommRing R]

/-- The permanent of a matrix defined as a sum over all permutations -/
def perm (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i

end Matrix
