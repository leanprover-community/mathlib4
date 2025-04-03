/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Algebra

#align_import linear_algebra.matrix.finite_dimensional from "leanprover-community/mathlib"@"b1c23399f01266afe392a0d8f71f599a0dad4f7b"

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `Module.Finite.matrix`; this file
exists only to provide an entry in the instance list for `FiniteDimensional`.

## Main definitions

 * `Matrix.finiteDimensional`: matrices form a finite dimensional vector space over a field `K`
 * `LinearMap.finiteDimensional`

## Tags

matrix, finite dimensional, findim, finrank

-/


universe u v

namespace Matrix

section FiniteDimensional

variable {m n : Type*} {R : Type v} [Field R]

instance finiteDimensional [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  Module.Finite.matrix

end FiniteDimensional

end Matrix

namespace LinearMap

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

instance finiteDimensional : FiniteDimensional K (V →ₗ[K] W) :=
  Module.Finite.linearMap _ _ _ _
#align linear_map.finite_dimensional LinearMap.finiteDimensional

variable {A : Type*} [Ring A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W]
  [IsScalarTower K A W]

/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, as they form a subspace of all `k`-linear maps. -/
instance finiteDimensional' : FiniteDimensional K (V →ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsLinearMap K A V W) (restrictScalars_injective _)
#align linear_map.finite_dimensional' LinearMap.finiteDimensional'

end LinearMap
