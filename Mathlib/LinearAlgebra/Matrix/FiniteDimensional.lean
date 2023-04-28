/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.finite_dimensional
! leanprover-community/mathlib commit b1c23399f01266afe392a0d8f71f599a0dad4f7b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.FreeModule.Finite.Matrix
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `module.finite.matrix`; this file
exists only to provide an entry in the instance list for `finite_dimensional`.

## Main definitions

 * `matrix.finite_dimensional`: matrices form a finite dimensional vector space over a field `K`
 * `linear_map.finite_dimensional`

## Tags

matrix, finite dimensional, findim, finrank

-/


universe u v

namespace Matrix

section FiniteDimensional

variable {m n : Type _} {R : Type v} [Field R]

instance [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  Module.Finite.matrix

end FiniteDimensional

end Matrix

namespace LinearMap

variable {K : Type _} [Field K]

variable {V : Type _} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {W : Type _} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

instance finiteDimensional : FiniteDimensional K (V →ₗ[K] W) :=
  Module.Finite.linearMap _ _
#align linear_map.finite_dimensional LinearMap.finiteDimensional

variable {A : Type _} [Ring A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W]
  [IsScalarTower K A W]

/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, as they form a subspace of all `k`-linear maps. -/
instance finite_dimensional' : FiniteDimensional K (V →ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsLinearMap K A V W) (restrictScalars_injective _)
#align linear_map.finite_dimensional' LinearMap.finite_dimensional'

end LinearMap

