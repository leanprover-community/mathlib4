/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.finite_dimensional
! leanprover-community/mathlib commit b1c23399f01266afe392a0d8f71f599a0dad4f7b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

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

variable {m n : Type _} {R : Type v} [Field R]

instance finiteDimensional [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  Module.Finite.matrix

end FiniteDimensional

end Matrix

namespace LinearMap

variable {K : Type _} [Field K]

variable {V : Type _} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable {W : Type _} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

set_option synthInstance.etaExperiment true in
instance finiteDimensional : FiniteDimensional K (V →ₗ[K] W) :=
  Module.Finite.linearMap _ _
#align linear_map.finite_dimensional LinearMap.finiteDimensional

variable {A : Type _} [Ring A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W]
  [IsScalarTower K A W]

set_option synthInstance.maxHeartbeats 50000 in
set_option synthInstance.etaExperiment true in
/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, as they form a subspace of all `k`-linear maps. -/
instance finiteDimensional' : FiniteDimensional K (V →ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsLinearMap K A V W) (restrictScalars_injective _)
#align linear_map.finite_dimensional' LinearMap.finiteDimensional'

end LinearMap
