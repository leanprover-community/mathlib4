/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `Module`, `Submodule`, and `LinearMap`, are found in
`Algebra/Module`.

## Main definitions

* Many constructors for (semi)linear maps

See `LinearAlgebra.Span` for the span of a set (as a submodule),
and `LinearAlgebra.Quotient` for quotients by submodules.

## Main theorems

See `LinearAlgebra.Isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`LinearMap.prod`, `LinearMap.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/

open Function

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} {R₄ : Type*}
variable {S : Type*}
variable {K : Type*} {K₂ : Type*}
variable {M : Type*} {M' : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} {M₄ : Type*}
variable {N : Type*} {N₂ : Type*}
variable {ι : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/

namespace IsLinearMap

theorem isLinearMap_add [Semiring R] [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · intro x y
    simp [smul_add]
#align is_linear_map.is_linear_map_add IsLinearMap.isLinearMap_add

theorem isLinearMap_sub {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · intro x y
    -- porting note (#10745): was `simp [add_comm, add_left_comm, sub_eq_add_neg]`
    rw [Prod.fst_add, Prod.snd_add]
    abel
  · intro x y
    simp [smul_sub]
#align is_linear_map.is_linear_map_sub IsLinearMap.isLinearMap_sub

end IsLinearMap

#align linear_equiv.map_sum map_sumₓ
#align linear_equiv.map_neg map_negₓ
#align linear_equiv.map_sub map_subₓ
