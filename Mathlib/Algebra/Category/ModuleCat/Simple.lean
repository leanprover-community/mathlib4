/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Scott Morrison
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.RingTheory.SimpleModule
import Mathlib.LinearAlgebra.FiniteDimensional

#align_import algebra.category.Module.simple from "leanprover-community/mathlib"@"4ed0bcaef698011b0692b93a042a2282f490f6b6"

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/


variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M :=
  (simple_iff_subobject_isSimpleOrder _).trans (subobjectModule (of R M)).isSimpleOrder_iff
#align simple_iff_is_simple_module simple_iff_isSimpleModule

theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  (Simple.iff_of_iso (ofSelfIso M).symm).trans simple_iff_isSimpleModule
#align simple_iff_is_simple_module' simple_iff_isSimpleModule'

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_isSimpleModule.mpr ‹_›
#align simple_of_is_simple_module simple_of_isSimpleModule

/-- A simple object in the category of modules is a simple module. -/
instance isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_isSimpleModule.mp (Simple.of_iso (ofSelfIso M))
#align is_simple_module_of_simple isSimpleModule_of_simple

open FiniteDimensional

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
  (simple_iff_isSimpleModule' V).mpr (is_simple_module_of_finrank_eq_one h)
#align simple_of_finrank_eq_one simple_of_finrank_eq_one
