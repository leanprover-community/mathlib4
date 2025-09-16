/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/


variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder, (subobjectModule (of R M)).isSimpleOrder_iff,
    isSimpleModule_iff]

theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  simple_iff_isSimpleModule

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_isSimpleModule.mpr ‹_›

/-- A simple object in the category of modules is a simple module. -/
instance isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_isSimpleModule.mp ‹_›

open Module

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
  (simple_iff_isSimpleModule' V).mpr <| (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one h
