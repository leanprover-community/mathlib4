/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Bijection

/-!

# Ext Commute with Ulift Functor

-/

universe u v v'

variable (R : Type u) [CommRing R]
-- need to investigate why `Ring` stop `Module` instance on `Ext`

open CategoryTheory Abelian

universe w w'

variable [UnivLE.{v, w}] [UnivLE.{max v v', w'}]

instance hasExt_of_small'' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

instance hasExt_of_small''_lift [Small.{v} R] :
    CategoryTheory.HasExt.{w'} (ModuleCat.{max v v'} R) :=
  let _ : Small.{max v v'} R := small_lift R
  CategoryTheory.hasExt_of_enoughProjectives.{w'} (ModuleCat.{max v v'} R)


def ModuleCat.extUliftLinearEquiv [Small.{v} R] (M N : ModuleCat.{v} R) (n : ℕ) :
    Ext.{w} M N n ≃ₗ[R] Ext.{w'} ((uliftFunctor.{u, v, v'} R).obj M)
    ((uliftFunctor.{u, v, v'} R).obj N) n := by

  sorry
