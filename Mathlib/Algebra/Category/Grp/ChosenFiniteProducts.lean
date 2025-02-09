/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Chosen finite products for `AddCommGrp.{u}`.
-/

universe u

open CategoryTheory MonoidalCategory

namespace AddCommGrp

/-- We choose `AddCommGrp.of (X × Y)` as the product of `X` and `Y` and `AddCommGrp.of PUnit` as
the terminal object. -/
noncomputable instance : ChosenFiniteProducts AddCommGrp.{u} where
  product X Y := binaryProductLimitCone X Y
  terminal := ⟨_, (isZero_of_subsingleton (AddCommGrp.of PUnit.{u + 1})).isTerminal⟩

attribute [local instance] Functor.monoidalOfChosenFiniteProducts

@[simp]
theorem μ_forget_apply {X Y : AddCommGrp.{u}} (p : X) (q : Y) :
    Functor.LaxMonoidal.μ (forget AddCommGrp.{u}) X Y (p, q) = (p, q) := by
  apply Prod.ext
  · exact congrFun (Functor.Monoidal.μ_fst (forget AddCommGrp.{u}) (X := X) (Y := Y)) (p, q)
  · exact congrFun (Functor.Monoidal.μ_snd (forget AddCommGrp.{u}) (X := X) (Y := Y)) (p, q)

end AddCommGrp
