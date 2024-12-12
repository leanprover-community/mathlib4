/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
/-!

# AB axioms in module categories
-/

universe u

open CategoryTheory Limits

variable (R : Type u) [Ring R]

instance : AB5 (ModuleCat.{u} R) where
  ofShape J _ _ :=
    hasExactColimitsOfShape_transport (J := J) (forget₂ (ModuleCat R) AddCommGrp)

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _

instance : AB4Star (ModuleCat.{u} R) where
  ofShape J :=
    hasExactLimitsOfShape_transport (J := Discrete J) (forget₂ (ModuleCat R) AddCommGrp.{u})
