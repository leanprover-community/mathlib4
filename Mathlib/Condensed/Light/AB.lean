/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Condensed.Light.Epi

@[expose] public section
/-!

# Grothendieck's AB axioms for light condensed modules

The category of light condensed `R`-modules over a ring satisfies the countable version of
Grothendieck's AB4* axiom
-/

universe u

open CategoryTheory Limits

namespace LightCondensed

variable {R : Type u} [Ring R]

attribute [local instance] Abelian.hasFiniteBiproducts

noncomputable instance : CountableAB4Star (LightCondMod.{u} R) :=
  have := hasExactLimitsOfShape_of_preservesEpi (LightCondMod R) (Discrete ℕ)
  CountableAB4Star.of_hasExactLimitsOfShape_nat _

instance : IsGrothendieckAbelian.{u} (LightCondMod.{u} R) :=
  inferInstanceAs (IsGrothendieckAbelian.{u} (Sheaf _ _))

end LightCondensed
