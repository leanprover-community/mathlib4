/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Limits
/-!

# AB axioms in condensed modules

This file proves that the category of condensed modules over a ring satisfies Grothendieck's axioms
AB5, AB4, and AB4*.
-/

universe u

open Condensed CategoryTheory Limits

namespace Condensed

variable (A J : Type*) [Category A] [Category J] [Preadditive A]
  [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [HasWeakSheafify (coherentTopology CompHaus.{u}) A]
  [HasWeakSheafify (extensiveTopology Stonean.{u}) A]
-- One of the `HasWeakSheafify` instances could be deduced from the other using the dense subsite
-- API, but when `A` is a concrete category, these will both be synthesized anyway.

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
lemma hasExactColimitsOfShape [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasFiniteLimits A] : HasExactColimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  exact HasExactColimitsOfShape.domain_of_functor _ e.functor

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
lemma hasExactLimitsOfShape [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [HasFiniteColimits A] : HasExactLimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  exact HasExactLimitsOfShape.domain_of_functor _ e.functor

section Module

variable (R : Type (u + 1)) [Ring R]

local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

variable (X Y : CondensedMod.{u} R)

instance : AB5 (CondensedMod.{u} R) where
  ofShape J _ _ := hasExactColimitsOfShape (ModuleCat R) J

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 (CondensedMod.{u} R) := AB4.of_AB5 _

instance : AB4Star (CondensedMod.{u} R) where
  ofShape J := hasExactLimitsOfShape (ModuleCat R) (Discrete J)

end Module

end Condensed
