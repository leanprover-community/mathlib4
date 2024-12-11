/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Condensed.Explicit
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Limits
import Mathlib.CategoryTheory.Sites.Coherent.AB
/-!

# AB axioms in condensed modules
-/

universe u

open Condensed CategoryTheory Limits

namespace Condensed

variable (A J : Type*) [Category A] [Category J] [Preadditive A]

variable [HasWeakSheafify (coherentTopology CompHaus.{u}) A]
  [HasWeakSheafify (extensiveTopology Stonean.{u}) A]
-- Here, one could be deduced from the other using the dense subsite API, but when `A` is a
-- concrete category, these will both be synthesized anyway.

variable [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]

def hasExactColimitsOfShape [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasFiniteLimits A] : HasExactColimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  have : HasColimitsOfShape J (Sheaf (extensiveTopology Stonean.{u}) A) :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape e.inverse
  exact hasExactColimitsOfShape_transport e.functor

def hasExactLimitsOfShape [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [HasFiniteColimits A] : HasExactLimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  have : HasLimitsOfShape J (Sheaf (extensiveTopology Stonean.{u}) A) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape e.inverse
  exact hasExactLimitsOfShape_transport e.functor

section Module

variable (R : Type (u+1)) [Ring R]

variable (X Y : CondensedMod.{u} R)

instance : AB5 (CondensedMod.{u} R) where
  ofShape J _ _ :=
    have : HasLimitsOfSize.{u, u+1} (ModuleCat.{u+1} R) := hasLimitsOfSizeShrink.{u, u+1, u+1, u} _
    hasExactColimitsOfShape (ModuleCat R) J

attribute [local instance] Abelian.hasFiniteBiproducts

instance : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _

end Module

end Condensed
