/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
import Mathlib.Condensed.Light.Epi
import Mathlib.Condensed.Light.Limits
/-!

# Grothendieck's AB axioms for light condensed modules
-/
universe u

open CategoryTheory Limits

namespace LightCondensed

variable {R : Type u} [Ring R]

attribute [local instance] Abelian.hasFiniteBiproducts

noncomputable instance : CountableAB4Star (LightCondMod.{u} R) :=
  have := ABStarOfShapeOfPreservesEpi (LightCondMod R) (Discrete ℕ)
  CountableAB4Star.ofABStarOfShapeNat _

end LightCondensed
