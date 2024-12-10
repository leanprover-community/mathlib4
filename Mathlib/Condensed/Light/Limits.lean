/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Module
/-!

# Limits in categories of light condensed objects

This file adds some instances for limits in light condensed sets and modules.
-/

universe u

open CategoryTheory Limits

instance : HasLimitsOfSize.{u, u} LightCondSet.{u} := by
  change HasLimitsOfSize (Sheaf _ _)
  infer_instance

instance : HasFiniteLimits LightCondSet.{u} := hasFiniteLimits_of_hasLimitsOfSize _

variable (R : Type u) [Ring R]

instance : HasLimitsOfSize.{u, u} (LightCondMod.{u} R) :=
  inferInstanceAs (HasLimitsOfSize (Sheaf _ _))

instance : HasLimitsOfSize.{0, 0} (LightCondMod.{u} R) :=
  inferInstanceAs (HasLimitsOfSize (Sheaf _ _))

instance : HasFiniteLimits (LightCondMod.{u} R) := hasFiniteLimits_of_hasLimitsOfSize _
