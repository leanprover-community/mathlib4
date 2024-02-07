/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Abelian

/-!

# Limits in categories of condensed objects

This file adds some instances for limits in condensed sets and condensed abelian groups.
-/

universe u

open CategoryTheory Limits

instance : HasLimits CondensedSet.{u} := by
  change HasLimits (Sheaf _ _)
  infer_instance

instance : HasLimitsOfSize.{u} CondensedSet.{u} := hasLimitsOfSizeShrink.{u, u+1, u+1, u} _

instance : HasLimits CondensedAb.{u} := by
  change HasLimits (Sheaf _ _)
  infer_instance

instance : HasLimitsOfSize.{u} CondensedAb.{u} := hasLimitsOfSizeShrink.{u, u+1, u+1, u} _
