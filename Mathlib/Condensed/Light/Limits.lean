/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.Module
/-!

# Limits in categories of light condensed objects

This file adds some instances for limits in light condensed sets and modules.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits

variable (R : Type u) [Ring R]

instance : HasCountableLimits (LightCondMod.{u} R) where
