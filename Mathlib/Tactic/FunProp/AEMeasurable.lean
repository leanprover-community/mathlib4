/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
## `fun_prop` minimal setup for AEMeasurable
-/

open Mathlib

-- lambda rules: these two are currently missing
-- attribute [fun_prop] AEMeasurable_apply AEMeasurable_pi

-- product: these are currently not valid fun_prop theorems!
-- attribute [fun_prop] AEMeasurable.fst AEMeasurable.snd
