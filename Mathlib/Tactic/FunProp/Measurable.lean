/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

import Mathlib.Tactic.FunProp

/-!
## `fun_prop` minimal setup for Measurable
-/

open Mathlib

-- mark definition
attribute [fun_prop]
  Measurable

-- lambda rules
attribute [fun_prop]
  measurable_id'
  measurable_const
  Measurable.comp'
  measurable_pi_apply
  measurable_pi_lambda

-- product
attribute [fun_prop]
  Measurable.prod_mk
  Measurable.fst
  Measurable.snd
