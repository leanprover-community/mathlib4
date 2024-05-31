/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

-- algebra
attribute [fun_prop]
  Measurable.add
  Measurable.sub
  Measurable.mul
  Measurable.neg
  Measurable.div
  Measurable.inv
  Measurable.smul


-- transitions
attribute [fun_prop]

  Continuous.measurable -- Continuous f → Measurable f
  measurable_of_continuousOn_compl_singleton

-- morphisms
attribute [fun_prop]
  ContinuousLinearMap.measurable
  ContinuousLinearMap.measurable_comp
  ContinuousLinearMap.measurable_apply
  Measurable.apply_continuousLinearMap
