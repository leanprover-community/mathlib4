/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Constructions

import Mathlib.Tactic.FProp

open Mathlib

-- mark definition
attribute [fprop]
  Measurable

-- lambda rules
attribute [fprop]
  measurable_id'
  measurable_const
  Measurable.comp'
  measurable_pi_apply
  measurable_pi_lambda

-- product
attribute [fprop]
  Measurable.prod_mk
  Measurable.fst
  Measurable.snd

-- algebra
attribute [fprop]
  Measurable.add
  Measurable.sub
  Measurable.mul
  Measurable.neg
  Measurable.div
  Measurable.inv
  Measurable.smul


-- transitions
attribute [fprop]
  Continuous.measurable -- Continuous f → Measurable f

-- morphisms
attribute [fprop]
  ContinuousLinearMap.measurable
  ContinuousLinearMap.measurable_comp
  ContinuousLinearMap.measurable_apply
  Measurable.apply_continuousLinearMap
