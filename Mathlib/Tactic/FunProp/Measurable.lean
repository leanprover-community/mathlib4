/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FunProp.Continuous

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



-- This theorem is meant to work together with `measurable_of_continuousOn_compl_singleton`
-- Unification of `(hf : ContinuousOn f {a}ᶜ)` with this theorem determines the point `a` to be `0`
@[fun_prop]
theorem ContinuousOn.log' : ContinuousOn Real.log {0}ᶜ := ContinuousOn.log (by fun_prop) (by aesop)

-- Notice that no theorems about measuability of log are used. It is infered from continuity.
example : Measurable (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) :=
  by fun_prop

private noncomputable def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

private noncomputable def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))

example : Measurable T := by
  unfold T S
  fun_prop
