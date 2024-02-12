/-
Copyright (c) 2024 Tomáš Skřivan All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Tactic.FunProp

/-!
## `funProp` minimal setup for Continuous(At/On)
-/


-- analysis
attribute [fun_prop]
  Continuous.edist

  Continuous.norm
  Continuous.nnnorm
  Continuous.norm'
  Continuous.nnnorm'

  ContinuousAt.norm
  ContinuousAt.nnnorm
  ContinuousAt.norm'
  ContinuousAt.nnnorm'

  ContinuousOn.norm
  ContinuousOn.nnnorm
  ContinuousOn.norm'
  ContinuousOn.nnnorm'

-- special function
attribute [fun_prop]
  Continuous.exp
  Continuous.cexp
  Continuous.log
  Continuous.pow
  Continuous.sqrt

  ContinuousAt.exp
  ContinuousAt.cexp
  ContinuousAt.log
  ContinuousAt.pow
  ContinuousAt.sqrt

  ContinuousOn.exp
  ContinuousOn.cexp
  ContinuousOn.log
  ContinuousOn.pow
  ContinuousOn.sqrt

-- FunLike
attribute [fun_prop]
  map_continuous
