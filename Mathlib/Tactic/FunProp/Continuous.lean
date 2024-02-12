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

section Missing

section div

variable {α β G₀ : Type*} [TopologicalSpace α]
variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀} {a} {s}

theorem Continuous.div₀ (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (fun x => f x / g x) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)

theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (fun x => f x / g x) a := ContinuousAt.div hf hg h₀

theorem ContinuousOn.div₀ (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x => f x / g x) s := ContinuousOn.div hf hg h₀


end div

end Missing




-- algebra
attribute [fun_prop]
  Continuous.add
  Continuous.sub
  Continuous.neg
  Continuous.pow
  Continuous.zpow
  Continuous.zpow₀
  Continuous.mul
  Continuous.smul
  Continuous.const_smul
  Continuous.vadd
  Continuous.const_vadd
  Continuous.div'
  Continuous.div₀
  Continuous.inv
  Continuous.inv₀
  Continuous.star
  Continuous.sup
  Continuous.inf
  Continuous.abs

  Continuous.max
  Continuous.min

  ContinuousAt.add
  ContinuousAt.sub
  ContinuousAt.neg
  ContinuousAt.pow
  ContinuousAt.zpow
  ContinuousAt.zpow₀
  ContinuousAt.mul
  ContinuousAt.smul
  ContinuousAt.const_smul
  ContinuousAt.vadd
  ContinuousAt.const_vadd
  ContinuousAt.div'
  ContinuousAt.div₀
  ContinuousAt.inv
  ContinuousAt.inv₀
  ContinuousAt.star
  ContinuousAt.sup
  ContinuousAt.inf
  ContinuousAt.abs

  ContinuousOn.add
  ContinuousOn.sub
  ContinuousOn.neg
  ContinuousOn.pow
  ContinuousOn.zpow
  ContinuousOn.zpow₀
  ContinuousOn.mul
  ContinuousOn.smul
  ContinuousOn.const_smul
  ContinuousOn.vadd
  ContinuousOn.const_vadd
  ContinuousOn.div'
  ContinuousOn.div₀
  ContinuousOn.inv
  ContinuousOn.inv₀
  ContinuousOn.star
  ContinuousOn.sup
  ContinuousOn.inf
  ContinuousOn.abs

-- analysis
attribute [fun_prop]
  Continuous.dist
  Continuous.nndist
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
