/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


import Mathlib.Tactic.FunProp

/-!
## `funProp` minimal setup for Differentiable(At/On)
-/


section Missing

section lambda_rules

variable {K : Type*} [NontriviallyNormedField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace K G']
variable {f f₀ f₁ g : E → F} {x} {s t}


theorem differentiableOn_id' : DifferentiableOn K (fun x : E => x) s :=
  differentiable_id.differentiableOn

theorem Differentiable.comp' {g : F → G} (hg : Differentiable K g) (hf : Differentiable K f) :
    Differentiable K (fun x => g (f x)) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

theorem DifferentiableAt.comp' {f : E → F} {g : F → G} (hg : DifferentiableAt K g (f x))
    (hf : DifferentiableAt K f x) : DifferentiableAt K (fun x => g (f x)) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

theorem DifferentiableOn.comp' {g : F → G} {t : Set F} (hg : DifferentiableOn K g t)
    (hf : DifferentiableOn K f s) (st : Set.MapsTo f s t) :
    DifferentiableOn K (fun x => g (f x)) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

end lambda_rules

end Missing


-- mark definition
attribute [fun_prop]
  Differentiable
  DifferentiableAt
  DifferentiableOn


-- lambda rules
attribute [fun_prop]
  differentiable_id'
  differentiable_const
  Differentiable.comp'

  differentiableAt_id'
  differentiableAt_const
  DifferentiableAt.comp'

  differentiableOn_id'
  differentiableOn_const
  DifferentiableOn.comp'

-- product
attribute [fun_prop]
  Differentiable.prod
  Differentiable.fst
  Differentiable.snd

  DifferentiableAt.prod
  DifferentiableAt.fst
  DifferentiableAt.snd

  DifferentiableOn.prod
  DifferentiableOn.fst
  DifferentiableOn.snd

-- transitions
attribute [fun_prop]
  Differentiable.differentiableAt
  Differentiable.differentiableOn
  DifferentiableAt.continuousAt
  DifferentiableOn.continuousOn

-- algebra
attribute [fun_prop]
  Differentiable.add
  Differentiable.sub
  Differentiable.neg
  Differentiable.mul
  Differentiable.smul
  Differentiable.div
  Differentiable.inv'
  Differentiable.inv

  DifferentiableAt.add
  DifferentiableAt.sub
  DifferentiableAt.neg
  DifferentiableAt.mul
  DifferentiableAt.smul
  DifferentiableAt.div
  DifferentiableAt.inv'
  DifferentiableAt.inv

  DifferentiableOn.add
  DifferentiableOn.sub
  DifferentiableOn.neg
  DifferentiableOn.mul
  DifferentiableOn.smul
  DifferentiableOn.div
  DifferentiableOn.inv'
  DifferentiableOn.inv


-- special function
attribute [fun_prop]
  Differentiable.exp
  Differentiable.log
  Differentiable.pow

  DifferentiableAt.exp
  DifferentiableAt.log
  DifferentiableAt.pow

  DifferentiableOn.exp
  DifferentiableOn.log
  DifferentiableOn.pow
