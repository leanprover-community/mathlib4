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
variable {f : E → F} {x} {s}


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

-- lambda rules
attribute [fun_prop]
  Differentiable.comp'
  DifferentiableAt.comp'
  differentiableOn_id'
  DifferentiableOn.comp'
