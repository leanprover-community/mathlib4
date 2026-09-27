/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Bundled maps with evaluation continuous in both variables

In this file we define a class `ContinuousEval F X Y`
saying that `F` is a bundled morphism class (in the sense of `FunLike`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function.
-/

public section

open scoped Topology
open Filter

/-- A typeclass saying that `F` is a bundled morphism class (in the sense of `FunLike`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function. -/
class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- Evaluation of a bundled morphism at a point is continuous in both variables. -/
  continuous_eval : Continuous fun fx : F × X ↦ fx.1 fx.2

export ContinuousEval (continuous_eval)

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z → F} {g : Z → X} {s : Set Z} {z : Z}

@[continuity, fun_prop]
protected theorem Continuous.eval (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z ↦ f z (g z) :=
  continuous_eval.comp (hf.prodMk hg)

/-- If a type `F'` of bundled morphisms admits a continuous projection
to a type satisfying `ContinuousEval`,
then `F'` satisfies this predicate too.

The word "forget" in the name is motivated by the term "forgetful functor". -/
theorem ContinuousEval.of_continuous_forget {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEval F' X Y where
  continuous_eval := by simpa only [← hf] using hc.fst'.eval continuous_snd

instance (priority := 100) ContinuousEval.toContinuousMapClass : ContinuousMapClass F X Y where
  map_continuous _ := continuous_const.eval continuous_id

instance (priority := 100) ContinuousEval.toContinuousEvalConst : ContinuousEvalConst F X Y where
  continuous_eval_const _ := continuous_id.eval continuous_const

protected theorem Filter.Tendsto.eval {α : Type*} {l : Filter α} {f : α → F} {f₀ : F}
    {g : α → X} {x₀ : X} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 x₀)) :
    Tendsto (fun a ↦ f a (g a)) l (𝓝 (f₀ x₀)) :=
  (ContinuousEval.continuous_eval.tendsto _).comp (hf.prodMk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z ↦ f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) : ContinuousWithinAt (fun z ↦ f z (g z)) s z :=
  hf.eval hg

protected theorem ContinuousOn.eval (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun z ↦ f z (g z)) s :=
  fun z hz ↦ (hf z hz).eval (hg z hz)
