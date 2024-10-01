/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.ContinuousMap.Basic

open scoped Topology
open Filter

class ContinuousEvalConst (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace Y] : Prop where
  continuous_eval_const (x : X) : Continuous fun f : F ↦ f x

section ContinuousEvalConst

variable {F X Y Z : Type*} [FunLike F X Y] [TopologicalSpace F] [TopologicalSpace Y]
  [ContinuousEvalConst F X Y] [TopologicalSpace Z] {f : Z → F} {s : Set Z} {z : Z}

@[continuity, fun_prop]
theorem Continuous.eval_const (hf : Continuous f) (x : X) : Continuous (f · x) :=
  (ContinuousEvalConst.continuous_eval_const x).comp hf

theorem Filter.Tendsto.eval_const {α : Type*} {l : Filter α} {f : α → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) (x : X) : Tendsto (f · x) l (𝓝 (g x)) :=
  ((continuous_id.eval_const x).tendsto _).comp hf

nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : X) : ContinuousAt (f · x) z :=
  hf.eval_const x

nonrec theorem ContinuousWithinAt.eval_const (hf : ContinuousWithinAt f s z) (x : X) :
    ContinuousWithinAt (f · x) s z :=
  hf.eval_const x

theorem ContinuousOn.eval_const (hf : ContinuousOn f s) (x : X) : ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x

end ContinuousEvalConst

class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  continuous_eval : Continuous fun fx : F × X ↦ fx.1 fx.2

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z → F} {g : Z → X} {s : Set Z} {z : Z}

protected theorem Continuous.eval (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z ↦ f z (g z) :=
  ContinuousEval.continuous_eval.comp (hf.prod_mk hg)

instance (priority := 100) ContinuousEval.toContinuousMapClass : ContinuousMapClass F X Y where
  map_continuous _ := continuous_const.eval continuous_id

protected theorem Filter.Tendsto.eval {α : Type*} {l : Filter α} {f : α → F} {f₀ : F}
    {g : α → X} {x₀ : X} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 x₀)) :
    Tendsto (fun a ↦ f a (g a)) l (𝓝 (f₀ x₀)) :=
  (ContinuousEval.continuous_eval.tendsto _).comp (hf.prod_mk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z ↦ f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) : ContinuousWithinAt (fun z ↦ f z (g z)) s z :=
  hf.eval hg

protected theorem ContinuousOn.eval (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun z ↦ f z (g z)) s :=
  fun z hz ↦ (hf z hz).eval (hg z hz)
