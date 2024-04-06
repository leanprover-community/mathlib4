/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Various complex special functions are analytic

`exp`, `log`, and `cpow` are analytic, since they are differentiable.
-/

open Complex Set
open scoped Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- `exp` is entire -/
theorem analyticOn_cexp : AnalyticOn ℂ exp univ := by
  rw [analyticOn_univ_iff_differentiable]; exact differentiable_exp

/-- `exp` is analytic at any point -/
theorem analyticAt_cexp : AnalyticAt ℂ exp z :=
  analyticOn_cexp z (mem_univ _)

/-- `exp ∘ f` is analytic -/
theorem AnalyticAt.cexp (fa : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun z ↦ exp (f z)) x :=
  analyticAt_cexp.comp fa

/-- `exp ∘ f` is analytic -/
theorem AnalyticOn.cexp (fs : AnalyticOn ℂ f s) : AnalyticOn ℂ (fun z ↦ exp (f z)) s :=
  fun z n ↦ analyticAt_cexp.comp (fs z n)

/-- `log` is analytic away from nonpositive reals -/
theorem analyticAt_clog (m : z ∈ slitPlane) : AnalyticAt ℂ log z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticAt.clog (fa : AnalyticAt ℂ f x) (m : f x ∈ slitPlane) :
    AnalyticAt ℂ (fun z ↦ log (f z)) x :=
  (analyticAt_clog m).comp fa

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticOn.clog (fs : AnalyticOn ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOn ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).comp (fs z n)

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
theorem AnalyticAt.cpow (fa : AnalyticAt ℂ f x) (ga : AnalyticAt ℂ g x)
    (m : f x ∈ slitPlane) : AnalyticAt ℂ (fun z ↦ f z ^ g z) x := by
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝 x] fun z ↦ exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousAt.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, if_false]
  rw [analyticAt_congr e]
  exact ((fa.clog m).mul ga).cexp

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
theorem AnalyticOn.cpow (fs : AnalyticOn ℂ f s) (gs : AnalyticOn ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOn ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)
