/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# Analyticity of dslope

``dslope`` is defined in ``Mathlib.Analysis.Calculus.DSlope``

    ``dslope f a = Function.update (slope f a) a (deriv f a)``

where


	``slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)``

We show in ``AnalyticOnNhd.dslope`` that if ``f`` is analytic on a set
then for any ``a`` the function ``dslope f a`` is analytic on the same
set.

-/

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
variable {a c : 𝕜} {f : 𝕜 → E} {s : Set 𝕜}

@[fun_prop]
lemma MeromorphicAt.slope (hf : MeromorphicAt f c) : MeromorphicAt (slope f a) c :=  
  ((id c).sub (const a c)).inv.smul (hf.sub (const (f a) c)) 

@[fun_prop]
lemma MeromorphicAt.dslope (hf : MeromorphicAt f c) : MeromorphicAt (dslope f a) c := by 
  classical exact hf.slope.update a (deriv f a)

@[fun_prop]
lemma ContinuousAt.dslope (hf : DifferentiableAt 𝕜 f c) : ContinuousAt (dslope f a) c := by
  by_cases h : c = a
  · rwa [← h, continuousAt_dslope_same]
  · rw [continuousAt_dslope_of_ne h]; exact hf.continuousAt

@[fun_prop]
theorem AnalyticAt.dslope (hf : AnalyticAt 𝕜 f c) : AnalyticAt 𝕜 (dslope f a) c := 
  hf.meromorphicAt.dslope.analyticAt (ContinuousAt.dslope hf.differentiableAt)

theorem AnalyticOnNhd.dslope (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (dslope f a) s :=
  fun x hx => (hf x hx).dslope
