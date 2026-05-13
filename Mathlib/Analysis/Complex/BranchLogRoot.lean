/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Branches of logarithm and `n`th root on simply connected domains

In this file we prove that for a function `g : X → ℂ` defined on a locally path connected space
that is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
there exist continuous branches of `log (g z)` and `ⁿ√(g z)` on `U`.
-/

public section

open Set

namespace Complex

variable {X : Type*} [TopologicalSpace X] [LocPathConnectedSpace X] {U : Set X}

/-- If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then there exists a continuous branch of `log ∘ g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `exp (f x) = g x` for all `x ∈ U`. -/
theorem exists_continuousOn_eqOn_exp_comp (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (exp ∘ f) g U := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ ≠ 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.restrict g, continuousOn_iff_continuous_restrict.mp hgc⟩ (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : ∃ g : X → ℂ, ∀ z : U, g z = f z :=
    ⟨fun z ↦ if hz : z ∈ U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

/-- If `g : X → ℂ` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → ℂ` continuous on `U`
such that `(f x) ^ n = g x` for all `x`. -/
theorem exists_continuousOn_pow_eq (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  classical
  rcases exists_continuousOn_eqOn_exp_comp hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : ℂ)), ?_, fun z ↦ ?_⟩
  · rw [continuousOn_iff_continuous_restrict, restrict_piecewise,
      ← continuousOn_iff_continuous_restrict]
    fun_prop
  · by_cases hz : z ∈ U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

namespace UnitDisc

/-- If `g : X → 𝔻` defined on a locally path connected space
is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
then for any `n ≠ 0`, there exists a continuous branch of `ⁿ√g` on `U`.
More precisely, there exists a function `f : X → 𝔻` continuous on `U`
such that `(f x) ^ n = g x` for all `x`. -/
protected theorem exists_continuousOn_pow_eq
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X → 𝔻}
    (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (n : ℕ+) :
    ∃ f : X → 𝔻, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  rcases exists_continuousOn_pow_eq hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices ∀ x, ‖f x‖ < 1 by
    lift f to X → 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x ↦ ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero, ← norm_pow, hf]
  exact (g x).norm_lt_one

end UnitDisc

end Complex
