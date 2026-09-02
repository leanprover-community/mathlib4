/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The functional equation for the logarithmic derivative of the Riemann zeta function

Differentiating the functional equation `riemannZeta_one_sub` logarithmically gives an identity
relating `ζ'/ζ (s)` and `ζ'/ζ (1 - s)`, involving the digamma function `ψ` and a tangent term.

## Main statements

* `logDeriv_riemannZeta_one_sub`: for `s` not an integer with `ζ s ≠ 0`,
  `ζ'/ζ (s) = -ζ'/ζ (1 - s) + log (2 π) - ψ s + (π / 2) * tan (π s / 2)`.
-/

@[expose] public section

open scoped Real
open Complex Filter Topology

/-- **The functional equation for the Riemann zeta function, in logarithmic-derivative form.**
For `s` not an integer with `riemannZeta s ≠ 0`,
`ζ'/ζ (s) = -ζ'/ζ (1 - s) + log (2 π) - ψ s + (π / 2) * tan (π s / 2)`, where `ψ` is the digamma
function. -/
theorem logDeriv_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + log (2 * π) - digamma s + π / 2 * tan (π * s / 2) := by
  have h2π : 2 * (π : ℂ) ≠ 0 := mod_cast by positivity
  have (m : ℕ) : s ≠ -m := mod_cast hs (-m)
  have : s ≠ 1 := mod_cast hs 1
  have : cos (π * s / 2) ≠ 0 :=
    mt cos_eq_zero_iff.mp fun ⟨k, _⟩ ↦ hs (2 * k + 1) (mod_cast by grind)
  have : logDeriv (fun z ↦ (2 * (π : ℂ)) ^ (-z)) s = -log (2 * π) := by
    simp [logDeriv_apply, ((hasDerivAt_neg' s).const_cpow (Or.inl h2π)).deriv, field]
  have : logDeriv (fun z ↦ cos (π * z / 2)) s = -(π / 2 * tan (π * s / 2)) := by
    simp [logDeriv_apply, (by simpa using ((hasDerivAt_id s).const_mul _).div_const 2 :
      HasDerivAt ((π : ℂ) * · / 2) (π / 2) s).ccos.deriv, tan_eq_sin_div_cos, field]
  have := (hasDerivAt_neg' s).differentiableAt.const_cpow (Or.inl h2π)
  have : riemannZeta ∘ (1 - ·) =ᶠ[𝓝 s]
      fun z ↦ 2 * (2 * π) ^ (-z) * Gamma z * cos (π * z / 2) * riemannZeta z := by
    filter_upwards [isClosed_range_intCast.isOpen_compl.mem_nhds (by grind)] with z hz
    rw [Set.mem_compl_iff, Set.mem_range, not_exists] at hz
    exact riemannZeta_one_sub (fun n h ↦ hz (-n) (by simp [h])) (by grind [hz 1])
  have := (logDeriv_congr_nhds this).eq_of_nhds
  rw [logDeriv_comp, logDeriv_fun_mul, logDeriv_fun_mul, logDeriv_fun_mul, logDeriv_fun_mul,
    ← digamma_def] at this
  <;> first | fun_prop | simp_all <;> grind [differentiableAt_riemannZeta, Gamma_ne_zero, hs 0]
