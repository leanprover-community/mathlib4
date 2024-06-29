/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has meromorphic continuation (away from a pole at `s = 1` if `χ` is trivial).

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
-/

open HurwitzZeta Complex Finset Classical

open scoped Real

section LemmasToBeRehomed

namespace DirichletCharacter

lemma Even.iff_coe {N : ℕ} {χ : DirichletCharacter ℂ N} : Even χ ↔ Function.Even χ := by
  refine ⟨fun h x ↦ by rw [← neg_one_mul, map_mul, h, one_mul],
    fun h ↦ by rw [Even, h 1, map_one]⟩

lemma Odd.iff_coe {N : ℕ} {χ : DirichletCharacter ℂ N} : Odd χ ↔ Function.Odd χ := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · rw [← neg_one_mul, map_mul, h, neg_one_mul]
  · rw [Odd, h 1, map_one]

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
 -/
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

/--
The completed L-function of a Dirichlet character, almost everywhere equal to
`LFunction χ s * gammaFactor χ s`.
-/
noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s

/-- The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) := ZMod.gammaFactor χ s

lemma gammaFactor_def (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ s = if χ.Even then Gammaℝ s else Gammaℝ (s + 1) := by
  rw [Even.iff_coe]; rfl

/-- The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function. -/
lemma LFunction_mod_one {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext1 s; rw [LFunction, ZMod.LFunction_mod_one, map_one, one_mul]

/--
The completed L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta
function.
-/
lemma completedLFunction_mod_one {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext1 s; rw [completedLFunction, ZMod.completedLFunction_mod_one, map_one, one_mul]

open scoped LSeries.notation in
/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries ↗χ s :=
  ZMod.LFunction_eq_LSeries χ hs

/--
The completed L-function of a Dirichlet character is differentiable, with the following
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at `s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunction χ) s :=
  ZMod.differentiableAt_completedLFunction _ _
    (by have := χ.map_zero'; tauto) (by have := χ.sum_eq_zero_of_ne_one; tauto)

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

/-- Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well. -/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) :
    LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  refine ZMod.LFunction_eq_completed_div_gammaFactor ?_ s (h.imp_right <| map_zero' χ)
  exact χ.even_or_odd.imp Even.iff_coe.mp Odd.iff_coe.mp

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-2 * (n + 1)) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one (Even.iff_coe.mp hχ) n

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
lemma Odd.LFunction_neg_two_mul_nat_sub_one {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-2 * n - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one (Odd.iff_coe.mp hχ) n

end DirichletCharacter
