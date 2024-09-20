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
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber`: the global root number of the L-series of `χ` (for `χ` primitive; junk otherwise).

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

open HurwitzZeta Complex Finset Classical ZMod

open scoped Real

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
 -/
@[pp_nodot]
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

/--
The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function.
(Compare `DirichletCharacter.LSeries_modOne_eq`.)
-/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext1; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
  {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

section gammaFactor

omit [NeZero N] -- not required for these declarations

/-- The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)

lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp only [gammaFactor, hχ, ↓reduceIte]

lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp only [gammaFactor, hχ.not_even, ↓reduceIte]

end gammaFactor

/--
The completed L-function of a Dirichlet character, almost everywhere equal to
`LFunction χ s * gammaFactor χ s`.
-/
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s

/--
The completed L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta
function.
-/
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext1 s; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

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
  ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

/--
Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well.
-/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) : LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

/--
Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if odd. (The factor
`1 / I ^ a` is the Archimedean root number.) This is a complex number of absolute value 1.
-/
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)

/-- The root number of the unique Dirichlet character modulo 1 is 1. -/
lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
  simp only [rootNumber, gaussSum, ← singleton_eq_univ (1 : ZMod 1), sum_singleton, map_one,
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _), one_mul,
    (show χ.Even from map_one _), ite_true, pow_zero, div_one, Nat.cast_one, one_cpow]

namespace IsPrimitive

/-- Functional equation for primitive Dirichlet L-functions. -/
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp only [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, Nat.cast_one, one_cpow,
      rootNumber_modOne, one_mul]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h ↦ hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one (NeZero.ne _)] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber, ← mul_div_assoc, ← div_mul_eq_mul_div₀, ← mul_div_assoc, ← div_mul_eq_mul_div₀,
    ← cpow_sub _ _ (NeZero.ne _), sub_sub, add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) /  ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction, completedLFunction_one_sub_odd h.to_fun,
        pow_one, h, div_I, mul_neg_one, ← neg_mul, neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)):= by
    rw [completedLFunction, completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg), mul_one]

end IsPrimitive

end DirichletCharacter
