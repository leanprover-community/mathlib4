/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Delta function

## Main definitions

* We define the Delta function as the infinite product
`η(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24 ` where `q = e ^ (2πiz)` and `z` is in the upper half-plane.
The product is taken over all non-negative integers `n`. We then show it is modular form and
non-vanishing.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/


open TopologicalSpace Set MeasureTheory intervalIntegral
 Metric Filter Function Complex

open UpperHalfPlane hiding I

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

@[expose] public section

namespace ModularForm

def Delta (z : ℍ) := (eta z) ^ 24

local notation "Δ" => Delta

lemma Delta_eq_q_prod (z : ℍ) : Δ z = 𝕢 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [Delta, eta, mul_pow]
  congr
  · simp [Periodic.qParam]
    simp only [← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    grind
  · rw [Multipliable.tprod_pow]
    exact multipliableLocallyUniformlyOn_eta.multipliable z.2

/-This should be easy from the definition and the Mulitpliable bit. -/
lemma Delta_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [Delta] using eta_ne_zero z.2

lemma exp_periodo (z : ℍ) :
    cexp (2 * ↑π * I  * (1 + ↑z)) = cexp (2 * ↑π * I * ↑z) := by
  rw [mul_add, ← exp_periodic (2 * π * I * z)]
  congr 1
  ring

lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [Delta_eq_q_prod, eta_q,  Periodic.qParam, exp_periodo z]


end ModularForm
