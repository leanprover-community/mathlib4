/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.IsBounded
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Representation of `FormalMultilinearSeries.radius` as a `liminf`
In this file we prove that the radius of convergence of a `FormalMultilinearSeries` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
because this would create a circular dependency once we redefine `exp` using
`FormalMultilinearSeries`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Topology NNReal ENNReal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
theorem radius_eq_liminf :
    p.radius = liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  have :
    ∀ (r : ℝ≥0) {n},
      0 < n → ((r : ℝ≥0∞) ≤ 1 / ↑(‖p n‖₊ ^ (1 / (n : ℝ))) ↔ ‖p n‖₊ * r ^ n ≤ 1) := by
    intro r n hn
    have : 0 < (n : ℝ) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div, ENNReal.le_inv_iff_mul_le, ← ENNReal.coe_mul, ENNReal.coe_le_one_iff, one_div, ←
        NNReal.rpow_one r, ← mul_inv_cancel₀ this.ne', NNReal.rpow_mul, ← NNReal.mul_rpow, ←
        NNReal.one_rpow n⁻¹, NNReal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm,
        NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 1 7).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · rw [← eventually_map]
      refine
        H.mp ((eventually_gt_atTop 0).mono fun n hn₀ hn => (this _ hn₀).2 (NNReal.coe_le_coe.1 ?_))
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
  · refine p.le_radius_of_isBigO <| .of_norm_eventuallyLE ?_
    filter_upwards [eventually_lt_of_lt_liminf hr, eventually_gt_atTop 0] with n hn hn₀
    simpa using NNReal.coe_le_coe.2 ((this _ hn₀).1 hn.le)

/-- The **Cauchy-Hadamard theorem** for formal multilinear series: The inverse of the radius
is equal to $\limsup_{n\to\infty} \sqrt[n]{‖p n‖}$. -/
theorem radius_inv_eq_limsup :
    p.radius⁻¹ = limsup (fun n ↦ ((‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

end FormalMultilinearSeries
