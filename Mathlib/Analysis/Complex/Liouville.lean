/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.NormedSpace.Completion

#align_import analysis.complex.liouville from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `Differentiable.apply_eq_apply_of_bounded`,
`Differentiable.exists_const_forall_eq_of_bounded`, and
`Differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`Complex.deriv_eq_smul_circleIntegral`.
-/


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory Bornology

open scoped Topology Filter NNReal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-- If `f` is complex differentiable on an open disc with center `c` and radius `R > 0` and is
continuous on its closure, then `f' c` can be represented as an integral over the corresponding
circle.

TODO: add a version for `w ∈ Metric.ball c R`.

TODO: add a version for higher derivatives. -/
theorem deriv_eq_smul_circleIntegral [CompleteSpace F] {R : ℝ} {c : ℂ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) :
    deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z := by
  lift R to ℝ≥0 using hR.le
  refine' (hf.hasFPowerSeriesOnBall hR).hasFPowerSeriesAt.deriv.trans _
  simp only [cauchyPowerSeries_apply, one_div, zpow_neg, pow_one, smul_smul, zpow_two, mul_inv]
#align complex.deriv_eq_smul_circle_integral Complex.deriv_eq_smul_circleIntegral

theorem norm_deriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  have : ∀ z ∈ sphere c R, ‖(z - c) ^ (-2 : ℤ) • f z‖ ≤ C / (R * R) :=
    fun z (hz : abs (z - c) = R) => by
    simpa [-mul_inv_rev, norm_smul, hz, zpow_two, ← div_eq_inv_mul] using
      (div_le_div_right (mul_pos hR hR)).2 (hC z hz)
  calc
    ‖deriv f c‖ = ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z‖ :=
      congr_arg norm (deriv_eq_smul_circleIntegral hR hf)
    _ ≤ R * (C / (R * R)) :=
      (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le this)
    _ = C / R := by rw [mul_div_left_comm, div_self_mul_self', div_eq_mul_inv]
#align complex.norm_deriv_le_aux Complex.norm_deriv_le_aux

/-- If `f` is complex differentiable on an open disc of radius `R > 0`, is continuous on its
closure, and its values on the boundary circle of this disc are bounded from above by `C`, then the
norm of its derivative at the center is at most `C / R`. -/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  have : HasDerivAt (e ∘ f) (e (deriv f c)) c :=
    e.hasFDerivAt.comp_hasDerivAt c
      (hd.differentiableAt isOpen_ball <| mem_ball_self hR).hasDerivAt
  calc
    ‖deriv f c‖ = ‖deriv (e ∘ f) c‖ := by
      rw [this.deriv]
      exact (UniformSpace.Completion.norm_coe _).symm
    _ ≤ C / R :=
      norm_deriv_le_aux hR (e.differentiable.comp_diffContOnCl hd) fun z hz =>
        (UniformSpace.Completion.norm_coe _).trans_le (hC z hz)
#align complex.norm_deriv_le_of_forall_mem_sphere_norm_le Complex.norm_deriv_le_of_forall_mem_sphere_norm_le

/-- An auxiliary lemma for Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`. -/
theorem liouville_theorem_aux {f : ℂ → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : ℂ) : f z = f w := by
  suffices : ∀ c, deriv f c = 0; exact is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ‖f z‖ ≤ C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine' norm_le_zero_iff.1 (le_of_forall_le_of_dense fun ε ε₀ => _)
  calc
    ‖deriv f c‖ ≤ C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diffContOnCl fun z _ => hC z
    _ = ε := div_div_cancel' C₀.lt.ne'
#align complex.liouville_theorem_aux Complex.liouville_theorem_aux

end Complex

namespace Differentiable

open Complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
theorem apply_eq_apply_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : E) : f z = f w := by
  set g : ℂ → F := f ∘ fun t : ℂ => t • (w - z) + z
  suffices g 0 = g 1 by simpa
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]
#align differentiable.apply_eq_apply_of_bounded Differentiable.apply_eq_apply_of_bounded

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_const_forall_eq_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩
#align differentiable.exists_const_forall_eq_of_bounded Differentiable.exists_const_forall_eq_of_bounded

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_eq_const_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext
#align differentiable.exists_eq_const_of_bounded Differentiable.exists_eq_const_of_bounded

end Differentiable
