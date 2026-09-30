/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-! # Characterization of positive continuous linear functionals on C⋆-algebras

In this file we show that a continuous linear functional `f` on a non-unital C⋆-algebra is
monotone if `f` tendsto `‖f‖` along any/some approximate unit. Therefore, when
the algebra is unital, `f` is monotone if and only if `‖f‖ = f 1`. -/

public section

open ComplexOrder Topology Filter Complex CStarRing

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PositiveContinuousLinearMap

theorem norm_map_le_sqrt_opNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ √‖(f : A →L[ℂ] ℂ)‖ * √‖f (star x * x)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine le_of_tendsto ((ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right _)).norm ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he1 he2
  grw [← he1.star_eq, Function.comp_apply, PositiveLinearMap.cauchy_schwarz_star_mul,
    ← f.coe_toContinuousLinearMap, f.toContinuousLinearMap.le_opNorm (star e * e),
    norm_star_mul_self, he2, he2, one_mul, mul_one]

theorem nnnorm_map_le_sqrt_opNNNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖₊ ≤ ‖(f : A →L[ℂ] ℂ)‖₊.sqrt * ‖f (star x * x)‖₊.sqrt := by
  simp [NNReal.toReal_le, norm_map_le_sqrt_opNorm_mul]

theorem norm_map_sq_le_opNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖ ^ 2 ≤ ‖(f : A →L[ℂ] ℂ)‖ * ‖f (star x * x)‖ := by
  grw [norm_map_le_sqrt_opNorm_mul, mul_pow]; simp

theorem nnnorm_map_sq_le_opNNNorm_mul (f : A →P[ℂ] ℂ) (x : A) :
    ‖f x‖₊ ^ 2 ≤ ‖(f : A →L[ℂ] ℂ)‖₊ * ‖f (star x * x)‖₊ :=
  norm_map_sq_le_opNorm_mul _ _

theorem tendsto_nhds_opNorm (f : A →P[ℂ] ℂ) {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    l.Tendsto (f ·) (𝓝 ‖(f : A →L[ℂ] ℂ)‖) := by
  suffices l.Tendsto (‖f ·‖) (𝓝 ‖f.toContinuousLinearMap‖) from this.ofReal.congr' <| by
    filter_upwards [hl.eventually_nonneg] using by simp_all [norm_of_nonneg' (f.map_nonneg _)]
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε ↦ ?_
  have h : ∀ᶠ x in l, ‖f x‖ ≤ ‖f.toContinuousLinearMap‖ := by
    filter_upwards [hl.eventually_norm] using f.toContinuousLinearMap.unit_le_opNorm
  have h2 : ∀ᶠ x in l, ‖f.toContinuousLinearMap‖ - ε ≤ ‖f x‖ := by
    obtain ⟨a, ha1, ha2⟩ := f.toContinuousLinearMap.exists_lt_apply_of_lt_opNorm
      (r := ‖f.toContinuousLinearMap‖ - ε / 2) (by grind)
    have h3 : ∀ᶠ x in l, ‖f (x * a)‖ ^ 2 ≤ ‖f x‖ * ‖f.toContinuousLinearMap‖ := by
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with x hx1 hx2
      have : ‖f (star x * x)‖ ≤ ‖f x‖ := by
        refine CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_
        exact f.mono <| hx1.star_eq.symm ▸ CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hx1 hx2
      conv_lhs => rw [← hx1.star_eq]
      grw [PositiveLinearMap.norm_map_star_mul_sq_le _ x a, this, ← f.coe_toContinuousLinearMap,
        f.toContinuousLinearMap.le_opNorm (star a * a), norm_star_mul_self, ← mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      grw [ha1, ha1, one_mul]
    have h4 : ∀ᶠ x in l, ‖f.toContinuousLinearMap‖ - ε / 2 < ‖f (x * a)‖ := by
      refine (Filter.Tendsto.norm ?_).eventually (lt_mem_nhds ha2)
      exact (ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right a)
    filter_upwards [h3, h4] with x _ _ using by nlinarith [norm_nonneg (f x)]
  filter_upwards [h, h2] using by grind [Real.closedBall_eq_Icc]

theorem ofReal_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →P[ℂ] ℂ) : ‖(f : A →L[ℂ] ℂ)‖ = f 1 :=
  tendsto_nhds_unique (f.tendsto_nhds_opNorm (.pure_one A)) (tendsto_pure_nhds _ _)

end PositiveContinuousLinearMap

namespace ContinuousLinearMap
variable {f : A →L[ℂ] ℂ}

/- This lemma is only used to prove `monotone_iff_tendsto_nhds_opNorm` below,
which can be used to construct a `PositiveContinuousLinearMap`. These may use
`IsSelfAdjoint.map` to conclude the same property as this lemma, so we mark it
`private`. -/
private lemma im_apply_eq_zero_of_tendsto_nhds_opNorm {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (hf : l.Tendsto (f ·) (𝓝 ‖f‖)) {a : A}
    (ha : IsSelfAdjoint a) : (f a).im = 0 := by
  by_cases ‖f‖ = 0
  · simp_all
  suffices ∀ (t : ℝ), ‖f a + I * t * ‖f‖‖ ^ 2 ≤ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2) by
    contrapose! this
    refine ⟨(‖f‖ ^ 2 * ‖a‖ ^ 2 - ‖f a‖ ^ 2 + 1) / (2 * (f a).im * ‖f‖), ?_⟩
    simp [normSq, ← normSq_eq_norm_sq, -ofReal_div]; field_simp; grind
  intro t
  suffices (fun x ↦ ‖f (a + (I * t) • x)‖ ^ 2) ≤ᶠ[l]
        (fun x ↦ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2 + |t| * ‖a * x - x * a‖)) by
    refine le_of_tendsto_of_tendsto (hb := hl.neBot) ?_ ?_ this
    · simp_rw [map_add, map_smul, smul_eq_mul]
      apply_rules [Tendsto.pow, Tendsto.norm, Tendsto.const_add, Tendsto.const_mul]
    · simpa using (hl.tendsto_mul_left a).sub (hl.tendsto_mul_right a)
        |>.norm |>.const_mul _ |>.const_add _ |>.const_mul _
  filter_upwards [hl.eventually_isSelfAdjoint, hl.eventually_norm] with x hx hx2
  grw [f.le_opNorm, mul_pow, mul_le_mul_iff_of_pos_left (by simp_all), sq, ← norm_star_mul_self]
  calc
    _ = ‖a * a + (t ^ 2 : ℂ) • (x * x) + (I * t) • (a * x + -(x * a))‖ := by
      simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, mul_mul_mul_comm]
      grind [sq]
    _ ≤ ‖a‖ ^ 2 + t ^ 2 + |t| * ‖a * x - x * a‖ := by
      grw [add_assoc, sq, norm_add_le, norm_add_le, ← sub_eq_add_neg, sq, ← norm_star_mul_self,
        add_assoc, ha.star_eq, add_le_add_iff_left, norm_smul, norm_mul_le x, hx2, hx2]
      simp [norm_smul, sq]

theorem monotone_iff_tendsto_nhds_opNorm {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Monotone f ↔ l.Tendsto (f ·) (𝓝 ‖f‖) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ monotone_iff_map_nonneg _ |>.mpr fun a ha ↦ ?_⟩
  · exact ({ __ := f, monotone' := hf } : _ →P[ℂ] _).tendsto_nhds_opNorm hl
  by_cases ha0 : a = 0
  · simp [ha0]
  suffices 0 ≤ (f (‖a‖⁻¹ • a)).re by simpa [Complex.le_def, ha0,
    im_apply_eq_zero_of_tendsto_nhds_opNorm hl hf ha.isSelfAdjoint] using this
  suffices ‖‖f‖ - f (‖a‖⁻¹ • a)‖ ≤ ‖f‖ by grw [← re_le_norm] at this; simpa
  refine le_of_tendsto (hx := hl.neBot) (hf.sub_const (f _) |>.norm) ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with y hy hy2
  grw [← map_sub, f.le_opNorm, CStarAlgebra.norm_sub_le_max_of_nonneg hy
    (by simp [smul_nonneg, ha]), hy2]
  simp [norm_smul, ha0]

theorem monotone_iff_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {f : A →L[ℂ] ℂ} : Monotone f ↔ ‖f‖ = f 1 := by
  rw [f.monotone_iff_tendsto_nhds_opNorm (.pure_one A)]
  have := tendsto_pure_nhds f 1
  exact ⟨fun h ↦ tendsto_nhds_unique h this, fun h ↦ by simpa [h]⟩

end ContinuousLinearMap
