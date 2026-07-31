import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

open scoped ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- this should be in `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric`
alias quasispectrum.norm_le_norm_of_mem :=
  NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le

open CStarAlgebra Unitization in
lemma CStarAlgebra.norm_sub_le_one_of_nonneg_of_norm_le_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {x y : A} (hx : 0 ≤ x) (hx0 : ‖x‖ ≤ 1) (hy : 0 ≤ y)
    (hy0 : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by sorry

section
-- don't we already have these results? did I not already upstream these?

open Unitization NNReal CStarAlgebra in
lemma CStarAlgebra.nnrpow_le_self_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn : 1 ≤ n) : e ^ n ≤ e := by
  have : n ≠ 0 := by aesop
  conv_rhs => rw [← cfcₙ_id' ℝ e]
  rw [CFC.nnrpow_eq_cfcₙ_real e, ← sub_nonneg, ← cfcₙ_sub ..]
  refine cfcₙ_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := quasispectrum.norm_le_norm_of_mem _ hx
  grw [he1, Real.norm_eq_abs] at this
  exact Real.rpow_le_self_of_le_one (quasispectrum_nonneg_of_nonneg _ he0 _ hx) (by grind) hn

/-- If `e` is an element of the nonnegative closed unit ball, then `e * e ≤ e`, with equality
if `e` is an extreme point
(see `isStarProjection_iff_mem_extremePoints_nonneg_and_mem_closedUnitBall`). -/
lemma CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e * e ≤ e := CFC.nnrpow_two e ▸ nnrpow_le_self_of_nonneg_of_norm_le_one he0 he1 one_le_two

open Unitization NNReal in
lemma CStarAlgebra.self_le_nnrpow_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    {n : ℝ≥0} (hn0 : n ≠ 0) (hn : n ≤ 1) : e ≤ e ^ n := by
  conv_lhs => rw [← cfcₙ_id' ℝ e]
  rw [CFC.nnrpow_eq_cfcₙ_real e, ← sub_nonneg, ← cfcₙ_sub ..]
  refine cfcₙ_nonneg fun x hx ↦ sub_nonneg.mpr ?_
  have := quasispectrum.norm_le_norm_of_mem _ hx
  grw [he1, Real.norm_eq_abs] at this
  exact Real.self_le_rpow_of_le_one (quasispectrum_nonneg_of_nonneg _ he0 _ hx) (by grind) hn

lemma CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one {e : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) :
    e ≤ CFC.sqrt e :=
  CFC.sqrt_eq_nnrpow e ▸ self_le_nnrpow_of_nonneg_of_norm_le_one he0 he1 (by simp) (by simp)

end

namespace PositiveLinearMap

section
-- should go in GNS file

lemma preGNS_norm_def' (f : A →ₚ[ℂ] ℂ) (a : f.PreGNS) :
    ‖a‖ = √‖f (star (f.ofPreGNS a) * f.ofPreGNS a)‖ := by
  rw [← sq_eq_sq₀ (by positivity) (by positivity), ← Complex.ofReal_inj,
    Complex.ofReal_pow, preGNS_norm_sq, Real.sq_sqrt (by positivity),
    ← Complex.eq_coe_norm_of_nonneg]
  exact f.map_nonneg (star_mul_self_nonneg _)

lemma cauchy_schwarz_star_mul (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (star x * y)‖ ≤ √‖f (star x * x)‖ * √‖f (star y * y)‖ := by
  simpa [preGNS_inner_def, preGNS_norm_def'] using
    norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)

lemma cauchy_schwarz_mul_star (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (x * star y)‖ ≤ √‖f (x * star x)‖ * √‖f (y * star y)‖ := by
  simpa using cauchy_schwarz_star_mul f (star x) (star y)

end

-- change to PCLM when that lands
theorem norm_apply_le_sqrt_opNorm_mul (f : A →ₚ[ℂ] ℂ) (x : A) :
    ‖f x‖ ≤ √‖f.toContinuousLinearMap‖ * √‖f (star x * x)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine le_of_tendsto ((ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right _)).norm ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he1 he2
  grw [← he1.star_eq, Function.comp_apply, f.cauchy_schwarz_star_mul,
    ← f.toContinuousLinearMap_apply, f.toContinuousLinearMap.le_opNorm (star e * e),
    CStarRing.norm_star_mul_self, he2, he2, one_mul, mul_one]

open Topology Complex in
theorem tendsto_nhds_opNorm (f : A →ₚ[ℂ] ℂ) {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    l.Tendsto (f ·) (𝓝 ‖f.toContinuousLinearMap‖) := by
  suffices l.Tendsto (‖f ·‖) (𝓝 ‖f.toContinuousLinearMap‖) from this.ofReal.congr' <| by
    filter_upwards [hl.eventually_nonneg] using by simp_all [norm_of_nonneg' (f.map_nonneg _)]
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have h : ∀ᶠ x in l, ‖f x‖ ≤ ‖f.toContinuousLinearMap‖ + ε / 2 := by
    filter_upwards [hl.eventually_norm] with x hx
    grw [← f.toContinuousLinearMap_apply, ContinuousLinearMap.le_opNorm, hx, mul_one]
    grind
  have h2 : ∀ᶠ x in l, ‖f.toContinuousLinearMap‖ - ε / 2 < ‖f x‖ := by
    obtain ⟨_, ⟨a, ha1, rfl⟩, ha2⟩ := exists_lt_of_lt_csSup (b := ‖f.toContinuousLinearMap‖ - ε / 4)
      ((Metric.nonempty_closedBall (x := 0).mpr zero_le_one).image (‖f ·‖))
      (by rw [← f.toContinuousLinearMap.sSup_unitClosedBall_eq_norm]; simp; grind)
    have h3 : ∀ᶠ x in l, ‖f (x * a)‖ ^ 2 ≤ ‖f x‖ * ‖f.toContinuousLinearMap‖ := by
      filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with x hx1 hx2
      have : ‖f (star x * x)‖ ≤ ‖f x‖ := by
        refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (star_mul_self_nonneg _)) ?_
        exact f.mono <| hx1.star_eq.symm ▸ CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hx1 hx2
      conv_lhs => rw [← hx1.star_eq]
      grw [f.cauchy_schwarz_star_mul x a, mul_pow, Real.sq_sqrt (norm_nonneg _),
        Real.sq_sqrt (norm_nonneg _), this, ← f.toContinuousLinearMap_apply (star a * a),
        f.toContinuousLinearMap.le_opNorm (star a * a), CStarRing.norm_star_mul_self, ← mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      grw [mem_closedBall_zero_iff.mp ha1, mem_closedBall_zero_iff.mp ha1, one_mul]
    have h4 : ∀ᶠ x in l, ‖f.toContinuousLinearMap‖ - ε / 4 < ‖f (x * a)‖ := by
      refine (Filter.Tendsto.norm ?_).eventually (lt_mem_nhds ha2)
      exact (ContinuousAt.tendsto (by fun_prop)).comp (hl.tendsto_mul_right a)
    filter_upwards [h3, h4] with x _ _ using by nlinarith [norm_nonneg (f x)]
  filter_upwards [h, h2] using by grind [Real.dist_eq]

theorem ofReal_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) : ‖f.toContinuousLinearMap‖ = f 1 :=
  tendsto_nhds_unique (f.tendsto_nhds_opNorm (.pure_one A)) (tendsto_pure_nhds _ _)

end PositiveLinearMap

namespace ContinuousLinearMap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {f : A →L[ℂ] ℂ}

open Topology Filter Complex CStarRing

section unital
variable {A : Type*} [CStarAlgebra A] {f : A →L[ℂ] ℂ}

lemma im_apply_eq_zero_of_opNorm_eq_map_one (hf : ‖f‖ = f 1) {a : A} (ha : IsSelfAdjoint a) :
    (f a).im = 0 := by
  by_cases h : ‖f‖ = 0
  · simp at h; simp [h]
  by_cases! Subsingleton A
  · simp [Subsingleton.eq_zero]
  suffices ∀ t, ‖f a‖ ^ 2 + ‖f‖ * t * (2 * (f a).im + ‖f‖ * t) ≤ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2) by
    contrapose! this
    refine ⟨(‖f‖ ^ 2 * ‖a‖ ^ 2 - ‖f a‖ ^ 2 + 1) / (2 * (f a).im * ‖f‖), ?_⟩
    simp [normSq, Complex.sq_norm (f a)]; field_simp; grind
  intro t
  calc _ = ‖f (a + (t * Complex.I) • 1)‖ ^ 2 := by
        norm_num [Complex.normSq, Complex.sq_norm, ← hf]; ring_nf
    _ ≤ ‖f‖ ^ 2 * (‖a‖ ^ 2 + t ^ 2) := by
      grw [f.le_opNorm, mul_pow, mul_le_mul_of_nonneg_left _ (sq_nonneg _)]
      simp_rw [sq, ← CStarRing.norm_star_mul_self, ha.star_eq]
      calc _ = ‖a * a + (t * t : ℂ) • 1‖ := by
            simp [ha.star_eq, mul_add, add_mul, ← smul_assoc, mul_assoc, mul_left_comm]
        _ ≤ _ := by grw [norm_add_le]; simp

end unital

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
  · exact ({ __ := f, monotone' := hf } : _ →ₚ[ℂ] _).tendsto_nhds_opNorm hl
  by_cases ha0 : a = 0
  · simp [ha0]
  suffices 0 ≤ (f (‖a‖⁻¹ • a)).re by simpa [Complex.le_def, ha0,
    im_apply_eq_zero_of_tendsto_nhds_opNorm hl hf ha.isSelfAdjoint] using this
  suffices ‖‖f‖ - f (‖a‖⁻¹ • a)‖ ≤ ‖f‖ by grw [← re_le_norm] at this; simpa
  refine le_of_tendsto (hx := hl.neBot) (hf.sub_const (f _) |>.norm) ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with y hy hy2
  grw [← map_sub, f.le_opNorm, CStarAlgebra.norm_sub_le_one_of_nonneg_of_norm_le_one hy hy2
    (by simp [smul_nonneg, ha]) (by simp [norm_smul, ha0]), mul_one]

theorem monotone_iff_opNorm_eq_map_one {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {f : A →L[ℂ] ℂ} : Monotone f ↔ ‖f‖ = f 1 := by
  rw [f.monotone_iff_tendsto_nhds_opNorm (.pure_one A)]
  have := tendsto_pure_nhds f 1
  exact ⟨fun h ↦ tendsto_nhds_unique h this, fun h ↦ by simpa [h]⟩

end ContinuousLinearMap
