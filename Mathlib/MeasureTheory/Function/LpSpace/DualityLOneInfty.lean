/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Duality between `L¹` and `L^∞` for finite measures

For a finite measure `μ` and a scalar field `𝕜` (either `ℝ` or `ℂ`, i.e., any
`RCLike` field), every bounded linear functional on `L¹(μ; 𝕜)` is of the form
`f ↦ ∫ f · g ∂μ` for a unique `g ∈ L^∞(μ; 𝕜)`, and the operator norm of the
functional equals the essential supremum norm of `g`. This file packages the
result as an isometric linear equivalence.

## Main declarations

* `MeasureTheory.Lp.toDualCLM`: The natural continuous linear map
  `L^∞(μ; StrongDual 𝕜 E) →L[𝕜] StrongDual 𝕜 (L¹(μ; E))` given by
  `g ↦ (f ↦ ∫ x, g x (f x) ∂μ)`. This is defined for any Banach space `E`.
* `MeasureTheory.Lp.toDualₗᵢ`: The same map restricted to the scalar case
  `E = 𝕜`, packaged as a linear isometry.
* `MeasureTheory.Lp.dualEquivLInfty`: For a finite measure `μ`, the above is an
  isometric linear equivalence `Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`.

## Implementation notes

The forward map `L^∞ → (L¹)*` is constructed via
`ContinuousLinearMap.lpPairing` with the evaluation bilinear form. Surjectivity
for finite measures is proved by Radon–Nikodym: a bounded linear functional
`φ : L¹ →L[𝕜] 𝕜` is decomposed via `RCLike.re` and `RCLike.im` into two
real-valued functionals, each of which induces a finite signed measure
absolutely continuous w.r.t. `μ`. The combined Radon–Nikodym derivative provides
the required `L^∞` element.

The σ-finite generalization is deferred to a follow-up — for a σ-finite `μ`,
exhaust by finite-measure spanning sets and glue.

## References

* Rudin, *Real and Complex Analysis*, Theorem 6.16.
-/

@[expose] public section

open ENNReal MeasureTheory NNReal

noncomputable section

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]

/-! ### The forward map `L^∞ → (L¹)*` -/

namespace Lp

section Forward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For `f ∈ Lp E ∞ μ`, the pointwise norm `‖f x‖` is bounded by the `Lp` norm `‖f‖`
almost everywhere. -/
lemma ae_norm_le_norm (f : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖(f : α → E) x‖ ≤ ‖f‖ := by
  have h₂ : eLpNormEssSup (f : α → E) μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top]; exact (Lp.memLp f).2.ne
  filter_upwards [ae_le_eLpNormEssSup (f := (f : α → E)) (μ := μ)] with x hx
  rw [Lp.norm_def, eLpNorm_exponent_top, ← ENNReal.toReal_ofReal (norm_nonneg _)]
  exact ENNReal.toReal_mono h₂ (by rwa [← ofReal_norm_eq_enorm] at hx)

/-- The natural map from `Lp (StrongDual 𝕜 E) ∞ μ` to `StrongDual 𝕜 (Lp E 1 μ)`,
sending a bounded linear functional-valued `L^∞` function `g` to the scalar
functional `f ↦ ∫ x, g x (f x) ∂μ`. This is a continuous `𝕜`-linear map. -/
def toDualCLM :
    Lp (StrongDual 𝕜 E) ∞ μ →L[𝕜] StrongDual 𝕜 (Lp E 1 μ) :=
  ((NormedSpace.inclusionInDoubleDual 𝕜 E).flip.lpPairing μ ∞ 1)

lemma toDualCLM_apply_apply (g : Lp (StrongDual 𝕜 E) ∞ μ) (f : Lp E 1 μ) :
    toDualCLM g f = ∫ x, g x (f x) ∂μ := by
  simp [toDualCLM, ContinuousLinearMap.lpPairing_eq_integral,
    NormedSpace.inclusionInDoubleDual]

lemma norm_toDualCLM_apply_apply_le (g : Lp (StrongDual 𝕜 E) ∞ μ) (f : Lp E 1 μ) :
    ‖toDualCLM g f‖ ≤ ‖g‖ * ‖f‖ := by
  rw [toDualCLM_apply_apply]
  have hf_int : Integrable (fun x => (f : α → E) x) μ := L1.integrable_coeFn f
  have hfg_int : Integrable (fun x => g x (f x)) μ :=
    (NormedSpace.inclusionInDoubleDual 𝕜 E).flip.integrable_of_bilin_of_bdd_left
      ‖g‖ (Lp.memLp g).1 (ae_norm_le_norm g) hf_int
  calc ‖∫ x, g x (f x) ∂μ‖
      ≤ ∫ x, ‖g x (f x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖g‖ * ‖(f : α → E) x‖ ∂μ :=
        integral_mono_ae hfg_int.norm (hf_int.norm.const_mul _) <|
          (ae_norm_le_norm g).mono fun x hx => ((g x).le_opNorm _).trans <|
            mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖g‖ * ‖f‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

lemma norm_toDualCLM_apply_le (g : Lp (StrongDual 𝕜 E) ∞ μ) :
    ‖toDualCLM g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_toDualCLM_apply_apply_le g)

end Forward

/-! ### Scalar-valued specialization -/

section Scalar

/-- The scalar-valued version of `Lp.toDualCLM`: maps `g : Lp 𝕜 ∞ μ` to the
functional `f ↦ ∫ x, g x * f x ∂μ = ∫ x, f x * g x ∂μ`. -/
def toDualCLMScalar : Lp 𝕜 ∞ μ →L[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ ∞ 1

lemma toDualCLMScalar_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    toDualCLMScalar g f = ∫ x, g x * f x ∂μ := by
  simp [toDualCLMScalar, ContinuousLinearMap.lpPairing_eq_integral]

lemma norm_toDualCLMScalar_apply_apply_le (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    ‖toDualCLMScalar g f‖ ≤ ‖g‖ * ‖f‖ := by
  rw [toDualCLMScalar_apply_apply]
  have hf_int : Integrable (fun x => (f : α → 𝕜) x) μ := L1.integrable_coeFn f
  have hfg_int : Integrable (fun x => g x * f x) μ :=
    (ContinuousLinearMap.mul 𝕜 𝕜).integrable_of_bilin_of_bdd_left
      ‖g‖ (Lp.memLp g).1 (ae_norm_le_norm g) hf_int
  calc ‖∫ x, g x * f x ∂μ‖
      ≤ ∫ x, ‖g x * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖g‖ * ‖(f : α → 𝕜) x‖ ∂μ :=
        integral_mono_ae hfg_int.norm (hf_int.norm.const_mul _) <| by
          filter_upwards [ae_norm_le_norm g] with x hx
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖g‖ * ‖f‖ := by rw [integral_const_mul, L1.norm_eq_integral_norm]

lemma norm_toDualCLMScalar_apply_le (g : Lp 𝕜 ∞ μ) :
    ‖toDualCLMScalar g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_toDualCLMScalar_apply_apply_le g)

end Scalar

/-! ### The scalar sign function -/

section ScalarSign

/-- The unimodular sign of a scalar: `sign z = star z / ‖z‖` for `z ≠ 0`, and `0`
otherwise (using the convention `a / 0 = 0` in a division ring). -/
private noncomputable def scalarSign (z : 𝕜) : 𝕜 := star z / (‖z‖ : 𝕜)

private lemma norm_scalarSign_le (z : 𝕜) : ‖scalarSign (𝕜 := 𝕜) z‖ ≤ 1 := by
  rw [scalarSign, norm_div, norm_star, RCLike.norm_ofReal, abs_norm]
  rcases eq_or_ne (‖z‖ : ℝ) 0 with h | h
  · simp [h]
  · exact (div_self h).le

private lemma scalarSign_mul_self (z : 𝕜) :
    scalarSign (𝕜 := 𝕜) z * z = (‖z‖ : 𝕜) := by
  rcases eq_or_ne z 0 with hz | hz
  · simp [scalarSign, hz]
  · have hz' : (‖z‖ : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rw [scalarSign, div_mul_eq_mul_div, show star z * z = ((‖z‖ : 𝕜)) ^ 2 from
      RCLike.conj_mul z, sq, mul_div_assoc, div_self hz', mul_one]

private lemma measurable_scalarSign : Measurable (scalarSign : 𝕜 → 𝕜) :=
  (continuous_star.measurable).div
    (RCLike.continuous_ofReal.comp continuous_norm).measurable

end ScalarSign

/-! ### The isometry lower bound (scalar case) -/

section IsometryLowerBound

variable [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- For `g : Lp 𝕜 ∞ μ` and `c < ‖g‖`, the set where `‖g x‖ > c` has positive
measure. -/
private lemma measure_norm_gt_pos_of_lt_norm {g : Lp 𝕜 ∞ μ} {c : ℝ}
    (hc : 0 ≤ c) (hcg : c < ‖g‖) :
    μ {x | c < ‖(g : α → 𝕜) x‖} ≠ 0 := fun h_null => absurd
  (by rw [Lp.norm_def, eLpNorm_exponent_top]
      exact ENNReal.toReal_le_of_le_ofReal hc <| eLpNormEssSup_le_of_ae_bound <| by
        rw [ae_iff]; convert h_null using 2; simp only [not_le]) (not_le.mpr hcg)

/-- The isometry lower bound: the operator norm of `toDualCLMScalar g` is at least
`‖g‖`. Combined with `norm_toDualCLMScalar_apply_le`, this shows the map is an
isometric embedding. The proof uses a sign-function test function. -/
lemma norm_le_norm_toDualCLMScalar_apply (g : Lp 𝕜 ∞ μ) :
    ‖g‖ ≤ ‖toDualCLMScalar g‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hg : ε < ‖g‖
  swap
  · linarith [norm_nonneg (toDualCLMScalar g), not_lt.mp hg]
  -- c := ‖g‖ - ε ∈ [0, ‖g‖)
  set c : ℝ := ‖g‖ - ε with hc_def
  have hc_nn : 0 ≤ c := by rw [hc_def]; linarith
  have hc_lt : c < ‖g‖ := by rw [hc_def]; linarith
  -- Strongly measurable representative g₀
  have hg_ae : AEStronglyMeasurable (g : α → 𝕜) μ := (Lp.memLp g).1
  set g₀ : α → 𝕜 := hg_ae.mk _
  have hg₀_sm : StronglyMeasurable g₀ := hg_ae.stronglyMeasurable_mk
  have hg_eq : (g : α → 𝕜) =ᵐ[μ] g₀ := hg_ae.ae_eq_mk
  -- S := {x | c < ‖g₀ x‖}
  set S : Set α := {x | c < ‖g₀ x‖}
  have hS_meas : MeasurableSet S :=
    measurableSet_lt measurable_const hg₀_sm.measurable.norm
  have hS_pos : μ S ≠ 0 := by
    rw [← measure_congr (hg_eq.mono fun x hx => by
      change (c < ‖(g : α → 𝕜) x‖) = (c < ‖g₀ x‖); rw [hx])]
    exact measure_norm_gt_pos_of_lt_norm hc_nn hc_lt
  set r : ℝ := μ.real S
  have hr_pos : 0 < r :=
    ENNReal.toReal_pos hS_pos (measure_lt_top μ S).ne
  -- Unnormalized test function ψ : α → 𝕜 = 𝟙_S · (scalarSign ∘ g₀)
  let ψ : α → 𝕜 := S.indicator (fun y => scalarSign (g₀ y))
  have hψ_meas : StronglyMeasurable ψ :=
    (measurable_scalarSign.comp hg₀_sm.measurable).stronglyMeasurable.indicator hS_meas
  -- Pointwise bound: ‖ψ x‖ ≤ 𝟙_S(x)
  have hψ_bound (x) : ‖ψ x‖ ≤ S.indicator (fun _ => (1 : ℝ)) x := by
    simp only [ψ, Set.indicator]
    split_ifs <;> simp [norm_scalarSign_le]
  have hψ_int : Integrable ψ μ := (integrable_const (1 : ℝ)).mono' hψ_meas.aestronglyMeasurable <|
    ae_of_all μ fun x => (hψ_bound x).trans <| Set.indicator_le_self' (fun _ _ => zero_le_one) x
  set ψ_Lp : Lp 𝕜 1 μ := hψ_int.toL1 ψ with hψ_Lp_def
  have hψ_Lp_eq : (ψ_Lp : α → 𝕜) =ᵐ[μ] ψ := Integrable.coeFn_toL1 hψ_int
  -- ‖ψ_Lp‖ ≤ r
  have hψ_Lp_norm : ‖ψ_Lp‖ ≤ r := by
    rw [hψ_Lp_def, L1.norm_of_fun_eq_integral_norm]
    calc ∫ x, ‖ψ x‖ ∂μ
        ≤ ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ :=
          integral_mono_ae hψ_int.norm
            ((integrable_indicator_iff hS_meas).mpr (integrable_const (1 : ℝ)).integrableOn)
            (ae_of_all μ hψ_bound)
      _ = r := by rw [integral_indicator_const (1 : ℝ) hS_meas, smul_eq_mul, mul_one]
  -- Integrability of ‖g₀‖ on S
  have hg₀_int_S : IntegrableOn (fun x => ‖g₀ x‖) S μ :=
    ((integrable_const ‖g‖).mono' hg₀_sm.measurable.norm.aestronglyMeasurable
      ((ae_norm_le_norm g).mp (hg_eq.mono fun x hxg hx => by
        rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ← hxg]))).integrableOn
  -- φ(ψ_Lp) = ∫_S ‖g₀ x‖ ∂μ (as a real embedded in 𝕜)
  have h_pairing : toDualCLMScalar g ψ_Lp = ((∫ x in S, ‖g₀ x‖ ∂μ : ℝ) : 𝕜) := by
    rw [toDualCLMScalar_apply_apply,
      integral_congr_ae (g := S.indicator (fun y => (‖g₀ y‖ : 𝕜))) ?_,
      integral_indicator hS_meas, integral_ofReal]
    filter_upwards [hg_eq, hψ_Lp_eq] with x hx hψx
    rw [hx, hψx]; simp only [ψ, Set.indicator]
    split_ifs with hS
    · rw [mul_comm, scalarSign_mul_self]
    · simp
  -- Combine: c · r ≤ ‖φ(ψ)‖ ≤ ‖φ‖ · ‖ψ‖ ≤ ‖φ‖ · r
  have h_mul : c * r ≤ ‖toDualCLMScalar g‖ * r :=
    calc c * r
        = ∫ _ in S, c ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, ‖g₀ x‖ ∂μ :=
          setIntegral_mono_on (integrable_const c).integrableOn hg₀_int_S hS_meas
            fun _ hx => hx.le
      _ = ‖toDualCLMScalar g ψ_Lp‖ := by
          rw [h_pairing, RCLike.norm_ofReal,
            abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      _ ≤ ‖toDualCLMScalar g‖ * ‖ψ_Lp‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖toDualCLMScalar g‖ * r :=
          mul_le_mul_of_nonneg_left hψ_Lp_norm (norm_nonneg _)
  linarith [le_of_mul_le_mul_right h_mul hr_pos]

/-- The forward map `L∞ → (L¹)*`, packaged as a linear isometry (for scalar
values and a finite measure). -/
def toDualₗᵢ : Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) where
  toLinearMap := (toDualCLMScalar : Lp 𝕜 ∞ μ →L[𝕜] _).toLinearMap
  norm_map' g := le_antisymm (norm_toDualCLMScalar_apply_le g)
                              (norm_le_norm_toDualCLMScalar_apply g)

@[simp]
lemma toDualₗᵢ_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    toDualₗᵢ g f = ∫ x, g x * f x ∂μ :=
  toDualCLMScalar_apply_apply g f

end IsometryLowerBound

/-! ### Vector measure from a bounded real-valued functional

Given a bounded linear functional `φ : StrongDual ℝ (Lp ℝ 1 μ)`, we build an
associated signed measure `φ.toSignedMeasure` satisfying
`φ.toSignedMeasure s = φ (𝟙_s)` on measurable sets `s`. -/

section VectorMeasureFromFunctional

variable [IsFiniteMeasure μ]

/-- In `Lp ℝ 1 μ`, the indicator functions of disjoint measurable sets are
summable (for finite measure `μ`). -/
private lemma summable_indicatorConstLp_one_disjoint
    {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Function.onFun Disjoint f)) :
    Summable fun i => (indicatorConstLp (μ := μ) (E := ℝ) 1 (hf i)
        (measure_ne_top μ (f i)) (1 : ℝ)) :=
  Summable.of_norm <| (summable_measure_toReal (μ := μ) hf hdisj).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun _ => by
      rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, norm_one, one_mul,
        ENNReal.toReal_one, div_one, Real.rpow_one]

/-- Partial sums of disjoint indicators (in `Lp ℝ 1 μ`) equal the indicator of
the partial union. -/
private lemma sum_range_indicatorConstLp_eq_biUnion
    {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Function.onFun Disjoint f)) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (indicatorConstLp (μ := μ) (E := ℝ) 1 (hf i)
          (measure_ne_top μ (f i)) (1 : ℝ)) =
      indicatorConstLp (μ := μ) (E := ℝ) 1
        ((Finset.range n).measurableSet_biUnion fun i _ => hf i)
        (measure_ne_top μ _) (1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← indicatorConstLp_disjoint_union
      ((Finset.range n).measurableSet_biUnion fun i _ => hf i) (hf n)
      (measure_ne_top μ _) (measure_ne_top μ _) (Set.disjoint_iUnion₂_left.mpr
        fun _ hi => hdisj (Finset.mem_range.mp hi).ne)]
    congr 1
    rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]

/-- The indicator of the union of a disjoint sequence is the `HasSum` of the
individual indicators in `Lp ℝ 1 μ`. This is the key analytic fact for
constructing a signed measure from a bounded linear functional. -/
private lemma hasSum_indicatorConstLp_one_disjoint
    {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun i => (indicatorConstLp (μ := μ) (E := ℝ) 1 (hf i)
                        (measure_ne_top μ (f i)) (1 : ℝ)))
           (indicatorConstLp 1 (MeasurableSet.iUnion hf)
                               (measure_ne_top μ (⋃ i, f i)) (1 : ℝ)) := by
  refine (summable_indicatorConstLp_one_disjoint hf hdisj).hasSum_iff_tendsto_nat.mpr ?_
  simp_rw [sum_range_indicatorConstLp_eq_biUnion hf hdisj]
  refine tendsto_indicatorConstLp_set (p := 1) (s := ⋃ i, f i)
    (ht := fun n => (Finset.range n).measurableSet_biUnion fun i _ => hf i)
    (hμt := fun _ => measure_ne_top _ _) one_ne_top ?_
  -- μ ((⋃ i ∈ range n, f i) ∆ (⋃ i, f i)) → 0
  simp_rw [symmDiff_comm, symmDiff_of_ge (Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i)]
  -- μ (⋃ f \ ⋃ i<n, f) = μ (⋃_{i ≥ n}, f i) = ∑' k, μ(f (k + n)) → 0
  refine (ENNReal.tendsto_sum_nat_add _ ((measure_iUnion hdisj hf).symm ▸
    (measure_lt_top μ _).ne)).congr' ?_
  filter_upwards with n
  -- Show μ (⋃ f \ ⋃_{i<n}, f i) = ∑' k, μ (f (k + n))
  have h_diff_eq : (⋃ i, f i) \ (⋃ i ∈ Finset.range n, f i) = ⋃ k, f (k + n) := by
    ext x
    simp only [Set.mem_diff, Set.mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
    refine ⟨fun ⟨⟨i, hx⟩, h⟩ => ⟨i - n, by rwa [Nat.sub_add_cancel
              (not_lt.mp fun hi => h i hi hx)]⟩,
            fun ⟨k, hx⟩ => ⟨⟨k + n, hx⟩, fun j hj hxj =>
              Set.disjoint_left.mp (hdisj (by omega : j ≠ k + n)) hxj hx⟩⟩
  rw [h_diff_eq, measure_iUnion _ (fun k => hf (k + n))]
  exact fun i j hij => hdisj (by omega : i + n ≠ j + n)

open Classical in
/-- The signed measure associated to a bounded linear functional on `L¹(μ; ℝ)`
for a finite measure `μ`. On a measurable set `s`, its value is
`φ (indicatorConstLp 1 hs _ 1)`. -/
noncomputable def _root_.ContinuousLinearMap.toSignedMeasure
    (φ : StrongDual ℝ (Lp ℝ 1 μ)) : SignedMeasure α where
  measureOf' s := if hs : MeasurableSet s
    then φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))
    else 0
  empty' := by
    simp only [dif_pos MeasurableSet.empty, indicatorConstLp_empty, map_zero]
  not_measurable' _ hs := dif_neg hs
  m_iUnion' f hf hdisj := by
    simp only [dif_pos (hf _), dif_pos (MeasurableSet.iUnion hf)]
    exact (hasSum_indicatorConstLp_one_disjoint hf hdisj).map φ φ.continuous

lemma _root_.ContinuousLinearMap.toSignedMeasure_apply
    (φ : StrongDual ℝ (Lp ℝ 1 μ)) {s : Set α} (hs : MeasurableSet s) :
    φ.toSignedMeasure s = φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) :=
  dif_pos hs

/-- The signed measure from a bounded functional is absolutely continuous w.r.t.
the underlying measure. -/
lemma _root_.ContinuousLinearMap.toSignedMeasure_absolutelyContinuous
    (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    φ.toSignedMeasure ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun s hs_meas hs_null => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs_meas] at hs_null
  rw [φ.toSignedMeasure_apply hs_meas]
  -- `indicatorConstLp 1 hs _ 1 = 0` when `μ s = 0`, so `φ` maps it to 0
  convert map_zero φ
  rw [← indicatorConstLp_empty (p := 1) (c := (1 : ℝ)) (μ := μ)]
  refine Lp.ext <| indicatorConstLp_coeFn.trans <| (?_ :
    s.indicator _ =ᵐ[μ] (∅ : Set α).indicator _).trans indicatorConstLp_coeFn.symm
  filter_upwards [ae_iff.mpr (by simpa using hs_null : μ {x | ¬x ∉ s} = 0)] with x hx
  simp [hx]

end VectorMeasureFromFunctional

/-! ### The real inclusion `Lp ℝ → Lp 𝕜`

Bridge from real-valued `L¹` functions to `𝕜`-valued ones, used to convert the
complex-scalar functional into a pair of real-scalar functionals. -/

section OfRealIncl

variable (𝕜 μ)

/-- The natural inclusion `Lp ℝ 1 μ →L[ℝ] Lp 𝕜 1 μ` sending a real-valued
`L¹` function to its complexification. -/
def ofRealIncl : Lp ℝ 1 μ →L[ℝ] Lp 𝕜 1 μ :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).compLpL 1 μ

variable {𝕜 μ}

lemma ofRealIncl_apply (f : Lp ℝ 1 μ) :
    (ofRealIncl μ 𝕜 f : α → 𝕜) =ᵐ[μ] fun x => ((f : α → ℝ) x : 𝕜) :=
  ContinuousLinearMap.coeFn_compLpL _ f

end OfRealIncl

/-! ### Surjectivity via Radon–Nikodym

For a finite measure `μ`, every bounded linear functional on `L¹(μ; 𝕜)` is
given by integration against an `L∞(μ; 𝕜)` function. The proof decomposes
a complex scalar functional into real and imaginary parts, applies the signed-
measure Radon–Nikodym to each, and recombines. -/

section Surjectivity

variable [IsFiniteMeasure μ]

/-- The real part of a `𝕜`-valued functional, as a bounded real-linear functional
on the real `L¹` space. -/
def _root_.ContinuousLinearMap.reFunctional
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) : StrongDual ℝ (Lp ℝ 1 μ) :=
  (RCLike.reCLM.comp (φ.restrictScalars ℝ)).comp (ofRealIncl μ 𝕜)

/-- The imaginary part of a `𝕜`-valued functional, as a bounded real-linear
functional on the real `L¹` space. -/
def _root_.ContinuousLinearMap.imFunctional
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) : StrongDual ℝ (Lp ℝ 1 μ) :=
  (RCLike.imCLM.comp (φ.restrictScalars ℝ)).comp (ofRealIncl μ 𝕜)

/-- The Radon–Nikodym density associated to a bounded linear functional on
`L¹(μ; 𝕜)` for a finite measure `μ`. -/
noncomputable def _root_.ContinuousLinearMap.density
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) : α → 𝕜 :=
  fun x => (algebraMap ℝ 𝕜) (φ.reFunctional.toSignedMeasure.rnDeriv μ x) +
    RCLike.I * (algebraMap ℝ 𝕜) (φ.imFunctional.toSignedMeasure.rnDeriv μ x)

/-- For a bounded real-valued functional on `L¹(μ; ℝ)` and finite `μ`, the
`Radon–Nikodym` derivative of its associated signed measure is essentially
bounded by the operator norm. -/
private lemma ae_abs_rnDeriv_toSignedMeasure_le_opNorm
    (ψ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∀ᵐ x ∂μ, |ψ.toSignedMeasure.rnDeriv μ x| ≤ ‖ψ‖ := by
  set d := ψ.toSignedMeasure.rnDeriv μ
  have h_int : Integrable d μ := SignedMeasure.integrable_rnDeriv _ _
  -- For measurable s, ∫_s d = ψ.toSignedMeasure s, and |ψ.toSignedMeasure s| ≤ ‖ψ‖ * μ.real s.
  have h_abs_bound : ∀ {s : Set α}, MeasurableSet s →
      |∫ x in s, d x ∂μ| ≤ ‖ψ‖ * μ.real s := fun hs => by
    rw [← withDensityᵥ_apply h_int hs,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ ψ.toSignedMeasure_absolutelyContinuous,
      ψ.toSignedMeasure_apply hs, ← Real.norm_eq_abs]
    refine (ψ.le_opNorm _).trans_eq ?_
    rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, norm_one, one_mul,
      ENNReal.toReal_one, div_one, Real.rpow_one]
  have h_le : d ≤ᵐ[μ] fun _ => ‖ψ‖ :=
    ae_le_of_forall_setIntegral_le h_int (integrable_const _) fun s hs _ => by
      rw [setIntegral_const, smul_eq_mul, mul_comm]; exact (le_abs_self _).trans (h_abs_bound hs)
  have h_ge : (fun _ => -‖ψ‖) ≤ᵐ[μ] d :=
    ae_le_of_forall_setIntegral_le (integrable_const _).neg h_int fun s hs _ => by
      rw [setIntegral_const, smul_eq_mul]; linarith [neg_le_of_abs_le (h_abs_bound hs)]
  filter_upwards [h_le, h_ge] with x hle hge using abs_le.mpr ⟨hge, hle⟩

/-- The density function is essentially bounded (lives in `L∞`). -/
lemma _root_.ContinuousLinearMap.density_memLp_top
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) : MemLp φ.density ∞ μ := by
  -- density = (ofReal ∘ d_re) + I * (ofReal ∘ d_im)
  have h : ∀ (ψ : StrongDual ℝ (Lp ℝ 1 μ)), MemLp (ψ.toSignedMeasure.rnDeriv μ) ∞ μ :=
    fun ψ => memLp_top_of_bound (SignedMeasure.integrable_rnDeriv _ _).aestronglyMeasurable ‖ψ‖ <|
      (ae_abs_rnDeriv_toSignedMeasure_le_opNorm ψ).mono fun _ hx => Real.norm_eq_abs _ ▸ hx
  exact ((h φ.reFunctional).ofReal (K := 𝕜)).add
    ((h φ.imFunctional).ofReal (K := 𝕜) |>.const_mul RCLike.I)

omit [IsFiniteMeasure μ] in
/-- The real inclusion sends the real unit indicator to the scalar unit
indicator. -/
private lemma ofRealIncl_indicatorConstLp_one
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ofRealIncl μ 𝕜 (indicatorConstLp 1 hs hμs (1 : ℝ)) =
      indicatorConstLp 1 hs hμs (1 : 𝕜) := by
  apply Lp.ext
  filter_upwards [ofRealIncl_apply (𝕜 := 𝕜) (indicatorConstLp 1 hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (μ := μ) (p := 1) (hs := hs) (hμs := hμs) (c := (1 : 𝕜))]
    with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]; by_cases hxs : x ∈ s <;> simp [hxs]

/-- Key identity: `φ` applied to the scalar unit indicator equals the set
integral of the density. -/
private lemma apply_indicator_one_eq_setIntegral_density
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) {s : Set α} (hs : MeasurableSet s) :
    φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : 𝕜)) =
      ∫ x in s, φ.density x ∂μ := by
  set d_re := φ.reFunctional.toSignedMeasure.rnDeriv μ
  set d_im := φ.imFunctional.toSignedMeasure.rnDeriv μ
  set z := φ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : 𝕜))
  have h_d_re_int : Integrable d_re μ := SignedMeasure.integrable_rnDeriv _ _
  have h_d_im_int : Integrable d_im μ := SignedMeasure.integrable_rnDeriv _ _
  -- Shared: ∫_s (rnDeriv ψ.toSignedMeasure μ) = ψ(indicator_ℝ)
  have h_int_ψ (ψ : StrongDual ℝ (Lp ℝ 1 μ)) (h_int : Integrable (ψ.toSignedMeasure.rnDeriv μ) μ) :
      ∫ x in s, ψ.toSignedMeasure.rnDeriv μ x ∂μ =
        ψ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) := by
    rw [← withDensityᵥ_apply h_int hs,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ ψ.toSignedMeasure_absolutelyContinuous,
      ψ.toSignedMeasure_apply hs]
  -- Step 1: ∫_s d_re = re z and ∫_s d_im = im z
  have h_int_re : ∫ x in s, d_re x ∂μ = RCLike.re z := (h_int_ψ _ h_d_re_int).trans <| by
    simp [ContinuousLinearMap.reFunctional, ofRealIncl_indicatorConstLp_one, z]
  have h_int_im : ∫ x in s, d_im x ∂μ = RCLike.im z := (h_int_ψ _ h_d_im_int).trans <| by
    simp [ContinuousLinearMap.imFunctional, ofRealIncl_indicatorConstLp_one, z]
  -- Step 2: Set integral of density = ofReal(∫_s d_re) + I * ofReal(∫_s d_im)
  have h_re_int_𝕜 : Integrable (fun x => ((d_re x : 𝕜))) μ := h_d_re_int.ofReal
  have h_im_int_𝕜 : Integrable (fun x => ((d_im x : 𝕜))) μ := h_d_im_int.ofReal
  have h_setInt : ∫ x in s, φ.density x ∂μ =
      ((∫ x in s, d_re x ∂μ : ℝ) : 𝕜) +
      RCLike.I * ((∫ x in s, d_im x ∂μ : ℝ) : 𝕜) := by
    change ∫ x in s, ((d_re x : 𝕜) + RCLike.I * ((d_im x : 𝕜))) ∂μ = _
    rw [integral_add h_re_int_𝕜.integrableOn (h_im_int_𝕜.const_mul RCLike.I).integrableOn,
      integral_const_mul, integral_ofReal, integral_ofReal]
  rw [h_setInt, h_int_re, h_int_im]
  linear_combination (norm := ring_nf) (RCLike.re_add_im z).symm

/-- Representation theorem: every bounded linear functional on `L¹(μ; 𝕜)` for
a finite measure `μ` is given by integration against its density. -/
lemma _root_.ContinuousLinearMap.apply_eq_integral_mul_density
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) (f : Lp 𝕜 1 μ) :
    φ f = ∫ x, f x * φ.density x ∂μ := by
  set F : Lp 𝕜 1 μ →L[𝕜] 𝕜 := toDualCLMScalar (φ.density_memLp_top.toLp)
  have h_F (g : Lp 𝕜 1 μ) : F g = ∫ x, g x * φ.density x ∂μ := by
    change toDualCLMScalar _ g = _
    rw [toDualCLMScalar_apply_apply]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp φ.density_memLp_top] with x hx
    rw [hx, mul_comm]
  -- It suffices to show φ = F as CLMs
  rw [← h_F]
  refine Lp.induction one_ne_top (fun g => φ g = F g) ?_ ?_ ?_ f
  · -- Indicator case: reduce to c = 1 via smul
    intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    have h_smul : (indicatorConstLp (μ := μ) (E := 𝕜) 1 hs hμs.ne c : Lp 𝕜 1 μ) =
        c • indicatorConstLp 1 hs hμs.ne (1 : 𝕜) := by
      simp_rw [indicatorConstLp, ← MemLp.toLp_const_smul]
      congr 1; ext x; simp [Set.indicator]
    rw [h_smul, map_smul, map_smul]
    congr 1
    -- Goal: φ (indicator_1) = F (indicator_1), i.e. ∫_s density = ∫ x, ind_1 · density
    rw [apply_indicator_one_eq_setIntegral_density φ hs, h_F, ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (E := 𝕜) (p := 1) (hs := hs)
      (hμs := hμs.ne) (c := (1 : 𝕜))] with x hx
    rw [hx]; by_cases hxs : x ∈ s <;> simp [hxs]
  · intro f g hf hg _ ihf ihg
    rw [map_add, ihf, ihg, F.map_add]
  · exact isClosed_eq φ.continuous F.continuous

lemma toDualₗᵢ_surjective :
    Function.Surjective (toDualₗᵢ : Lp 𝕜 ∞ μ → StrongDual 𝕜 (Lp 𝕜 1 μ)) := fun φ => by
  refine ⟨φ.density_memLp_top.toLp, ?_⟩
  ext f
  rw [toDualₗᵢ_apply_apply, φ.apply_eq_integral_mul_density f]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp φ.density_memLp_top] with x hx
  rw [hx, mul_comm]

end Surjectivity

/-! ### The final `L^∞ ≃ (L¹)*` isomorphism -/

section DualEquiv

variable [IsFiniteMeasure μ]

/-- **Duality of `L¹` and `L^∞` for finite measures.** For a finite measure `μ`
and scalar field `𝕜` (either `ℝ` or `ℂ`), the space `Lp 𝕜 ∞ μ` is isometrically
isomorphic to the strong dual of `Lp 𝕜 1 μ` via the pairing
`(g, f) ↦ ∫ x, g x * f x ∂μ`. -/
noncomputable def dualEquivLInfty :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) :=
  LinearIsometryEquiv.ofSurjective toDualₗᵢ toDualₗᵢ_surjective

@[simp]
lemma dualEquivLInfty_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    dualEquivLInfty g f = ∫ x, g x * f x ∂μ :=
  toDualₗᵢ_apply_apply g f

end DualEquiv

end Lp

end MeasureTheory
