/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

/-!
# Sub-Gaussian random variables

This presentation of sub-Gaussian random variables is inspired by section 2.5 of
[vershynin2018high]. Let `X` be a random variable. Consider the following five properties, in which
`Kᵢ` are positive reals,
* (i) for all `t ≥ 0`, `ℙ(|X| ≥ t) ≤ 2 * exp(-t^2 / K₁^2)`,
* (ii) for all `p : ℕ` with `1 ≤ p`, `𝔼[|X|^p]^(1/p) ≤ K₂ sqrt(p)`,
* (iii) for all `|t| ≤ 1/K₃`, `𝔼[exp (t^2 * X^2)] ≤ exp (K₃^2 * t^2)`,
* (iv) `𝔼[exp(X^2 / K₄)] ≤ 2`,
* (v) for all `t : ℝ`, `𝔼[exp (t * X)] ≤ exp (K₅ * t^2 / 2)`.

Properties (i) to (iv) are equivalent, in the sense that there exists a constant `C` such that
if `X` satisfies one of those properties with constant `K`, then it satisfies any other one with
constant at most `CK`.

If `𝔼[X] = 0` then properties (i)-(iv) are equivalent to (v) in that same sense.
Property (v) implies that `X` has expectation zero.

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian moment-generating function (mgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `exp (K₅ * t^2 / 2)` which appears in
property (v) is the mgf of a Gaussian with variance `K₅`.
That property (v) is the most convenient one to work with if one wants to prove concentration
inequalities using Chernoff's method.

TODO: implement definitions for (i)-(iv) when it makes sense. For example the maximal constant `K₄`
such that (iv) is true is an Orlicz norm. Prove relations between those properties.

### Conditionally sub-Gaussian random variables and kernels

A related notion to sub-Gaussian random variables is that of conditionally sub-Gaussian random
variables. A random variable `X` is conditionally sub-Gaussian in the sense of (v) with respect to
a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the conditional mgf of `X` conditioned on `m` is almost surely bounded by `exp (c * t^2 / 2)`
for some constant `c`.

As in other parts of Mathlib's probability library (notably the independence and conditional
independence definitions), we express both sub-Gaussian and conditionally sub-Gaussian properties
as special cases of a notion of sub-Gaussianity with respect to a kernel and a measure.

## Main definitions

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment-generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment-generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.

## Main statements

* `measure_sum_ge_le_of_iIndepFun`: Hoeffding's inequality for sums of independent sub-Gaussian
  random variables.
* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: Hoeffding's lemma for random variables with
  expectation zero.
* `measure_sum_ge_le_of_HasCondSubgaussianMGF`: the Azuma-Hoeffding inequality for sub-Gaussian
  random variables.

## Implementation notes

### Definition of `Kernel.HasSubgaussianMGF`

The definition of sub-Gaussian with respect to a kernel and a measure is the following:
```
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)
```
An interesting point is that the integrability condition is not integrability of `exp (t * X)`
with respect to `κ ω'` for `ν`-almost all `ω'`, but integrability with respect to `κ ∘ₘ ν`.
This is a stronger condition, as the weaker one did not allow to prove interesting results about
the sum of two sub-Gaussian random variables.

For the conditional case, that integrability condition reduces to integrability of `exp (t * X)`
with respect to `μ`.

### Definition of `HasCondSubgaussianMGF`

We define `HasCondSubgaussianMGF` as a special case of `Kernel.HasSubgaussianMGF` with the
conditional expectation kernel for `m`, `condExpKernel μ m`, and the restriction of `μ` to `m`,
`μ.trim hm` (where `hm` states that `m` is a sub-sigma-algebra).
Note that `condExpKernel μ m ∘ₘ μ.trim hm = μ`. The definition is equivalent to the two
conditions
* for all `t`, `exp (t * X)` is `μ`-integrable,
* for `μ.trim hm`-almost all `ω`, for all `t`, the mgf with respect to the conditional
  distribution `condExpKernel μ m ω` is bounded by `exp (c * t ^ 2 / 2)`.

For any `t`, we can write the mgf of `X` with respect to the conditional expectation kernel as
a conditional expectation, `(μ.trim hm)`-almost surely:
`mgf X (condExpKernel μ m ·) t =ᵐ[μ.trim hm] μ[fun ω' ↦ exp (t * X ω') | m]`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
  science*][vershynin2018high]

-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

/-- A random variable `X` has a sub-Gaussian moment-generating function with parameter `c`
with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`, for all `t : ℝ`,
the moment-generating function of `X` with respect to `κ ω'` is bounded by `exp (c * t ^ 2 / 2)`.
This implies in particular that `X` has expectation 0. -/
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

namespace Kernel.HasSubgaussianMGF

section BasicProperties

lemma aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  have h_int := h.ae_integrable_exp_mul 1
  filter_upwards [h_int] with ω h_int
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have h_int (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

set_option backward.isDefEq.respectTransparency false in
lemma ae_forall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : ℝ≥0) :
    ∀ᵐ ω' ∂ν, ∀ t, MemLp (fun ω ↦ exp (t * X ω)) p (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp),
      ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert hf using 3 with ω
    rw [enorm_eq_ofReal (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity),
      ← exp_mul, mul_comm, ← mul_assoc]
    positivity

set_option backward.isDefEq.respectTransparency false in
lemma memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert h' using 3 with ω
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
    positivity

lemma cgf_le (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ ≤ c * t ^ 2 / 2 := by rw [log_exp]

lemma isFiniteMeasure (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, IsFiniteMeasure (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h

lemma measure_univ_le_one (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, κ ω' Set.univ ≤ 1 := by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ ≤ 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

end BasicProperties

protected lemma of_rat (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.HasSubgaussianMGF X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
      have h_int' (n : ℤ) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_int t
      exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)
    filter_upwards [h_mgf, h_int] with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    exact isClosed_le (continuous_mgf h_int) (by fun_prop)

@[simp]
lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    HasSubgaussianMGF (fun _ ↦ 0) 0 κ ν where
  integrable_exp_mul := by simp
  mgf_le := by simpa using ae_of_all _ fun _ ↦ measureReal_le_one

@[simp]
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν := fun_zero

@[simp]
lemma zero_kernel : HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν := by
  constructor
  · simp
  · simp [exp_nonneg]

@[simp]
lemma zero_measure : HasSubgaussianMGF X c κ (0 : Measure Ω') := ⟨by simp, by simp⟩

lemma neg {c : ℝ≥0} (h : HasSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X) c κ ν where
  integrable_exp_mul t := by simpa using h.integrable_exp_mul (-t)
  mgf_le := by filter_upwards [h.mgf_le] with ω' hm t using by simpa [mgf] using hm (-t)

lemma congr {Y : Ω → ℝ} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF Y c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr {Y : Ω → ℝ} (h : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF X c κ ν ↔ HasSubgaussianMGF Y c κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY (ae_eq_symm h)⟩

lemma of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
    {Y : Ω'' → Ω} {X : Ω → ℝ} (hY : Measurable Y) (h : HasSubgaussianMGF X c (κ.map Y) ν) :
    HasSubgaussianMGF (X ∘ Y) c κ ν where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t
    convert h_mgf t
    ext t
    rw [map_apply _ hY, mgf_map hY.aemeasurable]
    convert (h_int t).1
    rw [map_apply _ hY]

lemma id_map_iff (hX : Measurable X) :
    HasSubgaussianMGF id c (κ.map X) ν ↔ HasSubgaussianMGF X c κ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ↦ ?_, ?_⟩⟩
  · change HasSubgaussianMGF (id ∘ X) c κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.integrable_exp_mul t
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h.mgf_le

protected lemma const_mul (h : HasSubgaussianMGF X c κ ν) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (.mk (r ^ 2) (sq_nonneg r) * c) κ ν where
  integrable_exp_mul t := by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul, mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring

section ChernoffBound

lemma measure_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (κ ω').real {ω | ε ≤ X ω} ≤ exp (-t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω').real {ω | ε ≤ X ω}
  _ ≤ exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le (h : HasSubgaussianMGF X c κ ν) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, (κ ω').real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc (κ ω').real {ω | ε ≤ X ω}
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (-(ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by congr; field

end ChernoffBound

section Zero

lemma measure_pos_eq_zero_of_hasSubGaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    ∀ᵐ ω' ∂ν, (κ ω') {ω | 0 < X ω} = 0 := by
  have hs : {ω | 0 < X ω} = ⋃ ε : {ε : ℚ // 0 < ε}, {ω | ε ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hp
      exact ⟨q, (q.cast_pos.1 h1), h2.le⟩
    · intro ⟨q, h1, h2⟩
      exact lt_of_lt_of_le (q.cast_pos.2 h1) h2
  have hb (ε : ℚ) : ∀ᵐ ω' ∂ν, 0 < ε → (κ ω') {ω | ε ≤ X ω} = 0 := by
    filter_upwards [h.measure_ge_le_exp_add ε, h.isFiniteMeasure] with ω' hm _ hε
    simp only [neg_mul, NNReal.coe_zero, zero_mul, zero_div, add_zero] at hm
    suffices (κ ω').real {ω | ε ≤ X ω} = 0 by simpa [Measure.real, ENNReal.toReal_eq_zero_iff]
    have hl : Filter.Tendsto (fun t ↦ rexp (-(t * ε))) Filter.atTop (𝓝 0) := by
      apply tendsto_exp_neg_atTop_nhds_zero.comp
      exact Filter.Tendsto.atTop_mul_const (ε.cast_pos.2 hε) (fun _ a ↦ a)
    apply le_antisymm
    · exact ge_of_tendsto hl (Filter.eventually_atTop.2 ⟨0, hm⟩)
    · exact measureReal_nonneg
  /- `ν`-almost everywhere, `{ω | 0 < X ω}` is a countable union of `κ ω'`-null sets. -/
  filter_upwards [ae_all_iff.2 hb] with ω' hn
  simp only [hs, measure_iUnion_null_iff, Subtype.forall]
  exact fun _ ↦ hn _

lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] 0 := by
  filter_upwards [(h.neg).measure_pos_eq_zero_of_hasSubGaussianMGF_zero,
    h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero]
  intro ω' h1 h2
  simp_rw [Pi.neg_apply, Left.neg_pos_iff] at h1
  apply nonpos_iff_eq_zero.1
  calc (κ ω') {ω | X ω ≠ 0}
  _ = (κ ω') {ω | X ω < 0 ∨ 0 < X ω} := by simp_rw [ne_iff_lt_or_gt]
  _ ≤ (κ ω') {ω | X ω < 0} + (κ ω') {ω | 0 < X ω} := measure_union_le _ _
  _ = 0 := by simp [h1, h2]

/-- Auxiliary lemma for `ae_eq_zero_of_hasSubgaussianMGF_zero'`. -/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable
    (hX : Measurable X) (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  rw [Filter.EventuallyEq, Measure.ae_comp_iff (measurableSet_eq_fun hX (by fun_prop))]
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

lemma ae_eq_zero_of_hasSubgaussianMGF_zero' (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  have hX := h.aestronglyMeasurable
  have h' : HasSubgaussianMGF (hX.mk X) 0 κ ν := h.congr hX.ae_eq_mk
  exact hX.ae_eq_mk.trans (ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable hX.measurable_mk h')

end Zero

section Add

set_option backward.isDefEq.respectTransparency false in
lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX κ ν)
    (hY : HasSubgaussianMGF Y cY κ ν) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) κ ν := by
  by_cases hX0 : cX = 0
  · simp only [hX0, NNReal.sqrt_zero, zero_add, NNReal.sq_sqrt] at hX ⊢
    refine hY.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hX] with ω hX0 using by simp [hX0]
  by_cases hY0 : cY = 0
  · simp only [hY0, NNReal.sqrt_zero, add_zero, NNReal.sq_sqrt] at hY ⊢
    refine hX.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hY] with ω hY0 using by simp [hY0]
  exact
  { integrable_exp_mul t := by
      simp_rw [mul_add, exp_add]
      convert MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
      norm_cast
      infer_instance
    mgf_le := by
      let p := (cX.sqrt + cY.sqrt) / cX.sqrt
      let q := (cX.sqrt + cY.sqrt) / cY.sqrt
      filter_upwards [hX.mgf_le, hY.mgf_le, hX.ae_forall_memLp_exp_mul p,
        hY.ae_forall_memLp_exp_mul q] with ω' hmX hmY hlX hlY t
      calc (κ ω')[fun ω ↦ exp (t * (X ω + Y ω))]
      _ ≤ (κ ω')[fun ω ↦ exp (t * X ω) ^ (p : ℝ)] ^ (1 / (p : ℝ)) *
          (κ ω')[fun ω ↦ exp (t * Y ω) ^ (q : ℝ)] ^ (1 / (q : ℝ)) := by
        simp_rw [mul_add, exp_add]
        apply integral_mul_le_Lp_mul_Lq_of_nonneg
        · exact ⟨by simp [field, p, q], by positivity, by positivity⟩
        · exact ae_of_all _ fun _ ↦ exp_nonneg _
        · exact ae_of_all _ fun _ ↦ exp_nonneg _
        · simpa using (hlX t)
        · simpa using (hlY t)
      _ ≤ exp (cX * (t * p) ^ 2 / 2) ^ (1 / (p : ℝ)) *
          exp (cY * (t * q) ^ 2 / 2) ^ (1 / (q : ℝ)) := by
        simp_rw [← exp_mul _ p, ← exp_mul _ q, mul_right_comm t _ p, mul_right_comm t _ q]
        gcongr
        · exact hmX (t * p)
        · exact hmY (t * q)
      _ = exp ((cX.sqrt + cY.sqrt) ^ 2 * t ^ 2 / 2) := by
        simp_rw [← exp_mul, ← exp_add]
        simp only [NNReal.coe_div, NNReal.coe_add, coe_sqrt, one_div, inv_div, exp_eq_exp, p, q]
        field_simp
        linear_combination t ^ 2 * (-√↑cY * Real.sq_sqrt cX.coe_nonneg
            -√↑cX * Real.sq_sqrt cY.coe_nonneg) }

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {cY : ℝ≥0}

lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF Y cY (prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω.1 + Y ω.2))) ((κ ⊗ₖ η) ∘ₘ ν) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_ofNat] at h
    have : κ ∘ₘ ν = ((κ ⊗ₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst, ← fst_eq, fst_compProd]
    rwa [this, memLp_map_measure_iff h.1 measurable_fst.aemeasurable] at h
  · have h := hY.memLp_exp_mul t 2
    rwa [ENNReal.coe_ofNat, Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff h.1 measurable_snd.aemeasurable] at h

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : (Ω' × Ω) Ω''`, if a random variable `X : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `ν ⊗ₘ κ : Measure (Ω' × Ω)`, then `X + Y` (random
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect to
`κ ⊗ₖ η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
lemma add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ η) ν := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_rat (integrable_exp_add_compProd hX hY) fun q ↦ ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul q, Measure.ae_ae_of_ae_compProd hY.mgf_le,
    Measure.ae_integrable_of_integrable_comp <| integrable_exp_add_compProd hX hY q]
    with ω' hX_mgf hX_int hY_mgf h_int_mul
  calc mgf (fun p ↦ X p.1 + Y p.2) ((κ ⊗ₖ η) ω') q
  _ = ∫ x, exp (q * X x) * ∫ y, exp (q * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    simp_rw [mgf, mul_add, exp_add] at h_int_mul ⊢
    simp_rw [integral_compProd h_int_mul, integral_const_mul]
  _ ≤ ∫ x, exp (q * X x) * exp (cY * q ^ 2 / 2) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun ω ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · filter_upwards [all_ae_of hY_mgf q] with ω hY_mgf
      gcongr
      exact hY_mgf
  _ ≤ exp (↑(c + cY) * q ^ 2 / 2) := by
    rw [integral_mul_const, NNReal.coe_add, add_mul, add_div, exp_add]
    gcongr
    exact hX_mgf q

/-- For `ν : Measure Ω'`, `κ : Kernel Ω' Ω` and `η : Ω Ω''`, if a random variable `X : Ω → ℝ`
has a sub-Gaussian mgf with respect to `κ` and `ν` and another random variable `Y : Ω'' → ℝ` has
a sub-Gaussian mgf with respect to `η` and `κ ∘ₘ ν : Measure Ω`, then `X + Y` (random
variable on the measurable space `Ω × Ω''`) has a sub-Gaussian mgf with respect to
`κ ⊗ₖ prodMkLeft Ω' η : Kernel Ω' (Ω × Ω'')` and `ν`. -/
lemma add_comp {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end Add

end Kernel.HasSubgaussianMGF

end Kernel

section Conditional

/-! ### Conditionally sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

variable (m) (hm) in
/-- A random variable `X` has a conditionally sub-Gaussian moment-generating function
with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`,
`exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned on `m` is
almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
to the sigma-algebra `m`. -/
def HasCondSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubgaussianMGF

lemma mgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, mgf X (condExpKernel μ m ω') t ≤ exp (c * t ^ 2 / 2) :=
  Kernel.HasSubgaussianMGF.mgf_le h

lemma cgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ t, cgf X (condExpKernel μ m ω') t ≤ c * t ^ 2 / 2 :=
  Kernel.HasSubgaussianMGF.cgf_le h

lemma ae_trim_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

lemma ae_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) :=
  ae_of_ae_trim hm (h.ae_trim_condExp_le t)

@[simp]
lemma fun_zero : HasCondSubgaussianMGF m hm (fun _ ↦ 0) 0 μ := Kernel.HasSubgaussianMGF.fun_zero

@[simp]
lemma zero : HasCondSubgaussianMGF m hm 0 0 μ := Kernel.HasSubgaussianMGF.zero

lemma memLp_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp_exp_mul h t p

lemma integrable_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

end HasCondSubgaussianMGF

end Conditional

/-! ### Sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A random variable `X` has a sub-Gaussian moment-generating function with parameter `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

This is equivalent to `Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ())`,
as proved in `HasSubgaussianMGF_iff_kernel`.
Properties about sub-Gaussian moment-generating functions should be proved first for
`Kernel.HasSubgaussianMGF` when possible. -/
structure HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

lemma HasSubgaussianMGF_iff_kernel :
    HasSubgaussianMGF X c μ
      ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

namespace HasSubgaussianMGF

lemma aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma aemeasurable (h : HasSubgaussianMGF X c μ) : AEMeasurable X μ :=
  h.aestronglyMeasurable.aemeasurable

lemma congr (h : HasSubgaussianMGF X c μ) {Y : Ω → ℝ} (h' : X =ᵐ[μ] Y) :
    HasSubgaussianMGF Y c μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa

lemma memLp_exp_mul (h : HasSubgaussianMGF X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul t p

lemma cgf_le (h : HasSubgaussianMGF X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using (all_ae_of h.cgf_le t)

@[simp]
lemma fun_zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF (fun _ ↦ 0) 0 μ := by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]
lemma zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF 0 0 μ := fun_zero

lemma neg {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : HasSubgaussianMGF (-X) c μ := by
  simpa [HasSubgaussianMGF_iff_kernel] using (HasSubgaussianMGF_iff_kernel.1 h).neg

lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)) :
    HasSubgaussianMGF (X ∘ Y) c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubgaussianMGF id c (μ.map X) ↔ HasSubgaussianMGF X c μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ↦ ?_, fun t ↦ ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t
  · rw [mgf_id_map hX]
    exact h.mgf_le t

lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (hX : HasSubgaussianMGF X c μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubgaussianMGF Y c μ' := by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF X c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t
    · exact Measurable.stronglyMeasurable <| by fun_prop

protected lemma const_mul (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * c) μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r

lemma integrableExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) :
    integrableExpSet X μ = Set.univ := by
  ext t
  simpa using hX.integrable_exp_mul t

lemma memLp (hX : HasSubgaussianMGF X c μ) (p : ℝ≥0) : MemLp X p μ :=
  memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX]) p

lemma integrable (hX : HasSubgaussianMGF X c μ) : Integrable X μ :=
  integrable_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX])

section ChernoffBound

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

end ChernoffBound

section Zero

lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 μ) : X =ᵐ[μ] 0 := by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).ae_eq_zero_of_hasSubgaussianMGF_zero

end Zero

section Add

lemma add {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) μ := by
  have := (HasSubgaussianMGF_iff_kernel.1 hX).add (HasSubgaussianMGF_iff_kernel.1 hY)
  simpa [HasSubgaussianMGF_iff_kernel] using this

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω ↦ X ω + Y ω) (cX + cY) μ where
  integrable_exp_mul t := by
    simp_rw [mul_add, exp_add]
    convert MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
    norm_cast
    infer_instance
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t).1 (hY.integrable_exp_mul t).1
    _ ≤ exp (cX * t ^ 2 / 2) * exp (cY * t ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX.mgf_le t
      · exact hY.mgf_le t
    _ = exp ((cX + cY) * t ^ 2 / 2) := by rw [← exp_add]; congr; ring

lemma sub_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω ↦ X ω - Y ω) (cX + cY) μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

set_option backward.isDefEq.respectTransparency false in
private lemma sum_of_iIndepFun_of_forall_aemeasurable
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finset_sum_of_notMem₀ h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) ?_
    · exact fun i hi ↦ h_subG _ (Finset.mem_insert_of_mem hi)
    · convert h_indep'
      rw [Finset.sum_apply]

lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ := by
  have : HasSubgaussianMGF (fun ω ↦ ∑ (i : s), X i ω) (∑ (i : s), c i) μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i ↦ (h_subG i i.2).aemeasurable
    · exact fun i _ ↦ h_subG i i.2
  rw [Finset.sum_coe_sort] at this
  exact this.congr (ae_of_all _ fun ω ↦ Finset.sum_attach s (fun i ↦ X i ω))

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  (sum_of_iIndepFun h_indep h_subG).measure_ge_le hε

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_range_ge_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    {n : ℕ} (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ exp (-ε ^ 2 / (2 * n * c)) := by
  have h := (sum_of_iIndepFun h_indep (c := fun _ ↦ c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

/-- For `X, Y` two independent sub-Gaussian random variables such that `μ[X] ≥ μ[Y]`,
the probability that `X ≤ Y` is bounded by an exponential decay term. -/
lemma measureReal_le_le_exp {Y : Ω → ℝ} {cX cY : ℝ≥0}
    (hX : HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) cX μ)
    (hY : HasSubgaussianMGF (fun ω ↦ Y ω - μ[Y]) cY μ)
    (hindep : IndepFun X Y μ) (h_le : μ[Y] ≤ μ[X]) :
    μ.real {ω | X ω ≤ Y ω} ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
  calc μ.real {ω | X ω ≤ Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) ≤ (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ ≤ Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω ↦ (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      ?_
    · rw [add_comm cX]
      refine sub_of_indepFun hY hX ?_
      exact hindep.symm.comp (φ := fun x ↦ x - μ[Y]) (ψ := fun x ↦ x - μ[X])
        (by fun_prop) (by fun_prop)
    · grind
    · congr 2
      grind

end Add

end HasSubgaussianMGF

section HoeffdingLemma

protected lemma mgf_le_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b t : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X] = 0) (ht : 0 < t) :
    mgf X μ t ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) := by
  have hi (u : ℝ) : Integrable (fun ω ↦ exp (u * X ω)) μ := integrable_exp_mul_of_mem_Icc hm hb
  have hs : Set.Icc 0 t ⊆ interior (integrableExpSet X μ) := by simp [hi, integrableExpSet]
  obtain ⟨u, h1, h2⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hc hs
  rw [← exp_cgf (hi t), exp_le_exp, h2]
  gcongr
  calc
  _ = Var[X; μ.tilted (u * X ·)] := by
    rw [← variance_tilted_mul (hs (Set.mem_Icc_of_Ioo h1))]
  _ ≤ ((b - a) / 2) ^ 2 := by
    convert variance_le_sq_of_bounded ((tilted_absolutelyContinuous μ (u * X ·)) hb) _
    · exact isProbabilityMeasure_tilted (hi u)
    · exact hm.mono_ac (tilted_absolutelyContinuous μ (u * X ·))
  _ = (‖b - a‖₊ / 2) ^ 2 := by simp [field]

/-- **Hoeffding's lemma**: with respect to a probability measure `μ`, if `X` is a random variable
that has expectation zero and is almost surely in `Set.Icc a b` for some `a ≤ b`, then `X` has a
sub-Gaussian moment-generating function with parameter `((b - a) / 2) ^ 2`. -/
lemma hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X] = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ where
  integrable_exp_mul t := integrable_exp_mul_of_mem_Icc hm hb
  mgf_le t := by
    obtain ht | ht | ht := lt_trichotomy 0 t
    · exact ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
    · simp [← ht]
    calc
    _ = mgf (-X) μ (-t) := by simp [mgf]
    _ ≤ exp ((‖-a - -b‖₊ / 2) ^ 2 * (-t) ^ 2 / 2) := by
      apply ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (hm.neg)
      · filter_upwards [hb] with ω ⟨hl, hr⟩ using ⟨neg_le_neg_iff.2 hr, neg_le_neg_iff.2 hl⟩
      · rw [integral_neg, hc, neg_zero]
      · rwa [Left.neg_pos_iff]
    _ = exp (((‖b - a‖₊ / 2) ^ 2) * t ^ 2 / 2) := by ring_nf

/-- A corollary of Hoeffding's lemma for bounded random variables. -/
lemma hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : ℝ} (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ := by
  rw [← sub_sub_sub_cancel_right b a μ[X]]
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm.sub_const _)
  · filter_upwards [hb] with ω hab using by simpa using hab
  · simp [integral_sub (Integrable.of_mem_Icc a b hm hb) (integrable_const _)]

end HoeffdingLemma

section Martingale

variable [StandardBorelSpace Ω]

/-- If `X` is sub-Gaussian with parameter `cX` with respect to the restriction of `μ` to
a sub-sigma-algebra `m` and `Y` is conditionally sub-Gaussian with parameter `cY` with respect to
`m` and `μ` then `X + Y` is sub-Gaussian with parameter `cX + cY` with respect to `μ`.

`HasSubgaussianMGF X cX (μ.trim hm)` can be obtained from `HasSubgaussianMGF X cX μ` if `X` is
`m`-measurable. See `HasSubgaussianMGF.trim`. -/
lemma HasSubgaussianMGF.add_of_hasCondSubgaussianMGF [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {cX cY : ℝ≥0} (hm : m ≤ mΩ)
    (hX : HasSubgaussianMGF X cX (μ.trim hm)) (hY : HasCondSubgaussianMGF m hm Y cY μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ := by
  suffices HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (cX + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ (fun ω ↦ (id ω, id ω)) := rfl
    rw [h_eq]
    refine HasSubgaussianMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [HasSubgaussianMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubgaussianMGF Y cY (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert hX.add_comp hY'
  ext
  rw [Kernel.const_apply, ← Measure.compProd, compProd_trim_condExpKernel]

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_add_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.add_of_hasCondSubgaussianMGF

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}

set_option backward.isDefEq.respectTransparency false in
/-- Let `Y` be a random process strongly adapted to a filtration `ℱ`, such that for all `i : ℕ`,
`Y i` is conditionally sub-Gaussian with parameter `cY i` with respect to `ℱ (i - 1)`.
In particular, `n ↦ ∑ i ∈ range n, Y i` is a martingale.
Then the sum `∑ i ∈ range n, Y i` is sub-Gaussian with parameter `∑ i ∈ range n, cY i`. -/
lemma HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi ↦ h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF.add_of_hasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by lia))
      refine HasSubgaussianMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun m hm ↦
        ((h_adapted m).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hm
      lia

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF

/-- **Azuma-Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_ge_le_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

@[deprecated (since := "2026-01-27")]
alias measure_sum_ge_le_of_HasCondSubgaussianMGF := measure_sum_ge_le_of_hasCondSubgaussianMGF

end Martingale

end ProbabilityTheory
