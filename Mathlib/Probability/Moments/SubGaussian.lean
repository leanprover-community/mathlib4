/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.MGFAnalytic

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
random variable has sub-Gaussian moment generating function (mgf) with constant `K₅` to mean that
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

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment generating function of `X` conditioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.

## Main statements

* `measure_sum_ge_le_of_iIndepFun`: Hoeffding's inequality for sums of independent sub-Gaussian
  random variables.
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
* for `μ.trim hm`-almost all `ω`, for all `t`, the mgf with respect to the the conditional
  distribution `condExpKernel μ m ω` is bounded by `exp (c * t ^ 2 / 2)`.

For any `t`, we can write the mgf of `X` with respect to the conditional expectation kernel as
a conditional expectation, `(μ.trim hm)`-almost surely:
`mgf X (condExpKernel μ m ·) t =ᵐ[μ.trim hm] μ[fun ω' ↦ exp (t * X ω') | m]`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
  science*][vershynin2018high]

-/

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

/-- A random variable `X` has a sub-Gaussian moment generating function with parameter `c`
with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`, for all `t : ℝ`,
the moment generating function of `X` with respect to `κ ω'` is bounded by `exp (c * t ^ 2 / 2)`.
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
  suffices (κ ω' Set.univ).toReal ≤ 1 by
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
  mgf_le := by simpa using ae_of_all _ fun _ ↦ toReal_prob_le_one

@[simp]
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν := fun_zero

@[simp]
lemma zero_kernel : HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν := by
  constructor
  · simp
  · simp [exp_nonneg]

@[simp]
lemma zero_measure : HasSubgaussianMGF X c κ (0 : Measure Ω') := ⟨by simp, by simp⟩

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

-- todo rename
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

section ChernoffBound

lemma measure_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (κ ω' {ω | ε ≤ X ω}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω' {ω | ε ≤ X ω}).toReal
  _ ≤ exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le (h : HasSubgaussianMGF X c κ ν) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, (κ ω' {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc (κ ω' {ω | ε ≤ X ω}).toReal
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (- (ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by congr; field_simp; ring

end ChernoffBound

section Add

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
    simp_rw [integral_compProd h_int_mul, integral_mul_left]
  _ ≤ ∫ x, exp (q * X x) * exp (cY * q ^ 2 / 2) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun  ω ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · filter_upwards [all_ae_of hY_mgf q] with ω hY_mgf
      gcongr
      exact hY_mgf
  _ ≤ exp (↑(c + cY) * q ^ 2 / 2) := by
    rw [integral_mul_right, NNReal.coe_add, add_mul, add_div, exp_add]
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

/-! ### Conditionally sub-Gaussian moment generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

variable (m) (hm) in
/-- A random variable `X` has a conditionally sub-Gaussian moment generating function
with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`,
`exp (t * X)` is `μ`-integrable and the moment generating function of `X` conditioned on `m` is
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

/-! ### Sub-Gaussian moment generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A random variable `X` has a sub-Gaussian moment generating function with parameter `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the moment generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
This implies in particular that `X` has expectation 0.

This is equivalent to `Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ())`,
as proved in `HasSubgaussianMGF_iff_kernel`.
Properties about sub-Gaussian moment generating functions should be proved first for
`Kernel.HasSubgaussianMGF` when possible. -/
structure HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

-- todo rename
lemma HasSubgaussianMGF_iff_kernel :
    HasSubgaussianMGF X c μ
      ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

namespace HasSubgaussianMGF

lemma aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

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

lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)) :
    HasSubgaussianMGF (X ∘ Y) c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF X c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t
    · exact Measurable.stronglyMeasurable <| by fun_prop

section ChernoffBound

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

end ChernoffBound

section Add

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : IndepFun X Y μ) :
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

lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, X i ω) (∑ i ∈ s, c i) μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finset_sum_of_not_mem h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) ?_
    · exact fun i hi ↦ h_subG _ (Finset.mem_insert_of_mem hi)
    · convert h_indep'
      rw [Finset.sum_apply]

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0} (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ ∑ i ∈ s, X i ω}).toReal ≤ exp (- ε ^ 2 / (2 * ∑ i ∈ s, c i)) :=
  (sum_of_iIndepFun h_indep h_meas h_subG).measure_ge_le hε

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_range_ge_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    (h_meas : ∀ i, Measurable (X i))
    {n : ℕ} (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω}).toReal ≤ exp (- ε ^ 2 / (2 * n * c)) := by
  have h := (sum_of_iIndepFun h_indep h_meas (c := fun _ ↦ c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

end Add

end HasSubgaussianMGF

section Martingale

variable [StandardBorelSpace Ω]

/-- If `X` is sub-Gaussian with parameter `cX` with respect to the restriction of `μ` to
a sub-sigma-algebra `m` and `Y` is conditionally sub-Gaussian with parameter `cY` with respect to
`m` and `μ` then `X + Y` is sub-Gaussian with parameter `cX + cY` with respect to `μ`.

`HasSubgaussianMGF X cX (μ.trim hm)` can be obtained from `HasSubgaussianMGF X cX μ` if `X` is
`m`-measurable. See `HasSubgaussianMGF.trim`. -/
lemma HasSubgaussianMGF_add_of_HasCondSubgaussianMGF [IsFiniteMeasure μ]
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

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}

/-- Let `Y` be a random process adapted to a filtration `ℱ`, such that for all `i : ℕ`, `Y i` is
conditionally sub-Gaussian with parameter `cY i` with respect to `ℱ (i - 1)`.
In particular, `n ↦ ∑ i ∈ range n, Y i` is a martingale.
Then the sum `∑ i ∈ range n, Y i` is sub-Gaussian with parameter `∑ i ∈ range n, cY i`. -/
lemma HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : Adapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi ↦ h_subG i (by omega)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF_add_of_HasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by omega))
      refine HasSubgaussianMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_sum (Finset.range (n + 1)) fun m hm ↦
        ((h_adapted m).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hm
      omega

/-- **Azuma-Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_ge_le_of_HasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : Adapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}).toReal
      ≤ exp (- ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) :=
  (HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

end Martingale

end ProbabilityTheory
