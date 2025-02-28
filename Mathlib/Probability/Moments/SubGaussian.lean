/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Martingale.Basic
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

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian moment generating function (mgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `exp (K₅ * t^2 / 2)` which appears in
property (v) is the mgf of a Gaussian with variance `K₅`.
That property (v) is the most convenient one to work with if one wants to prove concentration
inequalities using Chernoff's method.

TODO: implement definitions for (i)-(iv) when it makes sense (for example (iv) is linked to an
Orlicz norm) and prove relations between those properties.

### Conditionally sub-Gaussian random variables and kernels

TODO: talk about kernels, conditional sub-G, how sub-G is related.

## Main definitions

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment generating function of `X` contioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.

## Main statements

*
* `HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF`

## Implementation notes

TODO: talk about integrability wrt `κ ∘ₘ ν` instead of a.e. integrability.
In the conditional case, that's integrability wrt `μ`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
science*][vershynin2018high]

-/

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

@[simp]
lemma prodMkLeft_comp_compProd {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ}
    {ν : Measure α} {κ : Kernel α β} {η : Kernel β γ} [SFinite ν] [IsSFiniteKernel κ] :
    (η.prodMkLeft α) ∘ₘ ν ⊗ₘ κ = η ∘ₘ κ ∘ₘ ν := by
  conv_rhs => rw [← Measure.snd_compProd (μ := ν)]
  rw [Kernel.prodMkLeft, Measure.snd, ← Measure.deterministic_comp_eq_map measurable_snd,
    Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

/-- A random variable `X` has a sub-Gaussian moment generating function with parameter `c`
with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`, for all `t : ℝ`,
the moment generating function of `X` with respect to `κ ω'` is bounded by `exp (c * t ^ 2 / 2)`. -/
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t : ℝ, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

namespace Kernel.HasSubgaussianMGF

lemma aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul 1
  simp only [one_mul] at h_int
  exact (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  have h_int := h.ae_integrable_exp_mul 1
  simp only [one_mul] at h_int
  filter_upwards [h_int] with ω h_int
  exact (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    fun _ ↦ h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

lemma integrableExpSet_eq_univ (h : HasSubgaussianMGF X c κ ν) :
    ∀ᵐ ω' ∂ν, integrableExpSet X (κ ω') = Set.univ := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' h_int
  ext t
  simp [h_int t, integrableExpSet]

lemma integrable_exp_mul_of_int
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω')) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

protected lemma of_rat (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.HasSubgaussianMGF X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
      refine integrable_exp_mul_of_int (fun n ↦ ?_)
      exact Measure.ae_integrable_of_integrable_comp (h_int n)
    filter_upwards [h_mgf, h_int]
      with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    refine isClosed_le ?_ (by fun_prop)
    exact continuous_mgf fun u ↦ h_int _

protected lemma memLp (h : HasSubgaussianMGF X c κ ν) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simp only [hp0, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert h' using 3 with p
    rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
    simp

lemma cgf_le (h : HasSubgaussianMGF X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simp only [h0, mgf_zero_measure, Pi.zero_apply, log_zero, log_exp]
      positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ ≤ c * t ^ 2 / 2 := by rw [log_exp]

@[simp]
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    HasSubgaussianMGF (fun _ ↦ 0) 0 κ ν := by
  refine .of_rat ?_ ?_
  · simp
  · refine fun q ↦ ?_
    simp only [mgf_const', mul_zero, exp_zero, mul_one, NNReal.coe_zero, zero_mul, zero_div]
    exact ae_of_all _ fun _ ↦ toReal_prob_le_one

@[simp]
lemma zero' [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν := zero

lemma congr {Y : Ω → ℝ} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF Y c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω' hω'
    rw [hω']
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr {Y : Ω → ℝ} (h : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF X c κ ν ↔ HasSubgaussianMGF Y c κ ν :=
  ⟨fun hX ↦ congr hX h, fun hY ↦ congr hY <| by filter_upwards [h] with ω' hω' using hω'.symm⟩

protected lemma of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
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
    rw [Kernel.map_apply _ hY, mgf_map hY.aemeasurable]
    convert (h_int t).1
    rw [Kernel.map_apply _ hY]

lemma id_map (hX : Measurable X) :
    HasSubgaussianMGF id c (κ.map X) ν ↔ HasSubgaussianMGF X c κ ν := by
  have h_map : (κ.map X) ∘ₘ ν = (κ ∘ₘ ν).map X := by
    rw [← deterministic_comp_eq_map hX, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨fun t ↦ ?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨fun t ↦ ?_, ?_⟩⟩
  · specialize h1 t
    rw [h_map] at h1
    rwa [integrable_map_measure] at h1
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h2
  · specialize h1 t
    rwa [h_map, integrable_map_measure]
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h2

lemma measure_ge_le_exp_add [IsFiniteKernel κ] (h : HasSubgaussianMGF X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (κ ω' {ω | ε ≤ X ω}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h1 h2 t ht
  calc (κ ω' {ω | ε ≤ X ω}).toReal
  _ ≤ exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteKernel κ] (h : HasSubgaussianMGF X c κ ν) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, (κ ω' {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc (κ ω' {ω | ε ≤ X ω}).toReal
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (- (ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by congr; field_simp; ring

lemma prob_ge_le [IsMarkovKernel κ] (h : HasSubgaussianMGF X c κ ν)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, (κ ω' {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · refine ae_of_all _ fun ω' ↦ ?_
    simpa [hc0] using toReal_prob_le_one
  · exact h.measure_ge_le (lt_of_le_of_ne zero_le' (Ne.symm hc0)) hε

section Add

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {cY : ℝ≥0}
  [SFinite ν] [IsSFiniteKernel κ]

lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF Y cY (prodMkLeft Ω' η) (ν ⊗ₘ κ) where
  integrable_exp_mul := by
    convert h.integrable_exp_mul
    simp
  mgf_le := by
    have h2 := h.mgf_le
    simp only [prodMkLeft_apply] at h2
    rw [← Measure.snd_compProd, Measure.snd] at h2
    refine ae_of_ae_map ?_ h2
    fun_prop

lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω.1 + Y ω.2))) (⇑(κ ⊗ₖ η) ∘ₘ ν) := by
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp t 2
    simp only [ENNReal.coe_ofNat] at h
    have : κ ∘ₘ ν = ((κ ⊗ₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst, ← fst_eq, fst_compProd]
    rwa [this, memLp_map_measure_iff h.1 measurable_fst.aemeasurable] at h
  · have h := hY.memLp t 2
    simp only [ENNReal.coe_ofNat] at h
    rwa [Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff h.1 measurable_snd.aemeasurable] at h

lemma add {η : Kernel (Ω' × Ω) Ω''} [IsMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν ⊗ₘ κ)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ η) ν := by
  refine .of_rat (integrable_exp_add_compProd hX hY) ?_
  intro q
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

lemma add' {η : Kernel Ω Ω''} [IsMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY) (κ ⊗ₖ prodMkLeft Ω' η) ν :=
  hX.add hY.prodMkLeft_compProd

end Add

end Kernel.HasSubgaussianMGF

end Kernel

section Conditional

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

variable (m) (hm) in
/-- A random variable `X` has a conditionally sub-Gaussian moment generating function
with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`,
`exp (t * X)` is `μ`-integrable and the moment generating function of `X` contioned on `m` is
almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.

The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
to the sigma-algebra `m`. -/
def HasCondSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

lemma HasCondSubgaussianMGF.condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω) | m]) ω' ≤ exp (c * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [ae_of_ae_trim hm h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

@[simp]
lemma HasCondSubgaussianMGF.zero : HasCondSubgaussianMGF m hm (fun _ ↦ 0) 0 μ :=
  Kernel.HasSubgaussianMGF.zero

@[simp]
lemma HasCondSubgaussianMGF.zero' : HasCondSubgaussianMGF m hm 0 0 μ :=
  Kernel.HasSubgaussianMGF.zero'

lemma HasCondSubgaussianMGF.memLp (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp h t p

lemma HasCondSubgaussianMGF.integrable_exp_mul
    (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

end Conditional

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A random variable `X` has a sub-Gaussian moment generating function with parameter `c`
with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the moment generating function of `X` is bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`. -/
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
  simp only [one_mul] at h_int
  exact (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

lemma memLp (h : HasSubgaussianMGF X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp t p

lemma cgf_le (h : HasSubgaussianMGF X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.cgf_le t

@[simp]
lemma zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF (fun _ ↦ 0) 0 μ := by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]
lemma zero' [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF 0 0 μ := zero

protected lemma of_rat (h_int : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ)
    (h_mgf : ∀ q : ℚ, mgf X μ q ≤ exp (c * q ^ 2 / 2)) :
    HasSubgaussianMGF X c μ where
  integrable_exp_mul := h_int
  mgf_le t := by
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    exact isClosed_le (continuous_mgf h_int) (by fun_prop)

lemma id_map (hX : AEMeasurable X μ) :
    HasSubgaussianMGF id c (μ.map X) ↔ HasSubgaussianMGF X c μ := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨fun t ↦ ?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨fun t ↦ ?_, ?_⟩⟩
  · specialize h1 t
    rwa [integrable_map_measure] at h1
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _, mgf_id_map hX] using h2
  · specialize h1 t
    rwa [integrable_map_measure]
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop
  · simpa [Kernel.map_apply _, mgf_id_map hX] using h2

protected lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF X c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t
    · exact Measurable.stronglyMeasurable <| by fun_prop

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteMeasure μ] (h : HasSubgaussianMGF X c μ) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hc hε

lemma prob_ge_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.prob_ge_le hε

lemma add_of_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : IndepFun X Y μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ where
  integrable_exp_mul t := by
    simp_rw [Pi.add_apply, mul_add, exp_add]
    convert MemLp.integrable_mul (hX.memLp t 2) (hY.memLp t 2)
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

lemma sum_of_iIndepFun {ι : Type*} [IsZeroOrProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (h_indep : iIndepFun (fun _ ↦ inferInstance) X μ) {c : ι → ℝ≥0}
    (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (∑ i ∈ s, X i) (∑ i ∈ s, c i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his h =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    have h_indep' := (h_indep.indepFun_finset_sum_of_not_mem h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) h_indep'
    exact fun i hi ↦ h_subG _ (Finset.mem_insert_of_mem hi)

end HasSubgaussianMGF

lemma HasSubgaussianMGF_of_map  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)) :
    HasSubgaussianMGF (X ∘ Y) c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

section Martingale

lemma HasSubgaussianMGF_add_of_HasCondSubgaussianMGF
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {cY : ℝ≥0} (hm : m ≤ mΩ)
    (hX : HasSubgaussianMGF X c (μ.trim hm)) (hY : HasCondSubgaussianMGF m hm Y cY μ) :
    HasSubgaussianMGF (X + Y) (c + cY) μ := by
  suffices HasSubgaussianMGF (fun p ↦ X p.1 + Y p.2) (c + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ (fun ω ↦ (id ω, id ω)) := by ext; simp
    rw [h_eq]
    refine HasSubgaussianMGF_of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prod_mk measurable_id)
  rw [HasSubgaussianMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubgaussianMGF Y cY (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert hX.add' hY'
  simp only [id_eq]
  ext
  rw [Kernel.const_apply, ← Measure.compProd, compProd_trim_condExpKernel]
  rfl

variable {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}

-- In particular, `∑ i, Y i` is a martingale.
lemma HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF [StandardBorelSpace Ω]
    [IsZeroOrProbabilityMeasure μ] (h_adapted : Adapted ℱ Y)
    (h_subG : ∀ i, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y i) (cY i) μ) (n : ℕ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω) (∑ i ∈ Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_rw [Finset.sum_range_succ]
    refine HasSubgaussianMGF_add_of_HasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n)
    refine HasSubgaussianMGF.trim (ℱ.le n) ?_ hn
    exact Finset.measurable_sum (Finset.range n) fun m hm ↦
      ((h_adapted m).mono (ℱ.mono (Finset.mem_range_le hm))).measurable

end Martingale

end ProbabilityTheory
