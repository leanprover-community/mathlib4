/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Real

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here using
the L1 Bochner integral constructed in the file `Mathlib/MeasureTheory/Integral/Bochner/L1.lean`.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

* `MeasureTheory.integral`: the Bochner integral on functions defined as the Bochner integral of
  its equivalence class in L1 space, if it is in L1, and 0 otherwise.

The result of that construction is `∫ a, f a ∂μ`, which is definitionally equal to
`setToFun (dominatedFinMeasAdditive_weightedSMul μ) f`. Some basic properties of the integral
(like linearity) are particular cases of the properties of `setToFun` (which are described in the
file `Mathlib/MeasureTheory/Integral/SetToL1.lean`).

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ`

2. Basic order properties of the Bochner integral on functions of type `α → E`, where `α` is a
   measure space and `E` is a real ordered Banach space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` :
    `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. (In the file `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`)
  `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

5. (In `Mathlib/MeasureTheory/Integral/Bochner/Set.lean`) integration commutes with continuous
  linear maps.

  * `ContinuousLinearMap.integral_comp_comm`
  * `LinearIsometry.integral_comp_comm`


## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `Integrable.induction` in the file
`Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean` (or one of the related results, like
`Lp.induction` for functions in `Lp`), which allows you to prove something for an arbitrary
integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` for a complicated example, which proves
that `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and second and third integral sign being the integral on `ℝ≥0∞`-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`
is scattered in sections with the name `posPart`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ENNReal.toReal (∫⁻ a, ENNReal.ofReal <| ‖f a‖)`, that is the norm of
   `f` in `L¹` space. Rewrite using `L1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `isClosed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `SimpleFunc` counterpart, using lemmas
   like `L1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `isClosed_property` or `DenseRange.induction_on` for this argument.

## Notations

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `∫ a, f a ∂μ` : integral of `f` with respect to a measure `μ`
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the ambient type

We also define notations for integral on a set, which are described in the file
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable section

open Filter ENNReal EMetric Set TopologicalSpace Topology
open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

local infixr:25 " →ₛ " => SimpleFunc

/-!
## The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.
-/

variable [NormedAddCommGroup E] [hE : CompleteSpace E] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in
/-- The Bochner integral -/
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0

/-! In the notation for integrals, an expression like `∫ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => integral volume f) => r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => integral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => integral (Measure.restrict volume s) f) => r

section Properties

open ContinuousLinearMap MeasureTheory.SimpleFunc

variable [NormedSpace ℝ E]
variable {f : α → E} {m : MeasurableSpace α} {μ : Measure α}

theorem integral_eq (f : α → E) (hf : Integrable f μ) : ∫ a, f a ∂μ = L1.integral (hf.toL1 f) := by
  simp [integral, hE, hf]

theorem integral_eq_setToFun (f : α → E) :
    ∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul μ) f := by
  simp only [integral, hE, L1.integral]; rfl

theorem L1.integral_eq_integral (f : α →₁[μ] E) : L1.integral f = ∫ a, f a ∂μ := by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm

theorem integral_undef {f : α → G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  by_cases hG : CompleteSpace G
  · simp [integral, hG, h]
  · simp [integral, hG]

theorem Integrable.of_integral_ne_zero {f : α → G} (h : ∫ a, f a ∂μ ≠ 0) : Integrable f μ :=
  Not.imp_symm integral_undef h

theorem integral_non_aestronglyMeasurable {f : α → G} (h : ¬AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = 0 :=
  integral_undef <| not_and_of_not_left _ h

variable (α G)

@[simp]
theorem integral_zero : ∫ _ : α, (0 : G) ∂μ = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_zero (dominatedFinMeasAdditive_weightedSMul μ)
  · simp [integral, hG]

@[simp]
theorem integral_zero' : integral μ (0 : α → G) = 0 :=
  integral_zero α G

lemma integral_indicator₂ {β : Type*} (f : β → α → G) (s : Set β) (b : β) :
    ∫ y, s.indicator (f · y) b ∂μ = s.indicator (fun x ↦ ∫ y, f x y ∂μ) b := by
  by_cases hb : b ∈ s <;> simp [hb]

variable {α G}

theorem integrable_of_integral_eq_one {f : α → ℝ} (h : ∫ x, f x ∂μ = 1) : Integrable f μ :=
  .of_integral_ne_zero <| h ▸ one_ne_zero

theorem integral_add {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg
  · simp [integral, hG]

theorem integral_add' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg

theorem integral_finset_sum {ι} (s : Finset ι) {f : ι → α → G} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_finset_sum (dominatedFinMeasAdditive_weightedSMul _) s hf
  · simp [integral, hG]

@[integral_simps]
theorem integral_neg (f : α → G) : ∫ a, -f a ∂μ = -∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f
  · simp [integral, hG]

theorem integral_neg' (f : α → G) : ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ :=
  integral_neg f

theorem integral_sub {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg
  · simp [integral, hG]

theorem integral_sub' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
  integral_sub hf hg

/-- The Bochner integral is linear. Note this requires `𝕜` to be a normed division ring, in order
to ensure that for `c ≠ 0`, the function `c • f` is integrable iff `f` is. For an analogous
statement for more general rings with an *a priori* integrability assumption on `f`, see
`MeasureTheory.Integrable.integral_smul`. -/
@[integral_simps]
theorem integral_smul [Module 𝕜 G] [NormSMulClass 𝕜 G] [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α → G) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f
  · simp [integral, hG]

theorem Integrable.integral_smul {R : Type*} [NormedRing R] [Module R G] [IsBoundedSMul R G]
    [SMulCommClass ℝ R G] (c : R)
    {f : α → G} (hf : Integrable f μ) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simpa only [integral, hG, hf, hf.fun_smul c] using L1.integral_smul c (toL1 f hf)
  · simp [integral, hG]

theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ :=
  integral_smul r f

@[deprecated (since := "2025-04-27")]
alias integral_mul_left := integral_const_mul

theorem integral_mul_const {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r := by simp only [mul_comm, integral_const_mul r f]

@[deprecated (since := "2025-04-27")]
alias integral_mul_right := integral_mul_const

theorem integral_div {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r := by
  simpa only [← div_eq_mul_inv] using integral_mul_const r⁻¹ f

theorem integral_congr_ae {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h
  · simp [integral, hG]

lemma integral_congr_ae₂ {β : Type*} {_ : MeasurableSpace β} {ν : Measure β} {f g : α → β → G}
    (h : ∀ᵐ a ∂μ, f a =ᵐ[ν] g a) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

@[simp]
theorem L1.integral_of_fun_eq_integral' {f : α → G} (hf : Integrable f μ) :
    ∫ a, (AEEqFun.mk f hf.aestronglyMeasurable) a ∂μ = ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [MeasureTheory.integral, hG, L1.integral]
    exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf
  · simp [MeasureTheory.integral, hG]

theorem L1.integral_of_fun_eq_integral {f : α → G} (hf : Integrable f μ) :
    ∫ a, (hf.toL1 f) a ∂μ = ∫ a, f a ∂μ := by
  simp [hf]

@[continuity]
theorem continuous_integral : Continuous fun f : α →₁[μ] G => ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)
  · simp [integral, hG, continuous_const]

theorem norm_integral_le_lintegral_norm (f : α → G) :
    ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  by_cases hG : CompleteSpace G
  · by_cases hf : Integrable f μ
    · rw [integral_eq f hf, ← Integrable.norm_toL1_eq_lintegral_norm f hf]
      exact L1.norm_integral_le _
    · rw [integral_undef hf, norm_zero]; exact toReal_nonneg
  · simp [integral, hG]

theorem enorm_integral_le_lintegral_enorm (f : α → G) : ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp_rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_of_le_toReal
  exact norm_integral_le_lintegral_norm f

@[deprecated (since := "2025-01-21")]
alias ennnorm_integral_le_lintegral_ennnorm := enorm_integral_le_lintegral_enorm

theorem integral_eq_zero_of_ae {f : α → G} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 := by
  simp [integral_congr_ae hf, integral_zero]

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem HasFiniteIntegral.tendsto_setIntegral_nhds_zero {ι} {f : α → G}
    (hf : HasFiniteIntegral f μ) {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le _)
    fun i => enorm_integral_le_lintegral_enorm _

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι} {f : α → G} (hf : Integrable f μ)
    {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) :=
  hf.2.tendsto_setIntegral_nhds_zero hs

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
theorem tendsto_integral_of_L1 {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF
  · simp [integral, hG, tendsto_const_nhds]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
lemma tendsto_integral_of_L1' {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
lemma tendsto_setIntegral_of_L1 {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G}
    {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le')
      (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
lemma tendsto_setIntegral_of_L1' {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G}
    {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousWithinAt_const]

theorem continuousAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂μ) x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousAt_const]

theorem continuousOn_of_dominated {F : X → α → G} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂μ) s := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousOn_const]

theorem continuous_of_dominated {F : X → α → G} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuous_const]

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`. -/
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ =
      ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂μ) - ENNReal.toReal (∫⁻ a, .ofReal (-f a) ∂μ) := by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    rw [Real.nnnorm_of_nonneg (le_max_right _ _)]
    rw [Real.coe_toNNReal', NNReal.coe_mk]
  -- Go to the `L¹` space
  have eq₂ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (-f a) ∂μ) = ‖Lp.negPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_negPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    simp only [Real.coe_toNNReal', coe_nnnorm, nnnorm_neg]
    rw [Real.norm_of_nonpos (min_le_right _ _), ← max_neg_neg, neg_zero]
  rw [eq₁, eq₂, integral, dif_pos, dif_pos]
  exact L1.integral_eq_norm_posPart_sub _

theorem integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfm : AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff']
      · refine hf.mono ?_
        simp only [Pi.zero_apply]
        intro a h
        simp only [h, neg_nonpos, ofReal_eq_zero]
      · exact measurable_ofReal.comp_aemeasurable hfm.aemeasurable.neg
    rw [h_min, toReal_zero, _root_.sub_zero]
  · rw [integral_undef hfi]
    simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and,
      Classical.not_not] at hfi
    have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
      refine lintegral_congr_ae (hf.mono fun a h => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg h]
    rw [this, hfi, toReal_top]

theorem integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : AEStronglyMeasurable f μ) : ∫ x, ‖f x‖ ∂μ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm_eq_enorm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

@[deprecated (since := "2025-01-21")]
alias integral_norm_eq_lintegral_nnnorm := integral_norm_eq_lintegral_enorm

theorem ofReal_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)

@[deprecated (since := "2025-01-21")]
alias ofReal_integral_norm_eq_lintegral_nnnorm := ofReal_integral_norm_eq_lintegral_enorm

theorem SimpleFunc.integral_eq_integral (f : α →ₛ E) (hfi : Integrable f μ) :
    f.integral μ = ∫ x, f x ∂μ := by
  rw [MeasureTheory.integral_eq f hfi, ← L1.SimpleFunc.toLp_one_eq_toL1,
    L1.SimpleFunc.integral_L1_eq_integral, L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

theorem SimpleFunc.integral_eq_sum (f : α →ₛ E) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x := by
  rw [← f.integral_eq_integral hfi, SimpleFunc.integral, ← SimpleFunc.integral_eq]; rfl

theorem tendsto_integral_approxOn_of_measurable [MeasurableSpace E] [BorelSpace E] {f : α → E}
    {s : Set E} [SeparableSpace s] (hfi : Integrable f μ) (hfm : Measurable f)
    (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E} (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => (SimpleFunc.approxOn f hfm s y₀ h₀ n).integral μ)
      atTop (𝓝 <| ∫ x, f x ∂μ) := by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, hE, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

theorem tendsto_integral_approxOn_of_measurable_of_range_subset [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral μ) atTop
      (𝓝 <| ∫ x, f x ∂μ) := by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

-- We redeclare `E` here to temporarily avoid
-- the `[CompleteSpace E]` and `[NormedSpace ℝ E]` instances.
theorem tendsto_integral_norm_approxOn_sub
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) [SeparableSpace (range f ∪ {0} : Set E)] :
    Tendsto (fun n ↦ ∫ x, ‖SimpleFunc.approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ ∂μ)
      atTop (𝓝 0) := by
  convert (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .mono (.of_subtype (range f ∪ {0})) subset_union_left

theorem integral_eq_integral_pos_part_sub_integral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∫ a, (Real.toNNReal (f a) : ℝ) ∂μ - ∫ a, (Real.toNNReal (-f a) : ℝ) ∂μ := by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

section Order

variable [PartialOrder E] [IsOrderedAddMonoid E] [OrderedSMul ℝ E] [OrderClosedTopology E]

/-- The integral of a function which is nonnegative almost everywhere is nonnegative. -/
lemma integral_nonneg_of_ae {f : α → E} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ ∫ x, f x ∂μ :=
  integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf

lemma integral_nonneg {f : α → E} (hf : 0 ≤ f) :
    0 ≤ ∫ x, f x ∂μ :=
  integral_nonneg_of_ae (ae_of_all _ hf)

lemma integral_nonpos_of_ae {f : α → E} (hf : f ≤ᵐ[μ] 0) :
    ∫ x, f x ∂μ ≤ 0 := by
  rw [← neg_nonneg, ← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa

lemma integral_nonpos {f : α → E} (hf : f ≤ 0) :
    ∫ x, f x ∂μ ≤ 0 :=
  integral_nonpos_of_ae (ae_of_all _ hf)

lemma integral_mono_ae {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  rw [← sub_nonneg, ← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]
lemma integral_mono {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ g) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  integral_mono_ae hf hg (ae_of_all _ h)

lemma integral_mono_of_nonneg {f g : α → E} (hf : 0 ≤ᵐ[μ] f) (hgi : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)

lemma integral_mono_measure {f : α → E} {ν : Measure α} (hle : μ ≤ ν)
    (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν) : ∫ (a : α), f a ∂μ ≤ ∫ (a : α), f a ∂ν := by
  borelize E
  obtain ⟨g, hg, hg_nonneg, hfg⟩ := hfi.1.exists_stronglyMeasurable_range_subset
    isClosed_Ici.measurableSet (Set.nonempty_Ici (a := 0)) hf
  rw [integrable_congr hfg] at hfi
  simp only [integral_congr_ae hfg, integral_congr_ae (ae_mono hle hfg)]
  have _ := hg.separableSpace_range_union_singleton (b := 0)
  have h₁ := tendsto_integral_approxOn_of_measurable_of_range_subset hg.measurable hfi _ le_rfl
  have h₂ := tendsto_integral_approxOn_of_measurable_of_range_subset hg.measurable
    (hfi.mono_measure hle) _ le_rfl
  apply le_of_tendsto_of_tendsto' h₂ h₁
  exact fun n ↦ SimpleFunc.integral_mono_measure
    (Eventually.of_forall <| SimpleFunc.approxOn_range_nonneg hg_nonneg n) hle
    (SimpleFunc.integrable_approxOn_range _ hfi n)

lemma integral_monotoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α → β → E}
    {s : Set β} (hf_mono : ∀ᵐ x ∂μ, MonotoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : MonotoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab

lemma integral_antitoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : α → β → E}
    {s : Set β} (hf_anti : ∀ᵐ x ∂μ, AntitoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : AntitoneOn (fun b => ∫ x, f x b ∂μ) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab

lemma integral_convexOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : α → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conv : ∀ᵐ x ∂μ, ConvexOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConvexOn ℝ s (fun b => ∫ x, f x b ∂μ) := by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ x, f x (p • a + q • b) ∂μ ≤ ∫ x, p • f x a + q • f x b ∂μ := by
                  refine integral_mono_ae ?lhs ?rhs ?ae_le
                  case lhs =>
                    refine hf_int _ ?_
                    rw [convex_iff_add_mem] at hs
                    exact hs ha hb hp hq hpq
                  case rhs => fun_prop (disch := aesop)
                  case ae_le =>
                    filter_upwards [hf_conv] with x hx
                    exact hx.2 ha hb hp hq hpq
            _ = ∫ x, p • f x a ∂μ + ∫ x, q • f x b ∂μ := by
                  apply integral_add
                  all_goals fun_prop (disch := aesop)
            _ = p • ∫ x, f x a ∂μ + q • ∫ x, f x b ∂μ := by simp [integral_smul]

lemma integral_concaveOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : α → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conc : ∀ᵐ x ∂μ, ConcaveOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConcaveOn ℝ s (fun b => ∫ x, f x b ∂μ) := by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

end Order

theorem lintegral_coe_eq_integral (f : α → ℝ≥0) (hfi : Integrable (fun x => (f x : ℝ)) μ) :
    ∫⁻ a, f a ∂μ = ENNReal.ofReal (∫ a, f a ∂μ) := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral

theorem ofReal_integral_eq_lintegral_ofReal {f : α → ℝ} (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx ↦ (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm_eq_enorm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

theorem integral_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x < ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable,
    lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg

theorem lintegral_coe_le_coe_iff_integral_le {f : α → ℝ≥0} (hfi : Integrable (fun x => (f x : ℝ)) μ)
    {b : ℝ≥0} : ∫⁻ a, f a ∂μ ≤ b ↔ ∫ a, (f a : ℝ) ∂μ ≤ b := by
  rw [lintegral_coe_eq_integral f hfi, ENNReal.ofReal, ENNReal.coe_le_coe,
    Real.toNNReal_le_iff_le_coe]

theorem integral_coe_le_of_lintegral_coe_le {f : α → ℝ≥0} {b : ℝ≥0} (h : ∫⁻ a, f a ∂μ ≤ b) :
    ∫ a, (f a : ℝ) ∂μ ≤ b := by
  by_cases hf : Integrable (fun a => (f a : ℝ)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

theorem integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.zero_apply, ofReal_eq_zero]
  · exact (ENNReal.measurable_ofReal.comp_aemeasurable hfi.1.aemeasurable)

theorem integral_eq_zero_iff_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi

lemma integral_eq_iff_of_ae_le {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ = ∫ a, g a ∂μ ↔ f =ᵐ[μ] g := by
  refine ⟨fun h_le ↦ EventuallyEq.symm ?_, fun h ↦ integral_congr_ae h⟩
  rw [← sub_ae_eq_zero,
    ← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

theorem integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) := by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm ℝ 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

theorem integral_pos_iff_support_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    0 < ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (Real.exp_pos _).le) hf]
  suffices (Function.support fun x ↦ Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha (zero_le n)]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    simp_rw [f', integral_sub (hf _) (hf _), integral_sub' hF (hf 0),
      tendsto_sub_const_iff] at this
    exact this
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono (zero_le _))
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousAt_toReal (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ) ?_
  swap
  · rw [← ofReal_integral_eq_lintegral_ofReal (hF.sub (hf 0)) hF_ge]
    finiteness
  refine h_cont.tendsto.comp ?_
  -- use the result for the Lebesgue integral
  refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · exact fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [f', tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n ↦ ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n ↦ ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx n m hnm using neg_le_neg_iff.mpr <| hx hnm
  · filter_upwards [h_tendsto] with x hx using hx.neg

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
lemma tendsto_of_integral_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  -- reduce to the `ℝ≥0∞` case
  let f' : ℕ → α → ℝ≥0∞ := fun n a ↦ ENNReal.ofReal (f n a - f 0 a)
  let F' : α → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : ∀ i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold f'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub (hf_int i) (hf_int 0)]
    · exact (hf_int i).sub (hf_int 0)
    · filter_upwards [hf_mono] with a h_mono
      simp [h_mono (zero_le i)]
  have hF'_int_eq : ∫⁻ a, F' a ∂μ = ENNReal.ofReal (∫ a, F a ∂μ - ∫ a, f 0 a ∂μ) := by
    unfold F'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub hF_int (hf_int 0)]
    · exact hF_int.sub (hf_int 0)
    · filter_upwards [hf_bound] with a h_bound
      simp [h_bound 0]
  have h_tendsto : Tendsto (fun i ↦ ∫⁻ a, f' i a ∂μ) atTop (𝓝 (∫⁻ a, F' a ∂μ)) := by
    simp_rw [hf'_int_eq, hF'_int_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rwa [tendsto_sub_const_iff]
  have h_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f' i a) := by
    filter_upwards [hf_mono] with a ha_mono i j hij
    refine ENNReal.ofReal_le_ofReal ?_
    simp [ha_mono hij]
  have h_bound : ∀ᵐ a ∂μ, ∀ i, f' i a ≤ F' a := by
    filter_upwards [hf_bound] with a ha_bound i
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel, ha_bound i]
  -- use the corresponding lemma for `ℝ≥0∞`
  have h := tendsto_of_lintegral_tendsto_of_monotone ?_ h_tendsto h_mono h_bound ?_
  rotate_left
  · exact (hF_int.1.aemeasurable.sub (hf_int 0).1.aemeasurable).ennreal_ofReal
  · exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt (hF_int.sub (hf_int 0)).2).ne
  filter_upwards [h, hf_mono, hf_bound] with a ha ha_mono ha_bound
  have h1 : (fun i ↦ f i a) = fun i ↦ (f' i a).toReal + f 0 a := by
    unfold f'
    ext i
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_mono (zero_le i)]
  have h2 : F a = (F' a).toReal + f 0 a := by
    unfold F'
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_bound 0]
  rw [h1, h2]
  refine Filter.Tendsto.add ?_ tendsto_const_nhds
  exact (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp ha

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
lemma tendsto_of_integral_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  let f' : ℕ → α → ℝ := fun i a ↦ - f i a
  let F' : α → ℝ := fun a ↦ - F a
  suffices ∀ᵐ a ∂μ, Tendsto (fun i ↦ f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tendsto_of_monotone (fun n ↦ (hf_int n).neg) hF_int.neg ?_ ?_ ?_
  · convert hf_tendsto.neg
    · rw [integral_neg]
    · rw [integral_neg]
  · filter_upwards [hf_mono] with a ha i j hij
    simp [f', ha hij]
  · filter_upwards [hf_bound] with a ha i
    simp [f', F', ha i]

section NormedAddCommGroup

variable {H : Type*} [NormedAddCommGroup H]

theorem L1.norm_eq_integral_norm (f : α →₁[μ] H) : ‖f‖ = ∫ a, ‖f a‖ ∂μ := by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  simp

theorem L1.dist_eq_integral_dist (f g : α →₁[μ] H) : dist f g = ∫ a, dist (f a) (g a) ∂μ := by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
  exact integral_congr_ae <| (Lp.coeFn_sub _ _).fun_comp norm

theorem L1.norm_of_fun_eq_integral_norm {f : α → H} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ a, ‖f a‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae <| hf.coeFn_toL1.fun_comp _

theorem MemLp.eLpNorm_eq_integral_rpow_norm {f : α → H} {p : ℝ≥0∞} (hp1 : p ≠ 0) (hp2 : p ≠ ∞)
    (hf : MemLp f p μ) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ a, ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖ₑ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm_eq_enorm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate_left
  · exact ae_of_all _ fun x => by positivity
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [A, ← ofReal_rpow_of_nonneg toReal_nonneg (inv_nonneg.2 toReal_nonneg), ofReal_toReal]
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp1 hp2 hf.2).ne

@[deprecated (since := "2025-02-21")]
alias Memℒp.eLpNorm_eq_integral_rpow_norm := MemLp.eLpNorm_eq_integral_rpow_norm

end NormedAddCommGroup

theorem norm_integral_le_integral_norm (f : α → G) : ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ := by
  have le_ae : ∀ᵐ a ∂μ, 0 ≤ ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm).symm
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    exact integral_nonneg_of_ae le_ae

lemma abs_integral_le_integral_abs {f : α → ℝ} : |∫ a, f a ∂μ| ≤ ∫ a, |f a| ∂μ :=
  norm_integral_le_integral_norm f

theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) : ‖∫ x, f x ∂μ‖ ≤ ∫ x, g x ∂μ :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ ≤ ∫ x, g x ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]
theorem integral_const (c : E) : ∫ _ : α, c ∂μ = μ.real univ • c := by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral, hE, L1.integral]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, MeasureTheory.not_isFiniteMeasure_iff.mp hμ]

lemma integral_eq_const [IsProbabilityMeasure μ] {f : α → E} {c : E} (hf : ∀ᵐ x ∂μ, f x = c) :
    ∫ x, f x ∂μ = c := by simp [integral_congr_ae hf]

theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α → G} {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C * μ.real univ :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

variable {ν : Measure α}

theorem integral_add_measure {f : α → G} (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hfi := hμ.add_measure hν
  simp_rw [integral_eq_setToFun]
  have hμ_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul μ : Set α → G →L[ℝ] G) 1 :=
    DominatedFinMeasAdditive.add_measure_right μ ν (dominatedFinMeasAdditive_weightedSMul μ)
      zero_le_one
  have hν_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul ν : Set α → G →L[ℝ] G) 1 :=
    DominatedFinMeasAdditive.add_measure_left μ ν (dominatedFinMeasAdditive_weightedSMul ν)
      zero_le_one
  rw [← setToFun_congr_measure_of_add_right hμ_dfma
        (dominatedFinMeasAdditive_weightedSMul μ) f hfi,
    ← setToFun_congr_measure_of_add_left hν_dfma (dominatedFinMeasAdditive_weightedSMul ν) f hfi]
  refine setToFun_add_left' _ _ _ (fun s _ hμνs => ?_) f
  rw [Measure.coe_add, Pi.add_apply, add_lt_top] at hμνs
  rw [weightedSMul, weightedSMul, weightedSMul, ← add_smul,
    measureReal_add_apply hμνs.1.ne hμνs.2.ne]

@[simp]
theorem integral_zero_measure {m : MeasurableSpace α} (f : α → G) :
    (∫ x, f x ∂(0 : Measure α)) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl
  · simp [integral, hG]

@[simp]
theorem setIntegral_measure_zero (f : α → G) {μ : Measure α} {s : Set α} (hs : μ s = 0) :
    ∫ x in s, f x ∂μ = 0 := Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

@[deprecated (since := "2025-06-17")] alias setIntegral_zero_measure := setIntegral_measure_zero

lemma integral_of_isEmpty [IsEmpty α] {f : α → G} : ∫ x, f x ∂μ = 0 :=
  μ.eq_zero_of_isEmpty ▸ integral_zero_measure _

theorem integral_finset_sum_measure {ι} {m : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    {s : Finset ι} (hf : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ a, f a ∂μ i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finset_sum_measure.2 hf.2)

theorem nndist_integral_add_measure_le_lintegral
    {f : α → G} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : ℝ≥0∞) ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := by
  rw [integral_add_measure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

theorem hasSum_integral_measure {ι} {m : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i => ∫ a, f a ∂μ i) (∫ a, f a ∂Measure.sum μ) := by
  have hfi : ∀ i, Integrable f (μ i) := fun i => hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finset_sum_measure fun i _ => hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : ∀ᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := ℝ≥0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x => ‖f x‖ₑ) μ).eventually hmem).mono fun s hs => ?_
  obtain ⟨ν, hν⟩ : ∃ ν, (∑ i ∈ s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) => μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball, ← coe_nndist, NNReal.coe_lt_coe, ← ENNReal.coe_lt_coe, ← hν]
  rw [← hν, integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν, lintegral_add_measure, lintegral_finset_sum_measure] at hs
  exact lt_of_add_lt_add_left hs

theorem integral_sum_measure {ι} {_ : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    (hf : Integrable f (Measure.sum μ)) : ∫ a, f a ∂Measure.sum μ = ∑' i, ∫ a, f a ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

@[simp]
theorem integral_smul_measure (f : α → G) (c : ℝ≥0∞) :
    ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set α → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

@[simp]
theorem integral_smul_nnreal_measure (f : α → G) (c : ℝ≥0) :
    ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ :=
  integral_smul_measure f (c : ℝ≥0∞)

theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α → β} (hφ : Measurable φ)
    {f : β → G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  borelize G
  have : SeparableSpace (range f ∪ {0} : Set G) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_integral_approxOn_of_measurable_of_range_subset hfm.measurable hfi _ Subset.rfl) ?_
  convert tendsto_integral_approxOn_of_measurable_of_range_subset (hfm.measurable.comp hφ)
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) (range f ∪ {0})
    (union_subset_union_left {0} (range_comp_subset_range φ f)) using 1
  ext1 i
  simp only [SimpleFunc.integral_eq, hφ, SimpleFunc.measurableSet_preimage, map_measureReal_apply,
    ← preimage_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  rw [hy]
  simp

theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
    _ = ∫ x, f (φ x) ∂μ := integral_congr_ae <| ae_eq_comp hφ hfm.ae_eq_mk.symm

theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → G) : ∫ y, g y ∂Measure.map f μ = ∫ x, g (f x) ∂μ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

theorem _root_.Topology.IsClosedEmbedding.integral_map {β} [TopologicalSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : α → β} (hφ : IsClosedEmbedding φ)
    (f : β → G) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  hφ.measurableEmbedding.integral_map _

theorem integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → G) :
    ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ :=
  e.measurableEmbedding.integral_map f

omit hE in
lemma integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A → E) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

theorem MeasurePreserving.integral_comp {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  h₁.map_eq ▸ (h₂.integral_map g).symm

theorem MeasurePreserving.integral_comp' {β} [MeasurableSpace β] {ν} {f : α ≃ᵐ β}
    (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f (x : α) ∂(Measure.comap Subtype.val μ) = ∫ x in s, f x ∂μ := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f x = ∫ x in s, f x := integral_subtype_comap hs f

@[simp]
theorem integral_dirac' [MeasurableSpace α] (f : α → E) (a : α) (hfm : StronglyMeasurable f) :
    ∫ x, f x ∂Measure.dirac a = f a := by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
      integral_congr_ae <| ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]
theorem integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α) :
    ∫ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae <| ae_eq_dirac f
    _ = f a := by simp

theorem setIntegral_dirac' {mα : MeasurableSpace α} {f : α → E} (hf : StronglyMeasurable f) (a : α)
    {s : Set α} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

theorem setIntegral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α)
    (s : Set α) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_integral_of_nonneg {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real { x | ε ≤ f x } ≤ ∫ x, f x ∂μ := by
  rcases eq_top_or_lt_top (μ {x | ε ≤ f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε ≤ f x } = ∫ _ in {x | ε ≤ f x}, ε ∂μ := by simp [mul_comm]
      _ ≤ ∫ x in {x | ε ≤ f x}, f x ∂μ :=
        integral_mono_ae (integrable_const _) (hf_int.mono_measure μ.restrict_le_self) <|
          ae_restrict_mem₀ <| hf_int.aemeasurable.nullMeasurable measurableSet_Ici
      _ ≤ _ := integral_mono_measure μ.restrict_le_self hf_nonneg hf_int

/-- Hölder's inequality for the integral of a product of norms. The integral of the product of two
norms of functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are
conjugate exponents. -/
theorem integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : α → E} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) := by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _
  · exact (hg.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _
  · exact (hf.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact hf.1.norm.mul hg.1.norm
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  -- replace norms by nnnorm
  have h_left : ∫⁻ a, ENNReal.ofReal (‖f a‖ * ‖g a‖) ∂μ =
      ∫⁻ a, ((‖f ·‖ₑ) * (‖g ·‖ₑ)) a ∂μ := by
    simp_rw [Pi.mul_apply, ← ofReal_norm_eq_enorm, ENNReal.ofReal_mul (norm_nonneg _)]
  have h_right_f : ∫⁻ a, .ofReal (‖f a‖ ^ p) ∂μ = ∫⁻ a, ‖f a‖ₑ ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h_right_g : ∫⁻ a, .ofReal (‖g a‖ ^ q) ∂μ = ∫⁻ a, ‖g a‖ₑ ^ q ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg]
  rw [h_left, h_right_f, h_right_g]
  -- we can now apply `ENNReal.lintegral_mul_le_Lp_mul_Lq` (up to the `toReal` application)
  refine ENNReal.toReal_mono ?_ ?_
  · refine ENNReal.mul_ne_top ?_ ?_
    · convert hf.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm]
      · rw [ENNReal.toReal_ofReal hpq.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.pos
      · finiteness
    · convert hg.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm]
      · rw [ENNReal.toReal_ofReal hpq.symm.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.symm.pos
      · finiteness
  · exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.1.nnnorm.aemeasurable.coe_nnreal_ennreal
      hg.1.nnnorm.aemeasurable.coe_nnreal_ennreal

/-- Hölder's inequality for functions `α → ℝ`. The integral of the product of two nonnegative
functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q) := by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf, Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg] with x hxf
    rw [Real.norm_of_nonneg hxf]
  have h_right_g : ∫ a, g a ^ q ∂μ = ∫ a, ‖g a‖ ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg_nonneg] with x hxg
    rw [Real.norm_of_nonneg hxg]
  rw [h_left, h_right_f, h_right_g]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg

theorem integral_countable' [Countable α] [MeasurableSingletonClass α] {μ : Measure α}
    {f : α → E} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∑' a, μ.real {a} • f a := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ, integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac, measureReal_def]

theorem integral_singleton' {μ : Measure α} {f : α → E} (hf : StronglyMeasurable f) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

theorem integral_singleton [MeasurableSingletonClass α] {μ : Measure α} (f : α → E) (a : α) :
    ∫ a in {a}, f a ∂μ = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

theorem integral_countable [MeasurableSingletonClass α] (f : α → E) {s : Set α} (hs : s.Countable)
    (hf : IntegrableOn f s μ) :
    ∫ a in s, f a ∂μ = ∑' a : s, μ.real {(a : α)} • f a := by
  have hi : Countable { x // x ∈ s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet, integral_countable' hf']
  congr 1 with a : 1
  rw [measureReal_def, Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

theorem integral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → E)
    (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑ x ∈ s, μ.real {x} • f x := by
  rw [integral_countable _ s.countable_toSet hf, ← Finset.tsum_subtype']

theorem integral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → E)
    (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← integral_finset .univ, Finset.coe_univ, Measure.restrict_univ]
  simp [Finset.coe_univ, hf]

theorem integral_unique [Unique α] (f : α → E) : ∫ x, f x ∂μ = μ.real univ • f default :=
  calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]

theorem integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    {f : α → ℝ} {x : α} (f_cont : Continuous f) (f_int : Integrable f μ) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ x, f x ∂μ :=
  (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

@[simp] lemma integral_count [MeasurableSingletonClass α] [Fintype α] (f : α → E) :
    ∫ a, f a ∂.count = ∑ a, f a := by simp [integral_fintype]

end Properties

section IntegralTrim

variable {β γ : Type*} {m m0 : MeasurableSpace β} {μ : Measure β}

/-- Simple function seen as simple function of a larger `MeasurableSpace`. -/
def SimpleFunc.toLargerSpace (hm : m ≤ m0) (f : @SimpleFunc β m γ) : SimpleFunc β γ :=
  ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩

theorem SimpleFunc.coe_toLargerSpace_eq (hm : m ≤ m0) (f : @SimpleFunc β m γ) :
    ⇑(f.toLargerSpace hm) = f := rfl

theorem integral_simpleFunc_larger_space (hm : m ≤ m0) (f : @SimpleFunc β m F)
    (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ @SimpleFunc.range β F m f, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  have hf_int : Integrable (f.toLargerSpace hm) μ := by rwa [SimpleFunc.coe_toLargerSpace_eq]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

theorem integral_trim_simpleFunc (hm : m ≤ m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m,
    integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (trim_measurableSet_eq hm (@SimpleFunc.measurableSet_fiber β F m f x)).symm

theorem integral_trim (hm : m ≤ m0) {f : β → G} (hf : StronglyMeasurable[m] f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int, integral_undef hf_int_m]
  haveI : SeparableSpace (range f ∪ {0} : Set G) := hf.separableSpace_range_union_singleton
  let f_seq := @SimpleFunc.approxOn G β _ _ _ m _ hf.measurable (range f ∪ {0}) 0 (by simp) _
  have hf_seq_meas : ∀ n, StronglyMeasurable[m] (f_seq n) := fun n =>
    @SimpleFunc.stronglyMeasurable β G m _ (f_seq n)
  have hf_seq_int : ∀ n, Integrable (f_seq n) μ :=
    SimpleFunc.integrable_approxOn_range (hf.mono hm).measurable hf_int
  have hf_seq_int_m : ∀ n, Integrable (f_seq n) (μ.trim hm) := fun n =>
    (hf_seq_int n).trim hm (hf_seq_meas n)
  have hf_seq_eq : ∀ n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂μ.trim hm := fun n =>
    integral_trim_simpleFunc hm (f_seq n) (hf_seq_int n)
  have h_lim_1 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_L1 f hf_int (Eventually.of_forall hf_seq_int) ?_
    exact SimpleFunc.tendsto_approxOn_range_L1_enorm (hf.mono hm).measurable hf_int
  have h_lim_2 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ.trim hm)) := by
    simp_rw [hf_seq_eq]
    refine @tendsto_integral_of_L1 β G _ _ m (μ.trim hm) _ f (hf_int.trim hm hf) _ _
      (Eventually.of_forall hf_seq_int_m) ?_
    exact @SimpleFunc.tendsto_approxOn_range_L1_enorm β G m _ _ _ f _ _ hf.measurable
      (hf_int.trim hm hf)
  exact tendsto_nhds_unique h_lim_1 h_lim_2

theorem integral_trim_ae (hm : m ≤ m0) {f : β → G} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

end IntegralTrim

section SnormBound

variable {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

theorem eLpNorm_one_le_of_le {r : ℝ≥0} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * r := by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this, eLpNorm_zero, hr, ENNReal.coe_zero, mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg, neg_eq_zero]
      exact le_antisymm (integral_nonpos_of_ae hf) hfint'
    have := (integral_eq_zero_iff_of_nonneg_ae ?_ hfint.neg).1 hnegf
    · filter_upwards [this] with ω hω
      rwa [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at hω
    · filter_upwards [hf] with ω hω
      rwa [Pi.zero_apply, Pi.neg_apply, Right.nonneg_neg_iff]
  by_cases hμ : IsFiniteMeasure μ
  swap
  · have : μ Set.univ = ∞ := by
      by_contra hμ'
      exact hμ (IsFiniteMeasure.mk <| lt_top_iff_ne_top.2 hμ')
    rw [this, ENNReal.mul_top', if_neg, ENNReal.top_mul', if_neg]
    · exact le_top
    · simp [hr]
    · norm_num
  haveI := hμ
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint, sub_nonneg] at hfint'
  have hposbdd : ∫ ω, max (f ω) 0 ∂μ ≤ μ.real Set.univ • (r : ℝ) := by
    rw [← integral_const]
    refine integral_mono_ae hfint.real_toNNReal (integrable_const (r : ℝ)) ?_
    filter_upwards [hf] with ω hω using Real.toNNReal_le_iff_le_coe.2 hω
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memLp_one_iff_integrable.2 hfint),
    ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
  simp_rw [ENNReal.toReal_one, _root_.inv_one, Real.rpow_one, Real.norm_eq_abs, ←
    max_zero_add_max_neg_zero_eq_abs_self, ← Real.coe_toNNReal']
  rw [integral_add hfint.real_toNNReal]
  · simp only [Real.coe_toNNReal', ENNReal.toReal_mul, ENNReal.coe_toReal,
      toReal_ofNat] at hfint' ⊢
    refine (add_le_add_left hfint' _).trans ?_
    rwa [← two_mul, mul_assoc, mul_le_mul_left (two_pos : (0 : ℝ) < 2)]
  · exact hfint.neg.sup (integrable_zero _ _ μ)

theorem eLpNorm_one_le_of_le' {r : ℝ} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal r := by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

end SnormBound

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Qq Lean Meta MeasureTheory

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for integrals.

This extension only proves non-negativity, strict positivity is more delicate for integration and
requires more assumptions. -/
@[positivity MeasureTheory.integral _ _]
def evalIntegral : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@MeasureTheory.integral $i ℝ _ $inst2 _ _ $f) =>
    let i : Q($i) ← mkFreshExprMVarQ q($i) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    let pbody ← rbody.toNonneg
    let pr : Q(∀ x, 0 ≤ $f x) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(integral_nonneg $pr)
  | _ => throwError "not MeasureTheory.integral"

end Mathlib.Meta.Positivity
