/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Integral of vector-valued function against vector measure

We extend the definition of the Bochner integral (of vector-valued function against `ℝ≥0∞`-valued
measure) to vector measures through a bilinear pairing.
Let `E`, `F` be normed vector spaces, and `G` be a Banach space (complete normed vector space).
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] G` and an `F`-valued vector measure `μ`
on a measurable space `X`.
For an integrable function `f : X → E` with respect to the total variation of the vector measure
on `X` informally written `μ ∘ B.flip`, we define the `G`-valued integral, which is informally
written `∫ᵛ B (f x) ∂[B; μ] x`.

Such integral is defined through the general setting `setToFun` which sends a set function to the
integral of integrable functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The integral against vector measures is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on integrable functions `f` as `setToFun (...) f`.

## Notations

* `∫ᵛ x, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against the `F`-valued
  vector measure `μ` paired through `B`.
* `∫ᵛ x, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is an `F`-valued
  vector measure, with the pairing being the scalar multiplication by `ℝ`.

## Note

Let `μ` be a vector measure and `B` be a continuous linear pairing.
We often consider integrable functions with respect to the total variation of
`μ.transpose B` = `μ.mapRange B.flip.toAddMonoidHom B.flip.continuous`, which is the reference
measure for the pairing integral.

When `f` is not integrable with respect to `(μ.transpose B).variation`, the value of
`μ.integral B f` is set to `0`. This is an analogous convention to the Bochner integral. However,
there are cases where a natural definition of the integral as an unconditional sum exists, but `f`
is not integrable in this sense: Let `μ` be the `L∞(ℕ)`-valued measure on `ℕ` defined by extending
`{n} ↦ (0,0,..., 1/(n+1),0,0,...)` and `B` be the trivial coupling (the scalar multiplication by
`ℝ`). The total variation is `∑ n, 1/(n+1) = ∞`, but the sum of `(0,...,0,1/n,0,...)` in `L∞(ℕ)` is
unconditionally convergent.

-/

public section

open Set MeasureTheory VectorMeasure ContinuousLinearMap Filter Topology

variable {X E F G : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace MeasureTheory

section cbmApplyMeasure

/-- The composition of the vector measure with the linear pairing, giving the reference
vector measure. -/
@[expose]
noncomputable def VectorMeasure.transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X (E →L[ℝ] G) := μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

/-- Given a set `s`, return the continuous linear map `fun x : E ↦ B x (μ s)` (actually defined
using `transpose` through `mapRange`), where the `B` is a `G`-valued bilinear form on `E × F` and
`μ` is an `F`-valued vector measure. The extension of that set function through `setToFun` gives the
pairing integral of `E`-valued integrable functions. -/
noncomputable def cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    E →L[ℝ] G where
  toFun x := μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..

lemma transpose_eq_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose B = cbmApplyMeasure μ B := by rfl

@[simp]
theorem cbmApplyMeasure_apply (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) (x : E) :
    cbmApplyMeasure μ B s x = B x (μ s) := by
  rfl

theorem cbmApplyMeasure_union (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    cbmApplyMeasure μ B (s ∪ t) = cbmApplyMeasure μ B s + cbmApplyMeasure μ B t := by
  ext x
  simp [of_union hdisj hs ht]

theorem dominatedFinMeasAdditive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    DominatedFinMeasAdditive (μ.transpose B).variation
    (cbmApplyMeasure μ B : Set X → E →L[ℝ] G) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf ↦ ?_⟩
  simpa using norm_measure_le_variation hsf.ne

theorem norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    ‖cbmApplyMeasure μ B s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]

end cbmApplyMeasure

namespace VectorMeasure

lemma restrict_transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    (μ.transpose B).restrict s = (μ.restrict s).transpose B := by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs, transpose]

lemma variation_transpose_le (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.transpose B).variation ≤ ‖B‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  apply opENorm_le_bound _ (fun x ↦ ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opNorm_enorm, le_opNorm_enorm, enorm_measure_le_variation, ← enorm_eq_nnnorm]
  exact le_of_eq (by ring)

lemma absolutelyContinuous_variation_transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.transpose B).variation ≪ μ.variation :=
  Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` if it is integrable with
respect to `(μ.transpose B).variation`. -/
protected abbrev Integrable (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) : Prop :=
  MeasureTheory.Integrable f (μ.transpose B).variation

open Classical in
/-- The `G`-valued integral of `E`-valued function and the `F`-valued vector measure `μ` with linear
paring `B : E →L[ℝ] F →L[ℝ] G` . This is set to be `0` if `G` is not complete or if `f` is not
integrable with respect to `(μ.transpose B).variation`. -/
noncomputable def integral (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) : G :=
  setToFun (μ.transpose B).variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" => integral μ r B

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral μ r (lsmul ℝ ℝ)

@[inherit_doc integral]
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" =>
  integral (VectorMeasure.restrict μ s) r B

/-- The special case of the pairing integral in a set where the pairing is just the scalar
multiplication by `ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul ℝ ℝ)

variable {μ : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G} {f g : X → E}

@[simp] lemma integrable_zero : (0 : VectorMeasure X F).Integrable f B := by
  simp [VectorMeasure.Integrable, transpose]

lemma Integrable.restrict (hf : μ.Integrable f B) {s : Set X} :
    (μ.restrict s).Integrable f B := by
  by_cases hs : MeasurableSet s
  · simp only [VectorMeasure.Integrable, ← restrict_transpose, variation_restrict _ hs]
    exact MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp] theorem integral_zero_vectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0 := by
  apply setToFun_zero_left'
  simp [transpose]

theorem integral_fun_add (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_add (dominatedFinMeasAdditive_cbmApplyMeasure μ B) hf hg

theorem integral_add (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := integral_fun_add hf hg

variable (μ B) in
@[integral_simps]
theorem integral_fun_neg (f : X → E) :
    ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ] :=
  setToFun_neg (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

variable (μ B) in
@[integral_simps]
theorem integral_neg (f : X → E) :
    ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ] := integral_fun_neg μ B f

theorem integral_fun_sub (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_sub (dominatedFinMeasAdditive_cbmApplyMeasure μ B) hf hg

theorem integral_sub (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    ∫ᵛ x, (f - g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := integral_fun_sub hf hg

variable (μ B) in
@[integral_simps]
theorem integral_fun_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  setToFun_smul (dominatedFinMeasAdditive_cbmApplyMeasure μ B) (by simp) c f

variable (μ B) in
@[integral_simps]
theorem integral_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := integral_fun_smul μ B c f

theorem integral_finsetSum {ι} (s : Finset ι) {f : ι → X → E} (hf : ∀ i ∈ s, μ.Integrable (f i) B) :
    ∫ᵛ a, ∑ i ∈ s, f i a ∂[B; μ] = ∑ i ∈ s, ∫ᵛ a, f i a ∂[B; μ] :=
  setToFun_finsetSum _ s hf

theorem integral_undef (hf : ¬ μ.Integrable f B) :
    ∫ᵛ x, f x ∂[B; μ] = 0 :=
  setToFun_undef _ hf

theorem Integrable.of_integral_ne_zero (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : μ.Integrable f B :=
  Not.imp_symm integral_undef h

theorem integral_non_aestronglyMeasurable {f : X → E}
    (h : ¬AEStronglyMeasurable f (μ.transpose B).variation) :
    ∫ᵛ a, f a ∂[B; μ] = 0 :=
  integral_undef <| not_and_of_not_left _ h

@[simp]
theorem integral_zero : ∫ᵛ _, (0 : E) ∂[B; μ] = (0 : G) :=
  setToFun_zero _

lemma integral_indicator₂ {β : Type*} (f : β → X → E) (s : Set β) (b : β) :
    ∫ᵛ y, s.indicator (f · y) b ∂[B; μ] = s.indicator (fun x ↦ ∫ᵛ y, f x y ∂[B; μ]) b := by
  by_cases hb : b ∈ s <;> simp [hb]

theorem integral_congr_ae (h : f =ᵐ[(μ.transpose B).variation] g) :
    ∫ᵛ a, f a ∂[B; μ] = ∫ᵛ a, g a ∂[B; μ] :=
  setToFun_congr_ae _ h

theorem norm_integral_le_lintegral_norm (f : X → E) :
    ‖∫ᵛ a, f a ∂[B; μ]‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂(μ.transpose B).variation) :=
  (norm_setToFun_le_toReal _ (by simp)).trans (by simp)

theorem enorm_integral_le_lintegral_enorm (f : X → E) :
    ‖∫ᵛ a, f a ∂[B; μ]‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂(μ.transpose B).variation :=
  (enorm_setToFun_le _ (by simp)).trans (by simp)

theorem dist_integral_le_lintegral_edist (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    dist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) ≤
      (∫⁻ a, edist (f a) (g a) ∂(μ.transpose B).variation).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

theorem edist_integral_le_lintegral_edist (hf : μ.Integrable f B) (hg : μ.Integrable g B) :
    edist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) ≤
      ∫⁻ a, edist (f a) (g a) ∂(μ.transpose B).variation := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_of_le_toReal (dist_integral_le_lintegral_edist hf hg)

theorem integral_eq_zero_of_ae {f : X → E} (hf : f =ᵐ[(μ.transpose B).variation] 0) :
    ∫ᵛ a, f a ∂[B; μ] = 0 := by
  simp [integral_congr_ae hf, integral_zero]

theorem frequently_ae_ne_zero_of_integral_ne_zero {f : X → E}
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ᶠ a in ae (μ.transpose B).variation, f a ≠ 0 :=
  fun h' ↦ h (integral_eq_zero_of_ae (h'.mono fun _ ↦ not_not.mp))

theorem exists_ne_zero_of_integral_ne_zero {f : X → E}
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ a, f a ≠ 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists

/-- If `f` is integrable, then `∫ᵛ x in s, f x ∂[B; μ]` is absolutely continuous in `s`:
it tends to zero as `(μ.transpose B).variation s` tends to zero. -/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι} {f : X → E}
    (hf : μ.Integrable f B) {l : Filter ι} {s : ι → Set X}
    (hs : Tendsto ((μ.transpose B).variation ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x in s i, f x ∂[B; μ]) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (fun i => zero_le)
  intro i
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono' _ le_rfl
  rw [← restrict_transpose]
  apply variation_restrict_le

/-- If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`. -/
theorem tendsto_integral_of_L1 {ι} (f : X → E) (hfi : μ.Integrable f B) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂(μ.transpose B).variation) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) :=
  tendsto_setToFun_of_L1 _ f hfi hFi hF

/-- If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`. -/
lemma tendsto_integral_of_L1' {ι} (f : X → E) (hfi : μ.Integrable f B) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 (μ.transpose B).variation) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1 {ι} (f : X → E) (hfi : μ.Integrable f B) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂(μ.transpose B).variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le)
      (fun i ↦ ?_)
    apply eLpNorm_mono_measure
    grw [← restrict_transpose, variation_restrict_le]
    apply Measure.restrict_le_self

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1' {ι} (f : X → E) (hfi : μ.Integrable f B) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 (μ.transpose B).variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF


variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]

theorem continuousWithinAt_of_dominated {F : Y → Y → E} {x₀ : Y} {bound : Y → ℝ} {s : Set Y}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂(μ.transpose B).variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound (μ.transpose B).variation)
    (h_cont : ∀ᵐ a ∂(μ.transpose B).variation, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) s x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

#exit

theorem continuousAt_of_dominated {F : X → X → G} {x₀ : X} {bound : X → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂[B; μ], ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂[B; μ], ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) x₀ := by
  simp only [integral_eq_setToFun]
  exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

theorem continuousOn_of_dominated {F : X → X → G} {bound : X → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂[B; μ], ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂[B; μ], ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ᵛ a, F x a ∂[B; μ]) s := by
  simp only [integral_eq_setToFun]
  exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

theorem continuous_of_dominated {F : X → X → G} {bound : X → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂[B; μ], ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂[B; μ], Continuous fun x => F x a) :
    Continuous fun x => ∫ᵛ a, F x a ∂[B; μ] := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
    hF_meas h_bound bound_integrable h_cont

/-- The Bochner integral of a real-valued function `f : X → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`. -/
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : X → ℝ} (hf : Integrable f μ) :
    ∫ᵛ a, f a ∂[B; μ] =
      ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂[B; μ]) - ENNReal.toReal (∫⁻ a, .ofReal (-f a) ∂[B; μ]) := by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂[B; μ]) = ‖Lp.posPart f₁‖ := by
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
  have eq₂ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (-f a) ∂[B; μ]) = ‖Lp.negPart f₁‖ := by
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

theorem integral_eq_lintegral_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfm : AEStronglyMeasurable f μ) :
    ∫ᵛ a, f a ∂[B; μ] = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂[B; μ]) := by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂[B; μ] = 0 := by
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
    have : ∫⁻ a : X, ENNReal.ofReal (f a) ∂[B; μ] = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂[B; μ] := by
      refine lintegral_congr_ae (hf.mono fun a h => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg h]
    rw [this, hfi, toReal_top]

theorem integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : X → P}
    (hf : AEStronglyMeasurable f μ) : ∫ᵛ x, ‖f x‖ ∂[B; μ] = (∫⁻ x, ‖f x‖ₑ ∂[B; μ]).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm_eq_enorm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

theorem ofReal_integral_norm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : X → P}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ᵛ x, ‖f x‖ ∂[B; μ]) = ∫⁻ x, ‖f x‖ₑ ∂[B; μ] := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal]
  exact lt_top_iff_ne_top.mp (hasFiniteIntegral_iff_enorm.mpr hf.2)

theorem SimpleFunc.integral_eq_integral [CompleteSpace E] (f : X →ₛ E) (hfi : Integrable f μ) :
    f.integral μ = ∫ᵛ x, f x ∂[B; μ] := by
  rw [MeasureTheory.integral_eq f hfi, ← L1.SimpleFunc.toLp_one_eq_toL1,
    L1.SimpleFunc.integral_L1_eq_integral, L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

theorem SimpleFunc.integral_eq_sum [CompleteSpace E] (f : X →ₛ E) (hfi : Integrable f μ) :
    ∫ᵛ x, f x ∂[B; μ] = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x := by
  rw [← f.integral_eq_integral hfi, SimpleFunc.integral, ← SimpleFunc.integral_eq]; rfl

theorem tendsto_integral_approxOn_of_measurable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : X → E}
    {s : Set E} [SeparableSpace s] (hfi : Integrable f μ) (hfm : Measurable f)
    (hs : ∀ᵐ x ∂[B; μ], f x ∈ closure s) {y₀ : E} (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => (SimpleFunc.approxOn f hfm s y₀ h₀ n).integral μ)
      atTop (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) := by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

theorem tendsto_integral_approxOn_of_measurable_of_range_subset
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : X → E} (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral μ) atTop
      (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) := by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact Eventually.of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

-- We redeclare `E` here to temporarily avoid
-- the `[CompleteSpace E]` and `[NormedSpace ℝ E]` instances.
theorem tendsto_integral_norm_approxOn_sub
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {f : X → E}
    (fmeas : Measurable f) (hf : Integrable f μ) [SeparableSpace (range f ∪ {0} : Set E)] :
    Tendsto (fun n ↦ ∫ᵛ x, ‖SimpleFunc.approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ ∂[B; μ])
      atTop (𝓝 0) := by
  convert (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_enorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_enorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩).aestronglyMeasurable
    exact .mono (.of_subtype (range f ∪ {0})) subset_union_left

theorem integral_eq_integral_pos_part_sub_integral_neg_part {f : X → ℝ} (hf : Integrable f μ) :
    ∫ᵛ a, f a ∂[B; μ] = ∫ᵛ a, (Real.toNNReal (f a) : ℝ) ∂[B; μ] - ∫ᵛ a, (Real.toNNReal (-f a) : ℝ) ∂[B; μ] := by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

end Basic

section Order

variable [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

@[gcongr]
lemma integral_mono_measure [OrderClosedTopology E] {f : X → E} {ν : Measure X} (hle : μ ≤ ν)
    (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν) : ∫ᵛ (a : X), f a ∂[B; μ] ≤ ∫ᵛ (a : X), f a ∂ν := by
  by_cases hE : CompleteSpace E
  swap; · simp [integral, hE]
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

variable [ClosedIciTopology E]

/-- The integral of a function which is nonnegative almost everywhere is nonnegative. -/
lemma integral_nonneg_of_ae {f : X → E} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hE : CompleteSpace E
  · exact integral_eq_setToFun f ▸ setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
      (fun s _ _ => weightedSMul_nonneg s) hf
  · simp [integral, hE]

lemma integral_nonneg {f : X → E} (hf : 0 ≤ f) :
    0 ≤ ∫ᵛ x, f x ∂[B; μ] :=
  integral_nonneg_of_ae (ae_of_all _ hf)

lemma integral_nonpos_of_ae {f : X → E} (hf : f ≤ᵐ[μ] 0) :
    ∫ᵛ x, f x ∂[B; μ] ≤ 0 := by
  rw [← neg_nonneg, ← integral_neg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with x hx
  simpa

lemma integral_nonpos {f : X → E} (hf : f ≤ 0) :
    ∫ᵛ x, f x ∂[B; μ] ≤ 0 :=
  integral_nonpos_of_ae (ae_of_all _ hf)

lemma integral_mono_ae {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ᵛ x, f x ∂[B; μ] ≤ ∫ᵛ x, g x ∂[B; μ] := by
  rw [← sub_nonneg, ← integral_sub hg hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h] with x hx
  simpa

@[gcongr, mono]
lemma integral_mono {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : f ≤ g) : ∫ᵛ x, f x ∂[B; μ] ≤ ∫ᵛ x, g x ∂[B; μ] :=
  integral_mono_ae hf hg (ae_of_all _ h)

lemma integral_mono_of_nonneg {f g : X → E} (hf : 0 ≤ᵐ[μ] f) (hgi : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ᵛ a, f a ∂[B; μ] ≤ ∫ᵛ a, g a ∂[B; μ] := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · exact integral_undef hfi ▸ integral_nonneg_of_ae (hf.trans h)

lemma integral_monotoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : X → β → E}
    {s : Set β} (hf_mono : ∀ᵐ x ∂[B; μ], MonotoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : MonotoneOn (fun b => ∫ᵛ x, f x b ∂[B; μ]) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int a ha) (hf_int b hb) ?_
  filter_upwards [hf_mono] with x hx
  exact hx ha hb hab

lemma integral_antitoneOn_of_integrand_ae {β : Type*} [Preorder β] {f : X → β → E}
    {s : Set β} (hf_anti : ∀ᵐ x ∂[B; μ], AntitoneOn (f x) s)
    (hf_int : ∀ a ∈ s, Integrable (f · a) μ) : AntitoneOn (fun b => ∫ᵛ x, f x b ∂[B; μ]) s := by
  intro a ha b hb hab
  refine integral_mono_ae (hf_int b hb) (hf_int a ha) ?_
  filter_upwards [hf_anti] with x hx
  exact hx ha hb hab

lemma integral_convexOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : X → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conv : ∀ᵐ x ∂[B; μ], ConvexOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConvexOn ℝ s (fun b => ∫ᵛ x, f x b ∂[B; μ]) := by
  refine ⟨hs, ?_⟩
  intro a ha b hb p q hp hq hpq
  calc ∫ᵛ x, f x (p • a + q • b) ∂[B; μ] ≤ ∫ᵛ x, p • f x a + q • f x b ∂[B; μ] := by
                  refine integral_mono_ae ?lhs ?rhs ?ae_le
                  case lhs =>
                    refine hf_int _ ?_
                    rw [convex_iff_add_mem] at hs
                    exact hs ha hb hp hq hpq
                  case rhs => fun_prop (disch := aesop)
                  case ae_le =>
                    filter_upwards [hf_conv] with x hx
                    exact hx.2 ha hb hp hq hpq
            _ = ∫ᵛ x, p • f x a ∂[B; μ] + ∫ᵛ x, q • f x b ∂[B; μ] := by
                  apply integral_add
                  all_goals fun_prop (disch := aesop)
            _ = p • ∫ᵛ x, f x a ∂[B; μ] + q • ∫ᵛ x, f x b ∂[B; μ] := by simp [integral_smul]

lemma integral_concaveOn_of_integrand_ae {β : Type*} [AddCommMonoid β]
    [Module ℝ β] {f : X → β → E} {s : Set β} (hs : Convex ℝ s)
    (hf_conc : ∀ᵐ x ∂[B; μ], ConcaveOn ℝ s (f x)) (hf_int : ∀ a ∈ s, Integrable (f · a) μ) :
    ConcaveOn ℝ s (fun b => ∫ᵛ x, f x b ∂[B; μ]) := by
  simp_rw [← neg_convexOn_iff] at hf_conc ⊢
  simpa only [Pi.neg_apply, integral_neg] using
    integral_convexOn_of_integrand_ae hs hf_conc (hf_int · · |>.neg)

end Order

variable [hE : CompleteSpace E]

theorem lintegral_coe_eq_integral (f : X → ℝ≥0) (hfi : Integrable (fun x => (f x : ℝ)) μ) :
    ∫⁻ a, f a ∂[B; μ] = ENNReal.ofReal (∫ᵛ a, f a ∂[B; μ]) := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  simpa [← lt_top_iff_ne_top, hasFiniteIntegral_iff_enorm, NNReal.enorm_eq] using
    hfi.hasFiniteIntegral

theorem ofReal_integral_eq_lintegral_ofReal {f : X → ℝ} (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ᵛ x, f x ∂[B; μ]) = ∫⁻ x, ENNReal.ofReal (f x) ∂[B; μ] := by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx ↦ (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_enorm hfi,
    ← ofReal_norm_eq_enorm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

theorem integral_toReal {f : X → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : ∀ᵐ x ∂[B; μ], f x < ∞) :
    ∫ᵛ a, (f a).toReal ∂[B; μ] = (∫⁻ a, f a ∂[B; μ]).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable,
    lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact Eventually.of_forall fun x => ENNReal.toReal_nonneg

theorem lintegral_coe_le_coe_iff_integral_le {f : X → ℝ≥0} (hfi : Integrable (fun x => (f x : ℝ)) μ)
    {b : ℝ≥0} : ∫⁻ a, f a ∂[B; μ] ≤ b ↔ ∫ᵛ a, (f a : ℝ) ∂[B; μ] ≤ b := by
  rw [lintegral_coe_eq_integral f hfi, ENNReal.ofReal, ENNReal.coe_le_coe,
    Real.toNNReal_le_iff_le_coe]

theorem integral_coe_le_of_lintegral_coe_le {f : X → ℝ≥0} {b : ℝ≥0} (h : ∫⁻ a, f a ∂[B; μ] ≤ b) :
    ∫ᵛ a, (f a : ℝ) ∂[B; μ] ≤ b := by
  by_cases hf : Integrable (fun a => (f a : ℝ)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

theorem integral_eq_zero_iff_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    ∫ᵛ x, f x ∂[B; μ] = 0 ↔ f =ᵐ[μ] 0 := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false]
  rw [lintegral_eq_zero_iff']
  · rw [← hf.ge_iff_eq', Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.zero_apply, ofReal_eq_zero]
  · exact (ENNReal.measurable_ofReal.comp_aemeasurable hfi.1.aemeasurable)

theorem integral_eq_zero_iff_of_nonneg {f : X → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    ∫ᵛ x, f x ∂[B; μ] = 0 ↔ f =ᵐ[μ] 0 :=
  integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf) hfi

lemma integral_eq_iff_of_ae_le {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    ∫ᵛ a, f a ∂[B; μ] = ∫ᵛ a, g a ∂[B; μ] ↔ f =ᵐ[μ] g := by
  refine ⟨fun h_le ↦ EventuallyEq.symm ?_, fun h ↦ integral_congr_ae h⟩
  rw [← sub_ae_eq_zero,
    ← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

theorem integral_pos_iff_support_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (0 < ∫ᵛ x, f x ∂[B; μ]) ↔ 0 < μ (Function.support f) := by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm ℝ 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

theorem integral_pos_iff_support_of_nonneg {f : X → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    (0 < ∫ᵛ x, f x ∂[B; μ]) ↔ 0 < μ (Function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hf) hfi

lemma integral_exp_pos {μ : Measure X} {f : X → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    0 < ∫ᵛ x, Real.exp (f x) ∂[B; μ] := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (Real.exp_pos _).le) hf]
  suffices (Function.support fun x ↦ Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure X} {f : ℕ → X → ℝ} {F : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂[B; μ], Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂[B; μ], Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ᵛ x, f n x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, F x ∂[B; μ])) := by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂[B; μ], ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha zero_le]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ᵛ x, f' n x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, (F - f 0) x ∂[B; μ])) by
    simp_rw [f', integral_sub (hf _) (hf _), integral_sub' hF (hf 0),
      tendsto_sub_const_iff] at this
    exact this
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono zero_le)
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousAt_toReal (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂[B; μ]) ?_
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
lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure X} {f : ℕ → X → ℝ} {F : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂[B; μ], Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂[B; μ], Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ᵛ x, f n x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, F x ∂[B; μ])) := by
  suffices Tendsto (fun n ↦ ∫ᵛ x, -f n x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, -F x ∂[B; μ])) by
    suffices Tendsto (fun n ↦ ∫ᵛ x, - -f n x ∂[B; μ]) atTop (𝓝 (∫ᵛ x, - -F x ∂[B; μ])) by
      simpa [neg_neg] using this
    convert this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx n m hnm using neg_le_neg_iff.mpr <| hx hnm
  · filter_upwards [h_tendsto] with x hx using hx.neg

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
lemma tendsto_of_integral_tendsto_of_monotone {μ : Measure X} {f : ℕ → X → ℝ} {F : X → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ᵛ a, f i a ∂[B; μ]) atTop (𝓝 (∫ᵛ a, F a ∂[B; μ])))
    (hf_mono : ∀ᵐ a ∂[B; μ], Monotone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂[B; μ], ∀ i, f i a ≤ F a) :
    ∀ᵐ a ∂[B; μ], Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  -- reduce to the `ℝ≥0∞` case
  let f' : ℕ → X → ℝ≥0∞ := fun n a ↦ ENNReal.ofReal (f n a - f 0 a)
  let F' : X → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : ∀ i, ∫⁻ a, f' i a ∂[B; μ] = ENNReal.ofReal (∫ᵛ a, f i a ∂[B; μ] - ∫ᵛ a, f 0 a ∂[B; μ]) := by
    intro i
    unfold f'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub (hf_int i) (hf_int 0)]
    · exact (hf_int i).sub (hf_int 0)
    · filter_upwards [hf_mono] with a h_mono
      simp [h_mono zero_le]
  have hF'_int_eq : ∫⁻ a, F' a ∂[B; μ] = ENNReal.ofReal (∫ᵛ a, F a ∂[B; μ] - ∫ᵛ a, f 0 a ∂[B; μ]) := by
    unfold F'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub hF_int (hf_int 0)]
    · exact hF_int.sub (hf_int 0)
    · filter_upwards [hf_bound] with a h_bound
      simp [h_bound 0]
  have h_tendsto : Tendsto (fun i ↦ ∫⁻ a, f' i a ∂[B; μ]) atTop (𝓝 (∫⁻ a, F' a ∂[B; μ])) := by
    simp_rw [hf'_int_eq, hF'_int_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rwa [tendsto_sub_const_iff]
  have h_mono : ∀ᵐ a ∂[B; μ], Monotone (fun i ↦ f' i a) := by
    filter_upwards [hf_mono] with a ha_mono i j hij
    refine ENNReal.ofReal_le_ofReal ?_
    simp [ha_mono hij]
  have h_bound : ∀ᵐ a ∂[B; μ], ∀ i, f' i a ≤ F' a := by
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
    · simp [ha_mono zero_le]
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
lemma tendsto_of_integral_tendsto_of_antitone {μ : Measure X} {f : ℕ → X → ℝ} {F : X → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ᵛ a, f i a ∂[B; μ]) atTop (𝓝 (∫ᵛ a, F a ∂[B; μ])))
    (hf_mono : ∀ᵐ a ∂[B; μ], Antitone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂[B; μ], ∀ i, F a ≤ f i a) :
    ∀ᵐ a ∂[B; μ], Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  let f' : ℕ → X → ℝ := fun i a ↦ - f i a
  let F' : X → ℝ := fun a ↦ - F a
  suffices ∀ᵐ a ∂[B; μ], Tendsto (fun i ↦ f' i a) atTop (𝓝 (F' a)) by
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

theorem L1.norm_eq_integral_norm (f : X →₁[μ] H) : ‖f‖ = ∫ᵛ a, ‖f a‖ ∂[B; μ] := by
  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
    Lp.norm_def, if_false, ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  simp

theorem L1.dist_eq_integral_dist (f g : X →₁[μ] H) : dist f g = ∫ᵛ a, dist (f a) (g a) ∂[B; μ] := by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
  exact integral_congr_ae <| (Lp.coeFn_sub _ _).fun_comp norm

theorem L1.norm_of_fun_eq_integral_norm {f : X → H} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ᵛ a, ‖f a‖ ∂[B; μ] := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae <| hf.coeFn_toL1.fun_comp _

theorem MemLp.eLpNorm_eq_integral_rpow_norm {f : X → H} {p : ℝ≥0∞} (hp1 : p ≠ 0) (hp2 : p ≠ ∞)
    (hf : MemLp f p μ) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ᵛ a, ‖f a‖ ^ p.toReal ∂[B; μ]) ^ p.toReal⁻¹) := by
  have A : ∫⁻ a : X, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂[B; μ] = ∫⁻ a : X, ‖f a‖ₑ ^ p.toReal ∂[B; μ] := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm_eq_enorm]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate_left
  · exact ae_of_all _ fun x => by positivity
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [A, ← ofReal_rpow_of_nonneg toReal_nonneg (inv_nonneg.2 toReal_nonneg), ofReal_toReal]
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp1 hp2 hf.2).ne

end NormedAddCommGroup

theorem norm_integral_le_integral_norm (f : X → E) : ‖∫ᵛ a, f a ∂[B; μ]‖ ≤ ∫ᵛ a, ‖f a‖ ∂[B; μ] := by
  have le_ae : ∀ᵐ a ∂[B; μ], 0 ≤ ‖f a‖ := Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ᵛ a, f a ∂[B; μ]‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂[B; μ]) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ᵛ a, ‖f a‖ ∂[B; μ] := (integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm).symm
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    exact integral_nonneg_of_ae le_ae

lemma abs_integral_le_integral_abs {f : X → ℝ} : |∫ᵛ a, f a ∂[B; μ]| ≤ ∫ᵛ a, |f a| ∂[B; μ] :=
  norm_integral_le_integral_norm f

theorem norm_integral_le_of_norm_le {f : X → E} {g : X → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ x ∂[B; μ], ‖f x‖ ≤ g x) : ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ ∫ᵛ x, g x ∂[B; μ] :=
  calc
    ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ ∫ᵛ x, ‖f x‖ ∂[B; μ] := norm_integral_le_integral_norm f
    _ ≤ ∫ᵛ x, g x ∂[B; μ] := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hg h

@[simp]
theorem integral_const (c : E) : ∫ᵛ _ : X, c ∂[B; μ] = μ.real univ • c := by
  by_cases hμ : IsFiniteMeasure μ
  · simp only [integral_eq_setToFun]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  by_cases hc : c = 0
  · simp [hc, integral_zero]
  · simp [measureReal_def, (integrable_const_iff_isFiniteMeasure hc).not.2 hμ,
      integral_undef, MeasureTheory.not_isFiniteMeasure_iff.mp hμ]

lemma integral_eq_const [IsProbabilityMeasure μ] {f : X → E} {c : E} (hf : ∀ᵐ x ∂[B; μ], f x = c) :
    ∫ᵛ x, f x ∂[B; μ] = c := by simp [integral_congr_ae hf]

theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : X → E} {C : ℝ}
    (h : ∀ᵐ x ∂[B; μ], ‖f x‖ ≤ C) : ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ C * μ.real univ :=
  calc
    ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ ∫ᵛ _, C ∂[B; μ] := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

variable {ν : Measure X}

theorem integral_add_measure {f : X → E} (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ᵛ x, f x ∂(μ + ν) = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂ν := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hfi := hμ.add_measure hν
  simp_rw [integral_eq_setToFun]
  have hμ_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul μ : Set X → G →L[ℝ] G) 1 :=
    DominatedFinMeasAdditive.add_measure_right μ ν (dominatedFinMeasAdditive_weightedSMul μ)
      zero_le_one
  have hν_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul ν : Set X → G →L[ℝ] G) 1 :=
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
theorem integral_zero_measure {m : MeasurableSpace X} (f : X → E) :
    (∫ᵛ x, f x ∂(0 : Measure X)) = 0 := by
  simp only [integral_eq_setToFun]
  exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl

@[simp]
theorem setIntegral_measure_zero (f : X → E) {μ : Measure X} {s : Set X} (hs : μ s = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := Measure.restrict_eq_zero.mpr hs ▸ integral_zero_measure f

lemma integral_of_isEmpty [IsEmpty X] {f : X → E} : ∫ᵛ x, f x ∂[B; μ] = 0 :=
  μ.eq_zero_of_isEmpty ▸ integral_zero_measure _

theorem integral_finsetSum_measure {ι} {m : MeasurableSpace X} {f : X → E} {μ : ι → Measure X}
    {s : Finset ι} (hf : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ᵛ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ᵛ a, f a ∂[B; μ] i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finsetSum_measure.2 hf.2)

@[deprecated (since := "2026-04-08")]
alias integral_finset_sum_measure := integral_finsetSum_measure

theorem nndist_integral_add_measure_le_lintegral
    {f : X → E} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ᵛ x, f x ∂[B; μ]) (∫ᵛ x, f x ∂(μ + ν)) : ℝ≥0∞) ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := by
  rw [integral_add_measure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

@[simp]
theorem integral_smul_measure (f : X → E) (c : ℝ≥0∞) :
    ∫ᵛ x, f x ∂c • μ = c.toReal • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.toReal_top, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set X → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

@[simp]
theorem integral_smul_nnreal_measure (f : X → E) (c : ℝ≥0) :
    ∫ᵛ x, f x ∂(c • μ) = c • ∫ᵛ x, f x ∂[B; μ] :=
  integral_smul_measure f (c : ℝ≥0∞)

theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : X → β} (hφ : Measurable φ)
    {f : β → G} (hfm : StronglyMeasurable f) : ∫ᵛ y, f y ∂Measure.map φ μ = ∫ᵛ x, f (φ x) ∂[B; μ] := by
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

theorem integral_map {β} [MeasurableSpace β] {φ : X → β} (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ᵛ y, f y ∂Measure.map φ μ = ∫ᵛ x, f (φ x) ∂[B; μ] :=
  let g := hfm.mk f
  calc
    ∫ᵛ y, f y ∂Measure.map φ μ = ∫ᵛ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ᵛ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ᵛ x, g (hφ.mk φ x) ∂[B; μ] :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ᵛ x, g (φ x) ∂[B; μ] := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
    _ = ∫ᵛ x, f (φ x) ∂[B; μ] := integral_congr_ae <| ae_eq_comp hφ hfm.ae_eq_mk.symm

theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : X → β}
    (hf : MeasurableEmbedding f) (g : β → G) : ∫ᵛ y, g y ∂Measure.map f μ = ∫ᵛ x, g (f x) ∂[B; μ] := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

theorem _root_.Topology.IsClosedEmbedding.integral_map {β} [TopologicalSpace X] [BorelSpace X]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : X → β} (hφ : IsClosedEmbedding φ)
    (f : β → G) : ∫ᵛ y, f y ∂Measure.map φ μ = ∫ᵛ x, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.integral_map _

theorem integral_map_equiv {β} [MeasurableSpace β] (e : X ≃ᵐ β) (f : β → G) :
    ∫ᵛ y, f y ∂Measure.map e μ = ∫ᵛ x, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.integral_map f

omit hE in
lemma integral_domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [MeasurableConstSMul G A] {μ : Measure A} (g : Gᵈᵐᵃ) (f : A → E) :
    ∫ᵛ x, f x ∂g • μ = ∫ᵛ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂[B; μ] :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

theorem MeasurePreserving.integral_comp {β} {_ : MeasurableSpace β} {f : X → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → G) :
    ∫ᵛ x, g (f x) ∂[B; μ] = ∫ᵛ y, g y ∂ν :=
  h₁.map_eq ▸ (h₂.integral_map g).symm

theorem MeasurePreserving.integral_comp' {β} [MeasurableSpace β] {ν} {f : X ≃ᵐ β}
    (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ᵛ x, g (f x) ∂[B; μ] = ∫ᵛ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

theorem integral_subtype_comap {X} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (f : X → E) :
    ∫ᵛ x : s, f (x : X) ∂(Measure.comap Subtype.val μ) = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
theorem integral_subtype {X} [MeasureSpace X] {s : Set X} (hs : MeasurableSet s) (f : X → E) :
    ∫ᵛ x : s, f x = ∫ᵛ x in s, f x := integral_subtype_comap hs f

@[simp]
theorem integral_dirac' [MeasurableSpace X] (f : X → E) (a : X) (hfm : StronglyMeasurable f) :
    ∫ᵛ x, f x ∂Measure.dirac a = f a := by
  borelize E
  calc
    ∫ᵛ x, f x ∂Measure.dirac a = ∫ᵛ _, f a ∂Measure.dirac a :=
      integral_congr_ae <| ae_eq_dirac' hfm.measurable
    _ = f a := by simp

@[simp]
theorem integral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] (f : X → E) (a : X) :
    ∫ᵛ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫ᵛ x, f x ∂Measure.dirac a = ∫ᵛ _, f a ∂Measure.dirac a := integral_congr_ae <| ae_eq_dirac f
    _ = f a := by simp

theorem setIntegral_dirac' {mX : MeasurableSpace X} {f : X → E} (hf : StronglyMeasurable f) (a : X)
    {s : Set X} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

theorem setIntegral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] (f : X → E) (a : X)
    (s : Set X) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_integral_of_nonneg {f : X → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real { x | ε ≤ f x } ≤ ∫ᵛ x, f x ∂[B; μ] := by
  rcases eq_top_or_lt_top (μ {x | ε ≤ f x}) with hμ | hμ
  · simpa [measureReal_def, hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * μ.real { x | ε ≤ f x } = ∫ᵛ _ in {x | ε ≤ f x}, ε ∂[B; μ] := by simp [mul_comm]
      _ ≤ ∫ᵛ x in {x | ε ≤ f x}, f x ∂[B; μ] :=
        integral_mono_ae (integrable_const _) (hf_int.mono_measure μ.restrict_le_self) <|
          ae_restrict_mem₀ <| hf_int.aemeasurable.nullMeasurable measurableSet_Ici
      _ ≤ _ := integral_mono_measure μ.restrict_le_self hf_nonneg hf_int

/-- Hölder's inequality for the integral of a product of norms. The integral of the product of two
norms of functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are
conjugate exponents. -/
theorem integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : X → E} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ᵛ a, ‖f a‖ * ‖g a‖ ∂[B; μ] ≤ (∫ᵛ a, ‖f a‖ ^ p ∂[B; μ]) ^ (1 / p) * (∫ᵛ a, ‖g a‖ ^ q ∂[B; μ]) ^ (1 / q) := by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact (hg.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact (hf.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ by positivity
  · exact hf.1.norm.mul hg.1.norm
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  -- replace norms by nnnorm
  have h_left : ∫⁻ a, ENNReal.ofReal (‖f a‖ * ‖g a‖) ∂[B; μ] =
      ∫⁻ a, ((‖f ·‖ₑ) * (‖g ·‖ₑ)) a ∂[B; μ] := by
    simp_rw [Pi.mul_apply, ← ofReal_norm_eq_enorm, ENNReal.ofReal_mul (norm_nonneg _)]
  have h_right_f : ∫⁻ a, .ofReal (‖f a‖ ^ p) ∂[B; μ] = ∫⁻ a, ‖f a‖ₑ ^ p ∂[B; μ] := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h_right_g : ∫⁻ a, .ofReal (‖g a‖ ^ q) ∂[B; μ] = ∫⁻ a, ‖g a‖ₑ ^ q ∂[B; μ] := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg]
  rw [h_left, h_right_f, h_right_g]
  -- we can now apply `ENNReal.lintegral_mul_le_Lp_mul_Lq` (up to the `toReal` application)
  refine ENNReal.toReal_mono ?_ ?_
  · refine ENNReal.mul_ne_top ?_ ?_
    · convert hf.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · rw [ENNReal.toReal_ofReal hpq.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.pos
      · finiteness
    · convert hg.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · rw [ENNReal.toReal_ofReal hpq.symm.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.symm.pos
      · finiteness
  · exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.1.nnnorm.aemeasurable.coe_nnreal_ennreal
      hg.1.nnnorm.aemeasurable.coe_nnreal_ennreal

/-- Hölder's inequality for functions `X → ℝ`. The integral of the product of two nonnegative
functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : X → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ᵛ a, f a * g a ∂[B; μ] ≤ (∫ᵛ a, f a ^ p ∂[B; μ]) ^ (1 / p) * (∫ᵛ a, g a ^ q ∂[B; μ]) ^ (1 / q) := by
  have h_left : ∫ᵛ a, f a * g a ∂[B; μ] = ∫ᵛ a, ‖f a‖ * ‖g a‖ ∂[B; μ] := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf, Real.norm_of_nonneg hxg]
  have h_right_f : ∫ᵛ a, f a ^ p ∂[B; μ] = ∫ᵛ a, ‖f a‖ ^ p ∂[B; μ] := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg] with x hxf
    rw [Real.norm_of_nonneg hxf]
  have h_right_g : ∫ᵛ a, g a ^ q ∂[B; μ] = ∫ᵛ a, ‖g a‖ ^ q ∂[B; μ] := by
    refine integral_congr_ae ?_
    filter_upwards [hg_nonneg] with x hxg
    rw [Real.norm_of_nonneg hxg]
  rw [h_left, h_right_f, h_right_g]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg

theorem integral_singleton' {μ : Measure X} {f : X → E} (hf : StronglyMeasurable f) (a : X) :
    ∫ᵛ a in {a}, f a ∂[B; μ] = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf,
    measureReal_def]

theorem integral_singleton [MeasurableSingletonClass X] {μ : Measure X} (f : X → E) (a : X) :
    ∫ᵛ a in {a}, f a ∂[B; μ] = μ.real {a} • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, measureReal_def]

theorem integral_unique [Unique X] (f : X → E) : ∫ᵛ x, f x ∂[B; μ] = μ.real univ • f default :=
  calc
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ _, f default ∂[B; μ] := by congr with x; congr; exact Unique.uniq _ x
    _ = μ.real univ • f default := by rw [integral_const]

theorem integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace X] [Measure.IsOpenPosMeasure μ]
    {f : X → ℝ} {x : X} (f_cont : Continuous f) (f_int : Integrable f μ) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ᵛ x, f x ∂[B; μ] :=
  (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

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
    ∫ᵛ x, f x ∂[B; μ] = ∑ x ∈ @SimpleFunc.range β F m f, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

theorem integral_trim_simpleFunc (hm : m ≤ m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ].trim hm := by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m,
    integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  simp only [measureReal_def]
  congr 2
  exact (trim_measurableSet_eq hm (@SimpleFunc.measurableSet_fiber β F m f x)).symm

theorem integral_trim (hm : m ≤ m0) {f : β → G} (hf : StronglyMeasurable[m] f) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ].trim hm := by
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
  have hf_seq_eq : ∀ n, ∫ᵛ x, f_seq n x ∂[B; μ] = ∫ᵛ x, f_seq n x ∂[B; μ].trim hm := fun n =>
    integral_trim_simpleFunc hm (f_seq n) (hf_seq_int n)
  have h_lim_1 : atTop.Tendsto (fun n => ∫ᵛ x, f_seq n x ∂[B; μ]) (𝓝 (∫ᵛ x, f x ∂[B; μ])) := by
    refine tendsto_integral_of_L1 f hf_int (Eventually.of_forall hf_seq_int) ?_
    exact SimpleFunc.tendsto_approxOn_range_L1_enorm (hf.mono hm).measurable hf_int
  have h_lim_2 : atTop.Tendsto (fun n => ∫ᵛ x, f_seq n x ∂[B; μ]) (𝓝 (∫ᵛ x, f x ∂[B; μ].trim hm)) := by
    simp_rw [hf_seq_eq]
    refine @tendsto_integral_of_L1 β G _ _ m (μ.trim hm) _ f (hf_int.trim hm hf) _ _
      (Eventually.of_forall hf_seq_int_m) ?_
    exact @SimpleFunc.tendsto_approxOn_range_L1_enorm β G m _ _ _ f _ _ hf.measurable
      (hf_int.trim hm hf)
  exact tendsto_nhds_unique h_lim_1 h_lim_2

theorem integral_trim_ae (hm : m ≤ m0) {f : β → G} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ].trim hm := by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

end IntegralTrim

section SnormBound

variable {m0 : MeasurableSpace X} {μ : Measure X} {f : X → ℝ}

theorem eLpNorm_one_le_of_le {r : ℝ≥0} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ᵛ x, f x ∂[B; μ])
    (hf : ∀ᵐ ω ∂[B; μ], f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * r := by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this, eLpNorm_zero, hr, ENNReal.coe_zero, mul_zero]
    rw [hr] at hf
    norm_cast at hf
    have hnegf : ∫ᵛ x, -f x ∂[B; μ] = 0 := by
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
    · simp
  haveI := hμ
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint, sub_nonneg] at hfint'
  have hposbdd : ∫ᵛ ω, max (f ω) 0 ∂[B; μ] ≤ μ.real Set.univ • (r : ℝ) := by
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
    grw [hfint']
    rwa [← two_mul, mul_assoc, mul_le_mul_iff_right₀ (two_pos : (0 : ℝ) < 2)]
  · exact hfint.neg.sup (integrable_zero _ _ μ)

theorem eLpNorm_one_le_of_le' {r : ℝ} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ᵛ x, f x ∂[B; μ])
    (hf : ∀ᵐ ω ∂[B; μ], f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal r := by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

end SnormBound

end MeasureTheory


end VectorMeasure

end MeasureTheory
