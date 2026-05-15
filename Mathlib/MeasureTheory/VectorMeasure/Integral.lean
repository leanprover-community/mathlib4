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
open scoped ENNReal

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

lemma transpose_add (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

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

instance (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (μ.transpose B).variation :=
  isFiniteMeasure_of_le _ (variation_transpose_le μ B)

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

variable {μ ν : VectorMeasure X F} {B : E →L[ℝ] F →L[ℝ] G} {f g : X → E}

@[simp] lemma integrable_zero_vectorMeasure : (0 : VectorMeasure X F).Integrable f B := by
  simp [VectorMeasure.Integrable, transpose]

lemma integrable_add_vectorMeasure (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    (μ + ν).Integrable f B := by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [transpose_add, variation_add_le]

lemma integrable_finsetSum_vectorMeasure {ι : Type*} {μ : ι → VectorMeasure X F} {s : Finset ι}
    (h : ∀ i ∈ s, (μ i).Integrable f B) :
    (∑ i ∈ s, μ i).Integrable f B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact integrable_add_vectorMeasure h.1 (ih h.2)

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

theorem integral_eq_zero_of_ae (hf : f =ᵐ[(μ.transpose B).variation] 0) :
    ∫ᵛ a, f a ∂[B; μ] = 0 := by
  simp [integral_congr_ae hf, integral_zero]

theorem frequently_ae_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ᶠ a in ae (μ.transpose B).variation, f a ≠ 0 :=
  fun h' ↦ h (integral_eq_zero_of_ae (h'.mono fun _ ↦ not_not.mp))

theorem exists_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ a, f a ≠ 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists

/-- If `f` is integrable, then `∫ᵛ x in s, f x ∂[B; μ]` is absolutely continuous in `s`:
it tends to zero as `(μ.transpose B).variation s` tends to zero. -/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι : Type*}
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
theorem tendsto_integral_of_L1 {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f (μ.transpose B).variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂(μ.transpose B).variation) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) :=
  tendsto_setToFun_of_L1 _ f hfi hFi hF

/-- If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`. -/
lemma tendsto_integral_of_L1' {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f (μ.transpose B).variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 (μ.transpose B).variation) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1 {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f (μ.transpose B).variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂(μ.transpose B).variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [← restrict_transpose, variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le)
      (fun i ↦ ?_)
    apply eLpNorm_mono_measure
    grw [← restrict_transpose, variation_restrict_le]
    apply Measure.restrict_le_self

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
lemma tendsto_setIntegral_of_L1' {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f (μ.transpose B).variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i) B)
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 (μ.transpose B).variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]

theorem continuousWithinAt_of_dominated {F : Y → X → E} {x₀ : Y} {bound : X → ℝ} {s : Set Y}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.transpose B).variation)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂(μ.transpose B).variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound (μ.transpose B).variation)
    (h_cont : ∀ᵐ a ∂(μ.transpose B).variation, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) s x₀ :=
  continuousWithinAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

theorem continuousAt_of_dominated {F : Y → X → E} {x₀ : Y} {bound : X → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.transpose B).variation)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂(μ.transpose B).variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound (μ.transpose B).variation)
    (h_cont : ∀ᵐ a ∂(μ.transpose B).variation, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ᵛ a, F x a ∂[B; μ]) x₀ :=
  continuousAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

theorem continuousOn_of_dominated {F : Y → X → E} {bound : X → ℝ} {s : Set Y}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) (μ.transpose B).variation)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂(μ.transpose B).variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound (μ.transpose B).variation)
    (h_cont : ∀ᵐ a ∂(μ.transpose B).variation, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ᵛ a, F x a ∂[B; μ]) s :=
  continuousOn_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

theorem continuous_of_dominated {F : Y → X → E} {bound : X → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) (μ.transpose B).variation)
    (h_bound : ∀ x, ∀ᵐ a ∂(μ.transpose B).variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound (μ.transpose B).variation)
    (h_cont : ∀ᵐ a ∂(μ.transpose B).variation, Continuous fun x => F x a) :
    Continuous fun x => ∫ᵛ a, F x a ∂[B; μ] :=
  continuous_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont

@[simp]
theorem integral_const [CompleteSpace G] [IsFiniteMeasure (μ.transpose B).variation]
    (c : E) : ∫ᵛ _ : X, c ∂[B; μ] = B c (μ univ) :=
  setToFun_const _ _

theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure (μ.transpose B).variation]
    {C : ℝ} (h : ∀ᵐ x ∂(μ.transpose B).variation, ‖f x‖ ≤ C) :
    ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ C * (μ.transpose B).variation.real univ := calc
  ‖∫ᵛ x, f x ∂[B; μ]‖
  _ ≤ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂(μ.transpose B).variation).toReal :=
    norm_integral_le_lintegral_norm _
  _ ≤ (∫⁻ a, ENNReal.ofReal C ∂(μ.transpose B).variation).toReal := by
    apply ENNReal.toReal_mono
    · simp only [lintegral_const, ne_eq]
      finiteness
    · apply lintegral_mono_ae
      filter_upwards [h] with x hx using ENNReal.ofReal_mono hx
  _ = C * (μ.transpose B).variation.real univ := by
    by_cases hμ : (μ.transpose B).variation = 0
    · simp [hμ]
    have : (ae (μ.transpose B).variation).NeBot := ae_neBot.mpr hμ
    have hC : 0 ≤ C := by
      obtain ⟨x, hx⟩ := h.exists
      exact (norm_nonneg _).trans hx
    simp [ENNReal.toReal_ofReal hC, Measure.real]

theorem integral_add_vectorMeasure {ν : VectorMeasure X F}
    (hμ : μ.Integrable f B) (hν : ν.Integrable f B) :
    ∫ᵛ x, f x ∂[B; (μ + ν)] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp only [integral]
  have hfi := hμ.add_measure hν
  have hμ_dfma : DominatedFinMeasAdditive ((μ.transpose B).variation + (ν.transpose B).variation)
      (μ.transpose B) 1 :=
    DominatedFinMeasAdditive.add_measure_right (μ.transpose B).variation (ν.transpose B).variation
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) zero_le_one
  have hν_dfma : DominatedFinMeasAdditive ((μ.transpose B).variation + (ν.transpose B).variation)
      (ν.transpose B) 1 :=
    DominatedFinMeasAdditive.add_measure_left (μ.transpose B).variation (ν.transpose B).variation
    (dominatedFinMeasAdditive_cbmApplyMeasure ν B) zero_le_one
  have hμν_dfma : DominatedFinMeasAdditive ((μ.transpose B).variation + (ν.transpose B).variation)
      ((μ + ν).transpose B) 1 := by
    apply DominatedFinMeasAdditive.of_measure_le _
      (dominatedFinMeasAdditive_cbmApplyMeasure (μ + ν) B) zero_le_one
    grw [transpose_add, variation_add_le]
  rw [← setToFun_congr_measure_of_add_right hμ_dfma _ f hfi,
    ← setToFun_congr_measure_of_add_left hν_dfma _ f hfi,
    ← setToFun_congr_measure_of_integrable 1 ENNReal.one_ne_top ?_ hμν_dfma
      (dominatedFinMeasAdditive_cbmApplyMeasure (μ + ν) B) _ hfi]
  · refine setToFun_add_left' _ _ _ (fun s hs hμνs => ?_) f
    simp [transpose]
  · grw [transpose_add, variation_add_le]
    simp

theorem setIntegral_measure_zero (f : X → E) {s : Set X}
    (hs : (μ.transpose B).variation s = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : ((μ.restrict s).transpose B).variation = 0 := by
    rw [← restrict_transpose, variation_restrict _ h's]
    apply Measure.restrict_eq_zero.2 hs
  have : (μ.restrict s).transpose B = 0 := variation_eq_zero.1 this
  simp [integral, this]

lemma integral_of_isEmpty [IsEmpty X] : ∫ᵛ x, f x ∂[B; μ] = 0 :=
  μ.eq_zero_of_isEmpty ▸ integral_zero_vectorMeasure

theorem integral_finsetSum_measure {ι : Type*} {μ : ι → VectorMeasure X F}
    {s : Finset ι} (hf : ∀ i ∈ s, (μ i).Integrable f B) :
    ∫ᵛ a, f a ∂[B; ∑ i ∈ s, μ i] = ∑ i ∈ s, ∫ᵛ a, f a ∂[B; μ i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (integrable_finsetSum_vectorMeasure hf.2), ih hf.2]

theorem nndist_integral_add_vectorMeasure_le_lintegral
    (h₁ : μ.Integrable f B) (h₂ : ν.Integrable f B) :
    (nndist (∫ᵛ x, f x ∂[B; μ]) (∫ᵛ x, f x ∂[B; (μ + ν)]) : ℝ≥0∞) ≤
      ∫⁻ x, ‖f x‖ₑ ∂(ν.transpose B).variation := by
  rw [integral_add_vectorMeasure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm _

#check setToFun_congr_smul_measure

instance glou {R : Type*} [Ring R] : SMul R R := by infer_instance

#print  instSMulOfMul

@[simp]
theorem integral_smul_measure (f : X → E) (c : ℝ) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : ((c • μ).transpose B).variation = (ENNReal.ofReal |c|) • (μ.transpose B).variation := by

  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, Real.norm_eq_abs,
    mul_one]

  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set X → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

#exit


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
