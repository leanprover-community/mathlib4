/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = ContinuousLinearMap.lsmul ℝ ℝ` or
`L = ContinuousLinearMap.mul ℝ ℝ`.

We also define `ConvolutionExists` and `ConvolutionExistsAt` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `ConvolutionExistsAt.distrib_add`), but are generally not strong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

## Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `HasCompactSupport.hasFDerivAt_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

## Main Definitions

* `MeasureTheory.convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`
  is the convolution of `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `MeasureTheory.ConvolutionExistsAt f g x L μ` states that the convolution `(f ⋆[L, μ] g) x`
  is well-defined (i.e. the integral exists).
* `MeasureTheory.ConvolutionExists f g L μ` states that the convolution `f ⋆[L, μ] g`
  is well-defined at each point.

## Main Results

* `MeasureTheory.convolution_tendsto_right`: Given a sequence of nonnegative normalized functions
  whose support tends to a small neighborhood around `0`, the convolution tends to the right
  argument. This is specialized to bump functions in `ContDiffBump.convolution_tendsto_right`.

## Notation

The following notations are localized in the scope `Convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

## To do

* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `MeasureTheory.MemLp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is an `AEStronglyMeasurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere (this likely requires changes in `to_additive`)
-/

assert_not_exists ContDiffAt HasDerivAt

@[expose] public section
open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open Bornology ContinuousLinearMap Metric Topology
open scoped Pointwise NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

namespace MeasureTheory
section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]
variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

theorem convolution_integrand_bound_right_of_le_of_subset {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G}
    {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t := by
  -- Porting note: had to add `f := _`
  refine le_indicator (f := fun t ↦ ‖L (f t) (g (x - t))‖) (fun t _ => ?_) (fun t ht => ?_) t
  · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
  · have : x - t ∉ support g := by
      refine mt (fun hxt => hu ?_) ht
      refine ⟨_, Set.neg_mem_neg.mpr (subset_closure hxt), _, hx, ?_⟩
      simp only [neg_sub, sub_add_cancel]
    simp only [notMem_support.mp this, (L _).map_zero, norm_zero, le_rfl]

theorem _root_.HasCompactSupport.convolution_integrand_bound_right_of_subset
    (hcg : HasCompactSupport g) (hg : Continuous g)
    {x t : G} {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t := by
  refine convolution_integrand_bound_right_of_le_of_subset _ (fun i => ?_) hx hu
  exact le_ciSup (hg.norm.bddAbove_range_of_hasCompactSupport hcg.norm) _

theorem _root_.HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f t) (g (x - t))‖ ≤ (-tsupport g + s).indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  hcg.convolution_integrand_bound_right_of_subset L hg hx Subset.rfl

theorem _root_.Continuous.convolution_integrand_fst [ContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| by fun_prop

theorem _root_.HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f)
    (hf : Continuous f) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f (x - t)) (g t)‖ ≤
      (-tsupport f + s).indicator (fun t => (‖L‖ * ⨆ i, ‖f i‖) * ‖g t‖) t := by
  convert hcf.convolution_integrand_bound_right L.flip hf hx using 1
  simp_rw [L.opNorm_flip, mul_right_comm]

end NoMeasurability

section Measurability
variable [MeasurableSpace G] {μ ν : Measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ

section ConvolutionExists

variable {L} in
theorem ConvolutionExistsAt.integrable [Sub G] {x : G} (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f t) (g (x - t))) μ :=
  h

section Group

variable [AddGroup G]

theorem AEStronglyMeasurable.convolution_integrand' [MeasurableAdd₂ G]
    [MeasurableNeg G] (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.prod ν)) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  L.aestronglyMeasurable_comp₂ hf.comp_snd <| hg.comp_measurable measurable_sub

section

variable [MeasurableAdd G] [MeasurableNeg G]

theorem AEStronglyMeasurable.convolution_integrand_snd'
    (hf : AEStronglyMeasurable f μ) {x : G}
    (hg : AEStronglyMeasurable g <| map (fun t => x - t) μ) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aestronglyMeasurable_comp₂ hf <| hg.comp_measurable <| measurable_id.const_sub x

theorem AEStronglyMeasurable.convolution_integrand_swap_snd' {x : G}
    (hf : AEStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aestronglyMeasurable_comp₂ (hf.comp_measurable <| measurable_id.const_sub x) hg

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact support). -/
theorem _root_.BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) (μ.restrict s)) :
    ConvolutionExistsAt f g x₀ L μ := by
  rw [ConvolutionExistsAt]
  rw [← integrableOn_iff_integrable_of_support_subset h2s]
  set s' := (fun t => -t + x₀) ⁻¹' s
  have : ∀ᵐ t : G ∂μ.restrict s,
      ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t := by
    filter_upwards
    refine le_indicator (fun t ht => ?_) fun t ht => ?_
    · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
      refine (le_ciSup_set hbg <| mem_preimage.mpr ?_)
      rwa [neg_sub, sub_add_cancel]
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [notMem_support.mp this, norm_zero]
  refine Integrable.mono' ?_ ?_ this
  · rw [integrable_indicator_iff hs]; exact ((hf.norm.const_mul _).mul_const _).integrableOn
  · exact hf.aestronglyMeasurable.convolution_integrand_snd' L hmg

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.of_norm' {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ := by
  refine (h.const_mul ‖L‖).mono'
    (hmf.convolution_integrand_snd' L hmg) (Eventually.of_forall fun x => ?_)
  rw [mul_apply', ← mul_assoc]
  apply L.le_opNorm₂

end

section Left

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ]

theorem AEStronglyMeasurable.convolution_integrand_snd (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolution_integrand_snd' L <|
    hg.mono_ac <| (quasiMeasurePreserving_sub_left_of_right_invariant μ x).absolutelyContinuous

theorem AEStronglyMeasurable.convolution_integrand_swap_snd
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono_ac
        (quasiMeasurePreserving_sub_left_of_right_invariant μ
            x).absolutelyContinuous).convolution_integrand_swap_snd'
    L hg

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.of_norm {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g μ) :
    ConvolutionExistsAt f g x₀ L μ :=
  h.of_norm' L hmf <|
    hmg.mono_ac (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous

end Left

section Right

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ] [SFinite ν]

theorem AEStronglyMeasurable.convolution_integrand (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  hf.convolution_integrand' L <|
    hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ ν).absolutelyContinuous

theorem Integrable.convolution_integrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) := by
  have h_meas : AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable
  have h2_meas : AEStronglyMeasurable (fun y : G => ∫ x : G, ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine ⟨Eventually.of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), ?_⟩
  refine Integrable.mono' ?_ h2_meas
      (Eventually.of_forall fun t => (?_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ))
  · simp only [integral_sub_right_eq_self (‖g ·‖)]
    fun_prop
  · simp_rw [← integral_const_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      ((hg.comp_sub_right t).norm.const_mul _) (Eventually.of_forall fun t => L.le_opNorm₂ _ _)

theorem Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff <|
          hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable).mp <|
      hf.convolution_integrand L hg).1

end Right

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]

theorem _root_.HasCompactSupport.convolutionExistsAt {x₀ : G}
    (h : HasCompactSupport fun t => L (f t) (g (x₀ - t))) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ := by
  let u := (Homeomorph.neg G).trans (Homeomorph.addRight x₀)
  let v := (Homeomorph.neg G).trans (Homeomorph.addLeft x₀)
  apply ((u.isCompact_preimage.mpr h).bddAbove_image hg.norm.continuousOn).convolutionExistsAt' L
    isClosed_closure.measurableSet subset_closure (hf.integrableOn_isCompact h)
  have A : AEStronglyMeasurable (g ∘ v)
      (μ.restrict (tsupport fun t : G => L (f t) (g (x₀ - t)))) := by
    apply (hg.comp v.continuous).continuousOn.aestronglyMeasurable_of_isCompact h
    exact (isClosed_tsupport _).measurableSet
  convert ((v.continuous.measurable.measurePreserving
      (μ.restrict (tsupport fun t => L (f t) (g (x₀ - t))))).aestronglyMeasurable_comp_iff
    v.measurableEmbedding).1 A
  ext x
  simp only [v, Homeomorph.neg, sub_eq_add_neg, val_toAddUnits_apply, Homeomorph.trans_apply,
    Equiv.neg_apply, Homeomorph.homeomorph_mk_coe, Homeomorph.coe_addLeft]

theorem _root_.HasCompactSupport.convolutionExists_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono ?_
  refine fun t => mt fun ht : g (x₀ - t) = 0 => ?_
  simp_rw [ht, (L _).map_zero]

theorem _root_.HasCompactSupport.convolutionExists_left_of_continuous_right
    (hcf : HasCompactSupport f) (hf : LocallyIntegrable f μ) (hg : Continuous g) :
    ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine hcf.mono ?_
  refine fun t => mt fun ht : f t = 0 => ?_
  simp_rw [ht, L.map_zero₂]

end Group

section CommGroup

variable [AddCommGroup G]

section MeasurableGroup

variable [MeasurableNeg G] [IsAddLeftInvariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `BddAbove.convolutionExistsAt'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
theorem _root_.BddAbove.convolutionExistsAt [MeasurableAdd₂ G] [SFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine BddAbove.convolutionExistsAt' L ?_ hs h2s hf ?_
  · simp_rw [← sub_eq_neg_add, hbg]
  · have : AEStronglyMeasurable g (map (fun t : G => x₀ - t) μ) :=
      hmg.mono_ac (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous
    apply this.mono_measure
    exact map_mono restrict_le_self (measurable_const.sub measurable_id')

variable {L} [MeasurableAdd G] [IsNegInvariant μ]

theorem convolutionExistsAt_flip :
    ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x,
    sub_sub_cancel, flip_apply]

theorem ConvolutionExistsAt.integrable_swap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert h.comp_sub_left x
  simp_rw [sub_sub_self]

theorem convolutionExistsAt_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolutionExistsAt_flip.symm

end MeasurableGroup

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

theorem _root_.HasCompactSupport.convolutionExists_left
    (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcf.convolutionExists_right L.flip hg hf x₀

theorem _root_.HasCompactSupport.convolutionExists_right_of_continuous_left
    (hcg : HasCompactSupport g) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcg.convolutionExists_left_of_continuous_right L.flip hg hf x₀

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ

/-- The convolution of two functions with respect to a bilinear operation `L` and a measure `μ`. -/
scoped[Convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

/-- The convolution of two functions with respect to a bilinear operation `L` and the volume. -/
scoped[Convolution]
  notation:67 f " ⋆[" L:67 "] " g:66 => convolution f g L MeasureSpace.volume

/-- The convolution of two real-valued functions with respect to volume. -/
scoped[Convolution]
  notation:67 f " ⋆ " g:66 =>
    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureSpace.volume

open scoped Convolution

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]

theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]

@[simp]
theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]

@[simp]
theorem convolution_zero : f ⋆[L, μ] 0 = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, (L _).map_zero, integral_zero]

theorem ConvolutionExistsAt.distrib_add {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f g' x L μ) :
    (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']

theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' := by
  ext x
  exact (hfg x).distrib_add (hfg' x)

theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']

theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g := by
  ext x
  exact (hfg x).add_distrib (hfg' x)

theorem convolution_mono_right {f g g' : G → ℝ} (hfg : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ)
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x) :
    (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  apply integral_mono hfg hfg'
  simp only [lsmul_apply, smul_eq_mul]
  intro t
  apply mul_le_mul_of_nonneg_left (hg _) (hf _)

theorem convolution_mono_right_of_nonneg {f g g' : G → ℝ}
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x)
    (hg' : ∀ x, 0 ≤ g' x) : (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  by_cases H : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ
  · exact convolution_mono_right H hfg' hf hg
  have : (f ⋆[lsmul ℝ ℝ, μ] g) x = 0 := integral_undef H
  rw [this]
  exact integral_nonneg fun y => mul_nonneg (hf y) (hg' (x - y))

variable (L)

theorem convolution_congr [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ]
    [IsAddRightInvariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' := by
  ext x
  apply integral_congr_ae
  exact (h1.prodMk <| h2.comp_tendsto
    (quasiMeasurePreserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp ↿fun x y ↦ L x y

theorem support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f := by
  intro x h2x
  by_contra hx
  apply h2x
  simp_rw [Set.mem_add, ← exists_and_left, not_exists, not_and_or, notMem_support] at hx
  rw [convolution_def]
  convert integral_zero G F using 2
  ext t
  rcases hx (x - t) t with (h | h | h)
  · rw [h, (L _).map_zero]
  · rw [h, L.map_zero₂]
  · exact (h <| sub_add_cancel x t).elim

section

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ]

theorem Integrable.integrable_convolution (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolution_integrand L hg).integral_prod_left

end

variable [TopologicalSpace G]
variable [IsTopologicalAddGroup G]

protected theorem _root_.HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f)
    (hcg : HasCompactSupport g) : HasCompactSupport (f ⋆[L, μ] g) :=
  (hcg.isCompact.add hcf).of_isClosed_subset isClosed_closure <|
    closure_minimal
      ((support_convolution_subset_swap L).trans <| add_subset_add subset_closure subset_closure)
      (hcg.isCompact.add hcf).isClosed

variable [BorelSpace G] [TopologicalSpace P]

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem continuousOn_convolution_right_with_param {g : P → G → E'} {s : Set P} {k : Set G}
    (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn ↿g (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- First get rid of the case where the space is not locally compact. Then `g` vanishes everywhere
  and the conclusion is trivial. -/
  by_cases! H : ∀ p ∈ s, ∀ x, g p x = 0
  · apply (continuousOn_const (c := 0)).congr
    rintro ⟨p, x⟩ ⟨hp, -⟩
    apply integral_eq_zero_of_ae (Eventually.of_forall (fun y ↦ ?_))
    simp [H p hp _]
  have : LocallyCompactSpace G := by
    rcases H with ⟨p, hp, x, hx⟩
    have A : support (g p) ⊆ k := support_subset_iff'.2 (fun y hy ↦ hgs p y hp hy)
    have B : Continuous (g p) := by
      refine hg.comp_continuous (.prodMk_right _) fun x => ?_
      simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
    rcases eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_addGroup hk A B with H | H
    · simp [H] at hx
    · exact H
  /- Since `G` is locally compact, one may thicken `k` a little bit into a larger compact set
  `(-k) + t`, outside of which all functions that appear in the convolution vanish. Then we can
  apply a continuity statement for integrals depending on a parameter, with respect to
  locally integrable functions and compactly supported continuous functions. -/
  rintro ⟨q₀, x₀⟩ ⟨hq₀, -⟩
  obtain ⟨t, t_comp, ht⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x₀ := exists_compact_mem_nhds x₀
  let k' : Set G := (-k) +ᵥ t
  have k'_comp : IsCompact k' := IsCompact.vadd_set hk.neg t_comp
  let g' : (P × G) → G → E' := fun p x ↦ g p.1 (p.2 - x)
  let s' : Set (P × G) := s ×ˢ t
  have A : ContinuousOn g'.uncurry (s' ×ˢ univ) := by
    have : g'.uncurry = g.uncurry ∘ (fun w ↦ (w.1.1, w.1.2 - w.2)) := by ext y; rfl
    rw [this]
    refine hg.comp (by fun_prop) ?_
    simp +contextual [s', MapsTo]
  have B : ContinuousOn (fun a ↦ ∫ x, L (f x) (g' a x) ∂μ) s' := by
    apply continuousOn_integral_bilinear_of_locally_integrable_of_compact_support L k'_comp A _
      (hf.integrableOn_isCompact k'_comp)
    rintro ⟨p, x⟩ y ⟨hp, hx⟩ hy
    apply hgs p _ hp
    contrapose! hy
    exact ⟨y - x, by simpa using hy, x, hx, by simp⟩
  apply ContinuousWithinAt.mono_of_mem_nhdsWithin (B (q₀, x₀) ⟨hq₀, mem_of_mem_nhds ht⟩)
  exact mem_nhdsWithin_prod_iff.2 ⟨s, self_mem_nhdsWithin, t, nhdsWithin_le_nhds ht, Subset.rfl⟩

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map. -/
theorem continuousOn_convolution_right_with_param_comp {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn ↿g (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s := by
  apply
    (continuousOn_convolution_right_with_param L hk hgs hf hg).comp (continuousOn_id.prodMk hv)
  intro x hx
  simp only [hx, prodMk_mem_set_prod_eq, mem_univ, and_self_iff, _root_.id]

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
theorem _root_.HasCompactSupport.continuous_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  rw [← continuousOn_univ]
  let g' : G → G → E' := fun _ q => g q
  have : ContinuousOn ↿g' (univ ×ˢ univ) := (hg.comp continuous_snd).continuousOn
  exact continuousOn_convolution_right_with_param_comp L
    (continuousOn_univ.2 continuous_id) hcg
    (fun p x _ hx => image_eq_zero_of_notMem_tsupport hx) hf this

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
theorem _root_.BddAbove.continuous_convolution_right_of_integrable
    [FirstCountableTopology G] [SecondCountableTopologyEither G E']
    (hbg : BddAbove (range fun x => ‖g x‖)) (hf : Integrable f μ) (hg : Continuous g) :
    Continuous (f ⋆[L, μ] g) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ‖L (f t) (g (x - t))‖ ≤ ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖ := by
    filter_upwards with x; filter_upwards with t
    apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl, le_ciSup hbg (x - t)]
  refine continuousAt_of_dominated ?_ this (by fun_prop) ?_
  · exact Eventually.of_forall fun x =>
      hf.aestronglyMeasurable.convolution_integrand_snd' L hg.aestronglyMeasurable
  · filter_upwards with t; fun_prop

end Group

section CommGroup

variable [AddCommGroup G]

theorem support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
  (support_convolution_subset_swap L).trans (add_comm _ _).subset

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

section Measurable

variable [MeasurableNeg G]
variable [MeasurableAdd G]

/-- Commutativity of convolution -/
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g := by
  ext1 x
  simp_rw [convolution_def]
  rw [← integral_sub_left_eq_self _ μ x]
  simp_rw [sub_sub_self, flip_apply]

/-- The symmetric definition of convolution. -/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ := by
  rw [← convolution_flip]; rfl

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
  convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul_swap [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
  convolution_eq_swap _

/-- The convolution of two even functions is also even. -/
theorem convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
    (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
  calc
    ∫ t : G, (L (f t)) (g (-x - t)) ∂μ = ∫ t : G, (L (f (-t))) (g (x + t)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't
      simp_rw [ht, ← h't, neg_add']
    _ = ∫ t : G, (L (f t)) (g (x - t)) ∂μ := by
      rw [← integral_neg_eq_self]
      simp only [neg_neg, ← sub_eq_add_neg]

end Measurable

variable [TopologicalSpace G]
variable [IsTopologicalAddGroup G]
variable [BorelSpace G]

theorem _root_.HasCompactSupport.continuous_convolution_left
    (hcf : HasCompactSupport f) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right L.flip hg hf

theorem _root_.BddAbove.continuous_convolution_left_of_integrable
    [FirstCountableTopology G] [SecondCountableTopologyEither G E]
    (hbf : BddAbove (range fun x => ‖f x‖)) (hf : Continuous f) (hg : Integrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf

end CommGroup

section NormedAddCommGroup

variable [SeminormedAddCommGroup G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `Metric.ball 0 R`, and `g` is constant
on `Metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has an `AntilipschitzWith`-condition. -/
theorem convolution_eq_right' {x₀ : G} {R : ℝ} (hf : support f ⊆ ball (0 : G) R)
    (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ := by
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀) := fun t ↦ by
    by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      rw [hg h2t]
    · rw [notMem_support] at ht
      simp_rw [ht, L.map_zero₂]
  simp_rw [convolution_def, h2]

variable [BorelSpace G] [SecondCountableTopology G]
variable [IsAddLeftInvariant μ] [SFinite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
theorem dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε) (hif : Integrable f μ)
    (hf : support f ⊆ ball (0 : G) R) (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ (‖L‖ * ∫ x, ‖f x‖ ∂μ) * ε := by
  have hfg : ConvolutionExistsAt f g x₀ L μ := by
    refine BddAbove.convolutionExistsAt L ?_ Metric.isOpen_ball.measurableSet (Subset.trans ?_ hf)
      hif.integrableOn hmg
    swap; · refine fun t => mt fun ht : f t = 0 => ?_; simp_rw [ht, L.map_zero₂]
    rw [bddAbove_def]
    refine ⟨‖z₀‖ + ε, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine norm_le_norm_add_const_of_dist_le (hg x ?_)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ‖L (f t)‖ * ε := by
    intro t; by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      refine ((L (f t)).dist_le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _)
    · rw [notMem_support] at ht
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self]
      rfl
  simp_rw [convolution_def]
  simp_rw [dist_eq_norm] at h2 ⊢
  rw [← integral_sub hfg.integrable]; swap; · exact (L.flip z₀).integrable_comp hif
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (Eventually.of_forall h2)).trans ?_
  rw [integral_mul_const]
  refine mul_le_mul_of_nonneg_right ?_ hε
  have h3 : ∀ t, ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖ := by
    intro t
    exact L.le_opNorm (f t)
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq ?_
  rw [integral_const_mul]

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [CompleteSpace E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
theorem dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε)
    (hf : support f ⊆ ball (0 : G) R) (hnf : ∀ x, 0 ≤ f x) (hintf : ∫ x, f x ∂μ = 1)
    (hmg : AEStronglyMeasurable g μ) (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε := by
  have hif : Integrable f μ := integrable_of_integral_eq_one hintf
  convert (dist_convolution_le' (lsmul ℝ ℝ) hε hif hf hmg hg).trans _
  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
  · simp_rw [Real.norm_of_nonneg (hnf _), hintf, mul_one]
    exact (mul_le_mul_of_nonneg_right opNorm_lsmul_le hε).trans_eq (one_mul ε)

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `ContDiffBump.convolution_tendsto_right`.
-/
theorem convolution_tendsto_right {ι} {g : ι → G → E'} {l : Filter ι} {x₀ : G} {z₀ : E'}
    {φ : ι → G → ℝ} {k : ι → G} (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1)
    -- todo: we could weaken this to "the integral tends to 1"
    (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smallSets)
    (hmg : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i : ι => (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) := by
  simp_rw [tendsto_smallSets_iff] at hφ
  rw [Metric.tendsto_nhds] at hcg ⊢
  simp_rw [Metric.eventually_prod_nhds_iff] at hcg
  intro ε hε
  have h2ε : 0 < ε / 3 := div_pos hε (by simp)
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε
  dsimp only [uncurry] at hgδ
  have h2k := hk.eventually (ball_mem_nhds x₀ <| half_pos hδ)
  have h2φ := hφ (ball (0 : G) _) <| ball_mem_nhds _ (half_pos hδ)
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans <| half_lt_self hδ)
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3 := by
    intro x' hx'
    refine (dist_triangle_right _ _ _).trans (add_le_add (hgδ hpi ?_).le hgi.le)
    exact ((dist_triangle _ _ _).trans_lt (add_lt_add hx'.out hki)).trans_eq (add_halves δ)
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1
  refine ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq ?_
  ring

end NormedAddCommGroup

end Measurability

end NontriviallyNormedField

open scoped Convolution

section RCLike
variable [RCLike 𝕜]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 E']
variable [NormedSpace 𝕜 E'']
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable {n : ℕ∞}
variable [MeasurableSpace G] {μ ν : Measure G}
variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc
variable [CompleteSpace F]
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']
variable {k : G → E''}
variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')
variable [AddGroup G]
variable [SFinite μ] [SFinite ν] [IsAddRightInvariant μ]

theorem integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν)
    (hg : Integrable g μ) : ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) := by
  refine (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans ?_
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self]
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf

variable [MeasurableAdd₂ G] [IsAddRightInvariant ν] [MeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `MeasureTheory.convolution_assoc`. -/
theorem convolution_assoc' (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
    {x₀ : G} (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.prod ν)) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ :=
  calc
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = ∫ t, L₂ (∫ s, L (f s) (g (t - s)) ∂ν) (k (x₀ - t)) ∂μ := rfl
    _ = ∫ t, ∫ s, L₂ (L (f s) (g (t - s))) (k (x₀ - t)) ∂ν ∂μ :=
      (integral_congr_ae (hfg.mono fun t ht => ((L₂.flip (k (x₀ - t))).integral_comp_comm ht).symm))
    _ = ∫ t, ∫ s, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂ν ∂μ := by simp_rw [hL]
    _ = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν := by rw [integral_integral_swap hi]
    _ = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k (x₀ - s - u))) ∂μ ∂ν := by
      congr; ext t
      rw [eq_comm, ← integral_sub_right_eq_self _ t]
      simp_rw [sub_sub_sub_cancel_right]
    _ = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k (x₀ - s - u)) ∂μ) ∂ν := by
      refine integral_congr_ae ?_
      refine ((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => ?_
      exact (L₃ (f t)).integral_comp_comm ht
    _ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := rfl

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t. one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g μ) (hk : AEStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (fun x => ‖g x‖) (fun x => ‖k x‖) x (mul ℝ ℝ) μ)
    (hfgk :
      ConvolutionExistsAt (fun x => ‖f x‖) ((fun x => ‖g x‖) ⋆[mul ℝ ℝ, μ] fun x => ‖k x‖) x₀
        (mul ℝ ℝ) ν) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := by
  refine convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono fun x hx => hx.of_norm L₄ hg hk) ?_
  -- the following is similar to `Integrable.convolution_integrand`
  have h_meas :
    AEStronglyMeasurable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x))))
      (μ.prod ν) := by
    refine L₃.aestronglyMeasurable_comp₂ hf.comp_snd ?_
    refine L₄.aestronglyMeasurable_comp₂ hg.comp_fst ?_
    refine (hk.mono_ac ?_).comp_measurable (by fun_prop)
    refine QuasiMeasurePreserving.absolutelyContinuous ?_
    refine QuasiMeasurePreserving.prod_of_left (by fun_prop) (Eventually.of_forall fun y => ?_)
    dsimp only
    exact quasiMeasurePreserving_sub_left_of_right_invariant μ _
  have h2_meas :
      AEStronglyMeasurable (fun y => ∫ x, ‖L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  have h3 : map (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν :=
    (measurePreserving_sub_prod μ ν).map_eq
  suffices Integrable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) by
    rw [← h3] at this
    convert this.comp_measurable (measurable_sub.prodMk measurable_snd)
    ext ⟨x, y⟩
    simp +unfoldPartialApp only [uncurry, Function.comp_apply,
      sub_sub_sub_cancel_right]
  simp_rw [integrable_prod_iff' h_meas]
  refine ⟨((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht =>
    (L₃ (f t)).integrable_comp <| ht.of_norm L₄ hg hk, ?_⟩
  refine (hfgk.const_mul (‖L₃‖ * ‖L₄‖)).mono' h2_meas
    (((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => ?_)
  simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ‖L₃‖ ‖L₄‖, ← integral_const_mul]
  rw [Real.norm_of_nonneg (by positivity)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
    ((ht.const_mul _).const_mul _) (Eventually.of_forall fun s => ?_)
  simp only [← mul_assoc ‖L₄‖]
  apply_rules [ContinuousLinearMap.le_of_opNorm₂_le_of_le, le_rfl]

end Assoc

theorem convolution_precompR_apply [NormedAddCommGroup G] [BorelSpace G]
    {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ)
    (hcg : HasCompactSupport g) (hg : Continuous g) (x₀ : G) (x : E'') :
    (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ := by
  have := hcg.convolutionExists_right (L.precompR E'' :) hf hg x₀
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  rfl

end RCLike

section Nonneg

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [NormedSpace ℝ F]

/-- The forward convolution of two functions `f` and `g` on `ℝ`, with respect to a continuous
bilinear map `L` and measure `ν`. It is defined to be the function mapping `x` to
`∫ t in 0..x, L (f t) (g (x - t)) ∂ν` if `0 < x`, and 0 otherwise. -/
noncomputable def posConvolution (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : Measure ℝ := by volume_tac) : ℝ → F :=
  indicator (Ioi (0 : ℝ)) fun x => ∫ t in 0..x, L (f t) (g (x - t)) ∂ν

theorem posConvolution_eq_convolution_indicator (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : Measure ℝ := by volume_tac) [NoAtoms ν] :
    posConvolution f g L ν = convolution (indicator (Ioi 0) f) (indicator (Ioi 0) g) L ν := by
  ext1 x
  rw [convolution, posConvolution, indicator]
  split_ifs with h
  · rw [intervalIntegral.integral_of_le (le_of_lt h), integral_Ioc_eq_integral_Ioo, ←
      integral_indicator (measurableSet_Ioo : MeasurableSet (Ioo 0 x))]
    congr 1 with t : 1
    have : t ≤ 0 ∨ t ∈ Ioo 0 x ∨ x ≤ t := by
      rcases le_or_gt t 0 with (h | h)
      · exact Or.inl h
      · rcases lt_or_ge t x with (h' | h')
        exacts [Or.inr (Or.inl ⟨h, h'⟩), Or.inr (Or.inr h')]
    rcases this with (ht | ht | ht)
    · rw [indicator_of_notMem (notMem_Ioo_of_le ht), indicator_of_notMem (notMem_Ioi.mpr ht),
        map_zero, ContinuousLinearMap.zero_apply]
    · rw [indicator_of_mem ht, indicator_of_mem (mem_Ioi.mpr ht.1),
          indicator_of_mem (mem_Ioi.mpr <| sub_pos.mpr ht.2)]
    · rw [indicator_of_notMem (notMem_Ioo_of_ge ht),
          indicator_of_notMem (notMem_Ioi.mpr (sub_nonpos_of_le ht)), map_zero]
  · convert (integral_zero ℝ F).symm with t
    by_cases ht : 0 < t
    · rw [indicator_of_notMem (_ : x - t ∉ Ioi 0), map_zero]
      rw [notMem_Ioi] at h ⊢
      exact sub_nonpos.mpr (h.trans ht.le)
    · rw [indicator_of_notMem (mem_Ioi.not.mpr ht), map_zero, ContinuousLinearMap.zero_apply]

theorem integrable_posConvolution {f : ℝ → E} {g : ℝ → E'} {μ ν : Measure ℝ} [SFinite μ]
    [SFinite ν] [IsAddRightInvariant μ] [NoAtoms ν] (hf : IntegrableOn f (Ioi 0) ν)
    (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    Integrable (posConvolution f g L ν) μ := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] at hf hg
  rw [posConvolution_eq_convolution_indicator f g L ν]
  exact (hf.convolution_integrand L hg).integral_prod_left

/-- The integral over `Ioi 0` of a forward convolution of two functions is equal to the product
of their integrals over this set. (Compare `integral_convolution` for the two-sided convolution.) -/
theorem integral_posConvolution [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] [IsAddRightInvariant μ] [NoAtoms ν] {f : ℝ → E} {g : ℝ → E'}
    (hf : IntegrableOn f (Ioi 0) ν) (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    ∫ x : ℝ in Ioi 0, ∫ t : ℝ in 0..x, L (f t) (g (x - t)) ∂ν ∂μ =
      L (∫ x : ℝ in Ioi 0, f x ∂ν) (∫ x : ℝ in Ioi 0, g x ∂μ) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf hg
  simp_rw [← integral_indicator measurableSet_Ioi]
  convert integral_convolution L hf hg using 4 with x
  apply posConvolution_eq_convolution_indicator

end Nonneg
end MeasureTheory
