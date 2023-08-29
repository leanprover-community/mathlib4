/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integration
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral

#align_import analysis.convolution from "leanprover-community/mathlib"@"8905e5ed90859939681a725b00f6063e65096d95"

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
computations (e.g. `ConvolutionExistsAt.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

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

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `ConvolutionExistsAt f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `ConvolutionExists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `HasCompactSupport.hasFDerivAt_convolution_right` and
  `HasCompactSupport.hasFDerivAt_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `HasCompactSupport.contDiff_convolution_right` and
  `HasCompactSupport.contDiff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.

Versions of these statements for functions depending on a parameter are also given.

* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `ContDiffBump.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `MeasureTheory.Memℒp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is an `AEStronglyMeasurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/
open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open ContinuousLinearMap Metric

open scoped Pointwise Topology NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]

variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

theorem convolution_integrand_bound_right_of_le_of_subset {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G}
    {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t := by
  -- porting note: had to add `f := _`
  refine' le_indicator (f := fun t ↦ ‖L (f t) (g (x - t))‖) (fun t _ => _) (fun t ht => _) t
  -- ⊢ (fun t => ‖↑(↑L (f t)) (g (x - t))‖) t ≤ ‖L‖ * ‖f t‖ * C
  · apply_rules [L.le_of_op_norm₂_le_of_le, le_rfl]
    -- 🎉 no goals
  · have : x - t ∉ support g := by
      refine mt (fun hxt => hu ?_) ht
      refine' ⟨_, _, Set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩
      simp only [neg_sub, sub_add_cancel]
    simp only [nmem_support.mp this, (L _).map_zero, norm_zero, le_rfl]
    -- 🎉 no goals
#align convolution_integrand_bound_right_of_le_of_subset convolution_integrand_bound_right_of_le_of_subset

theorem HasCompactSupport.convolution_integrand_bound_right_of_subset (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t := by
  refine convolution_integrand_bound_right_of_le_of_subset _ (fun i => ?_) hx hu
  -- ⊢ ‖g i‖ ≤ ⨆ (i : G), ‖g i‖
  exact le_ciSup (hg.norm.bddAbove_range_of_hasCompactSupport hcg.norm) _
  -- 🎉 no goals
#align has_compact_support.convolution_integrand_bound_right_of_subset HasCompactSupport.convolution_integrand_bound_right_of_subset

theorem HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f t) (g (x - t))‖ ≤ (-tsupport g + s).indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  hcg.convolution_integrand_bound_right_of_subset L hg hx Subset.rfl
#align has_compact_support.convolution_integrand_bound_right HasCompactSupport.convolution_integrand_bound_right

theorem Continuous.convolution_integrand_fst [ContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| hg.comp <| continuous_id.sub continuous_const
#align continuous.convolution_integrand_fst Continuous.convolution_integrand_fst

theorem HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f)
    (hf : Continuous f) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f (x - t)) (g t)‖ ≤
      (-tsupport f + s).indicator (fun t => (‖L‖ * ⨆ i, ‖f i‖) * ‖g t‖) t := by
  convert hcf.convolution_integrand_bound_right L.flip hf hx using 1
  -- ⊢ indicator (-tsupport f + s) (fun t => (‖L‖ * ⨆ (i : G), ‖f i‖) * ‖g t‖) t =  …
  simp_rw [L.op_norm_flip, mul_right_comm]
  -- 🎉 no goals
#align has_compact_support.convolution_integrand_bound_left HasCompactSupport.convolution_integrand_bound_left

end NoMeasurability

section Measurability
-- porting note: throughout this file we use `MeasureTheory.Measure` instead of `Measure`.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Measure.20is.20overloaded
variable [MeasurableSpace G] {μ ν : MeasureTheory.Measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : MeasureTheory.Measure G := by volume_tac) : Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ
#align convolution_exists_at ConvolutionExistsAt

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : MeasureTheory.Measure G := by volume_tac) : Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ
#align convolution_exists ConvolutionExists

section ConvolutionExists

variable {L}

theorem ConvolutionExistsAt.integrable [Sub G] {x : G} (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f t) (g (x - t))) μ :=
  h
#align convolution_exists_at.integrable ConvolutionExistsAt.integrable

variable (L)

section Group

variable [AddGroup G]

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand' [MeasurableAdd₂ G]
    [MeasurableNeg G] [SigmaFinite ν] (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.prod ν)) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  L.aestronglyMeasurable_comp₂ hf.snd <| hg.comp_measurable measurable_sub
#align measure_theory.ae_strongly_measurable.convolution_integrand' MeasureTheory.AEStronglyMeasurable.convolution_integrand'

section

variable [MeasurableAdd G] [MeasurableNeg G]

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd'
    (hf : AEStronglyMeasurable f μ) {x : G}
    (hg : AEStronglyMeasurable g <| map (fun t => x - t) μ) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aestronglyMeasurable_comp₂ hf <| hg.comp_measurable <| measurable_id.const_sub x
#align measure_theory.ae_strongly_measurable.convolution_integrand_snd' MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd'

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd' {x : G}
    (hf : AEStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aestronglyMeasurable_comp₂ (hf.comp_measurable <| measurable_id.const_sub x) hg
#align measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd' MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd'

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact support). -/
theorem BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) (μ.restrict s)) :
    ConvolutionExistsAt f g x₀ L μ := by
  -- porting note: can't `rw [ConvolutionExistsAt]`
  unfold ConvolutionExistsAt
  -- ⊢ Integrable fun t => ↑(↑L (f t)) (g (x₀ - t))
  rw [← integrableOn_iff_integrable_of_support_subset h2s]
  -- ⊢ IntegrableOn (fun t => ↑(↑L (f t)) (g (x₀ - t))) s
  set s' := (fun t => -t + x₀) ⁻¹' s
  -- ⊢ IntegrableOn (fun t => ↑(↑L (f t)) (g (x₀ - t))) s
  have : ∀ᵐ t : G ∂μ.restrict s,
      ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t
  · refine' eventually_of_forall _
    -- ⊢ ∀ (x : G), ‖↑(↑L (f x)) (g (x₀ - x))‖ ≤ indicator s (fun t => ‖L‖ * ‖f t‖ *  …
    refine' le_indicator (fun t ht => _) fun t ht => _
    -- ⊢ ‖↑(↑L (f t)) (g (x₀ - t))‖ ≤ ‖L‖ * ‖f t‖ * ⨆ (i : ↑s'), ‖g ↑i‖
    · apply_rules [L.le_of_op_norm₂_le_of_le, le_rfl]
      -- ⊢ ‖g (x₀ - t)‖ ≤ ⨆ (i : ↑s'), ‖g ↑i‖
      refine' (le_ciSup_set hbg <| mem_preimage.mpr _)
      -- ⊢ -(x₀ - t) + x₀ ∈ s
      rwa [neg_sub, sub_add_cancel]
      -- 🎉 no goals
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      -- ⊢ ‖↑(↑L (f t)) (g (x₀ - t))‖ ≤ 0
      rw [nmem_support.mp this, norm_zero]
      -- 🎉 no goals
  refine' Integrable.mono' _ _ this
  -- ⊢ Integrable fun a => indicator s (fun t => ‖L‖ * ‖f t‖ * ⨆ (i : ↑s'), ‖g ↑i‖) a
  · rw [integrable_indicator_iff hs]; exact ((hf.norm.const_mul _).mul_const _).integrableOn
    -- ⊢ IntegrableOn (fun t => ‖L‖ * ‖f t‖ * ⨆ (i : ↑s'), ‖g ↑i‖) s
                                      -- 🎉 no goals
  · exact hf.aestronglyMeasurable.convolution_integrand_snd' L hmg
    -- 🎉 no goals
#align bdd_above.convolution_exists_at' BddAbove.convolutionExistsAt'

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm' {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ := by
  refine'
    (h.const_mul ‖L‖).mono' (hmf.convolution_integrand_snd' L hmg) (eventually_of_forall fun x => _)
  rw [mul_apply', ← mul_assoc]
  -- ⊢ ‖↑(↑L (f x)) (g (x₀ - x))‖ ≤ ‖L‖ * (fun x => ‖f x‖) x * (fun x => ‖g x‖) (x₀ …
  apply L.le_op_norm₂
  -- 🎉 no goals
#align convolution_exists_at.of_norm' ConvolutionExistsAt.ofNorm'

end

section Left

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolution_integrand_snd' L <|
    hg.mono' <| (quasiMeasurePreserving_sub_left_of_right_invariant μ x).absolutelyContinuous
#align measure_theory.ae_strongly_measurable.convolution_integrand_snd MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono'
        (quasiMeasurePreserving_sub_left_of_right_invariant μ
            x).absolutelyContinuous).convolution_integrand_swap_snd'
    L hg
#align measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
theorem ConvolutionExistsAt.ofNorm {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g μ) :
    ConvolutionExistsAt f g x₀ L μ :=
  h.ofNorm' L hmf <|
    hmg.mono' (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous
#align convolution_exists_at.of_norm ConvolutionExistsAt.ofNorm

end Left

section Right

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]
  [SigmaFinite ν]

theorem MeasureTheory.AEStronglyMeasurable.convolution_integrand (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  hf.convolution_integrand' L <|
    hg.mono' (quasiMeasurePreserving_sub_of_right_invariant μ ν).absolutelyContinuous
#align measure_theory.ae_strongly_measurable.convolution_integrand MeasureTheory.AEStronglyMeasurable.convolution_integrand

theorem MeasureTheory.Integrable.convolution_integrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) := by
  have h_meas : AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable
  have h2_meas : AEStronglyMeasurable (fun y : G => ∫ x : G, ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  -- ⊢ (∀ᵐ (y : G) ∂ν, Integrable fun x => ↑(↑L (f y)) (g (x - y))) ∧ Integrable fu …
  refine' ⟨eventually_of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), _⟩
  -- ⊢ Integrable fun y => ∫ (x : G), ‖↑(↑L (f y)) (g (x - y))‖ ∂μ
  refine' Integrable.mono' _ h2_meas
      (eventually_of_forall fun t => (_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ))
  · simp only [integral_sub_right_eq_self (‖g ·‖)]
    -- ⊢ Integrable fun t => ‖L‖ * ‖f t‖ * ∫ (x : G), ‖g x‖ ∂μ
    exact (hf.norm.const_mul _).mul_const _
    -- 🎉 no goals
  · simp_rw [← integral_mul_left]
    -- ⊢ ‖∫ (x : G), ‖↑(↑L (f t)) (g (x - t))‖ ∂μ‖ ≤ ∫ (a : G), ‖L‖ * ‖f t‖ * ‖g (a - …
    rw [Real.norm_of_nonneg]
    -- ⊢ ∫ (x : G), ‖↑(↑L (f t)) (g (x - t))‖ ∂μ ≤ ∫ (a : G), ‖L‖ * ‖f t‖ * ‖g (a - t …
    · exact integral_mono_of_nonneg (eventually_of_forall fun t => norm_nonneg _)
        ((hg.comp_sub_right t).norm.const_mul _) (eventually_of_forall fun t => L.le_op_norm₂ _ _)
    exact integral_nonneg fun x => norm_nonneg _
    -- 🎉 no goals
#align measure_theory.integrable.convolution_integrand MeasureTheory.Integrable.convolution_integrand

theorem MeasureTheory.Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff <|
          hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable).mp <|
      hf.convolution_integrand L hg).1
#align measure_theory.integrable.ae_convolution_exists MeasureTheory.Integrable.ae_convolution_exists

end Right

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G]

theorem HasCompactSupport.convolutionExistsAt {x₀ : G}
    (h : HasCompactSupport fun t => L (f t) (g (x₀ - t))) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ := by
  let u := (Homeomorph.neg G).trans (Homeomorph.addRight x₀)
  -- ⊢ ConvolutionExistsAt f g x₀ L
  let v := (Homeomorph.neg G).trans (Homeomorph.addLeft x₀)
  -- ⊢ ConvolutionExistsAt f g x₀ L
  apply ((u.isCompact_preimage.mpr h).bddAbove_image hg.norm.continuousOn).convolutionExistsAt' L
    isClosed_closure.measurableSet subset_closure (hf.integrableOn_isCompact h)
  have A : AEStronglyMeasurable (g ∘ v) (μ.restrict (tsupport fun t : G => L (f t) (g (x₀ - t))))
  -- ⊢ AEStronglyMeasurable (g ∘ ↑v) (Measure.restrict μ (tsupport fun t => ↑(↑L (f …
  · apply (hg.comp v.continuous).continuousOn.aestronglyMeasurable_of_isCompact h
    -- ⊢ MeasurableSet (tsupport fun t => ↑(↑L (f t)) (g (x₀ - t)))
    exact (isClosed_tsupport _).measurableSet
    -- 🎉 no goals
  convert ((v.continuous.measurable.measurePreserving
      (μ.restrict (tsupport fun t => L (f t) (g (x₀ - t))))).aestronglyMeasurable_comp_iff
    v.toMeasurableEquiv.measurableEmbedding).1 A
  ext x
  -- ⊢ ↑(↑toAddUnits x₀) - x = ↑v x
  simp only [Homeomorph.neg, sub_eq_add_neg, coe_toAddUnits, Homeomorph.trans_apply,
    Equiv.neg_apply, Equiv.toFun_as_coe, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    Homeomorph.coe_addLeft]
#align has_compact_support.convolution_exists_at HasCompactSupport.convolutionExistsAt

theorem HasCompactSupport.convolutionExists_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  -- ⊢ ConvolutionExistsAt f g x₀ L
  refine' HasCompactSupport.convolutionExistsAt L _ hf hg
  -- ⊢ HasCompactSupport fun t => ↑(↑L (f t)) (g (x₀ - t))
  refine' (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono _
  -- ⊢ (support fun t => ↑(↑L (f t)) (g (x₀ - t))) ⊆ support (g ∘ ↑(Homeomorph.subL …
  refine' fun t => mt fun ht : g (x₀ - t) = 0 => _
  -- ⊢ (fun t => ↑(↑L (f t)) (g (x₀ - t))) t = 0
  simp_rw [ht, (L _).map_zero]
  -- 🎉 no goals
#align has_compact_support.convolution_exists_right HasCompactSupport.convolutionExists_right

theorem HasCompactSupport.convolutionExists_left_of_continuous_right (hcf : HasCompactSupport f)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  -- ⊢ ConvolutionExistsAt f g x₀ L
  refine' HasCompactSupport.convolutionExistsAt L _ hf hg
  -- ⊢ HasCompactSupport fun t => ↑(↑L (f t)) (g (x₀ - t))
  refine' hcf.mono _
  -- ⊢ (support fun t => ↑(↑L (f t)) (g (x₀ - t))) ⊆ support f
  refine' fun t => mt fun ht : f t = 0 => _
  -- ⊢ (fun t => ↑(↑L (f t)) (g (x₀ - t))) t = 0
  simp_rw [ht, L.map_zero₂]
  -- 🎉 no goals
#align has_compact_support.convolution_exists_left_of_continuous_right HasCompactSupport.convolutionExists_left_of_continuous_right

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
theorem BddAbove.convolutionExistsAt [MeasurableAdd₂ G] [SigmaFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine' BddAbove.convolutionExistsAt' L _ hs h2s hf _
  -- ⊢ BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))
  · simp_rw [← sub_eq_neg_add, hbg]
    -- 🎉 no goals
  · have : AEStronglyMeasurable g (map (fun t : G => x₀ - t) μ) :=
      hmg.mono' (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous
    apply this.mono_measure
    -- ⊢ Measure.map (fun t => x₀ - t) (Measure.restrict μ s) ≤ Measure.map (fun t => …
    exact map_mono restrict_le_self (measurable_const.sub measurable_id')
    -- 🎉 no goals
#align bdd_above.convolution_exists_at BddAbove.convolutionExistsAt

variable {L} [MeasurableAdd G] [IsNegInvariant μ]

theorem convolutionExistsAt_flip :
    ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt,
    -- porting note: added `(μ := μ)`
    ← integrable_comp_sub_left (μ := μ) (fun t => L (f t) (g (x - t))) x,
    sub_sub_cancel, flip_apply]
#align convolution_exists_at_flip convolutionExistsAt_flip

theorem ConvolutionExistsAt.integrable_swap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert h.comp_sub_left x
  -- ⊢ x✝ = x - (x - x✝)
  simp_rw [sub_sub_self]
  -- 🎉 no goals
#align convolution_exists_at.integrable_swap ConvolutionExistsAt.integrable_swap

theorem convolutionExistsAt_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolutionExistsAt_flip.symm
#align convolution_exists_at_iff_integrable_swap convolutionExistsAt_iff_integrable_swap

end MeasurableGroup

variable [TopologicalSpace G] [TopologicalAddGroup G] [BorelSpace G] [IsAddLeftInvariant μ]
  [IsNegInvariant μ]

theorem HasCompactSupport.convolutionExistsLeft (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcf.convolutionExists_right L.flip hg hf x₀
#align has_compact_support.convolution_exists_left HasCompactSupport.convolutionExistsLeft

theorem HasCompactSupport.convolutionExistsRightOfContinuousLeft (hcg : HasCompactSupport g)
    (hf : Continuous f) (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcg.convolutionExists_left_of_continuous_right L.flip hg hf x₀
#align has_compact_support.convolution_exists_right_of_continuous_left HasCompactSupport.convolutionExistsRightOfContinuousLeft

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : MeasureTheory.Measure G := by volume_tac) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ
#align convolution convolution

-- mathport name: convolution
scoped[Convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

-- mathport name: convolution.volume
scoped[Convolution]
  notation:67 f " ⋆[" L:67 "]" g:66 => convolution f g L MeasureTheory.MeasureSpace.volume

-- mathport name: convolution.lsmul
scoped[Convolution]
  notation:67 f " ⋆ " g:66 =>
    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.MeasureSpace.volume

open scoped Convolution

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
#align convolution_def convolution_def

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl
#align convolution_lsmul convolution_lsmul

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl
#align convolution_mul convolution_mul

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]
  -- ⊢ y • f ⋆[L, x✝] g = (y • convolution f g L) x✝
       -- 🎉 no goals
#align smul_convolution smul_convolution

theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]
  -- ⊢ f ⋆[L, x✝] y • g = (y • convolution f g L) x✝
       -- 🎉 no goals
#align convolution_smul convolution_smul

@[simp]
theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  -- ⊢ 0 ⋆[L, x✝] g = OfNat.ofNat 0 x✝
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]
  -- 🎉 no goals
#align zero_convolution zero_convolution

@[simp]
theorem convolution_zero : f ⋆[L, μ] 0 = 0 := by
  ext
  -- ⊢ f ⋆[L, x✝] 0 = OfNat.ofNat 0 x✝
  simp_rw [convolution_def, Pi.zero_apply, (L _).map_zero, integral_zero]
  -- 🎉 no goals
#align convolution_zero convolution_zero

theorem ConvolutionExistsAt.distrib_add {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f g' x L μ) :
    (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
  -- 🎉 no goals
#align convolution_exists_at.distrib_add ConvolutionExistsAt.distrib_add

theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' := by
  ext x
  -- ⊢ f ⋆[L, x] (g + g') = (convolution f g L + convolution f g' L) x
  exact (hfg x).distrib_add (hfg' x)
  -- 🎉 no goals
#align convolution_exists.distrib_add ConvolutionExists.distrib_add

theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
  -- 🎉 no goals
#align convolution_exists_at.add_distrib ConvolutionExistsAt.add_distrib

theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g := by
  ext x
  -- ⊢ (f + f') ⋆[L, x] g = (convolution f g L + convolution f' g L) x
  exact (hfg x).add_distrib (hfg' x)
  -- 🎉 no goals
#align convolution_exists.add_distrib ConvolutionExists.add_distrib

theorem convolution_mono_right {f g g' : G → ℝ} (hfg : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ)
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x) :
    (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  apply integral_mono hfg hfg'
  -- ⊢ (fun t => ↑(↑(lsmul ℝ ℝ) (f t)) (g (x - t))) ≤ fun t => ↑(↑(lsmul ℝ ℝ) (f t) …
  simp only [lsmul_apply, Algebra.id.smul_eq_mul]
  -- ⊢ (fun t => f t * g (x - t)) ≤ fun t => f t * g' (x - t)
  intro t
  -- ⊢ (fun t => f t * g (x - t)) t ≤ (fun t => f t * g' (x - t)) t
  apply mul_le_mul_of_nonneg_left (hg _) (hf _)
  -- 🎉 no goals
#align convolution_mono_right convolution_mono_right

theorem convolution_mono_right_of_nonneg {f g g' : G → ℝ}
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x)
    (hg' : ∀ x, 0 ≤ g' x) : (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  by_cases H : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ
  -- ⊢ f ⋆[lsmul ℝ ℝ, x] g ≤ f ⋆[lsmul ℝ ℝ, x] g'
  · exact convolution_mono_right H hfg' hf hg
    -- 🎉 no goals
  have : (f ⋆[lsmul ℝ ℝ, μ] g) x = 0 := integral_undef H
  -- ⊢ f ⋆[lsmul ℝ ℝ, x] g ≤ f ⋆[lsmul ℝ ℝ, x] g'
  rw [this]
  -- ⊢ 0 ≤ f ⋆[lsmul ℝ ℝ, x] g'
  exact integral_nonneg fun y => mul_nonneg (hf y) (hg' (x - y))
  -- 🎉 no goals
#align convolution_mono_right_of_nonneg convolution_mono_right_of_nonneg

variable (L)

theorem convolution_congr [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ]
    [IsAddRightInvariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' := by
  ext x
  -- ⊢ f ⋆[L, x] g = f' ⋆[L, x] g'
  apply integral_congr_ae
  -- ⊢ (fun a => ↑(↑L (f a)) (g (x - a))) =ᶠ[ae μ] fun a => ↑(↑L (f' a)) (g' (x - a))
  exact
    (h1.prod_mk <|
          h2.comp_tendsto
            (quasiMeasurePreserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp
      ↿fun x y => L x y
#align convolution_congr convolution_congr

theorem support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f := by
  intro x h2x
  -- ⊢ x ∈ support g + support f
  by_contra hx
  -- ⊢ False
  apply h2x
  -- ⊢ f ⋆[L, x] g = 0
  simp_rw [Set.mem_add, not_exists, not_and_or, nmem_support] at hx
  -- ⊢ f ⋆[L, x] g = 0
  rw [convolution_def]
  -- ⊢ ∫ (t : G), ↑(↑L (f t)) (g (x - t)) ∂μ = 0
  convert integral_zero G F using 2
  -- ⊢ (fun t => ↑(↑L (f t)) (g (x - t))) = fun x => 0
  ext t
  -- ⊢ ↑(↑L (f t)) (g (x - t)) = 0
  rcases hx (x - t) t with (h | h | h)
  · rw [h, (L _).map_zero]
    -- 🎉 no goals
  · rw [h, L.map_zero₂]
    -- 🎉 no goals
  · exact (h <| sub_add_cancel x t).elim
    -- 🎉 no goals
#align support_convolution_subset_swap support_convolution_subset_swap

section

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SigmaFinite μ] [IsAddRightInvariant μ]

theorem MeasureTheory.Integrable.integrable_convolution (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolution_integrand L hg).integral_prod_left
#align measure_theory.integrable.integrable_convolution MeasureTheory.Integrable.integrable_convolution

end

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

protected theorem HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f)
    (hcg : HasCompactSupport g) : HasCompactSupport (f ⋆[L, μ] g) :=
  isCompact_of_isClosed_subset (hcg.isCompact.add hcf) isClosed_closure <|
    closure_minimal
      ((support_convolution_subset_swap L).trans <| add_subset_add subset_closure subset_closure)
      (hcg.isCompact.add hcf).isClosed
#align has_compact_support.convolution HasCompactSupport.convolution

variable [BorelSpace G] [FirstCountableTopology G] [TopologicalSpace P] [FirstCountableTopology P]

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
not assuming `T2Space G`. -/
theorem continuousOn_convolution_right_with_param' {g : P → G → E'} {s : Set P} {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn (↿g) (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  intro q₀ hq₀
  -- ⊢ ContinuousWithinAt (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) q₀
  replace hq₀ : q₀.1 ∈ s; · simpa only [mem_prod, mem_univ, and_true] using hq₀
  -- ⊢ q₀.fst ∈ s
                            -- 🎉 no goals
  have A : ∀ p ∈ s, Continuous (g p) := fun p hp ↦ by
    refine hg.comp_continuous (continuous_const.prod_mk continuous_id') fun x => ?_
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hp
  have B : ∀ p ∈ s, tsupport (g p) ⊆ k := fun p hp =>
    closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) h'k
  /- We find a small neighborhood of `{q₀.1} × k` on which the function is uniformly bounded.
      This follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨w, C, w_open, q₀w, hw⟩ :
    ∃ w C, IsOpen w ∧ q₀.1 ∈ w ∧ ∀ p x, p ∈ w ∩ s → ‖g p x‖ ≤ C := by
    have A : IsCompact ({q₀.1} ×ˢ k) := isCompact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ :
        ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ IsOpen t ∧ Bounded (↿g '' (t ∩ s ×ˢ univ)) := by
      apply exists_isOpen_bounded_image_inter_of_isCompact_of_continuousOn A _ hg
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or_iff]
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ ↿g '' (t ∩ s ×ˢ univ) ⊆ closedBall (0 : E') C :=
      ht.subset_ball_lt 0 0
    obtain ⟨w, w_open, q₀w, hw⟩ : ∃ w, IsOpen w ∧ q₀.1 ∈ w ∧ w ×ˢ k ⊆ t
    · obtain ⟨w, v, w_open, -, hw, hv, hvw⟩ :
        ∃ (w : Set P) (v : Set G), IsOpen w ∧ IsOpen v ∧ {q₀.fst} ⊆ w ∧ k ⊆ v ∧ w ×ˢ v ⊆ t
      exact generalized_tube_lemma isCompact_singleton hk t_open kt
      exact ⟨w, w_open, singleton_subset_iff.1 hw, Subset.trans (Set.prod_mono Subset.rfl hv) hvw⟩
    refine' ⟨w, C, w_open, q₀w, _⟩
    rintro p x ⟨hp, hps⟩
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hw
        simp only [prod_mk_mem_set_prod_eq, hp, hx, and_true_iff]
      have H' : (p, x) ∈ (s ×ˢ univ : Set (P × G)) := by
        simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hps
      have : g p x ∈ closedBall (0 : E') C := hC (mem_image_of_mem _ (mem_inter H H'))
      rwa [mem_closedBall_zero_iff] at this
    · have : g p x = 0 := hgs _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  have I1 :
    ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀,
      AEStronglyMeasurable (fun a : G => L (f a) (g q.1 (q.2 - a))) μ := by
    filter_upwards [self_mem_nhdsWithin]
    rintro ⟨p, x⟩ ⟨hp, -⟩
    refine' (HasCompactSupport.convolutionExists_right L _ hf (A _ hp) _).1
    exact isCompact_of_isClosed_subset hk (isClosed_tsupport _) (B p hp)
  let K' := -k + {q₀.2}
  -- ⊢ ContinuousWithinAt (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) q₀
  have hK' : IsCompact K' := hk.neg.add isCompact_singleton
  -- ⊢ ContinuousWithinAt (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) q₀
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ IntegrableOn f U μ :=
    hf.integrableOn_nhds_isCompact hK'
  let bound : G → ℝ := indicator U fun a => ‖L‖ * ‖f a‖ * C
  -- ⊢ ContinuousWithinAt (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) q₀
  have I2 : ∀ᶠ q : P × G in 𝓝[s ×ˢ univ] q₀, ∀ᵐ a ∂μ, ‖L (f a) (g q.1 (q.2 - a))‖ ≤ bound a := by
    obtain ⟨V, V_mem, hV⟩ : ∃ V ∈ 𝓝 (0 : G), K' + V ⊆ U :=
      compact_open_separated_add_right hK' U_open K'U
    have : ((w ∩ s) ×ˢ ({q₀.2} + V) : Set (P × G)) ∈ 𝓝[s ×ˢ univ] q₀ := by
      conv_rhs => rw [← @Prod.mk.eta _ _ q₀, nhdsWithin_prod_eq, nhdsWithin_univ]
      refine' Filter.prod_mem_prod _ (singleton_add_mem_nhds_of_nhds_zero q₀.2 V_mem)
      exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨w, w_open.mem_nhds q₀w, Subset.rfl⟩
    filter_upwards [this]
    rintro ⟨p, x⟩ hpx
    simp only [prod_mk_mem_set_prod_eq] at hpx
    refine eventually_of_forall fun a => ?_
    apply convolution_integrand_bound_right_of_le_of_subset _ _ hpx.2 _
    · intro x
      exact hw _ _ hpx.1
    · rw [← add_assoc]
      apply Subset.trans (add_subset_add_right (add_subset_add_right _)) hV
      rw [neg_subset_neg]
      exact B p hpx.1.2
  have I3 : Integrable bound μ := by
    rw [integrable_indicator_iff U_open.measurableSet]
    exact (hU.norm.const_mul _).mul_const _
  have I4 : ∀ᵐ a : G ∂μ,
      ContinuousWithinAt (fun q : P × G => L (f a) (g q.1 (q.2 - a))) (s ×ˢ univ) q₀ := by
    refine eventually_of_forall fun a => ?_
    suffices H : ContinuousWithinAt (fun q : P × G => (f a, g q.1 (q.2 - a))) (s ×ˢ univ) q₀
    exact L.continuous₂.continuousAt.comp_continuousWithinAt H
    apply continuousWithinAt_const.prod
    change ContinuousWithinAt (fun q : P × G => (↿g) (q.1, q.2 - a)) (s ×ˢ univ) q₀
    have : ContinuousAt (fun q : P × G => (q.1, q.2 - a)) (q₀.1, q₀.2) :=
      (continuous_fst.prod_mk (continuous_snd.sub continuous_const)).continuousAt
    rw [← @Prod.mk.eta _ _ q₀]
    have h'q₀ : (q₀.1, q₀.2 - a) ∈ (s ×ˢ univ : Set (P × G)) := ⟨hq₀, mem_univ _⟩
    refine' ContinuousWithinAt.comp (hg _ h'q₀) this.continuousWithinAt _
    rintro ⟨q, x⟩ ⟨hq, -⟩
    exact ⟨hq, mem_univ _⟩
  exact continuousWithinAt_of_dominated I1 I2 I3 I4
  -- 🎉 no goals
#align continuous_on_convolution_right_with_param' continuousOn_convolution_right_with_param'

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem continuousOn_convolution_right_with_param [T2Space G] {g : P → G → E'} {s : Set P}
    {k : Set G} (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn (↿g) (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
  continuousOn_convolution_right_with_param' L hk hk.isClosed hgs hf hg
#align continuous_on_convolution_right_with_param continuousOn_convolution_right_with_param

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map.
Version not assuming `T2Space G`. -/
theorem continuousOn_convolution_right_with_param_comp' {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k) (h'k : IsClosed k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn (↿g) (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s := by
  apply
    (continuousOn_convolution_right_with_param' L hk h'k hgs hf hg).comp (continuousOn_id.prod hv)
  intro x hx
  -- ⊢ (fun x => (_root_.id x, v x)) x ∈ s ×ˢ univ
  simp only [hx, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
  -- 🎉 no goals
#align continuous_on_convolution_right_with_param_comp' continuousOn_convolution_right_with_param_comp'

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map. -/
theorem continuousOn_convolution_right_with_param_comp [T2Space G] {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn (↿g) (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s :=
  continuousOn_convolution_right_with_param_comp' L hv hk hk.isClosed hgs hf hg
#align continuous_on_convolution_right_with_param_comp continuousOn_convolution_right_with_param_comp

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
theorem HasCompactSupport.continuous_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  rw [continuous_iff_continuousOn_univ]
  -- ⊢ ContinuousOn (convolution f g L) univ
  let g' : G → G → E' := fun _ q => g q
  -- ⊢ ContinuousOn (convolution f g L) univ
  have : ContinuousOn (↿g') (univ ×ˢ univ) := (hg.comp continuous_snd).continuousOn
  -- ⊢ ContinuousOn (convolution f g L) univ
  exact continuousOn_convolution_right_with_param_comp' L
    (continuous_iff_continuousOn_univ.1 continuous_id) hcg (isClosed_tsupport _)
    (fun p x _ hx => image_eq_zero_of_nmem_tsupport hx) hf this
#align has_compact_support.continuous_convolution_right HasCompactSupport.continuous_convolution_right

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
theorem BddAbove.continuous_convolution_right_of_integrable [SecondCountableTopologyEither G E']
    (hbg : BddAbove (range fun x => ‖g x‖)) (hf : Integrable f μ) (hg : Continuous g) :
    Continuous (f ⋆[L, μ] g) := by
  refine' continuous_iff_continuousAt.mpr fun x₀ => _
  -- ⊢ ContinuousAt (convolution f g L) x₀
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ‖L (f t) (g (x - t))‖ ≤ ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖ := by
    refine' eventually_of_forall fun x => eventually_of_forall fun t => _
    apply_rules [L.le_of_op_norm₂_le_of_le, le_rfl, le_ciSup hbg (x - t)]
  refine' continuousAt_of_dominated _ this _ _
  · exact eventually_of_forall fun x =>
      hf.aestronglyMeasurable.convolution_integrand_snd' L hg.aestronglyMeasurable
  · exact (hf.norm.const_mul _).mul_const _
    -- 🎉 no goals
  · exact eventually_of_forall fun t => (L.continuous₂.comp₂ continuous_const <|
      hg.comp <| continuous_id.sub continuous_const).continuousAt
#align bdd_above.continuous_convolution_right_of_integrable BddAbove.continuous_convolution_right_of_integrable

end Group

section CommGroup

variable [AddCommGroup G]

theorem support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
  (support_convolution_subset_swap L).trans (add_comm _ _).subset
#align support_convolution_subset support_convolution_subset

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

section Measurable

variable [MeasurableNeg G]

variable [MeasurableAdd G]

/-- Commutativity of convolution -/
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g := by
  ext1 x
  -- ⊢ g ⋆[ContinuousLinearMap.flip L, x] f = f ⋆[L, x] g
  simp_rw [convolution_def]
  -- ⊢ ∫ (t : G), ↑(↑(ContinuousLinearMap.flip L) (g t)) (f (x - t)) ∂μ = ∫ (t : G) …
  rw [← integral_sub_left_eq_self _ μ x]
  -- ⊢ ∫ (x_1 : G), ↑(↑(ContinuousLinearMap.flip L) (g (x - x_1))) (f (x - (x - x_1 …
  simp_rw [sub_sub_self, flip_apply]
  -- 🎉 no goals
#align convolution_flip convolution_flip

/-- The symmetric definition of convolution. -/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ := by
  rw [← convolution_flip]; rfl
  -- ⊢ g ⋆[ContinuousLinearMap.flip L, x] f = ∫ (t : G), ↑(↑L (f (x - t))) (g t) ∂μ
                           -- 🎉 no goals
#align convolution_eq_swap convolution_eq_swap

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
  convolution_eq_swap _
#align convolution_lsmul_swap convolution_lsmul_swap

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul_swap [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
  convolution_eq_swap _
#align convolution_mul_swap convolution_mul_swap

/-- The convolution of two even functions is also even. -/
theorem convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
    (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
  calc
    ∫ t : G, (L (f t)) (g (-x - t)) ∂μ = ∫ t : G, (L (f (-t))) (g (x + t)) ∂μ := by
      apply integral_congr_ae
      -- ⊢ (fun a => ↑(↑L (f a)) (g (-x - a))) =ᶠ[ae μ] fun a => ↑(↑L (f (-a))) (g (x + …
      filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't
      -- ⊢ ↑(↑L (f t)) (g (-x - t)) = ↑(↑L (f (-t))) (g (x + t))
      simp_rw [ht, ← h't, neg_add']
      -- 🎉 no goals
    _ = ∫ t : G, (L (f t)) (g (x - t)) ∂μ := by
      rw [← integral_neg_eq_self]
      -- ⊢ ∫ (x_1 : G), ↑(↑L (f (- -x_1))) (g (x + -x_1)) ∂μ = ∫ (t : G), ↑(↑L (f t)) ( …
      simp only [neg_neg, ← sub_eq_add_neg]
      -- 🎉 no goals
#align convolution_neg_of_neg_eq convolution_neg_of_neg_eq

end Measurable

variable [TopologicalSpace G]

variable [TopologicalAddGroup G]

variable [BorelSpace G]

theorem HasCompactSupport.continuous_convolution_left [FirstCountableTopology G]
    (hcf : HasCompactSupport f) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  -- ⊢ Continuous (convolution g f (ContinuousLinearMap.flip L))
  exact hcf.continuous_convolution_right L.flip hg hf
  -- 🎉 no goals
#align has_compact_support.continuous_convolution_left HasCompactSupport.continuous_convolution_left

theorem BddAbove.continuous_convolution_left_of_integrable
    [FirstCountableTopology G] [SecondCountableTopologyEither G E]
    (hbf : BddAbove (range fun x => ‖f x‖)) (hf : Continuous f) (hg : Integrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  -- ⊢ Continuous (convolution g f (ContinuousLinearMap.flip L))
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf
  -- 🎉 no goals
#align bdd_above.continuous_convolution_left_of_integrable BddAbove.continuous_convolution_left_of_integrable

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
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂]
  simp_rw [convolution_def, h2]
  -- 🎉 no goals
#align convolution_eq_right' convolution_eq_right'

variable [BorelSpace G] [SecondCountableTopology G]

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
theorem dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε) (hif : Integrable f μ)
    (hf : support f ⊆ ball (0 : G) R) (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ (‖L‖ * ∫ x, ‖f x‖ ∂μ) * ε := by
  have hfg : ConvolutionExistsAt f g x₀ L μ := by
    refine' BddAbove.convolutionExistsAt L _ Metric.isOpen_ball.measurableSet (Subset.trans _ hf)
      hif.integrableOn hmg
    swap; · refine' fun t => mt fun ht : f t = 0 => _; simp_rw [ht, L.map_zero₂]
    rw [bddAbove_def]
    refine' ⟨‖z₀‖ + ε, _⟩
    rintro _ ⟨x, hx, rfl⟩
    refine' norm_le_norm_add_const_of_dist_le (hg x _)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ‖L (f t)‖ * ε := by
    intro t; by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      refine' ((L (f t)).dist_le_op_norm _ _).trans _
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _)
    · rw [nmem_support] at ht
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self]
      rfl
  simp_rw [convolution_def]
  -- ⊢ dist (∫ (t : G), ↑(↑L (f t)) (g (x₀ - t)) ∂μ) (∫ (t : G), ↑(↑L (f t)) z₀ ∂μ) …
  simp_rw [dist_eq_norm] at h2 ⊢
  -- ⊢ ‖∫ (t : G), ↑(↑L (f t)) (g (x₀ - t)) ∂μ - ∫ (t : G), ↑(↑L (f t)) z₀ ∂μ‖ ≤ (‖ …
  rw [← integral_sub hfg.integrable]; swap; · exact (L.flip z₀).integrable_comp hif
  -- ⊢ ‖∫ (a : G), ↑(↑L (f a)) (g (x₀ - a)) - ↑(↑L (f a)) z₀ ∂μ‖ ≤ (‖L‖ * ∫ (x : G) …
                                      -- ⊢ Integrable fun t => ↑(↑L (f t)) z₀
                                              -- 🎉 no goals
  refine' (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (eventually_of_forall h2)).trans _
  rw [integral_mul_right]
  -- ⊢ (∫ (a : G), ‖↑L (f a)‖ ∂μ) * ε ≤ (‖L‖ * ∫ (x : G), ‖f x‖ ∂μ) * ε
  refine' mul_le_mul_of_nonneg_right _ hε
  -- ⊢ ∫ (a : G), ‖↑L (f a)‖ ∂μ ≤ ‖L‖ * ∫ (x : G), ‖f x‖ ∂μ
  have h3 : ∀ t, ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖ := by
    intro t
    exact L.le_op_norm (f t)
  refine' (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _
  -- ⊢ ∫ (a : G), ‖L‖ * ‖f a‖ ∂μ = ‖L‖ * ∫ (x : G), ‖f x‖ ∂μ
  rw [integral_mul_left]
  -- 🎉 no goals
#align dist_convolution_le' dist_convolution_le'

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
  -- ⊢ dist (f ⋆[lsmul ℝ ℝ, x₀] g) z₀ ≤ ε
  convert (dist_convolution_le' (lsmul ℝ ℝ) hε hif hf hmg hg).trans _
  -- ⊢ z₀ = ∫ (t : G), ↑(↑(lsmul ℝ ℝ) (f t)) z₀ ∂μ
  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
    -- 🎉 no goals
  · simp_rw [Real.norm_of_nonneg (hnf _), hintf, mul_one]
    -- ⊢ ‖lsmul ℝ ℝ‖ * ε ≤ ε
    exact (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mul ε)
    -- 🎉 no goals
#align dist_convolution_le dist_convolution_le

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
  -- ⊢ Tendsto (fun i => φ i ⋆[lsmul ℝ ℝ, k i] g i) l (𝓝 z₀)
  rw [Metric.tendsto_nhds] at hcg ⊢
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  simp_rw [Metric.eventually_prod_nhds_iff] at hcg
  -- ⊢ ∀ (ε : ℝ), ε > 0 → ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  intro ε hε
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  have h2ε : 0 < ε / 3 := div_pos hε (by norm_num)
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  dsimp only [uncurry] at hgδ
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  have h2k := hk.eventually (ball_mem_nhds x₀ <| half_pos hδ)
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  have h2φ := hφ (ball (0 : G) _) <| ball_mem_nhds _ (half_pos hδ)
  -- ⊢ ∀ᶠ (x : ι) in l, dist (φ x ⋆[lsmul ℝ ℝ, k x] g x) z₀ < ε
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi
  -- ⊢ dist (φ i ⋆[lsmul ℝ ℝ, k i] g i) z₀ < ε
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans <| half_lt_self hδ)
  -- ⊢ dist (φ i ⋆[lsmul ℝ ℝ, k i] g i) z₀ < ε
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3 := by
    intro x' hx'
    refine' (dist_triangle_right _ _ _).trans (add_le_add (hgδ hpi _).le hgi.le)
    exact ((dist_triangle _ _ _).trans_lt (add_lt_add hx'.out hki)).trans_eq (add_halves δ)
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1
  -- ⊢ dist (φ i ⋆[lsmul ℝ ℝ, k i] g i) z₀ < ε
  refine' ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq _
  -- ⊢ ε / 3 + ε / 3 + ε / 3 = ε
  field_simp; ring_nf
  -- ⊢ ε + ε + ε = ε * 3
              -- 🎉 no goals
#align convolution_tendsto_right convolution_tendsto_right

end NormedAddCommGroup

end Measurability

end NontriviallyNormedField

open scoped Convolution

section IsROrC

variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace 𝕜 E'']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {n : ℕ∞}

variable [CompleteSpace F]

variable [MeasurableSpace G] {μ ν : MeasureTheory.Measure G}

variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc

variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']

variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']

variable {k : G → E''}

variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')

variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')

variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

variable [AddGroup G]

variable [SigmaFinite μ] [SigmaFinite ν] [IsAddRightInvariant μ]

theorem integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν)
    (hg : Integrable g μ) : ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) := by
  refine' (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans _
  -- ⊢ ∫ (y : G), ∫ (x : G), ↑(↑L (f y)) (g (x - y)) ∂μ ∂ν = ↑(↑L (∫ (x : G), f x ∂ …
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self]
  -- ⊢ ∫ (y : G), ↑(↑L (f y)) (∫ (x : G), g x ∂μ) ∂ν = ↑(↑L (∫ (x : G), f x ∂ν)) (∫ …
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf
  -- 🎉 no goals
#align integral_convolution integral_convolution

variable [MeasurableAdd₂ G] [IsAddRightInvariant ν] [MeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `convolution_assoc`. -/
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
                                                                     -- 🎉 no goals
    _ = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν := by rw [integral_integral_swap hi]
                                                                     -- 🎉 no goals
    _ = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k (x₀ - s - u))) ∂μ ∂ν := by
      congr; ext t
      -- ⊢ (fun s => ∫ (t : G), ↑(↑L₃ (f s)) (↑(↑L₄ (g (t - s))) (k (x₀ - t))) ∂μ) = fu …
             -- ⊢ ∫ (t_1 : G), ↑(↑L₃ (f t)) (↑(↑L₄ (g (t_1 - t))) (k (x₀ - t_1))) ∂μ = ∫ (u :  …
      rw [eq_comm, ← integral_sub_right_eq_self _ t]
      -- ⊢ ∫ (x : G), ↑(↑L₃ (f t)) (↑(↑L₄ (g (x - t))) (k (x₀ - t - (x - t)))) ∂μ = ∫ ( …
      simp_rw [sub_sub_sub_cancel_right]
      -- 🎉 no goals
    _ = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k (x₀ - s - u)) ∂μ) ∂ν := by
      refine' integral_congr_ae _
      -- ⊢ (fun s => ∫ (u : G), ↑(↑L₃ (f s)) (↑(↑L₄ (g u)) (k (x₀ - s - u))) ∂μ) =ᶠ[ae  …
      refine' ((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => _
      -- ⊢ (fun s => ∫ (u : G), ↑(↑L₃ (f s)) (↑(↑L₄ (g u)) (k (x₀ - s - u))) ∂μ) t = (f …
      exact (L₃ (f t)).integral_comp_comm ht
      -- 🎉 no goals
    _ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := rfl
#align convolution_assoc' convolution_assoc'

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
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
  refine' convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono fun x hx => hx.ofNorm L₄ hg hk) _
  -- ⊢ Integrable (uncurry fun x y => ↑(↑L₃ (f y)) (↑(↑L₄ (g (x - y))) (k (x₀ - x))))
  -- the following is similar to `integrable.convolution_integrand`
  have h_meas :
    AEStronglyMeasurable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x))))
      (μ.prod ν) := by
    refine' L₃.aestronglyMeasurable_comp₂ hf.snd _
    refine' L₄.aestronglyMeasurable_comp₂ hg.fst _
    refine' (hk.mono' _).comp_measurable ((measurable_const.sub measurable_snd).sub measurable_fst)
    refine' QuasiMeasurePreserving.absolutelyContinuous _
    refine' QuasiMeasurePreserving.prod_of_left
      ((measurable_const.sub measurable_snd).sub measurable_fst) (eventually_of_forall fun y => _)
    dsimp only
    exact quasiMeasurePreserving_sub_left_of_right_invariant μ _
  have h2_meas :
    AEStronglyMeasurable (fun y => ∫ x, ‖L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  have h3 : map (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν :=
    (measurePreserving_sub_prod μ ν).map_eq
  suffices Integrable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) by
    rw [← h3] at this
    convert this.comp_measurable (measurable_sub.prod_mk measurable_snd)
    ext ⟨x, y⟩
    simp_rw [uncurry, Function.comp_apply, sub_sub_sub_cancel_right]
  simp_rw [integrable_prod_iff' h_meas]
  -- ⊢ (∀ᵐ (y : G) ∂ν, Integrable fun x => uncurry (fun x y => ↑(↑L₃ (f y)) (↑(↑L₄  …
  refine' ⟨((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht =>
    (L₃ (f t)).integrable_comp <| ht.ofNorm L₄ hg hk, _⟩
  refine' (hfgk.const_mul (‖L₃‖ * ‖L₄‖)).mono' h2_meas
    (((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => _)
  · simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ‖L₃‖ ‖L₄‖, ← integral_mul_left]
    -- ⊢ ‖∫ (x : G), ‖uncurry (fun x y => ↑(↑L₃ (f y)) (↑(↑L₄ (g x)) (k (x₀ - y - x)) …
    rw [Real.norm_of_nonneg]
    -- ⊢ ∫ (x : G), ‖uncurry (fun x y => ↑(↑L₃ (f y)) (↑(↑L₄ (g x)) (k (x₀ - y - x))) …
    · refine' integral_mono_of_nonneg (eventually_of_forall fun t => norm_nonneg _)
        ((ht.const_mul _).const_mul _) (eventually_of_forall fun s => _)
      simp only [← mul_assoc ‖L₄‖]
      -- ⊢ ‖uncurry (fun x y => ↑(↑L₃ (f y)) (↑(↑L₄ (g x)) (k (x₀ - y - x)))) (s, t)‖ ≤ …
      apply_rules [ContinuousLinearMap.le_of_op_norm₂_le_of_le, le_rfl]
      -- 🎉 no goals
    exact integral_nonneg fun x => norm_nonneg _
    -- 🎉 no goals
#align convolution_assoc convolution_assoc

end Assoc

variable [NormedAddCommGroup G] [BorelSpace G]

theorem convolution_precompR_apply {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ)
    (hcg : HasCompactSupport g) (hg : Continuous g) (x₀ : G) (x : E'') :
    (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ := by
  have := hcg.convolutionExists_right (L.precompR E'' : _) hf hg x₀
  -- ⊢ ↑(f ⋆[precompR E'' L, x₀] g) x = f ⋆[L, x₀] fun a => ↑(g a) x
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  -- ⊢ ∫ (a : G), ↑(↑(↑(precompR E'' L) (f a)) (g (x₀ - a))) x ∂μ = ∫ (t : G), ↑(↑L …
  rfl
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align convolution_precompR_apply convolution_precompR_apply

variable [NormedSpace 𝕜 G] [SigmaFinite μ] [IsAddLeftInvariant μ]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`ContinuousLinearMap.precompR`. -/
theorem HasCompactSupport.hasFDerivAt_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 1 g) (x₀ : G) :
    HasFDerivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ := by
  rcases hcg.eq_zero_or_finiteDimensional 𝕜 hg.continuous with (rfl | fin_dim)
  -- ⊢ HasFDerivAt (convolution f 0 L) (f ⋆[precompR G L, x₀] fderiv 𝕜 0) x₀
  · have : fderiv 𝕜 (0 : G → E') = 0 := fderiv_const (0 : E')
    -- ⊢ HasFDerivAt (convolution f 0 L) (f ⋆[precompR G L, x₀] fderiv 𝕜 0) x₀
    simp only [this, convolution_zero, Pi.zero_apply]
    -- ⊢ HasFDerivAt 0 0 x₀
    exact hasFDerivAt_const (0 : F) x₀
    -- 🎉 no goals
  have : ProperSpace G := FiniteDimensional.proper_isROrC 𝕜 G
  -- ⊢ HasFDerivAt (convolution f g L) (f ⋆[precompR G L, x₀] fderiv 𝕜 g) x₀
  set L' := L.precompR G
  -- ⊢ HasFDerivAt (convolution f g L) (f ⋆[L', x₀] fderiv 𝕜 g) x₀
  have h1 : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
    eventually_of_forall
      (hf.aestronglyMeasurable.convolution_integrand_snd L hg.continuous.aestronglyMeasurable)
  have h2 : ∀ x, AEStronglyMeasurable (fun t => L' (f t) (fderiv 𝕜 g (x - t))) μ :=
    hf.aestronglyMeasurable.convolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).aestronglyMeasurable
  have h3 : ∀ x t, HasFDerivAt (fun x => g (x - t)) (fderiv 𝕜 g (x - t)) x := fun x t ↦ by
    simpa using
      (hg.differentiable le_rfl).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const t x))
  let K' := -tsupport (fderiv 𝕜 g) + closedBall x₀ 1
  -- ⊢ HasFDerivAt (convolution f g L) (f ⋆[L', x₀] fderiv 𝕜 g) x₀
  have hK' : IsCompact K' := (hcg.fderiv 𝕜).neg.add (isCompact_closedBall x₀ 1)
  -- ⊢ HasFDerivAt (convolution f g L) (f ⋆[L', x₀] fderiv 𝕜 g) x₀
  -- porting note: was
  -- `refine' hasFDerivAt_integral_of_dominated_of_fderiv_le zero_lt_one h1 _ (h2 x₀) _ _ _`
  -- but it failed; surprisingly, `apply` works
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le zero_lt_one h1 _ (h2 x₀)
  · refine' eventually_of_forall fun t x hx =>
      (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv le_rfl)
        (ball_subset_closedBall hx)
  · rw [integrable_indicator_iff hK'.measurableSet]
    -- ⊢ IntegrableOn (fun t => ‖L'‖ * ‖f t‖ * ⨆ (i : G), ‖fderiv 𝕜 g i‖) K'
    exact ((hf.integrableOn_isCompact hK').norm.const_mul _).mul_const _
    -- 🎉 no goals
  · exact eventually_of_forall fun t x _ => (L _).hasFDerivAt.comp x (h3 x t)
    -- 🎉 no goals
  · exact hcg.convolutionExists_right L hf hg.continuous x₀
    -- 🎉 no goals
#align has_compact_support.has_fderiv_at_convolution_right HasCompactSupport.hasFDerivAt_convolution_right

theorem HasCompactSupport.hasFDerivAt_convolution_left [IsNegInvariant μ]
    (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 1 f) (hg : LocallyIntegrable g μ) (x₀ : G) :
    HasFDerivAt (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ := by
  simp (config := { singlePass := true }) only [← convolution_flip]
  -- ⊢ HasFDerivAt (convolution g f (ContinuousLinearMap.flip L)) (g ⋆[ContinuousLi …
  exact hcf.hasFDerivAt_convolution_right L.flip hg hf x₀
  -- 🎉 no goals
#align has_compact_support.has_fderiv_at_convolution_left HasCompactSupport.hasFDerivAt_convolution_left

end IsROrC

section Real

/-! The one-variable case -/

variable [IsROrC 𝕜]

variable [NormedSpace 𝕜 E]

variable [NormedSpace 𝕜 E']

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}

variable {n : ℕ∞}

variable (L : E →L[𝕜] E' →L[𝕜] F)

variable [CompleteSpace F]

variable {μ : MeasureTheory.Measure 𝕜}

variable [IsAddLeftInvariant μ] [SigmaFinite μ]

theorem HasCompactSupport.hasDerivAt_convolution_right (hf : LocallyIntegrable f₀ μ)
    (hcg : HasCompactSupport g₀) (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ := by
  convert (hcg.hasFDerivAt_convolution_right L hf hg x₀).hasDerivAt using 1
  -- ⊢ f₀ ⋆[L, x₀] deriv g₀ = ↑(f₀ ⋆[precompR 𝕜 L, x₀] fderiv 𝕜 g₀) 1
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)]
  -- ⊢ f₀ ⋆[L, x₀] deriv g₀ = f₀ ⋆[L, x₀] fun a => ↑(fderiv 𝕜 g₀ a) 1
  rfl
  -- 🎉 no goals
#align has_compact_support.has_deriv_at_convolution_right HasCompactSupport.hasDerivAt_convolution_right

theorem HasCompactSupport.hasDerivAt_convolution_left [IsNegInvariant μ]
    (hcf : HasCompactSupport f₀) (hf : ContDiff 𝕜 1 f₀) (hg : LocallyIntegrable g₀ μ) (x₀ : 𝕜) :
    HasDerivAt (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ := by
  simp (config := { singlePass := true }) only [← convolution_flip]
  -- ⊢ HasDerivAt (convolution g₀ f₀ (ContinuousLinearMap.flip L)) (g₀ ⋆[Continuous …
  exact hcf.hasDerivAt_convolution_right L.flip hg hf x₀
  -- 🎉 no goals
#align has_compact_support.has_deriv_at_convolution_left HasCompactSupport.hasDerivAt_convolution_left

end Real

section WithParam

variable [IsROrC 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace G] [NormedAddCommGroup G] [BorelSpace G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P] {μ : MeasureTheory.Measure G}
  (L : E →L[𝕜] E' →L[𝕜] F)

-- porting note: the lemma is slow, added `set_option maxHeartbeats 300000 in`
set_option maxHeartbeats 300000 in
/-- The derivative of the convolution `f * g` is given by `f * Dg`, when `f` is locally integrable
and `g` is `C^1` and compactly supported. Version where `g` depends on an additional parameter in an
open subset `s` of a parameter space `P` (and the compact support `k` is independent of the
parameter in `s`). -/
theorem hasFDerivAt_convolution_right_with_param {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 1 (↿g) (s ×ˢ univ)) (q₀ : P × G)
    (hq₀ : q₀.1 ∈ s) :
    HasFDerivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2)
      ((f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 (↿g) (q₀.1, x)) q₀.2) q₀ := by
  let g' := fderiv 𝕜 ↿g
  -- ⊢ HasFDerivAt (fun q => f ⋆[L, q.snd] g q.fst) (f ⋆[precompR (P × G) L, q₀.snd …
  have A : ∀ p ∈ s, Continuous (g p) := fun p hp ↦ by
    refine hg.continuousOn.comp_continuous (continuous_const.prod_mk continuous_id') fun x => ?_
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hp
  have A' : ∀ q : P × G, q.1 ∈ s → s ×ˢ univ ∈ 𝓝 q := fun q hq ↦ by
    apply (hs.prod isOpen_univ).mem_nhds
    simpa only [mem_prod, mem_univ, and_true_iff] using hq
  -- The derivative of `g` vanishes away from `k`.
  have g'_zero : ∀ p x, p ∈ s → x ∉ k → g' (p, x) = 0 := by
    intro p x hp hx
    refine' (hasFDerivAt_zero_of_eventually_const 0 _).fderiv
    have M2 : kᶜ ∈ 𝓝 x := hk.isClosed.isOpen_compl.mem_nhds hx
    have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod M1 M2]
    rintro ⟨p, y⟩ ⟨hp, hy⟩
    exact hgs p y hp hy
  /- We find a small neighborhood of `{q₀.1} × k` on which the derivative is uniformly bounded. This
    follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨ε, C, εpos, h₀ε, hε⟩ :
      ∃ ε C, 0 < ε ∧ ball q₀.1 ε ⊆ s ∧ ∀ p x, ‖p - q₀.1‖ < ε → ‖g' (p, x)‖ ≤ C := by
    have A : IsCompact ({q₀.1} ×ˢ k) := isCompact_singleton.prod hk
    obtain ⟨t, kt, t_open, ht⟩ : ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ IsOpen t ∧ Bounded (g' '' t) := by
      have B : ContinuousOn g' (s ×ˢ univ) :=
        hg.continuousOn_fderiv_of_open (hs.prod isOpen_univ) le_rfl
      apply exists_isOpen_bounded_image_of_isCompact_of_continuousOn A (hs.prod isOpen_univ) _ B
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self_iff,
        true_or_iff]
    obtain ⟨ε, εpos, hε, h'ε⟩ :
      ∃ ε : ℝ, 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t ∧ ball q₀.1 ε ⊆ s := by
      obtain ⟨ε, εpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ thickening ε (({q₀.fst} : Set P) ×ˢ k) ⊆ t
      · exact A.exists_thickening_subset_open t_open kt
      obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ball q₀.1 δ ⊆ s
      · exact Metric.isOpen_iff.1 hs _ hq₀
      refine' ⟨min ε δ, lt_min εpos δpos, _, _⟩
      · exact Subset.trans (thickening_mono (min_le_left _ _) _) hε
      · exact Subset.trans (ball_subset_ball (min_le_right _ _)) hδ
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ g' '' t ⊆ closedBall 0 C; exact ht.subset_ball_lt 0 0
    refine' ⟨ε, C, εpos, h'ε, fun p x hp => _⟩
    have hps : p ∈ s := h'ε (mem_ball_iff_norm.2 hp)
    by_cases hx : x ∈ k
    · have H : (p, x) ∈ t := by
        apply hε
        refine' mem_thickening_iff.2 ⟨(q₀.1, x), _, _⟩
        · simp only [hx, singleton_prod, mem_image, Prod.mk.inj_iff, eq_self_iff_true, true_and_iff,
            exists_eq_right]
        · rw [← dist_eq_norm] at hp
          simpa only [Prod.dist_eq, εpos, dist_self, max_lt_iff, and_true_iff] using hp
      have : g' (p, x) ∈ closedBall (0 : P × G →L[𝕜] E') C := hC (mem_image_of_mem _ H)
      rwa [mem_closedBall_zero_iff] at this
    · have : g' (p, x) = 0 := g'_zero _ _ hps hx
      rw [this]
      simpa only [norm_zero] using Cpos.le
  /- Now, we wish to apply a theorem on differentiation of integrals. For this, we need to check
    trivial measurability or integrability assumptions (in `I1`, `I2`, `I3`), as well as a uniform
    integrability assumption over the derivative (in `I4` and `I5`) and pointwise differentiability
    in `I6`. -/
  have I1 :
    ∀ᶠ x : P × G in 𝓝 q₀, AEStronglyMeasurable (fun a : G => L (f a) (g x.1 (x.2 - a))) μ := by
    filter_upwards [A' q₀ hq₀]
    rintro ⟨p, x⟩ ⟨hp, -⟩
    refine' (HasCompactSupport.convolutionExists_right L _ hf (A _ hp) _).1
    apply isCompact_of_isClosed_subset hk (isClosed_tsupport _)
    exact closure_minimal (support_subset_iff'.2 fun z hz => hgs _ _ hp hz) hk.isClosed
  have I2 : Integrable (fun a : G => L (f a) (g q₀.1 (q₀.2 - a))) μ := by
    have M : HasCompactSupport (g q₀.1) := HasCompactSupport.intro hk fun x hx => hgs q₀.1 x hq₀ hx
    apply M.convolutionExists_right L hf (A q₀.1 hq₀) q₀.2
  have I3 : AEStronglyMeasurable (fun a : G => (L (f a)).comp (g' (q₀.fst, q₀.snd - a))) μ := by
    have T : HasCompactSupport fun y => g' (q₀.1, y) :=
      HasCompactSupport.intro hk fun x hx => g'_zero q₀.1 x hq₀ hx
    apply (HasCompactSupport.convolutionExists_right (L.precompR (P × G) : _) T hf _ q₀.2).1
    have : ContinuousOn g' (s ×ˢ univ) :=
      hg.continuousOn_fderiv_of_open (hs.prod isOpen_univ) le_rfl
    apply this.comp_continuous (continuous_const.prod_mk continuous_id')
    intro x
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff] using hq₀
  set K' := (-k + {q₀.2} : Set G) with K'_def
  -- ⊢ HasFDerivAt (fun q => f ⋆[L, q.snd] g q.fst) (f ⋆[precompR (P × G) L, q₀.snd …
  have hK' : IsCompact K' := hk.neg.add isCompact_singleton
  -- ⊢ HasFDerivAt (fun q => f ⋆[L, q.snd] g q.fst) (f ⋆[precompR (P × G) L, q₀.snd …
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, IsOpen U ∧ K' ⊆ U ∧ IntegrableOn f U μ
  -- ⊢ ∃ U, IsOpen U ∧ K' ⊆ U ∧ IntegrableOn f U
  exact hf.integrableOn_nhds_isCompact hK'
  -- ⊢ HasFDerivAt (fun q => f ⋆[L, q.snd] g q.fst) (f ⋆[precompR (P × G) L, q₀.snd …
  obtain ⟨δ, δpos, δε, hδ⟩ : ∃ δ, (0 : ℝ) < δ ∧ δ ≤ ε ∧ K' + ball 0 δ ⊆ U := by
    obtain ⟨V, V_mem, hV⟩ : ∃ V ∈ 𝓝 (0 : G), K' + V ⊆ U :=
      compact_open_separated_add_right hK' U_open K'U
    rcases Metric.mem_nhds_iff.1 V_mem with ⟨δ, δpos, hδ⟩
    refine' ⟨min δ ε, lt_min δpos εpos, min_le_right δ ε, _⟩
    exact (add_subset_add_left ((ball_subset_ball (min_le_left _ _)).trans hδ)).trans hV
  -- Porting note: added to speed up the line below.
  letI := ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜) (E := E)
    (F := (P × G →L[𝕜] E') →L[𝕜] P × G →L[𝕜] F) (σ₁₂ := RingHom.id 𝕜)
  let bound : G → ℝ := indicator U fun t => ‖(L.precompR (P × G))‖ * ‖f t‖ * C
  -- ⊢ HasFDerivAt (fun q => f ⋆[L, q.snd] g q.fst) (f ⋆[precompR (P × G) L, q₀.snd …
  have I4 : ∀ᵐ a : G ∂μ, ∀ x : P × G, dist x q₀ < δ →
      ‖L.precompR (P × G) (f a) (g' (x.fst, x.snd - a))‖ ≤ bound a := by
    apply eventually_of_forall
    intro a x hx
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hx
    have : (-tsupport fun a => g' (x.1, a)) + ball q₀.2 δ ⊆ U := by
      apply Subset.trans _ hδ
      rw [K'_def, add_assoc]
      apply add_subset_add
      · rw [neg_subset_neg]
        refine closure_minimal (support_subset_iff'.2 fun z hz => ?_) hk.isClosed
        apply g'_zero x.1 z (h₀ε _) hz
        rw [mem_ball_iff_norm]
        exact ((le_max_left _ _).trans_lt hx).trans_le δε
      · simp only [add_ball, thickening_singleton, zero_vadd, subset_rfl]
    apply convolution_integrand_bound_right_of_le_of_subset _ _ _ this
    · intro y
      exact hε _ _ (((le_max_left _ _).trans_lt hx).trans_le δε)
    · rw [mem_ball_iff_norm]
      exact (le_max_right _ _).trans_lt hx
  have I5 : Integrable bound μ := by
    rw [integrable_indicator_iff U_open.measurableSet]
    exact (hU.norm.const_mul _).mul_const _
  have I6 : ∀ᵐ a : G ∂μ, ∀ x : P × G, dist x q₀ < δ →
      HasFDerivAt (fun x : P × G => L (f a) (g x.1 (x.2 - a)))
        ((L (f a)).comp (g' (x.fst, x.snd - a))) x := by
    apply eventually_of_forall
    intro a x hx
    apply (L _).hasFDerivAt.comp x
    have N : s ×ˢ univ ∈ 𝓝 (x.1, x.2 - a) := by
      apply A'
      apply h₀ε
      rw [Prod.dist_eq] at hx
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hx) δε
    have Z := ((hg.differentiableOn le_rfl).differentiableAt N).hasFDerivAt
    have Z' :
        HasFDerivAt (fun x : P × G => (x.1, x.2 - a)) (ContinuousLinearMap.id 𝕜 (P × G)) x := by
      have : (fun x : P × G => (x.1, x.2 - a)) = _root_.id - fun x => (0, a) := by
        ext x <;> simp only [Pi.sub_apply, id.def, Prod.fst_sub, sub_zero, Prod.snd_sub]
      rw [this]
      exact (hasFDerivAt_id x).sub_const (0, a)
    exact Z.comp x Z'
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le δpos I1 I2 I3 I4 I5 I6
  -- 🎉 no goals
#align has_fderiv_at_convolution_right_with_param hasFDerivAt_convolution_right_with_param

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`).
In this version, all the types belong to the same universe (to get an induction working in the
proof). Use instead `contDiffOn_convolution_right_with_param`, which removes this restriction. -/
theorem contDiffOn_convolution_right_with_param_aux {G : Type uP} {E' : Type uP} {F : Type uP}
    {P : Type uP} [NormedAddCommGroup E'] [NormedAddCommGroup F] [NormedSpace 𝕜 E']
    [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace G]
    {μ : MeasureTheory.Measure G}
    [NormedAddCommGroup G] [BorelSpace G] [NormedSpace 𝕜 G] [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- We have a formula for the derivation of `f * g`, which is of the same form, thanks to
    `hasFDerivAt_convolution_right_with_param`. Therefore, we can prove the result by induction on
    `n` (but for this we need the spaces at the different steps of the induction to live in the same
    universe, which is why we make the assumption in the lemma that all the relevant spaces
    come from the same universe). -/
  induction' n using ENat.nat_induction with n ih ih generalizing g E' F
  · rw [contDiffOn_zero] at hg ⊢
    -- ⊢ ContinuousOn (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
    exact continuousOn_convolution_right_with_param L hk hgs hf hg
    -- 🎉 no goals
  · let f' : P → G → P × G →L[𝕜] F := fun p a =>
      (f ⋆[L.precompR (P × G), μ] fun x : G => fderiv 𝕜 (uncurry g) (p, x)) a
    have A : ∀ q₀ : P × G, q₀.1 ∈ s →
        HasFDerivAt (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (f' q₀.1 q₀.2) q₀ :=
      hasFDerivAt_convolution_right_with_param L hs hk hgs hf hg.one_of_succ
    rw [contDiffOn_succ_iff_fderiv_of_open (hs.prod (@isOpen_univ G _))] at hg ⊢
    -- ⊢ DifferentiableOn 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) ∧ ContDiffOn …
    constructor
    -- ⊢ DifferentiableOn 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
    · rintro ⟨p, x⟩ ⟨hp, -⟩
      -- ⊢ DifferentiableWithinAt 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ) (p, x)
      exact (A (p, x) hp).differentiableAt.differentiableWithinAt
      -- 🎉 no goals
    · suffices H : ContDiffOn 𝕜 n (↿f') (s ×ˢ univ)
      -- ⊢ ContDiffOn 𝕜 (↑n) (fun y => fderiv 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) y) (s  …
      · apply H.congr
        -- ⊢ ∀ (x : P × G), x ∈ s ×ˢ univ → fderiv 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) x = …
        rintro ⟨p, x⟩ ⟨hp, -⟩
        -- ⊢ fderiv 𝕜 (fun q => f ⋆[L, q.snd] g q.fst) (p, x) = (↿f') (p, x)
        exact (A (p, x) hp).fderiv
        -- 🎉 no goals
      have B : ∀ (p : P) (x : G), p ∈ s → x ∉ k → fderiv 𝕜 (uncurry g) (p, x) = 0 := by
        intro p x hp hx
        apply (hasFDerivAt_zero_of_eventually_const (0 : E') _).fderiv
        have M2 : kᶜ ∈ 𝓝 x := IsOpen.mem_nhds hk.isClosed.isOpen_compl hx
        have M1 : s ∈ 𝓝 p := hs.mem_nhds hp
        rw [nhds_prod_eq]
        filter_upwards [prod_mem_prod M1 M2]
        rintro ⟨p, y⟩ ⟨hp, hy⟩
        exact hgs p y hp hy
      apply ih (L.precompR (P × G) : _) B
      -- ⊢ ContDiffOn 𝕜 (↑n) (↿fun p x => fderiv 𝕜 (uncurry g) (p, x)) (s ×ˢ univ)
      convert hg.2
      -- 🎉 no goals
  · rw [contDiffOn_top] at hg ⊢
    -- ⊢ ∀ (n : ℕ), ContDiffOn 𝕜 (↑n) (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
    intro n
    -- ⊢ ContDiffOn 𝕜 (↑n) (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
    exact ih n L hgs (hg n)
    -- 🎉 no goals
#align cont_diff_on_convolution_right_with_param_aux contDiffOn_convolution_right_with_param_aux

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem contDiffOn_convolution_right_with_param {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F)
    {g : P → G → E'} {s : Set P} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- The result is known when all the universes are the same, from
    `contDiffOn_convolution_right_with_param_aux`. We reduce to this situation by pushing
    everything through `ULift` continuous linear equivalences. -/
  let eG : Type max uG uE' uF uP := ULift.{max uE' uF uP} G
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  borelize eG
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eE' : Type max uE' uG uF uP := ULift.{max uG uF uP} E'
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eF : Type max uF uG uE' uP := ULift.{max uG uE' uP} F
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eP : Type max uP uG uE' uF := ULift.{max uG uE' uF} P
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  have isoG : eG ≃L[𝕜] G := ContinuousLinearEquiv.ulift
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  have isoE' : eE' ≃L[𝕜] E' := ContinuousLinearEquiv.ulift
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  have isoF : eF ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  have isoP : eP ≃L[𝕜] P := ContinuousLinearEquiv.ulift
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let ef := f ∘ isoG
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eμ : MeasureTheory.Measure eG := Measure.map isoG.symm μ
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eg : eP → eG → eE' := fun ep ex => isoE'.symm (g (isoP ep) (isoG ex))
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  let eL :=
    ContinuousLinearMap.comp
      ((ContinuousLinearEquiv.arrowCongr isoE' isoF).symm : (E' →L[𝕜] F) →L[𝕜] eE' →L[𝕜] eF) L
  let R := fun q : eP × eG => (ef ⋆[eL, eμ] eg q.1) q.2
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  have R_contdiff : ContDiffOn 𝕜 n R ((isoP ⁻¹' s) ×ˢ univ) := by
    have hek : IsCompact (isoG ⁻¹' k) := isoG.toHomeomorph.closedEmbedding.isCompact_preimage hk
    have hes : IsOpen (isoP ⁻¹' s) := isoP.continuous.isOpen_preimage _ hs
    refine' contDiffOn_convolution_right_with_param_aux eL hes hek _ _ _
    · intro p x hp hx
      simp only [(· ∘ ·), ContinuousLinearEquiv.prod_apply, LinearIsometryEquiv.coe_coe,
        ContinuousLinearEquiv.map_eq_zero_iff]
      exact hgs _ _ hp hx
    · apply (locallyIntegrable_map_homeomorph isoG.symm.toHomeomorph).2
      convert hf
      ext1 x
      simp only [ContinuousLinearEquiv.coe_toHomeomorph, (· ∘ ·),
        ContinuousLinearEquiv.apply_symm_apply]
    · apply isoE'.symm.contDiff.comp_contDiffOn
      apply hg.comp (isoP.prod isoG).contDiff.contDiffOn
      rintro ⟨p, x⟩ ⟨hp, -⟩
      simpa only [mem_preimage, ContinuousLinearEquiv.prod_apply, prod_mk_mem_set_prod_eq, mem_univ,
        and_true_iff] using hp
  have A : ContDiffOn 𝕜 n (isoF ∘ R ∘ (isoP.prod isoG).symm) (s ×ˢ univ) := by
    apply isoF.contDiff.comp_contDiffOn
    apply R_contdiff.comp (ContinuousLinearEquiv.contDiff _).contDiffOn
    rintro ⟨p, x⟩ ⟨hp, -⟩
    simpa only [mem_preimage, mem_prod, mem_univ, and_true_iff, ContinuousLinearEquiv.prod_symm,
      ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.apply_symm_apply] using hp
  have : isoF ∘ R ∘ (isoP.prod isoG).symm = fun q : P × G => (f ⋆[L, μ] g q.1) q.2 := by
    apply funext
    rintro ⟨p, x⟩
    simp only [LinearIsometryEquiv.coe_coe, (· ∘ ·), ContinuousLinearEquiv.prod_symm,
      ContinuousLinearEquiv.prod_apply]
    simp only [convolution, coe_comp', ContinuousLinearEquiv.coe_coe, (· ∘ ·)]
    rw [ClosedEmbedding.integral_map, ← isoF.integral_comp_comm]
    swap; · exact isoG.symm.toHomeomorph.closedEmbedding
    congr 1
    ext1 a
    simp only [(· ∘ ·), ContinuousLinearEquiv.apply_symm_apply, coe_comp',
      ContinuousLinearEquiv.prod_apply, ContinuousLinearEquiv.map_sub,
      ContinuousLinearEquiv.arrowCongr, ContinuousLinearEquiv.arrowCongrSL_symm_apply,
      ContinuousLinearEquiv.coe_coe, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [this] at A
  -- ⊢ ContDiffOn 𝕜 n (fun q => f ⋆[L, q.snd] g q.fst) (s ×ˢ univ)
  exact A
  -- 🎉 no goals
#align cont_diff_on_convolution_right_with_param contDiffOn_convolution_right_with_param

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with an additional smooth function. -/
theorem contDiffOn_convolution_right_with_param_comp {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {s : Set P}
    {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E} {g : P → G → E'} {k : Set G} (hs : IsOpen s)
    (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (f ⋆[L, μ] g x) (v x)) s := by
  apply (contDiffOn_convolution_right_with_param L hs hk hgs hf hg).comp (contDiffOn_id.prod hv)
  -- ⊢ s ⊆ (fun x => (_root_.id x, v x)) ⁻¹' s ×ˢ univ
  intro x hx
  -- ⊢ x ∈ (fun x => (_root_.id x, v x)) ⁻¹' s ×ˢ univ
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
  -- 🎉 no goals
#align cont_diff_on_convolution_right_with_param_comp contDiffOn_convolution_right_with_param_comp

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
theorem contDiffOn_convolution_left_with_param [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {f : G → E} {n : ℕ∞} {g : P → G → E'} {s : Set P} {k : Set G}
    (hs : IsOpen s) (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) :
    ContDiffOn 𝕜 n (fun q : P × G => (g q.1 ⋆[L, μ] f) q.2) (s ×ˢ univ) := by
  simpa only [convolution_flip] using contDiffOn_convolution_right_with_param L.flip hs hk hgs hf hg
  -- 🎉 no goals
#align cont_diff_on_convolution_left_with_param contDiffOn_convolution_left_with_param

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with additional smooth functions. -/
theorem contDiffOn_convolution_left_with_param_comp [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (L : E' →L[𝕜] E →L[𝕜] F) {s : Set P} {n : ℕ∞} {v : P → G} (hv : ContDiffOn 𝕜 n v s) {f : G → E}
    {g : P → G → E'} {k : Set G} (hs : IsOpen s) (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContDiffOn 𝕜 n (↿g) (s ×ˢ univ)) : ContDiffOn 𝕜 n (fun x => (g x ⋆[L, μ] f) (v x)) s := by
  apply (contDiffOn_convolution_left_with_param L hs hk hgs hf hg).comp (contDiffOn_id.prod hv)
  -- ⊢ s ⊆ (fun x => (_root_.id x, v x)) ⁻¹' s ×ˢ univ
  intro x hx
  -- ⊢ x ∈ (fun x => (_root_.id x, v x)) ⁻¹' s ×ˢ univ
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self_iff, id.def]
  -- 🎉 no goals
#align cont_diff_on_convolution_left_with_param_comp contDiffOn_convolution_left_with_param_comp

theorem HasCompactSupport.contDiff_convolution_right {n : ℕ∞} (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rcases exists_compact_iff_hasCompactSupport.2 hcg with ⟨k, hk, h'k⟩
  -- ⊢ ContDiff 𝕜 n (convolution f g L)
  rw [← contDiffOn_univ]
  -- ⊢ ContDiffOn 𝕜 n (convolution f g L) univ
  exact contDiffOn_convolution_right_with_param_comp L contDiffOn_id isOpen_univ hk
    (fun p x _ hx => h'k x hx) hf (hg.comp contDiff_snd).contDiffOn
#align has_compact_support.cont_diff_convolution_right HasCompactSupport.contDiff_convolution_right

theorem HasCompactSupport.contDiff_convolution_left [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    {n : ℕ∞} (hcf : HasCompactSupport f) (hf : ContDiff 𝕜 n f) (hg : LocallyIntegrable g μ) :
    ContDiff 𝕜 n (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  -- ⊢ ContDiff 𝕜 n (convolution g f (ContinuousLinearMap.flip L))
  exact hcf.contDiff_convolution_right L.flip hg hf
  -- 🎉 no goals
#align has_compact_support.cont_diff_convolution_left HasCompactSupport.contDiff_convolution_left

end WithParam

section Nonneg

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [NormedSpace ℝ F] [CompleteSpace F]

/-- The forward convolution of two functions `f` and `g` on `ℝ`, with respect to a continuous
bilinear map `L` and measure `ν`. It is defined to be the function mapping `x` to
`∫ t in 0..x, L (f t) (g (x - t)) ∂ν` if `0 < x`, and 0 otherwise. -/
noncomputable def posConvolution (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : MeasureTheory.Measure ℝ := by volume_tac) : ℝ → F :=
  indicator (Ioi (0 : ℝ)) fun x => ∫ t in (0)..x, L (f t) (g (x - t)) ∂ν
#align pos_convolution posConvolution

theorem posConvolution_eq_convolution_indicator (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : MeasureTheory.Measure ℝ := by volume_tac) [NoAtoms ν] :
    posConvolution f g L ν = convolution (indicator (Ioi 0) f) (indicator (Ioi 0) g) L ν := by
  ext1 x
  -- ⊢ posConvolution f g L x = indicator (Ioi 0) f ⋆[L, x] indicator (Ioi 0) g
  -- porting note: was `rw [convolution, posConvolution, indicator]`, now `rw` can't do it
  -- the `rw` unfolded only one `indicator`; now we unfold it everywhere, so we need to adjust
  -- `rw`s below
  unfold convolution posConvolution indicator; simp only
  -- ⊢ (if x ∈ Ioi 0 then (fun x => ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x - t)) ∂ν) …
                                               -- ⊢ (if x ∈ Ioi 0 then ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x - t)) ∂ν else 0) =  …
  split_ifs with h
  -- ⊢ ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x - t)) ∂ν = ∫ (t : ℝ), ↑(↑L (if t ∈ Ioi …
  · rw [intervalIntegral.integral_of_le (le_of_lt h), integral_Ioc_eq_integral_Ioo, ←
      integral_indicator (measurableSet_Ioo : MeasurableSet (Ioo 0 x))]
    congr 1 with t : 1
    -- ⊢ indicator (Ioo 0 x) (fun t => ↑(↑L (f t)) (g (x - t))) t = ↑(↑L (if t ∈ Ioi  …
    have : t ≤ 0 ∨ t ∈ Ioo 0 x ∨ x ≤ t := by
      rcases le_or_lt t 0 with (h | h)
      · exact Or.inl h
      · rcases lt_or_le t x with (h' | h')
        exacts [Or.inr (Or.inl ⟨h, h'⟩), Or.inr (Or.inr h')]
    rcases this with (ht | ht | ht)
    · -- Porting note: was
      -- rw [indicator_of_not_mem (not_mem_Ioo_of_le ht), indicator_of_not_mem (not_mem_Ioi.mpr ht),
      --   ContinuousLinearMap.map_zero, ContinuousLinearMap.zero_apply]
      rw [indicator_of_not_mem (not_mem_Ioo_of_le ht), if_neg (not_mem_Ioi.mpr ht),
        ContinuousLinearMap.map_zero, ContinuousLinearMap.zero_apply]
    · -- Porting note: was
      -- rw [indicator_of_mem ht, indicator_of_mem (mem_Ioi.mpr ht.1),
      --     indicator_of_mem (mem_Ioi.mpr <| sub_pos.mpr ht.2)]
      rw [indicator_of_mem ht, if_pos (mem_Ioi.mpr ht.1),
        if_pos (mem_Ioi.mpr <| sub_pos.mpr ht.2)]
    · -- Porting note: was
      -- rw [indicator_of_not_mem (not_mem_Ioo_of_ge ht),
      --     indicator_of_not_mem (not_mem_Ioi.mpr (sub_nonpos_of_le ht)),
      --     ContinuousLinearMap.map_zero]
      rw [indicator_of_not_mem (not_mem_Ioo_of_ge ht),
        if_neg (not_mem_Ioi.mpr (sub_nonpos_of_le ht)), ContinuousLinearMap.map_zero]
  · convert (integral_zero ℝ F).symm with t
    -- ⊢ ↑(↑L (if t ∈ Ioi 0 then f t else 0)) (if x - t ∈ Ioi 0 then g (x - t) else 0 …
    by_cases ht : 0 < t
    -- ⊢ ↑(↑L (if t ∈ Ioi 0 then f t else 0)) (if x - t ∈ Ioi 0 then g (x - t) else 0 …
    · -- Porting note: was
      -- rw [indicator_of_not_mem (_ : x - t ∉ Ioi 0), ContinuousLinearMap.map_zero]
      rw [if_neg (_ : x - t ∉ Ioi 0), ContinuousLinearMap.map_zero]
      -- ⊢ ¬x - t ∈ Ioi 0
      rw [not_mem_Ioi] at h ⊢
      -- ⊢ x - t ≤ 0
      exact sub_nonpos.mpr (h.trans ht.le)
      -- 🎉 no goals
    · -- Porting note: was
      -- rw [indicator_of_not_mem (mem_Ioi.not.mpr ht), ContinuousLinearMap.map_zero,
      --  ContinuousLinearMap.zero_apply]
      rw [if_neg (mem_Ioi.not.mpr ht), ContinuousLinearMap.map_zero,
        ContinuousLinearMap.zero_apply]
#align pos_convolution_eq_convolution_indicator posConvolution_eq_convolution_indicator

theorem integrable_posConvolution {f : ℝ → E} {g : ℝ → E'} {μ ν : MeasureTheory.Measure ℝ}
    [SigmaFinite μ]
    [SigmaFinite ν] [IsAddRightInvariant μ] [NoAtoms ν] (hf : IntegrableOn f (Ioi 0) ν)
    (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    Integrable (posConvolution f g L ν) μ := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] at hf hg
  -- ⊢ Integrable (posConvolution f g L)
  rw [posConvolution_eq_convolution_indicator f g L ν]
  -- ⊢ Integrable (convolution (indicator (Ioi 0) f) (indicator (Ioi 0) g) L)
  exact (hf.convolution_integrand L hg).integral_prod_left
  -- 🎉 no goals
#align integrable_pos_convolution integrable_posConvolution

/-- The integral over `Ioi 0` of a forward convolution of two functions is equal to the product
of their integrals over this set. (Compare `integral_convolution` for the two-sided convolution.) -/
theorem integral_posConvolution [CompleteSpace E] [CompleteSpace E']
    {μ ν : MeasureTheory.Measure ℝ}
    [SigmaFinite μ] [SigmaFinite ν] [IsAddRightInvariant μ] [NoAtoms ν] {f : ℝ → E} {g : ℝ → E'}
    (hf : IntegrableOn f (Ioi 0) ν) (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    ∫ x : ℝ in Ioi 0, ∫ t : ℝ in (0)..x, L (f t) (g (x - t)) ∂ν ∂μ =
      L (∫ x : ℝ in Ioi 0, f x ∂ν) (∫ x : ℝ in Ioi 0, g x ∂μ) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf hg
  -- ⊢ ∫ (x : ℝ) in Ioi 0, ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x - t)) ∂ν ∂μ = ↑(↑L …
  simp_rw [← integral_indicator measurableSet_Ioi]
  -- ⊢ ∫ (x : ℝ), indicator (Ioi 0) (fun x => ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x …
  convert integral_convolution L hf hg using 4 with x
  -- ⊢ (indicator (Ioi 0) fun x => ∫ (t : ℝ) in 0 ..x, ↑(↑L (f t)) (g (x - t)) ∂ν)  …
  apply posConvolution_eq_convolution_indicator
  -- 🎉 no goals
#align integral_pos_convolution integral_posConvolution

end Nonneg
