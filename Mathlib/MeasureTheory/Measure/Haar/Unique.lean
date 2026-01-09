/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.EverywherePos
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Uniqueness of Haar measure in locally compact groups

## Main results

In a locally compact group, we prove that two left-invariant measures `μ'` and `μ` which are finite
on compact sets coincide, up to a normalizing scalar that we denote with `haarScalarFactor μ' μ`,
in the following sense:
* `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`: they give the same value to the
  integral of continuous compactly supported functions, up to a scalar.
* `measure_isMulInvariant_eq_smul_of_isCompact_closure`: they give the same value to sets with
  compact closure, up to a scalar.
* `measure_isHaarMeasure_eq_smul_of_isOpen`: they give the same value to open sets, up to a scalar.

To get genuine equality of measures, we typically need additional regularity assumptions:

* `isMulLeftInvariant_eq_smul_of_innerRegular`: two left invariant measures which are
  inner regular coincide up to a scalar.
* `isMulLeftInvariant_eq_smul_of_regular`: two left invariant measures which are
  regular coincide up to a scalar.
* `isHaarMeasure_eq_smul`: in a second countable space, two Haar measures coincide up to a
  scalar.
* `isMulInvariant_eq_smul_of_compactSpace`: two left-invariant measures on a compact group coincide
  up to a scalar.
* `isHaarMeasure_eq_of_isProbabilityMeasure`: two Haar measures which are probability measures
  coincide exactly.

In general, uniqueness statements for Haar measures in the literature make some assumption of
regularity, either regularity or inner regularity. We have tried to minimize the assumptions in the
theorems above, and cover the different results that exist in the literature.

## Implementation

The first result `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport` is classical. To prove
it, we use a change of variables to express integrals with respect to a left-invariant measure as
integrals with respect to a given right-invariant measure (with a suitable density function).
The uniqueness readily follows.

Uniqueness results for the measure of compact sets and open sets, without any regularity assumption,
are significantly harder. They rely on the completion-regularity of the standard regular Haar
measure. We follow McQuillan's answer at https://mathoverflow.net/questions/456670/.

On second-countable groups, one can arrive to slightly different uniqueness results by using that
the operations are measurable. In particular, one can get uniqueness assuming σ-finiteness of
the measures but discarding the assumption that they are finite on compact sets. See
`haarMeasure_unique` in the file `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`.

## References

[Halmos, Measure Theory][halmos1950measure]
[Fremlin, *Measure Theory* (volume 4)][fremlin_vol4]
-/

@[expose] public section

open Filter Set TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal

namespace MeasureTheory

/-- The parameterized integral `x ↦ ∫ y, g (y⁻¹ * x) ∂μ` depends continuously on `y` when `g` is a
compactly supported continuous function on a topological group `G`, and `μ` is finite on compact
sets. -/
@[to_additive]
lemma continuous_integral_apply_inv_mul
    {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : G → E}
    (hg : Continuous g) (h'g : HasCompactSupport g) :
    Continuous (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) := by
  let k := tsupport g
  have k_comp : IsCompact k := h'g
  apply continuous_iff_continuousAt.2 (fun x₀ ↦ ?_)
  obtain ⟨t, t_comp, ht⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x₀ := exists_compact_mem_nhds x₀
  let k' : Set G := t • k⁻¹
  have k'_comp : IsCompact k' := t_comp.smul_set k_comp.inv
  have A : ContinuousOn (fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂μ) t := by
    apply continuousOn_integral_of_compact_support k'_comp
    · exact (hg.comp (continuous_snd.inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * x, ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

namespace Measure

section Group

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-!
### Uniqueness of integrals of compactly supported functions

Two left invariant measures coincide when integrating continuous compactly supported functions,
up to a scalar that we denote with `haarScalarFactor μ' μ `.

This is proved by relating the integral for arbitrary left invariant and right invariant measures,
applying a version of Fubini.
As one may use the same right invariant measure, this shows that two different left invariant
measures will give the same integral, up to some fixed scalar.
-/

/-- In a group with a left invariant measure `μ` and a right invariant measure `ν`, one can express
integrals with respect to `μ` as integrals with respect to `ν` up to a constant scaling factor
(given in the statement as `∫ x, g x ∂μ` where `g` is a fixed reference function) and an
explicit density `y ↦ 1/∫ z, g (z⁻¹ * y) ∂ν`. -/
@[to_additive]
lemma integral_isMulLeftInvariant_isMulRightInvariant_combo
    {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [IsMulLeftInvariant μ] [IsMulRightInvariant ν] [IsOpenPosMeasure ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) (g_nonneg : 0 ≤ g) {x₀ : G} (g_pos : g x₀ ≠ 0) :
    ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ := by
  -- The group has to be locally compact, otherwise all integrals vanish and the result is trivial.
  rcases h'f.eq_zero_or_locallyCompactSpace_of_group hf with Hf | Hf
  · simp [Hf]
  let D : G → ℝ := fun (x : G) ↦ ∫ y, g (y⁻¹ * x) ∂ν
  have D_cont : Continuous D := continuous_integral_apply_inv_mul hg h'g
  have D_pos : ∀ x, 0 < D x := by
    intro x
    have C : Continuous (fun y ↦ g (y⁻¹ * x)) := hg.comp (continuous_inv.mul continuous_const)
    apply (integral_pos_iff_support_of_nonneg _ _).2
    · apply C.isOpen_support.measure_pos ν
      exact ⟨x * x₀⁻¹, by simpa using g_pos⟩
    · exact fun y ↦ g_nonneg (y⁻¹ * x)
    · apply C.integrable_of_hasCompactSupport
      exact h'g.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  calc
  ∫ x, f x ∂μ = ∫ x, f x * (D x)⁻¹ * D x ∂μ := by
    congr with x; rw [mul_assoc, inv_mul_cancel₀ (D_pos x).ne', mul_one]
  _ = ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ := by simp_rw [D, integral_const_mul]
  _ = ∫ y, (∫ x, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂μ) ∂ν := by
      apply integral_integral_swap_of_hasCompactSupport
      · apply Continuous.mul
        · exact (hf.comp continuous_fst).mul
            ((D_cont.comp continuous_fst).inv₀ (fun x ↦ (D_pos _).ne'))
        · exact hg.comp (continuous_snd.inv.mul continuous_fst)
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ K ×ˢ closure M → f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1) = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ K; swap
          · simp [image_eq_zero_of_notMem_tsupport H]
          have : g (y⁻¹ * x) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [M, mem_image, mem_prod, Prod.exists]
            exact ⟨x, y⁻¹ * x, ⟨H, hxy⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (K_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport f).prod isClosed_closure
  _ = ∫ y, (∫ x, f (y * x) * (D (y * x))⁻¹ * g x ∂μ) ∂ν := by
      congr with y
      rw [← integral_mul_left_eq_self _ y]
      simp
  _ = ∫ x, (∫ y, f (y * x) * (D (y * x))⁻¹ * g x ∂ν) ∂μ := by
      apply (integral_integral_swap_of_hasCompactSupport _ _).symm
      · apply Continuous.mul ?_ (hg.comp continuous_fst)
        exact (hf.comp (continuous_snd.mul continuous_fst)).mul
          ((D_cont.comp (continuous_snd.mul continuous_fst)).inv₀ (fun x ↦ (D_pos _).ne'))
      · let K := tsupport f
        have K_comp : IsCompact K := h'f
        let L := tsupport g
        have L_comp : IsCompact L := h'g
        let M := (fun (p : G × G) ↦ p.1 * p.2⁻¹) '' (K ×ˢ L)
        have M_comp : IsCompact M :=
          (K_comp.prod L_comp).image (continuous_fst.mul continuous_snd.inv)
        have M'_comp : IsCompact (closure M) := M_comp.closure
        have : ∀ (p : G × G), p ∉ L ×ˢ closure M →
            f (p.2 * p.1) * (D (p.2 * p.1))⁻¹ * g p.1 = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ L; swap
          · simp [image_eq_zero_of_notMem_tsupport H]
          have : f (y * x) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [M, mem_image, mem_prod, Prod.exists]
            exact ⟨y * x, x, ⟨hxy, H⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (L_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport g).prod isClosed_closure
  _ = ∫ x, (∫ y, f y * (D y)⁻¹ ∂ν) * g x ∂μ := by
      simp_rw [integral_mul_const]
      congr with x
      conv_rhs => rw [← integral_mul_right_eq_self _ x]
  _ = (∫ y, f y * (D y)⁻¹ ∂ν) * ∫ x, g x ∂μ := integral_const_mul _ _

/-- Given two left-invariant measures which are finite on
compacts, they coincide in the following sense: they give the same value to the integral of
continuous compactly supported functions, up to a multiplicative constant. -/
@[to_additive exists_integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport]
lemma exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    ∃ (c : ℝ≥0), ∀ (f : G → ℝ), Continuous f → HasCompactSupport f →
      ∫ x, f x ∂μ' = ∫ x, f x ∂(c • μ) := by
  -- The group has to be locally compact, otherwise all integrals vanish and the result is trivial.
  by_cases H : LocallyCompactSpace G; swap
  · refine ⟨0, fun f f_cont f_comp ↦ ?_⟩
    rcases f_comp.eq_zero_or_locallyCompactSpace_of_group f_cont with hf | hf
    · simp [hf]
    · exact (H hf).elim
  -- Fix some nonzero continuous function with compact support `g`.
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ (g : C(G, ℝ)), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_pos : 0 < ∫ x, g x ∂μ :=
    g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one
  -- The proportionality constant we are looking for will be the ratio of the integrals of `g`
  -- with respect to `μ'` and `μ`.
  let c : ℝ := (∫ x, g x ∂μ)⁻¹ * (∫ x, g x ∂μ')
  have c_nonneg : 0 ≤ c :=
    mul_nonneg (inv_nonneg.2 (integral_nonneg g_nonneg)) (integral_nonneg g_nonneg)
  refine ⟨⟨c, c_nonneg⟩, fun f f_cont f_comp ↦ ?_⟩
  /- use the lemma `integral_mulLeftInvariant_mulRightInvariant_combo` for `μ` and then `μ'`
  to reexpress the integral of `f` as the integral of `g` times a factor which only depends
  on a right-invariant measure `ν`. We use `ν = μ.inv` for convenience. -/
  let ν := μ.inv
  have A : ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ :=
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  rw [← mul_inv_eq_iff_eq_mul₀ int_g_pos.ne'] at A
  have B : ∫ x, f x ∂μ' = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ' :=
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  /- Since the `ν`-factor is the same for `μ` and `μ'`, this gives the result. -/
  rw [← A, mul_assoc, mul_comm] at B
  simp [B, integral_smul_nnreal_measure, c, NNReal.smul_def]

open scoped Classical in
/-- Given two left-invariant measures which are finite on compacts, `haarScalarFactor μ' μ` is a
scalar such that `∫ f dμ' = (haarScalarFactor μ' μ) ∫ f dμ` for any compactly supported continuous
function `f`.

Note that there is a dissymmetry in the assumptions between `μ'` and `μ`: the measure `μ'` needs
only be finite on compact sets, while `μ` has to be finite on compact sets and positive on open
sets, i.e., a Haar measure, to exclude for instance the case where `μ = 0`, where the definition
doesn't make sense. -/
@[to_additive /-- Given two left-invariant measures which are finite on compacts,
`addHaarScalarFactor μ' μ` is a scalar such that `∫ f dμ' = (addHaarScalarFactor μ' μ) ∫ f dμ` for
any compactly supported continuous function `f`.

Note that there is a dissymmetry in the assumptions between `μ'` and `μ`: the measure `μ'` needs
only be finite on compact sets, while `μ` has to be finite on compact sets and positive on open
sets, i.e., an additive Haar measure, to exclude for instance the case where `μ = 0`, where the
definition doesn't make sense. -/]
noncomputable def haarScalarFactor
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    ℝ≥0 :=
  if ¬ LocallyCompactSpace G then 1
  else (exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ).choose

/-- Two left invariant measures integrate in the same way continuous compactly supported functions,
up to the scalar `haarScalarFactor μ' μ`. See also
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which gives the same result for compact
sets, and `measure_isHaarMeasure_eq_smul_of_isOpen` for open sets. -/
@[to_additive integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
/-- Two left invariant measures integrate in the same way continuous compactly supported functions,
up to the scalar `addHaarScalarFactor μ' μ`. See also
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which gives the same result for compact
sets, and `measure_isAddHaarMeasure_eq_smul_of_isOpen` for open sets. -/]
theorem integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {f : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f) :
    ∫ x, f x ∂μ' = ∫ x, f x ∂(haarScalarFactor μ' μ • μ) := by
  classical
  rcases h'f.eq_zero_or_locallyCompactSpace_of_group hf with Hf | Hf
  · simp [Hf]
  · simp only [haarScalarFactor, Hf, not_true_eq_false, ite_false]
    exact (exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ).choose_spec
      f hf h'f

@[to_additive addHaarScalarFactor_eq_integral_div]
lemma haarScalarFactor_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {f : G → ℝ} (hf : Continuous f)
    (h'f : HasCompactSupport f) (int_nonzero : ∫ x, f x ∂μ ≠ 0) :
    haarScalarFactor μ' μ = (∫ x, f x ∂μ') / ∫ x, f x ∂μ := by
  have := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ hf h'f
  rw [integral_smul_nnreal_measure] at this
  exact EuclideanDomain.eq_div_of_mul_eq_left int_nonzero this.symm

@[to_additive (attr := simp) addHaarScalarFactor_smul]
lemma haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0} :
    haarScalarFactor (c • μ') μ = c • haarScalarFactor μ' μ := by
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(G, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  apply NNReal.coe_injective
  calc
    haarScalarFactor (c • μ') μ = (∫ x, g x ∂(c • μ')) / ∫ x, g x ∂μ :=
      haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero
    _ = (c • (∫ x, g x ∂μ')) / ∫ x, g x ∂μ := by simp
    _ = c • ((∫ x, g x ∂μ') / ∫ x, g x ∂μ) := smul_div_assoc c _ _
    _ = c • haarScalarFactor μ' μ := by
      rw [← haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero]

@[to_additive mul_addHaarScalarFactor_smul]
lemma mul_haarScalarFactor_smul [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : c ≠ 0) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
    c * haarScalarFactor μ' (c • μ) = haarScalarFactor μ' μ := by
  have : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(G, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  apply NNReal.coe_injective
  calc
    c * haarScalarFactor μ' (c • μ) = c * ((∫ x, g x ∂μ') / ∫ x, g x ∂(c • μ)) :=
      by rw [haarScalarFactor_eq_integral_div _ _ g_cont g_comp (by simp [int_g_ne_zero, hc])]
    _ = c * ((∫ x, g x ∂μ') / (c • ∫ x, g x ∂μ)) := by simp
    _ = (∫ x, g x ∂μ') / (∫ x, g x ∂μ) := by
      rw [NNReal.smul_def, smul_eq_mul, ← mul_div_assoc]
      exact mul_div_mul_left (∫ (x : G), g x ∂μ') (∫ (x : G), g x ∂μ) (by simp [hc])
    _ = μ'.haarScalarFactor μ :=
      (haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero).symm

@[to_additive addHaarScalarFactor_smul_smul]
lemma haarScalarFactor_smul_smul [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : c ≠ 0) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul _ hc
    haarScalarFactor (c • μ') (c • μ) = haarScalarFactor μ' μ := by
  rw [haarScalarFactor_smul, smul_eq_mul, mul_haarScalarFactor_smul _ _ hc]

@[to_additive (attr := simp)]
lemma haarScalarFactor_self (μ : Measure G) [IsHaarMeasure μ] :
    haarScalarFactor μ μ = 1 := by
  by_cases hG : LocallyCompactSpace G; swap
  · simp [haarScalarFactor, hG]
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(G, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  apply NNReal.coe_injective
  calc
    haarScalarFactor μ μ = (∫ x, g x ∂μ) / ∫ x, g x ∂μ :=
      haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero
    _ = 1 := div_self int_g_ne_zero

@[to_additive addHaarScalarFactor_eq_mul]
lemma haarScalarFactor_eq_mul (μ' μ ν : Measure G)
    [IsHaarMeasure μ] [IsHaarMeasure ν] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    haarScalarFactor μ' ν = haarScalarFactor μ' μ * haarScalarFactor μ ν := by
  -- The group has to be locally compact, otherwise the scalar factor is 1 by definition.
  by_cases hG : LocallyCompactSpace G; swap
  · simp [haarScalarFactor, hG]
  -- Fix some nonzero continuous function with compact support `g`.
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ (g : C(G, ℝ)), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have Z := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ g_cont g_comp
  simp only [integral_smul_nnreal_measure, smul_smul,
    integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' ν g_cont g_comp,
    integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ ν g_cont g_comp] at Z
  have int_g_pos : 0 < ∫ x, g x ∂ν := by
    apply (integral_pos_iff_support_of_nonneg g_nonneg _).2
    · exact IsOpen.measure_pos ν g_cont.isOpen_support ⟨1, g_one⟩
    · exact g_cont.integrable_of_hasCompactSupport g_comp
  change (haarScalarFactor μ' ν : ℝ) * ∫ (x : G), g x ∂ν =
    (haarScalarFactor μ' μ * haarScalarFactor μ ν : ℝ≥0) * ∫ (x : G), g x ∂ν at Z
  simpa only [mul_eq_mul_right_iff (M₀ := ℝ), int_g_pos.ne', or_false, ← NNReal.eq_iff] using Z

/-- The scalar factor between two left-invariant measures is non-zero when both measures are
positive on open sets. -/
@[to_additive]
lemma haarScalarFactor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ]
    [IsHaarMeasure μ'] : 0 < haarScalarFactor μ' μ :=
  pos_iff_ne_zero.2 (fun H ↦ by simpa [H] using haarScalarFactor_eq_mul μ' μ μ')

/-!
### Uniqueness of measure of sets with compact closure

Two left invariant measures give the same measure to sets with compact closure, up to the
scalar `haarScalarFactor μ' μ`.

This is a tricky argument, typically not done in textbooks (the textbooks version all require one
version of regularity or another). Here is a sketch, based on
McQuillan's answer at https://mathoverflow.net/questions/456670/.

Assume for simplicity that all measures are normalized, so that the scalar factors are all `1`.
First, from the fact that `μ` and `μ'` integrate in the same way compactly supported functions,
they give the same measure to compact "zero sets", i.e., sets of the form `f⁻¹ {1}`
for `f` continuous and compactly supported.
See `measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport`.

If `μ` is inner regular, a theorem of Halmos shows that any measurable set `s` of finite measure can
be approximated from inside by a compact zero set `k`. Then `μ s ≤ μ k + ε = μ' k + ε ≤ μ' s + ε`.
Letting `ε` tend to zero, one gets `μ s ≤ μ' s`.
See `smul_measure_isMulInvariant_le_of_isCompact_closure`.

Assume now that `s` is a measurable set of compact closure. It is contained in a compact
zero set `t`. The same argument applied to `t - s` gives `μ (t \ s) ≤ μ' (t \ s)`, i.e.,
`μ t - μ s ≤ μ' t - μ' s`. As `μ t = μ' t` (since these are zero sets), we get the inequality
`μ' s ≤ μ s`. Together with the previous one, this gives `μ' s = μ s`.
See `measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop`.

If neither `μ` nor `μ'` is inner regular, we can use the existence of another inner regular
left-invariant measure `ν`, so get `μ s = ν s = μ' s`, by applying twice the previous argument.
Here, the uniqueness argument uses the existence of a Haar measure with a nice behavior!
See `measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet`.

Finally, if `s` has compact closure but is not measurable, its measure is the infimum of the
measures of its measurable supersets, and even of those contained in `closure s`. As `μ`
and `μ'` coincide on these supersets, this yields `μ s = μ' s`.
See `measure_isMulInvariant_eq_smul_of_isCompact_closure`.
-/

/-- Two left invariant measures give the same mass to level sets of continuous compactly supported
functions, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure. -/
@[to_additive measure_preimage_isAddLeftInvariant_eq_smul_of_hasCompactSupport
/-- Two left invariant measures give the same mass to level sets of continuous compactly supported
functions, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure. -/]
lemma measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {f : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f) :
    μ' (f ⁻¹' {1}) = haarScalarFactor μ' μ • μ (f ⁻¹' {1}) := by
  /- This follows from the fact that the two measures integrate in the same way continuous
  functions, by approximating the indicator function of `f ⁻¹' {1}` by continuous functions
  (namely `vₙ ∘ f` where `vₙ` is equal to `1` at `1`, and `0` outside of a small neighborhood
  `(1 - uₙ, 1 + uₙ)` where `uₙ` is a sequence tending to `0`).
  We use `vₙ = thickenedIndicator uₙ {1}` to take advantage of existing lemmas. -/
  obtain ⟨u, -, u_mem, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 1)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ) < 1)
  let v : ℕ → ℝ → ℝ := fun n x ↦ thickenedIndicator (u_mem n).1 ({1} : Set ℝ) x
  have vf_cont n : Continuous ((v n) ∘ f) := by
    apply Continuous.comp (continuous_induced_dom.comp ?_) hf
    exact BoundedContinuousFunction.continuous (thickenedIndicator (u_mem n).left {1})
  have I : ∀ (ν : Measure G), IsFiniteMeasureOnCompacts ν →
      Tendsto (fun n ↦ ∫ x, v n (f x) ∂ν) atTop
      (𝓝 (∫ x, Set.indicator ({1} : Set ℝ) (fun _ ↦ 1) (f x) ∂ν)) := by
    intro ν hν
    apply tendsto_integral_of_dominated_convergence
        (bound := (tsupport f).indicator (fun (_ : G) ↦ (1 : ℝ)))
    · exact fun n ↦ (vf_cont n).aestronglyMeasurable
    · apply IntegrableOn.integrable_indicator _ (isClosed_tsupport f).measurableSet
      simpa using IsCompact.measure_lt_top h'f
    · refine fun n ↦ Eventually.of_forall (fun x ↦ ?_)
      by_cases hx : x ∈ tsupport f
      · simp only [v, Real.norm_eq_abs, NNReal.abs_eq, hx, indicator_of_mem]
        norm_cast
        exact thickenedIndicator_le_one _ _ _
      · simp only [v, Real.norm_eq_abs, NNReal.abs_eq, hx, not_false_eq_true, indicator_of_notMem]
        rw [thickenedIndicator_zero]
        · simp
        · simpa [image_eq_zero_of_notMem_tsupport hx] using (u_mem n).2.le
    · filter_upwards with x
      have T := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure
        (fun n ↦ (u_mem n).1) u_lim ({1} : Set ℝ)) (f x)
      simp only [thickenedIndicator_apply, closure_singleton] at T
      convert NNReal.tendsto_coe.2 T
      simp
  have M n : ∫ (x : G), v n (f x) ∂μ' = ∫ (x : G), v n (f x) ∂(haarScalarFactor μ' μ • μ) := by
    apply integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ (vf_cont n)
    apply h'f.comp_left
    simp only [v, thickenedIndicator_apply, NNReal.coe_eq_zero]
    rw [thickenedIndicatorAux_zero (u_mem n).1]
    · simp only [ENNReal.toNNReal_zero]
    · simpa using (u_mem n).2.le
  have I1 := I μ' (by infer_instance)
  simp_rw [M] at I1
  have J1 : ∫ (x : G), indicator {1} (fun _ ↦ (1 : ℝ)) (f x) ∂μ'
      = ∫ (x : G), indicator {1} (fun _ ↦ 1) (f x) ∂(haarScalarFactor μ' μ • μ) :=
    tendsto_nhds_unique I1 (I (haarScalarFactor μ' μ • μ) (by infer_instance))
  have J2 : μ'.real (f ⁻¹' {1})
      = (haarScalarFactor μ' μ • μ).real (f ⁻¹' {1}) := by
    have : (fun x ↦ indicator {1} (fun _ ↦ (1 : ℝ)) (f x)) =
        (fun x ↦ indicator (f ⁻¹' {1}) (fun _ ↦ (1 : ℝ)) x) := by
      ext x
      exact (indicator_comp_right f (s := ({1} : Set ℝ)) (g := (fun _ ↦ (1 : ℝ))) (x := x)).symm
    have mf : MeasurableSet (f ⁻¹' {1}) := (isClosed_singleton.preimage hf).measurableSet
    simpa only [this, mf, integral_indicator_const, smul_eq_mul, mul_one, Pi.smul_apply,
      nnreal_smul_coe_apply, ENNReal.toReal_mul, ENNReal.coe_toReal] using J1
  have C : IsCompact (f ⁻¹' {1}) := h'f.isCompact_preimage hf isClosed_singleton (by simp)
  rw [measureReal_eq_measureReal_iff C.measure_lt_top.ne C.measure_lt_top.ne] at J2
  simpa using J2

/-- If an invariant measure is inner regular, then it gives less mass to sets with compact closure
than any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which gives equality for any
set with compact closure. -/
@[to_additive smul_measure_isAddInvariant_le_of_isCompact_closure
/-- If an invariant measure is inner regular, then it gives less mass to sets with compact closure
than any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which gives equality for any
set with compact closure. -/]
lemma smul_measure_isMulInvariant_le_of_isCompact_closure [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ]
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    haarScalarFactor μ' μ • μ s ≤ μ' s := by
  apply le_of_forall_lt (fun r hr ↦ ?_)
  let ν := haarScalarFactor μ' μ • μ
  have : ν s ≠ ∞ := ((measure_mono subset_closure).trans_lt h's.measure_lt_top).ne
  obtain ⟨-, hf, ⟨f, f_cont, f_comp, rfl⟩, νf⟩ :
      ∃ K ⊆ s, (∃ f, Continuous f ∧ HasCompactSupport f ∧ K = f ⁻¹' {1}) ∧ r < ν K :=
    innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group ⟨hs, this⟩ r
      (by convert hr)
  calc
  r < ν (f ⁻¹' {1}) := νf
  _ = μ' (f ⁻¹' {1}) :=
    (measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport _ _ f_cont f_comp).symm
  _ ≤ μ' s := measure_mono hf

/-- If an invariant measure is inner regular, then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure, and removes the inner regularity assumption. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop
/-- If an invariant measure is inner regular, then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which works for any set with
compact closure, and removes the inner regularity assumption. -/]
lemma measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop
    [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ]
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  apply le_antisymm ?_ (smul_measure_isMulInvariant_le_of_isCompact_closure μ' μ hs h's)
  let ν := haarScalarFactor μ' μ • μ
  change μ' s ≤ ν s
  obtain ⟨⟨f, f_cont⟩, hf, -, f_comp, -⟩ : ∃ f : C(G, ℝ), EqOn f 1 (closure s) ∧ EqOn f 0 ∅
      ∧ HasCompactSupport f ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact h's isClosed_empty (disjoint_empty _)
  let t := f ⁻¹' {1}
  have t_closed : IsClosed t := isClosed_singleton.preimage f_cont
  have t_comp : IsCompact t := f_comp.isCompact_preimage f_cont isClosed_singleton (by simp)
  have st : s ⊆ t := (IsClosed.closure_subset_iff t_closed).mp hf
  have A : ν (t \ s) ≤ μ' (t \ s) := by
    apply smul_measure_isMulInvariant_le_of_isCompact_closure _ _ (t_closed.measurableSet.diff hs)
    exact t_comp.closure_of_subset diff_subset
  have B : μ' t = ν t :=
    measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport _ _ f_cont f_comp
  rwa [measure_diff st hs.nullMeasurableSet, measure_diff st hs.nullMeasurableSet, ← B,
    ENNReal.sub_le_sub_iff_left] at A
  · exact measure_mono st
  · exact t_comp.measure_lt_top.ne
  · exact ((measure_mono st).trans_lt t_comp.measure_lt_top).ne
  · exact ((measure_mono st).trans_lt t_comp.measure_lt_top).ne

/-- Given an invariant measure then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `haarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isMulInvariant_eq_smul_of_isCompact_closure`, which removes the
measurability assumption. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure_of_measurableSet
/-- Given an invariant measure then it gives the same mass to measurable sets with
compact closure as any other invariant measure, up to the scalar `addHaarScalarFactor μ' μ`.

Auxiliary lemma in the proof of the more general
`measure_isAddInvariant_eq_smul_of_isCompact_closure`, which removes the
measurability assumption. -/]
lemma measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {s : Set G} (hs : MeasurableSet s) (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν : Measure G := haar
  have A : μ' s = haarScalarFactor μ' ν • ν s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop μ' ν hs h's
  have B : μ s = haarScalarFactor μ ν • ν s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop μ ν hs h's
  rw [A, B, smul_smul, haarScalarFactor_eq_mul μ' μ ν]

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on compacts, they coincide in the following
sense: they give the same value to sets with compact closure, up to the multiplicative
constant `haarScalarFactor μ' μ`. -/
@[to_additive measure_isAddInvariant_eq_smul_of_isCompact_closure
/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on compacts, they coincide in the following
sense: they give the same value to sets with compact closure, up to the multiplicative
constant `addHaarScalarFactor μ' μ`. -/]
theorem measure_isMulInvariant_eq_smul_of_isCompact_closure [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {s : Set G} (h's : IsCompact (closure s)) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν := haarScalarFactor μ' μ • μ
  apply le_antisymm
  · calc
    μ' s ≤ μ' ((toMeasurable ν s) ∩ (closure s)) :=
      measure_mono <| subset_inter (subset_toMeasurable ν s) subset_closure
    _ = ν ((toMeasurable ν s) ∩ (closure s)) := by
      apply measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet _ _ _ _
      · exact (measurableSet_toMeasurable ν s).inter isClosed_closure.measurableSet
      · exact h's.closure_of_subset inter_subset_right
    _ ≤ ν (toMeasurable ν s) := measure_mono inter_subset_left
    _ = ν s := measure_toMeasurable s
  · calc
    ν s ≤ ν ((toMeasurable μ' s) ∩ (closure s)) :=
      measure_mono <| subset_inter (subset_toMeasurable μ' s) subset_closure
    _ = μ' ((toMeasurable μ' s) ∩ (closure s)) := by
      apply (measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet _ _ _ _).symm
      · exact (measurableSet_toMeasurable μ' s).inter isClosed_closure.measurableSet
      · exact h's.closure_of_subset inter_subset_right
    _ ≤ μ' (toMeasurable μ' s) := measure_mono inter_subset_left
    _ = μ' s := measure_toMeasurable s

/-- **Uniqueness of Haar measures**:
Two Haar measures on a compact group coincide up to a multiplicative factor. -/
@[to_additive isAddInvariant_eq_smul_of_compactSpace]
lemma isMulInvariant_eq_smul_of_compactSpace [CompactSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsMulLeftInvariant μ'] [IsFiniteMeasureOnCompacts μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s _hs
  exact measure_isMulInvariant_eq_smul_of_isCompact_closure _ _ isClosed_closure.isCompact

@[to_additive]
instance (priority := 100) instInnerRegularOfIsHaarMeasureOfCompactSpace
    [CompactSpace G] (μ : Measure G) [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] :
    InnerRegular μ := by
  rw [isMulInvariant_eq_smul_of_compactSpace μ haar]
  infer_instance

@[to_additive]
instance (priority := 100) instRegularOfIsHaarMeasureOfCompactSpace
    [CompactSpace G] (μ : Measure G) [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] :
    Regular μ := by
  rw [isMulInvariant_eq_smul_of_compactSpace μ haar]
  infer_instance

/-- **Uniqueness of Haar measures**:
Two Haar measures which are probability measures coincide. -/
@[to_additive]
lemma isHaarMeasure_eq_of_isProbabilityMeasure [LocallyCompactSpace G] (μ' μ : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [IsHaarMeasure μ] [IsHaarMeasure μ'] :
    μ' = μ := by
  have : CompactSpace G := by
    by_contra H
    rw [not_compactSpace_iff] at H
    simpa using measure_univ_of_isMulLeftInvariant μ
  have A s : μ' s = haarScalarFactor μ' μ • μ s :=
    measure_isMulInvariant_eq_smul_of_isCompact_closure _ _ isClosed_closure.isCompact
  have Z := A univ
  simp only [measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.one_eq_coe] at Z
  ext s _hs
  simp [A s, ← Z]

/-!
### Uniqueness of measure of open sets

Two Haar measures give the same measure to open sets (or more generally to sets which are everywhere
positive), up to the scalar `haarScalarFactor μ' μ `.
-/

@[to_additive measure_isAddHaarMeasure_eq_smul_of_isEverywherePos]
theorem measure_isHaarMeasure_eq_smul_of_isEverywherePos [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ']
    {s : Set G} (hs : MeasurableSet s) (h's : IsEverywherePos μ s) :
    μ' s = haarScalarFactor μ' μ • μ s := by
  let ν := haarScalarFactor μ' μ • μ
  change μ' s = ν s
  /- Fix a compact neighborhood `k` of the identity, and consider a maximal disjoint family `m` of
  sets `x • k` centered at points in `s`. Then `s` is covered by the sets `x • (k * k⁻¹)` by
  maximality. If the family is countable, then since `μ'` and `ν` coincide in compact sets, and
  the measure of a countable disjoint union is the sum of the measures, we get `μ' s = ν s`.
  Otherwise, the family is uncountable, and each intersection with `s` has positive measure by
  the everywhere positivity assumption, so `ν s = ∞`, and `μ' s = ∞` in the same way. -/
  obtain ⟨k, k_comp, k_closed, k_mem⟩ : ∃ k, IsCompact k ∧ IsClosed k ∧ k ∈ 𝓝 (1 : G) := by
    rcases exists_compact_mem_nhds (1 : G) with ⟨k, hk, hmem⟩
    exact ⟨closure k, hk.closure, isClosed_closure, mem_of_superset hmem subset_closure⟩
  have one_k : 1 ∈ k := mem_of_mem_nhds k_mem
  let A : Set (Set G) := {t | t ⊆ s ∧ PairwiseDisjoint t (fun x ↦ x • k)}
  obtain ⟨m, m_max⟩ : ∃ m, Maximal (· ∈ A) m := by
    apply zorn_subset
    intro c cA hc
    refine ⟨⋃ a ∈ c, a, ⟨?_, ?_⟩, ?_⟩
    · simp only [iUnion_subset_iff]
      intro a ac x hx
      simp only [A, subset_def, mem_setOf_eq] at cA
      exact (cA _ ac).1 x hx
    · rintro x hx y hy hxy
      simp only [mem_iUnion, exists_prop] at hx hy
      rcases hx with ⟨a, ac, xa⟩
      rcases hy with ⟨b, bc, yb⟩
      obtain ⟨m, mc, am, bm⟩ : ∃ m ∈ c, a ⊆ m ∧ b ⊆ m := hc.directedOn _ ac _ bc
      exact (cA mc).2 (am xa) (bm yb) hxy
    · intro a ac
      exact subset_biUnion_of_mem (u := id) ac
  obtain ⟨hms : m ⊆ s, hdj : PairwiseDisjoint m (fun x ↦ x • k)⟩ := m_max.prop
  have sm : s ⊆ ⋃ x ∈ m, x • (k * k⁻¹) := by
    intro y hy
    by_cases h'y : m ∪ {y} ∈ A
    · have ym : y ∈ m := m_max.mem_of_prop_insert (by simpa using h'y)
      have : y ∈ y • (k * k⁻¹) := by
        simpa using mem_leftCoset y (Set.mul_mem_mul one_k (Set.inv_mem_inv.mpr one_k))
      exact mem_biUnion ym this
    · obtain ⟨x, xm, -, z, zy, zx⟩ : ∃ x ∈ m, y ≠ x ∧ ∃ z, z ∈ y • k ∧ z ∈ x • k := by
        simpa [A, hms, hy, insert_subset_iff, pairwiseDisjoint_insert, hdj, not_disjoint_iff]
          using h'y
      have : y ∈ x • (k * k⁻¹) := by
        rw [show y = x * ((x⁻¹ * z) * (y⁻¹ * z)⁻¹) by group]
        have : (x⁻¹ * z) * (y⁻¹ * z)⁻¹ ∈ k * k⁻¹ := Set.mul_mem_mul ((mem_leftCoset_iff x).mp zx)
          (Set.inv_mem_inv.mpr ((mem_leftCoset_iff y).mp zy))
        exact mem_leftCoset x this
      exact mem_biUnion xm this
  rcases eq_empty_or_nonempty m with rfl | hm
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, subset_empty_iff] at sm
    simp [sm]
  by_cases h'm : Set.Countable m
  · rcases h'm.exists_eq_range hm with ⟨f, rfl⟩
    have M i : MeasurableSet (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) i) := by
      apply MeasurableSet.disjointed (fun j ↦ hs.inter ?_)
      have : IsClosed (k • k⁻¹) := IsClosed.smul_left_of_isCompact k_closed.inv k_comp
      exact (IsClosed.smul this (f j)).measurableSet
    simp only [mem_range, iUnion_exists, iUnion_iUnion_eq'] at sm
    have s_eq : s = ⋃ n, s ∩ (f n • (k * k⁻¹)) := by rwa [← inter_iUnion, eq_comm, inter_eq_left]
    have I : μ' s = ∑' n, μ' (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) n) := by
      rw [← measure_iUnion (disjoint_disjointed _) M, iUnion_disjointed, ← s_eq]
    have J : ν s = ∑' n, ν (disjointed (fun n ↦ s ∩ f n • (k * k⁻¹)) n) := by
      rw [← measure_iUnion (disjoint_disjointed _) M, iUnion_disjointed, ← s_eq]
    rw [I, J]
    congr with n
    apply measure_isMulInvariant_eq_smul_of_isCompact_closure
    have : IsCompact (f n • (k * k⁻¹)) := IsCompact.smul (f n) (k_comp.mul k_comp.inv)
    exact this.closure_of_subset <| (disjointed_subset _ _).trans inter_subset_right
  · have H : ∀ (ρ : Measure G), IsEverywherePos ρ s → ρ s = ∞ := by
      intro ρ hρ
      have M : ∀ (i : ↑m), MeasurableSet (s ∩ (i : G) • k) :=
        fun i ↦ hs.inter (IsClosed.smul k_closed _).measurableSet
      contrapose! h'm
      have : ∑' (x : m), ρ (s ∩ ((x : G) • k)) < ∞ := by
        apply lt_of_le_of_lt (MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint _ M _) _
        · have I : PairwiseDisjoint m fun x ↦ s ∩ x • k :=
            hdj.mono (fun x ↦ inter_subset_right)
          exact I.on_injective Subtype.val_injective (fun x ↦ x.2)
        · exact lt_of_le_of_lt (measure_mono (by simp [inter_subset_left])) h'm.lt_top
      have C : Set.Countable (support fun (i : m) ↦ ρ (s ∩ (i : G) • k)) :=
        Summable.countable_support_ennreal this.ne
      have : support (fun (i : m) ↦ ρ (s ∩ (i : G) • k)) = univ := by
        refine eq_univ_iff_forall.2 fun i ↦ ?_
        refine ne_of_gt (hρ (i : G) (hms i.2) _ ?_)
        exact inter_mem_nhdsWithin s (by simpa)
      rw [this] at C
      have : Countable m := countable_univ_iff.mp C
      exact to_countable m
    have Hν : IsEverywherePos ν s :=
      h's.smul_measure_nnreal (haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
    have Hμ' : IsEverywherePos μ' s := by
      apply Hν.of_forall_exists_nhds_eq (fun x _hx ↦ ?_)
      obtain ⟨t, t_comp, t_mem⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x := exists_compact_mem_nhds x
      refine ⟨t, t_mem, fun u hu ↦ ?_⟩
      apply measure_isMulInvariant_eq_smul_of_isCompact_closure
      exact t_comp.closure_of_subset hu
    rw [H ν Hν, H μ' Hμ']

/-- **Uniqueness of Haar measures**:
Given two Haar measures, they coincide in the following sense: they give the same value to open
sets, up to the multiplicative constant `haarScalarFactor μ' μ`. -/
@[to_additive measure_isAddHaarMeasure_eq_smul_of_isOpen
/-- **Uniqueness of Haar measures**:
Given two additive Haar measures, they coincide in the following sense: they give the same value to
open sets, up to the multiplicative constant `addHaarScalarFactor μ' μ`. -/]
theorem measure_isHaarMeasure_eq_smul_of_isOpen [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] {s : Set G} (hs : IsOpen s) :
    μ' s = haarScalarFactor μ' μ • μ s :=
  measure_isHaarMeasure_eq_smul_of_isEverywherePos μ' μ hs.measurableSet hs.isEverywherePos

/-!
### Uniqueness of Haar measure under regularity assumptions.
-/

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite on
compacts and inner regular for finite measure sets with respect to compact sets,
they coincide in the following sense: they give the same value to finite measure sets,
up to a multiplicative constant. -/
@[to_additive]
lemma measure_isMulLeftInvariant_eq_smul_of_ne_top [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ'] {s : Set G}
    (hs : μ s ≠ ∞) (h's : μ' s ≠ ∞) : μ' s = haarScalarFactor μ' μ • μ s := by
  /- We know that the measures integrate in the same way continuous compactly supported functions,
  up to the factor `c = haarScalarFactor μ' μ`. -/
  let c := haarScalarFactor μ' μ
  /- By regularity, every measurable set of finite measure may be approximated by compact sets.
  Therefore, the measures coincide on measurable sets of finite measure. -/
  have B : ∀ s, MeasurableSet s → μ s < ∞ → μ' s < ∞ → μ' s = (c • μ) s := by
    intro s s_meas hs h's
    have : (c • μ) s ≠ ∞ := by simp [ENNReal.mul_eq_top, hs.ne]
    rw [s_meas.measure_eq_iSup_isCompact_of_ne_top h's.ne,
        s_meas.measure_eq_iSup_isCompact_of_ne_top this]
    congr! 4 with K _Ks K_comp
    exact measure_isMulInvariant_eq_smul_of_isCompact_closure μ' μ K_comp.closure
  /- Finally, replace an arbitrary finite measure set with a measurable version, and use the
  version for measurable sets. -/
  let t := toMeasurable μ' s ∩ toMeasurable μ s
  have st : s ⊆ t := subset_inter (subset_toMeasurable μ' s) (subset_toMeasurable μ s)
  have mu'_t : μ' t = μ' s := by
    apply le_antisymm
    · exact (measure_mono inter_subset_left).trans (measure_toMeasurable s).le
    · exact measure_mono st
  have mu_t : μ t = μ s := by
    apply le_antisymm
    · exact (measure_mono inter_subset_right).trans (measure_toMeasurable s).le
    · exact measure_mono st
  simp only [← mu'_t, ← mu_t, nnreal_smul_coe_apply]
  apply B
  · exact (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
  · exact mu_t.le.trans_lt hs.lt_top
  · exact mu'_t.le.trans_lt h's.lt_top

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and inner regular, they coincide up to a multiplicative constant. -/
@[to_additive isAddLeftInvariant_eq_smul_of_innerRegular]
lemma isMulLeftInvariant_eq_smul_of_innerRegular [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [InnerRegular μ] [InnerRegular μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  ext s hs
  rw [hs.measure_eq_iSup_isCompact, hs.measure_eq_iSup_isCompact]
  congr! 4 with K _Ks K_comp
  exact measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ K_comp.measure_lt_top.ne
    K_comp.measure_lt_top.ne

/-- **Uniqueness of left-invariant measures**:
Given two left-invariant measures which are finite
on compacts and regular, they coincide up to a multiplicative constant. -/
@[to_additive isAddLeftInvariant_eq_smul_of_regular]
lemma isMulLeftInvariant_eq_smul_of_regular [LocallyCompactSpace G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    [Regular μ] [Regular μ'] :
    μ' = haarScalarFactor μ' μ • μ := by
  have A : ∀ U, IsOpen U → μ' U = (haarScalarFactor μ' μ • μ) U := by
    intro U hU
    rw [hU.measure_eq_iSup_isCompact, hU.measure_eq_iSup_isCompact]
    congr! 4 with K _KU K_comp
    exact measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ K_comp.measure_lt_top.ne
      K_comp.measure_lt_top.ne
  ext s _hs
  rw [s.measure_eq_iInf_isOpen, s.measure_eq_iInf_isOpen]
  congr! 4 with U _sU U_open
  exact A U U_open

/-- **Uniqueness of left-invariant measures**:
Two Haar measures coincide up to a multiplicative constant in a second countable group. -/
@[to_additive isAddLeftInvariant_eq_smul]
lemma isMulLeftInvariant_eq_smul [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] :
    μ' = haarScalarFactor μ' μ • μ :=
  isMulLeftInvariant_eq_smul_of_regular μ' μ
  -- one could use as well `isMulLeftInvariant_eq_smul_of_innerRegular`, as in a
  -- second countable topological space all Haar measures are regular and inner regular


/-- An invariant σ-finite measure is absolutely continuous with respect to a Haar measure in a
second countable group. -/
@[to_additive
/-- An invariant measure is absolutely continuous with respect to an additive Haar measure. -/]
theorem absolutelyContinuous_isHaarMeasure [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ ν : Measure G)
    [SigmaFinite μ] [IsMulLeftInvariant μ] [IsHaarMeasure ν] : μ ≪ ν := by
  have K : PositiveCompacts G := Classical.arbitrary _
  have h : haarMeasure K = (haarScalarFactor (haarMeasure K) ν : ℝ≥0∞) • ν :=
    isMulLeftInvariant_eq_smul (haarMeasure K) ν
  rw [haarMeasure_unique μ K, h, smul_smul]
  exact smul_absolutelyContinuous

/-- A continuous surjective monoid homomorphism of topological groups with compact codomain
is measure preserving, provided that the Haar measures on the domain and on the codomain
have the same total mass.
-/
@[to_additive
  /-- A continuous surjective additive monoid homomorphism of topological groups with compact
  codomain is measure preserving, provided that the Haar measures on the domain and on the codomain
  have the same total mass. -/]
theorem _root_.MonoidHom.measurePreserving
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure G} [IsHaarMeasure μ] {ν : Measure H} [IsHaarMeasure ν]
    {f : G →* H} (hcont : Continuous f) (hsurj : Surjective f) (huniv : μ univ = ν univ) :
    MeasurePreserving f μ ν where
  measurable := hcont.measurable
  map_eq := by
    have : IsFiniteMeasure μ := ⟨by rw [huniv]; apply measure_lt_top⟩
    have : (μ.map f).IsHaarMeasure := isHaarMeasure_map_of_isFiniteMeasure μ f hcont hsurj
    set C : ℝ≥0 := haarScalarFactor (μ.map f) ν
    have hC : μ.map f = C • ν := isMulLeftInvariant_eq_smul_of_innerRegular _ _
    suffices C = 1 by rwa [this, one_smul] at hC
    have : C * ν univ = 1 * ν univ := by
      rw [one_mul, ← smul_eq_mul, ← ENNReal.smul_def, ← smul_apply, ← hC,
        map_apply hcont.measurable .univ, preimage_univ, huniv]
    rwa [ENNReal.mul_left_inj (NeZero.ne _) (measure_ne_top _ _), ENNReal.coe_eq_one] at this

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]

/-- Any regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive
/-- Any regular additive Haar measure is invariant under negation in an abelian group. -/]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_regular
    [LocallyCompactSpace G] [Regular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id]
  have K : PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

/-- Any inner regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive
/-- Any regular additive Haar measure is invariant under negation in an abelian group. -/]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_innerRegular
    [LocallyCompactSpace G] [InnerRegular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ, hc, Measure.map_smul, ← inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id]
  have K : PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

@[to_additive]
theorem measurePreserving_zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) :
    MeasurePreserving (fun g : G => g ^ n) μ μ :=
  (zpowGroupHom n).measurePreserving (μ := μ) (continuous_zpow n)
    (RootableBy.surjective_pow G ℤ hn) rfl

@[to_additive]
theorem MeasurePreserving.zpow [CompactSpace G] [RootableBy G ℤ]
    {n : ℤ} (hn : n ≠ 0) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x ^ n) μ' μ :=
  (measurePreserving_zpow μ hn).comp hf

end CommGroup

section DistribMulAction
variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [MeasurableSpace A]
  [TopologicalSpace A] [BorelSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] {μ ν : Measure A} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {g : G}

variable (μ ν) in
lemma addHaarScalarFactor_domSMul (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ ν := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have int_f_ne_zero : ∫ x, f x ∂g • ν ≠ 0 :=
    (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'
  apply NNReal.coe_injective
  rw [addHaarScalarFactor_eq_integral_div (g • μ) (g • ν) f_cont f_comp int_f_ne_zero,
    integral_domSMul, integral_domSMul]
  refine (addHaarScalarFactor_eq_integral_div _ _ (by fun_prop) ?_ ?_).symm
  · exact f_comp.comp_isClosedEmbedding (Homeomorph.smul _).isClosedEmbedding
  · rw [← integral_domSMul]
    exact (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'

variable (μ) in
lemma addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) :
    addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_domSMul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

variable (μ) in
lemma addHaarScalarFactor_smul_congr' (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) μ = addHaarScalarFactor (g • ν) ν := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_domSMul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

end DistribMulAction
end Measure

end MeasureTheory
