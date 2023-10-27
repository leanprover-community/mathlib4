/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Uniqueness of Haar measure in locally compact groups

In a locally compact group, we prove that two left-invariant measures which are finite on compact
sets give the same value to the integral of continuous compactly supported functions, in
`integral_mulLeftInvariant_unique_of_hasCompactSupport`. From this, we deduce various uniqueness
statements for left invariant measures (up to scalar multiplication):
* `measure_mulLeftInvariant_unique_of_ne_top`: two left-invariant measures which are inner regular
  for finite measure sets with respect to compact sets give the same measure to compact sets.
* `mulLeftInvariant_unique_of_innerRegular`: two left invariant measure which are
  inner regular coincide.
* `mulLeftInvariant_unique_of_regular`: two left invariant measure which are
  regular coincide.
* `mulLeftInvariant_unique_of_isProbabilityMeasure`: two left-invariant probability measures which
  are inner regular for finite measure sets with respect to compact sets coincide.

In general, uniqueness statements for Haar measures in the literature make some assumption of
regularity, either regularity or inner regularity. We have tried to minimize the assumptions in the
theorems above (notably in `integral_mulLeftInvariant_unique_of_hasCompactSupport`, which doesn't
make any regularity assumption), and cover the different results that exist in the literature.

The main result is `integral_mulLeftInvariant_unique_of_hasCompactSupport`, and the other ones
follow readily from this one by using continuous compactly supported functions to approximate
characteristic functions of set.

To prove `integral_mulLeftInvariant_unique_of_hasCompactSupport`, we use a change of variables
to express integrals with respect to a left-invariant measure as integrals with respect to a given
right-invariant measure (with a suitable density function). The uniqueness readily follows.
-/

open MeasureTheory Filter Set TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal


lemma _root_.IsCompact.measure_eq_biInf_integral_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : Set X} (hk : IsCompact k)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]
    [LocallyCompactSpace X] [RegularSpace X] :
    μ k = ⨅ (f : X → ℝ) (_ : Continuous f) (_ : HasCompactSupport f) (_ : EqOn f 1 k)
      (_ : 0 ≤ f), ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact eventually_of_forall f_nonneg
    · exact fun x hx ↦ by simp [fk hx]
  · apply le_of_forall_lt' (fun r hr ↦ ?_)
    simp only [iInf_lt_iff, exists_prop, exists_and_left]
    obtain ⟨U, kU, U_open, mu_U⟩ : ∃ U, k ⊆ U ∧ IsOpen U ∧ μ U < r :=
      hk.exists_isOpen_lt_of_lt r hr
    obtain ⟨⟨f, f_cont⟩, fk, fU, f_comp, f_range⟩ : ∃ (f : C(X, ℝ)), EqOn f 1 k ∧ EqOn f 0 Uᶜ
        ∧ HasCompactSupport f ∧ ∀ (x : X), f x ∈ Icc 0 1 := exists_continuous_one_zero_of_isCompact
      hk U_open.isClosed_compl (disjoint_compl_right_iff_subset.mpr kU)
    refine ⟨f, f_cont, f_comp, fk, fun x ↦ (f_range x).1, ?_⟩
    exact (integral_le_measure (fun x _hx ↦ (f_range x).2) (fun x hx ↦ (fU hx).le)).trans_lt mu_U


namespace MeasureTheory

section

variable {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

@[to_additive]
lemma continuous_integral_apply_inv_mul
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
      refine ⟨p, p⁻¹ * x, hp, ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

@[to_additive]
lemma integral_mulLeftInvariant_mulRightInvariant_combo
    {μ ν : Measure G} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [IsMulLeftInvariant μ] [IsMulRightInvariant ν] [IsOpenPosMeasure ν]
    {f g : G → ℝ} (hf : Continuous f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (h'g : HasCompactSupport g) (g_nonneg : 0 ≤ g) {x₀ : G} (g_pos : g x₀ ≠ 0) :
    ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ := by
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
    congr with x; rw [mul_assoc, inv_mul_cancel (D_pos x).ne', mul_one]
  _ = ∫ x, (∫ y, f x * (D x)⁻¹ * g (y⁻¹ * x) ∂ν) ∂μ := by simp_rw [integral_mul_left]
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
        have M'_comp : IsCompact (closure M) := M_comp.closure_of_group
        have : ∀ (p : G × G), p ∉ K ×ˢ closure M → f p.1 * (D p.1)⁻¹ * g (p.2⁻¹ * p.1) = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ K; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : g (y⁻¹ * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [mem_image, mem_prod, Prod.exists]
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
        have M'_comp : IsCompact (closure M) := M_comp.closure_of_group
        have : ∀ (p : G × G), p ∉ L ×ˢ closure M →
            f (p.2 * p.1) * (D (p.2 * p.1))⁻¹ * g p.1 = 0 := by
          rintro ⟨x, y⟩ hxy
          by_cases H : x ∈ L; swap
          · simp [image_eq_zero_of_nmem_tsupport H]
          have : f (y * x) = 0 := by
            apply image_eq_zero_of_nmem_tsupport
            contrapose! hxy
            simp only [mem_prod, H, true_and]
            apply subset_closure
            simp only [mem_image, mem_prod, Prod.exists]
            refine ⟨y * x, x, ⟨hxy, H⟩, by group⟩
          simp [this]
        apply HasCompactSupport.intro' (L_comp.prod M'_comp) ?_ this
        exact (isClosed_tsupport g).prod isClosed_closure
  _ = ∫ x, (∫ y, f y * (D y)⁻¹ ∂ν) * g x ∂μ := by
      simp_rw [integral_mul_right]
      congr with x
      conv_rhs => rw [← integral_mul_right_eq_self _ x]
  _ = (∫ y, f y * (D y)⁻¹ ∂ν) * ∫ x, g x ∂μ := integral_mul_left _ _

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite on
compacts, they coincide in the following sense: they give the same value to the integral of
continuous compactly supported functions, up to a multiplicative constant. -/
@[to_additive]
lemma integral_mulLeftInvariant_unique_of_hasCompactSupport
    (μ μ' : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ] :
    ∃ (c : ℝ≥0), ∀ (f : G → ℝ), Continuous f → HasCompactSupport f →
      ∫ x, f x ∂μ' = ∫ x, f x ∂(c • μ) := by
  -- The group has to be locally compact, otherwise all integrals vanish and the result is trivial.
  by_cases H : LocallyCompactSpace G; swap
  · refine ⟨0, fun f f_cont f_comp ↦ ?_⟩
    rcases f_comp.eq_zero_or_locallyCompactSpace_of_group f_cont with hf|hf
    · simp [hf]
    · exact (H hf).elim
  -- Fix some nonzero continuous function with compact support `g`.
  obtain ⟨g, g_cont, g_comp, g_nonneg, g_one⟩ :
      ∃ (g : G → ℝ), Continuous g ∧ HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := by
    rcases exists_compact_mem_nhds (1 : G) with ⟨k, hk, k_mem⟩
    rcases exists_continuous_one_zero_of_isCompact hk isClosed_empty (disjoint_empty k)
      with ⟨⟨g, g_cont⟩, gk, -, g_comp, hg⟩
    refine ⟨g, g_cont, g_comp, fun x ↦ (hg x).1, ?_⟩
    have := gk (mem_of_mem_nhds k_mem)
    simp only [ContinuousMap.coe_mk, Pi.one_apply] at this
    simp [this]
  have int_g_pos : 0 < ∫ x, g x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg g_nonneg _).2
    · exact IsOpen.measure_pos μ g_cont.isOpen_support ⟨1, g_one⟩
    · exact g_cont.integrable_of_hasCompactSupport g_comp
  -- The proportionality constant we are looking for will be the ratio of the integrals of `g`
  -- with respect to `μ'` and `μ`.
  let c : ℝ := (∫ x, g x ∂μ) ⁻¹ * (∫ x, g x ∂μ')
  have c_nonneg : 0 ≤ c :=
    mul_nonneg (inv_nonneg.2 (integral_nonneg g_nonneg)) (integral_nonneg g_nonneg)
  refine ⟨⟨c, c_nonneg⟩, fun f f_cont f_comp ↦ ?_⟩
  /- use the lemma `integral_mulLeftInvariant_mulRightInvariant_combo` for `μ` and then `μ'`
  to reexpress the integral of `f` as the integral of `g` times a factor which only depends
  on a right-invariant measure `ν`. We use `ν = μ.inv` for convenience. -/
  let ν := μ.inv
  have A : ∫ x, f x ∂μ = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ :=
    integral_mulLeftInvariant_mulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  rw [← mul_inv_eq_iff_eq_mul₀ int_g_pos.ne'] at A
  have B : ∫ x, f x ∂μ' = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ' :=
    integral_mulLeftInvariant_mulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  /- Since the `ν`-factor is the same for `μ` and `μ'`, this gives the result. -/
  rw [← A, mul_assoc, mul_comm] at B
  simp only [B, integral_smul_nnreal_measure]
  rfl

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite on
compacts and inner regular for finite measure sets with respect to compact sets,
they coincide in the following sense: they give the same value to finite measure sets,
up to a multiplicative constant. -/
@[to_additive]
lemma measure_mulLeftInvariant_unique_of_ne_top
    (μ μ' : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ'] :
    ∃ (c : ℝ≥0), ∀ (s : Set G), μ s < ∞ → μ' s < ∞ → μ' s = (c • μ) s := by
  /- We know that the measures integrate in the same way continuous compactly supported functions,
  up to a constant `c`. We will use this constant `c`. -/
  rcases integral_mulLeftInvariant_unique_of_hasCompactSupport μ μ' with ⟨c, hc⟩
  refine ⟨c, fun s hs h's ↦ ?_⟩
  /- By regularity, every compact set may be approximated by a continuous compactly supported
  function. Therefore, the measures coincide on compact sets. -/
  have A : ∀ k, IsCompact k → μ' k = (c • μ) k := by
    intro k hk
    rw [hk.measure_eq_biInf_integral_hasCompactSupport μ',
        hk.measure_eq_biInf_integral_hasCompactSupport (c • μ)]
    congr! 7 with f f_cont f_comp _fk _f_nonneg
    exact hc f f_cont f_comp
  /- By regularity, every measurable set of finite measure may be approximated by compactsets.
  Therefore, the measures coincide on measurable sets of finite measure. -/
  have B : ∀ s, MeasurableSet s → μ s < ∞ → μ' s < ∞ → μ' s = (c • μ) s := by
    intro s s_meas hs h's
    have : (c • μ) s ≠ ∞ := by simp [ENNReal.mul_eq_top, hs.ne]
    rw [s_meas.measure_eq_iSup_isCompact_of_ne_top h's.ne,
        s_meas.measure_eq_iSup_isCompact_of_ne_top this]
    congr! 4 with K _Ks K_comp
    exact A K K_comp
  /- Finally, replace an arbitrary finite measure set with a measurable version, and use the
  version for measurable sets. -/
  let t := toMeasurable μ' s ∩ toMeasurable μ s
  have st : s ⊆ t := subset_inter (subset_toMeasurable μ' s) (subset_toMeasurable μ s)
  have mu'_t : μ' t = μ' s := by
    apply le_antisymm
    · exact (measure_mono (inter_subset_left _ _)).trans (measure_toMeasurable s).le
    · exact measure_mono st
  have mu_t : μ t = μ s := by
    apply le_antisymm
    · exact (measure_mono (inter_subset_right _ _)).trans (measure_toMeasurable s).le
    · exact measure_mono st
  simp only [← mu'_t, smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, ← mu_t,
    nnreal_smul_coe_apply]
  apply B
  · exact (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
  · exact mu_t.le.trans_lt hs
  · exact mu'_t.le.trans_lt h's

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite
on compacts and inner regular, they coincide up to a multiplicative constant. -/
@[to_additive]
lemma mulLeftInvariant_unique_of_innerRegular
    (μ μ' : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [InnerRegular μ] [InnerRegular μ'] :
    ∃ (c : ℝ≥0), μ' = c • μ := by
  rcases measure_mulLeftInvariant_unique_of_ne_top μ μ' with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext s hs
  rw [hs.measure_eq_iSup_isCompact, hs.measure_eq_iSup_isCompact]
  congr! 4 with K _Ks K_comp
  exact hc K K_comp.measure_lt_top K_comp.measure_lt_top

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite
on compacts and inner regular, they coincide up to a multiplicative constant. -/
@[to_additive]
lemma mulLeftInvariant_unique_of_regular
    (μ μ' : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [Regular μ] [Regular μ'] :
    ∃ (c : ℝ≥0), μ' = c • μ := by
  rcases measure_mulLeftInvariant_unique_of_ne_top μ μ' with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have A : ∀ U, IsOpen U → μ' U = (c • μ) U := by
    intro U hU
    rw [hU.measure_eq_iSup_isCompact, hU.measure_eq_iSup_isCompact]
    congr! 4 with K _KU K_comp
    exact hc K K_comp.measure_lt_top K_comp.measure_lt_top
  ext s _hs
  rw [s.measure_eq_iInf_isOpen, s.measure_eq_iInf_isOpen]
  congr! 4 with U _sU U_open
  exact A U U_open

/-- **Uniqueness of left-invariant measures**: Given two left-invariant probability measures which
are inner regular for finite measure sets with respect to compact sets, they coincide. -/
@[to_additive]
lemma mulLeftInvariant_unique_of_isProbabilityMeasure
    (μ μ' : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] : μ' = μ := by
  have : InnerRegular μ := InnerRegularCompactLTTop.innerRegular_of_finiteMeasure
  have : InnerRegular μ' := InnerRegularCompactLTTop.innerRegular_of_finiteMeasure
  have : IsOpenPosMeasure μ :=
    isOpenPosMeasure_of_mulLeftInvariant_of_innerRegular (IsProbabilityMeasure.ne_zero μ)
  rcases mulLeftInvariant_unique_of_innerRegular μ μ' with ⟨c, hc⟩
  have : ((c : ℝ≥0∞) • μ) univ = μ' univ := by rw [hc]; rfl
  simp only [smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, measure_univ, smul_eq_mul,
    mul_one, ENNReal.coe_eq_one] at this
  simp [hc, this]

theorem isHaarMeasure_eq_smul_isHaarMeasure (μ ν : Measure G)
    [IsHaarMeasure μ] [IsHaarMeasure ν] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by


end

namespace Measure
section SecondCountable

variable {G : Type*} [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [SecondCountableTopology G]

/-lemma foo (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ] : Regular μ := by
  exact?


#exit-/

/-- The Haar measure is unique up to scaling. More precisely: every σ-finite left invariant measure
  is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`). -/
@[to_additive
"The additive Haar measure is unique up to scaling. More precisely: every σ-finite left invariant
measure is a scalar multiple of the additive Haar measure. This is slightly weaker than assuming
that `μ` is an additive Haar measure (in particular we don't require `μ ≠ 0`)."]
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ :=
  (measure_eq_div_smul μ (haarMeasure K₀) K₀.isCompact.measurableSet
        (measure_pos_of_nonempty_interior _ K₀.interior_nonempty).ne'
        K₀.isCompact.measure_lt_top.ne).trans
    (by rw [haarMeasure_self, div_one])
#align measure_theory.measure.haar_measure_unique MeasureTheory.Measure.haarMeasure_unique
#align measure_theory.measure.add_haar_measure_unique MeasureTheory.Measure.addHaarMeasure_unique

/-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the Haar measure
defined by `K₀` iff `μ K₀ = 1`. -/
@[to_additive]
theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1 :=
  ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive
"To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite on
some compact set with non-empty interior."]
theorem regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
    {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ K ≠ ∞) : Regular μ := by
  rw [haarMeasure_unique μ ⟨⟨K, hK⟩, h2K⟩]; exact Regular.smul hμK
#align measure_theory.measure.regular_of_is_mul_left_invariant MeasureTheory.Measure.regular_of_isMulLeftInvariant
#align measure_theory.measure.regular_of_is_add_left_invariant MeasureTheory.Measure.regular_of_isAddLeftInvariant

@[to_additive isAddHaarMeasure_eq_smul_isAddHaarMeasure]
theorem isHaarMeasure_eq_smul_isHaarMeasure [LocallyCompactSpace G] (μ ν : Measure G)
    [IsHaarMeasure μ] [IsHaarMeasure ν] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  have K : PositiveCompacts G := Classical.arbitrary _
  have νpos : 0 < ν K := measure_pos_of_nonempty_interior _ K.interior_nonempty
  have νne : ν K ≠ ∞ := K.isCompact.measure_lt_top.ne
  refine' ⟨μ K / ν K, _, _, _⟩
  · simp only [νne, (μ.measure_pos_of_nonempty_interior K.interior_nonempty).ne', Ne.def,
      ENNReal.div_eq_zero_iff, not_false_iff, or_self_iff]
  · simp only [div_eq_mul_inv, νpos.ne', (K.isCompact.measure_lt_top (μ := μ)).ne, or_self_iff,
      ENNReal.inv_eq_top, ENNReal.mul_eq_top, Ne.def, not_false_iff, and_false_iff,
      false_and_iff]
  · calc
      μ = μ K • haarMeasure K := haarMeasure_unique μ K
      _ = (μ K / ν K) • ν K • haarMeasure K := by
        rw [smul_smul, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel νpos.ne' νne, mul_one]
      _ = (μ K / ν K) • ν := by rw [← haarMeasure_unique ν K]
#align measure_theory.measure.is_haar_measure_eq_smul_is_haar_measure MeasureTheory.Measure.isHaarMeasure_eq_smul_isHaarMeasure
#align measure_theory.measure.is_add_haar_measure_eq_smul_is_add_haar_measure MeasureTheory.Measure.isAddHaarMeasure_eq_smul_isAddHaarMeasure

/-- An invariant measure is absolutely continuous with respect to a Haar measure. -/
@[to_additive
"An invariant measure is absolutely continuous with respect to an additive Haar measure. "]
theorem absolutelyContinuous_isHaarMeasure [LocallyCompactSpace G] (μ ν : Measure G)
    [SigmaFinite μ] [IsMulLeftInvariant μ] [IsHaarMeasure ν] : μ ≪ ν := by
  have K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨c, -, -, h⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ haarMeasure K = c • ν :=
    isHaarMeasure_eq_smul_isHaarMeasure _ _
  rw [haarMeasure_unique μ K, h, smul_smul]
  exact AbsolutelyContinuous.smul (Eq.absolutelyContinuous rfl) _

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 90) regular_of_isHaarMeasure [LocallyCompactSpace G] (μ : Measure G)
    [IsHaarMeasure μ] : Regular μ := by
  have K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨c, _, ctop, hμ⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • haarMeasure K :=
    isHaarMeasure_eq_smul_isHaarMeasure μ _
  rw [hμ]
  exact Regular.smul ctop
#align measure_theory.measure.regular_of_is_haar_measure MeasureTheory.Measure.regular_of_isHaarMeasure
#align measure_theory.measure.regular_of_is_add_haar_measure MeasureTheory.Measure.regular_of_isAddHaarMeasure

/-- **Steinhaus Theorem** In any locally compact group `G` with a haar measure `μ`, for any
  measurable set `E` of positive measure, the set `E / E` is a neighbourhood of `1`. -/
@[to_additive
"**Steinhaus Theorem** In any locally compact group `G` with a haar measure `μ`, for any measurable
set `E` of positive measure, the set `E - E` is a neighbourhood of `0`."]
theorem div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
    (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ E) : E / E ∈ 𝓝 (1 : G) := by
  /- For any regular measure `μ` and set `E` of positive measure, we can find a compact set `K` of
       positive measure inside `E`. Further, for any outer regular measure `μ` there exists an open
       set `U` containing `K` with measure arbitrarily close to `K` (here `μ U < 2 * μ K` suffices).
       Then, we can pick an open neighborhood of `1`, say `V` such that such that `V * K` is
       contained in `U`. Now note that for any `v` in `V`, the sets `K` and `{v} * K` can not be
       disjoint because they are both of measure `μ K` (since `μ` is left regular) and also
       contained in `U`, yet we have that `μ U < 2 * μ K`. This show that `K / K` contains the
       neighborhood `V` of `1`, and therefore that it is itself such a neighborhood. -/
  obtain ⟨L, hL, hLE, hLpos, hLtop⟩ : ∃ L : Set G, MeasurableSet L ∧ L ⊆ E ∧ 0 < μ L ∧ μ L < ∞ :=
    exists_subset_measure_lt_top hE hEpos
  obtain ⟨K, hKL, hK, hKpos⟩ : ∃ (K : Set G), K ⊆ L ∧ IsCompact K ∧ 0 < μ K :=
    MeasurableSet.exists_lt_isCompact_of_ne_top hL (ne_of_lt hLtop) hLpos
  have hKtop : μ K ≠ ∞ := by
    apply ne_top_of_le_ne_top (ne_of_lt hLtop)
    apply measure_mono hKL
  obtain ⟨U, hUK, hU, hμUK⟩ : ∃ (U : Set G), U ⊇ K ∧ IsOpen U ∧ μ U < μ K + μ K :=
    Set.exists_isOpen_lt_add K hKtop hKpos.ne'
  obtain ⟨V, hV1, hVKU⟩ : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U :=
    compact_open_separated_mul_left hK hU hUK
  have hv : ∀ v : G, v ∈ V → ¬Disjoint ({v} * K) K := by
    intro v hv hKv
    have hKvsub : {v} * K ∪ K ⊆ U := by
      apply Set.union_subset _ hUK
      apply _root_.subset_trans _ hVKU
      apply Set.mul_subset_mul _ (Set.Subset.refl K)
      simp only [Set.singleton_subset_iff, hv]
    replace hKvsub := @measure_mono _ _ μ _ _ hKvsub
    have hcontr := lt_of_le_of_lt hKvsub hμUK
    rw [measure_union hKv (IsCompact.measurableSet hK)] at hcontr
    have hKtranslate : μ ({v} * K) = μ K := by
      simp only [singleton_mul, image_mul_left, measure_preimage_mul]
    rw [hKtranslate, lt_self_iff_false] at hcontr
    assumption
  suffices V ⊆ E / E from Filter.mem_of_superset hV1 this
  intro v hvV
  obtain ⟨x, hxK, hxvK⟩ : ∃ x : G, x ∈ {v} * K ∧ x ∈ K := Set.not_disjoint_iff.1 (hv v hvV)
  refine' ⟨x, v⁻¹ * x, hLE (hKL hxvK), _, _⟩
  · apply hKL.trans hLE
    simpa only [singleton_mul, image_mul_left, mem_preimage] using hxK
  · simp only [div_eq_iff_eq_mul, ← mul_assoc, mul_right_inv, one_mul]
#align measure_theory.measure.div_mem_nhds_one_of_haar_pos MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos
#align measure_theory.measure.sub_mem_nhds_zero_of_add_haar_pos MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos

end SecondCountable

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [TopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [IsHaarMeasure μ]

/-- Any Haar measure is invariant under inversion in an abelian group. -/
@[to_additive "Any additive Haar measure is invariant under negation in an abelian group."]
instance (priority := 100) IsHaarMeasure.isInvInvariant [LocallyCompactSpace G] :
    IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  haveI : IsHaarMeasure (Measure.map Inv.inv μ) :=
    (MulEquiv.inv G).isHaarMeasure_map μ continuous_inv continuous_inv
  obtain ⟨c, _, _, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ Measure.map Inv.inv μ = c • μ :=
    isHaarMeasure_eq_smul_isHaarMeasure _ _
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    simp only [hc, smul_smul, pow_two, Measure.map_smul]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Involutive.comp_self, map_id]
  have K : PositiveCompacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_eq_mul_right (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_strictMono two_ne_zero).injective this
  rw [Measure.inv, hc, this, one_smul]
#align measure_theory.measure.is_haar_measure.is_inv_invariant MeasureTheory.Measure.IsHaarMeasure.isInvInvariant
#align measure_theory.measure.is_add_haar_measure.is_neg_invariant MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant

@[to_additive]
theorem measurePreserving_zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) :
    MeasurePreserving (fun g : G => g ^ n) μ μ :=
  { measurable := (continuous_zpow n).measurable
    map_eq := by
      let f := @zpowGroupHom G _ n
      have hf : Continuous f := continuous_zpow n
      haveI : (μ.map f).IsHaarMeasure :=
        isHaarMeasure_map μ f hf (RootableBy.surjective_pow G ℤ hn) (by simp)
      obtain ⟨C, -, -, hC⟩ := isHaarMeasure_eq_smul_isHaarMeasure (μ.map f) μ
      suffices C = 1 by rwa [this, one_smul] at hC
      have h_univ : (μ.map f) univ = μ univ := by
        rw [map_apply_of_aemeasurable hf.measurable.aemeasurable MeasurableSet.univ,
          preimage_univ]
      have hμ₀ : μ univ ≠ 0 := IsOpenPosMeasure.open_pos univ isOpen_univ univ_nonempty
      have hμ₁ : μ univ ≠ ∞ := CompactSpace.isFiniteMeasure.measure_univ_lt_top.ne
      rwa [hC, smul_apply, Algebra.id.smul_eq_mul, mul_comm, ← ENNReal.eq_div_iff hμ₀ hμ₁,
        ENNReal.div_self hμ₀ hμ₁] at h_univ }
#align measure_theory.measure.measure_preserving_zpow MeasureTheory.Measure.measurePreserving_zpow
#align measure_theory.measure.measure_preserving_zsmul MeasureTheory.Measure.measurePreserving_zsmul

@[to_additive]
theorem MeasurePreserving.zpow [CompactSpace G] [RootableBy G ℤ] {n : ℤ} (hn : n ≠ 0) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x ^ n) μ' μ :=
  (measurePreserving_zpow μ hn).comp hf
#align measure_theory.measure.measure_preserving.zpow MeasureTheory.Measure.MeasurePreserving.zpow
#align measure_theory.measure.measure_preserving.zsmul MeasureTheory.Measure.MeasurePreserving.zsmul

end CommGroup

end Measure

end MeasureTheory
