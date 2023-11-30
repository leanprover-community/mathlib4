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
`integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`. From this, we deduce various uniqueness
statements for left invariant measures (up to scalar multiplication):
* `measure_isMulLeftInvariant_eq_smul_of_ne_top`: two left-invariant measures which are inner
  regular for finite measure sets with respect to compact sets give the same measure to
  compact sets.
* `isMulLeftInvariant_eq_smul_of_innerRegular`: two left invariant measures which are
  inner regular coincide up to a scalar.
* `isHaarMeasure_eq_smul_of_innerRegular`: two Haar measures which are inner regular coincide up
  to a nonzero scalar.
* `isMulLeftInvariant_eq_smul_of_regular`: two left invariant measure which are
  regular coincide up to a scalar.
* `isHaarMeasure_eq_smul_of_regular`: two Haar measures which are regular coincide up to a
  nonzero scalar.
* `isHaarMeasure_eq_smul`: in a second countable space, two Haar measures coincide up to a
  nonzero scalar.
* `isMulLeftInvariant_eq_of_isProbabilityMeasure`: two left-invariant probability measures which
  are inner regular for finite measure sets with respect to compact sets coincide.

In general, uniqueness statements for Haar measures in the literature make some assumption of
regularity, either regularity or inner regularity. We have tried to minimize the assumptions in the
theorems above (notably in `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, which doesn't
make any regularity assumption), and cover the different results that exist in the literature.

The main result is `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, and the other ones
follow readily from this one by using continuous compactly supported functions to approximate
characteristic functions of set.

To prove `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, we use a change of variables
to express integrals with respect to a left-invariant measure as integrals with respect to a given
right-invariant measure (with a suitable density function). The uniqueness readily follows.

On second-countable groups, one can arrive to slightly different uniqueness results by using that
the operations are measurable. In particular, one can get uniqueness assuming σ-finiteness of
the measures but discarding the assumption that they are finite on compact sets. See
`haarMeasure_unique` in the file `MeasureTheory.Measure.Haar.Basic`.
-/

open MeasureTheory Filter Set TopologicalSpace Function MeasureTheory Measure
open scoped Uniformity Topology ENNReal Pointwise NNReal

/-- In a locally compact regular space with an inner regular measure, the measure of a compact
set `k` is the infimum of the integrals of compactly supported functions equal to `1` on `k`. -/
lemma IsCompact.measure_eq_biInf_integral_hasCompactSupport
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

/-- The parameterized integral `x ↦ ∫ y, g (y⁻¹ * x) ∂μ` depends continuously on `y` when `g` is a
compactly supported continuous function on a topological group `G`, and `μ` is finite on compact
sets. -/
@[to_additive]
lemma continuous_integral_apply_inv_mul
    {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
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
      refine ⟨p, p⁻¹ * x, hp, ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

namespace Measure

section Group

variable {G : Type*} [TopologicalSpace G] [LocallyCompactSpace G] [Group G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

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
        have M'_comp : IsCompact (closure M) := M_comp.closure
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
        have M'_comp : IsCompact (closure M) := M_comp.closure
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
@[to_additive integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport]
lemma integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport
    (μ' μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
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
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  rw [← mul_inv_eq_iff_eq_mul₀ int_g_pos.ne'] at A
  have B : ∫ x, f x ∂μ' = (∫ y, f y * (∫ z, g (z⁻¹ * y) ∂ν)⁻¹ ∂ν) * ∫ x, g x ∂μ' :=
    integral_isMulLeftInvariant_isMulRightInvariant_combo f_cont f_comp g_cont g_comp g_nonneg g_one
  /- Since the `ν`-factor is the same for `μ` and `μ'`, this gives the result. -/
  rw [← A, mul_assoc, mul_comm] at B
  simp only [B, integral_smul_nnreal_measure]
  rfl

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite on
compacts and inner regular for finite measure sets with respect to compact sets,
they coincide in the following sense: they give the same value to finite measure sets,
up to a multiplicative constant. -/
@[to_additive]
lemma measure_isMulLeftInvariant_eq_smul_of_ne_top
    (μ' μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ'] :
    ∃ (c : ℝ≥0), ∀ (s : Set G), μ s < ∞ → μ' s < ∞ → μ' s = (c • μ) s := by
  /- We know that the measures integrate in the same way continuous compactly supported functions,
  up to a constant `c`. We will use this constant `c`. -/
  rcases integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ with ⟨c, hc⟩
  refine ⟨c, fun s hs h's ↦ ?_⟩
  /- By regularity, every compact set may be approximated by a continuous compactly supported
  function. Therefore, the measures coincide on compact sets. -/
  have A : ∀ k, IsCompact k → μ' k = (c • μ) k := by
    intro k hk
    rw [hk.measure_eq_biInf_integral_hasCompactSupport μ',
        hk.measure_eq_biInf_integral_hasCompactSupport (c • μ)]
    congr! 7 with f f_cont f_comp _fk _f_nonneg
    exact hc f f_cont f_comp
  /- By regularity, every measurable set of finite measure may be approximated by compact sets.
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
@[to_additive isAddLeftInvariant_eq_smul_of_innerRegular]
lemma isMulLeftInvariant_eq_smul_of_innerRegular
    (μ' μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [InnerRegular μ] [InnerRegular μ'] :
    ∃ (c : ℝ≥0), μ' = c • μ := by
  rcases measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  ext s hs
  rw [hs.measure_eq_iSup_isCompact, hs.measure_eq_iSup_isCompact]
  congr! 4 with K _Ks K_comp
  exact hc K K_comp.measure_lt_top K_comp.measure_lt_top

/-- **Uniqueness of left-invariant measures**: Two inner regular Haar measures coincide up to a
multiplicative constant. -/
@[to_additive isAddHaarMeasure_eq_smul_of_innerRegular]
lemma isHaarMeasure_eq_smul_of_innerRegular
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] [InnerRegular μ] [InnerRegular μ'] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ' = c • μ := by
  rcases isMulLeftInvariant_eq_smul_of_innerRegular μ' μ with ⟨c, hc⟩
  refine ⟨c, ?_, ENNReal.coe_ne_top, hc⟩
  intro h
  simp only [ENNReal.coe_eq_zero.1 h, zero_smul] at hc
  have : 0 < μ' univ := NeZero.pos (μ' univ)
  simp [hc] at this

/-- **Uniqueness of left-invariant measures**: Given two left-invariant measures which are finite
on compacts and regular, they coincide up to a multiplicative constant. -/
@[to_additive isAddLeftInvariant_eq_smul_of_regular]
lemma isMulLeftInvariant_eq_smul_of_regular
    (μ' μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] [IsOpenPosMeasure μ]
    [Regular μ] [Regular μ'] :
    ∃ (c : ℝ≥0), μ' = c • μ := by
  rcases measure_isMulLeftInvariant_eq_smul_of_ne_top μ' μ with ⟨c, hc⟩
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

/-- **Uniqueness of left-invariant measures**: Two regular Haar measures coincide up to a
multiplicative constant. -/
@[to_additive isAddHaarMeasure_eq_smul_of_regular]
lemma isHaarMeasure_eq_smul_of_regular
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] [Regular μ] [Regular μ'] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ' = c • μ := by
  rcases isMulLeftInvariant_eq_smul_of_regular μ' μ with ⟨c, hc⟩
  refine ⟨c, ?_, ENNReal.coe_ne_top, hc⟩
  intro h
  simp only [ENNReal.coe_eq_zero.1 h, zero_smul] at hc
  have : 0 < μ' univ := NeZero.pos (μ' univ)
  simp [hc] at this

/-- **Uniqueness of left-invariant measures**: Two Haar measures coincide up to a multiplicative
constant in a second countable group. -/
@[to_additive isAddHaarMeasure_eq_smul]
lemma isHaarMeasure_eq_smul [SecondCountableTopology G]
    (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ' = c • μ :=
  isHaarMeasure_eq_smul_of_regular μ' μ
  -- one could use as well `isHaarMeasure_eq_smul_isHaarMeasure_of_innerRegular μ' μ`, as in a
  -- second countable topological space all Haar measures are regular and inner regular
#align measure_theory.measure.is_haar_measure_eq_smul_is_haar_measure MeasureTheory.Measure.isHaarMeasure_eq_smul
#align measure_theory.measure.is_add_haar_measure_eq_smul_is_add_haar_measure MeasureTheory.Measure.isAddHaarMeasure_eq_smul

/-- **Uniqueness of left-invariant measures**: Given two left-invariant probability measures which
are inner regular for finite measure sets with respect to compact sets, they coincide. -/
@[to_additive]
lemma isMulLeftInvariant_eq_of_isProbabilityMeasure
    (μ' μ : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [InnerRegularCompactLTTop μ] [InnerRegularCompactLTTop μ']
    [IsMulLeftInvariant μ] [IsMulLeftInvariant μ'] : μ' = μ := by
  rcases isMulLeftInvariant_eq_smul_of_regular μ' μ with ⟨c, hc⟩
  have : ((c : ℝ≥0∞) • μ) univ = μ' univ := by rw [hc]; rfl
  simp only [smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, measure_univ, smul_eq_mul,
    mul_one, ENNReal.coe_eq_one] at this
  simp [hc, this]

/-- An invariant σ-finite measure is absolutely continuous with respect to a Haar measure in a
second countable grop. -/
@[to_additive
"An invariant measure is absolutely continuous with respect to an additive Haar measure. "]
theorem absolutelyContinuous_isHaarMeasure [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (μ ν : Measure G)
    [SigmaFinite μ] [IsMulLeftInvariant μ] [IsHaarMeasure ν] : μ ≪ ν := by
  have K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨c, -, -, h⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ haarMeasure K = c • ν :=
    isHaarMeasure_eq_smul _ _
  rw [haarMeasure_unique μ K, h, smul_smul]
  exact AbsolutelyContinuous.smul (Eq.absolutelyContinuous rfl) _

end Group

section CommGroup

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [TopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]

/-- Any regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive "Any regular additive Haar measure is invariant under negation in an abelian group."]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_regular
    [LocallyCompactSpace G] [Regular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  have : IsHaarMeasure μ.inv := (MulEquiv.inv G).isHaarMeasure_map μ continuous_inv continuous_inv
  obtain ⟨c, _, _, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ.inv = c • μ :=
    isHaarMeasure_eq_smul_of_regular _ _
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
    (ENNReal.mul_eq_mul_right (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]
#align measure_theory.measure.is_haar_measure.is_inv_invariant MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_regular
#align measure_theory.measure.is_add_haar_measure.is_neg_invariant MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_regular

/-- Any inner regular Haar measure is invariant under inversion in an abelian group. -/
@[to_additive "Any regular additive Haar measure is invariant under negation in an abelian group."]
instance (priority := 100) IsHaarMeasure.isInvInvariant_of_innerRegular
    [LocallyCompactSpace G] [InnerRegular μ] : IsInvInvariant μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  constructor
  have : IsHaarMeasure μ.inv := (MulEquiv.inv G).isHaarMeasure_map μ continuous_inv continuous_inv
  obtain ⟨c, _, _, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ.inv = c • μ :=
    isHaarMeasure_eq_smul_of_innerRegular _ _
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
    (ENNReal.mul_eq_mul_right (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 this
  have : c = 1 := (ENNReal.pow_strictMono two_ne_zero).injective this
  rw [hc, this, one_smul]

@[to_additive]
theorem measurePreserving_zpow [CompactSpace G] [RootableBy G ℤ]
    [InnerRegularCompactLTTop μ] {n : ℤ} (hn : n ≠ 0) :
    MeasurePreserving (fun g : G => g ^ n) μ μ :=
  { measurable := (continuous_zpow n).measurable
    map_eq := by
      let f := @zpowGroupHom G _ n
      have hf : Continuous f := continuous_zpow n
      have : (μ.map f).IsHaarMeasure :=
        isHaarMeasure_map_of_isFiniteMeasure μ f hf (RootableBy.surjective_pow G ℤ hn)
      have : InnerRegular (μ.map f) := InnerRegular.map_of_continuous hf
      obtain ⟨C, -, -, hC⟩ := isHaarMeasure_eq_smul_of_innerRegular (μ.map f) μ
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
theorem MeasurePreserving.zpow [CompactSpace G] [RootableBy G ℤ]
    [InnerRegularCompactLTTop μ] {n : ℤ} (hn : n ≠ 0) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x ^ n) μ' μ :=
  (measurePreserving_zpow μ hn).comp hf
#align measure_theory.measure.measure_preserving.zpow MeasureTheory.Measure.MeasurePreserving.zpow
#align measure_theory.measure.measure_preserving.zsmul MeasureTheory.Measure.MeasurePreserving.zsmul

end CommGroup

end Measure

end MeasureTheory
