/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.Order.Floor

#align_import measure_theory.integral.periodic from "leanprover-community/mathlib"@"9f55d0d4363ae59948c33864cbc52e0b12e0e8ce"

/-!
# Integrals of periodic functions

In this file we prove that the half-open interval `Ioc t (t + T)` in `ℝ` is a fundamental domain of
the action of the subgroup `ℤ ∙ T` on `ℝ`.

A consequence is `AddCircle.measurePreserving_mk`: the covering map from `ℝ` to the "additive
circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving, with respect to the restriction of Lebesgue measure to
`Ioc t (t + T)` (upstairs) and with respect to Haar measure (downstairs).

Another consequence (`Function.Periodic.intervalIntegral_add_eq` and related declarations) is that
`∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily measurable) function with
period `T`.
-/

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

@[measurability]
protected theorem AddCircle.measurable_mk' {a : ℝ} :
    Measurable (β := AddCircle a) ((↑) : ℝ → AddCircle a) :=
  Continuous.measurable <| AddCircle.continuous_mk' a
#align add_circle.measurable_mk' AddCircle.measurable_mk'

theorem isAddFundamentalDomain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' measurableSet_Ioc.nullMeasurableSet fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_strictMono_left hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa only [add_comm x] using existsUnique_add_zsmul_mem_Ioc hT x t
#align is_add_fundamental_domain_Ioc isAddFundamentalDomain_Ioc

theorem isAddFundamentalDomain_Ioc' {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' measurableSet_Ioc.nullMeasurableSet fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_strictMono_left hT).injective).bijective
  refine (AddSubgroup.equivOp _).bijective.comp this |>.existsUnique_iff.2 ?_
  simpa using existsUnique_add_zsmul_mem_Ioc hT x t
#align is_add_fundamental_domain_Ioc' isAddFundamentalDomain_Ioc'

namespace AddCircle

variable (T : ℝ) [hT : Fact (0 < T)]

/-- Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar measure of total
mass `T` -/
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }
#align add_circle.measure_space AddCircle.measureSpace

-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma.
@[simp, nolint simpNF]
protected theorem measure_univ : volume (Set.univ : Set (AddCircle T)) = ENNReal.ofReal T := by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]
#align add_circle.measure_univ AddCircle.measure_univ

instance : IsAddHaarMeasure (volume : Measure (AddCircle T)) :=
  IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top

instance isFiniteMeasure : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  measure_univ_lt_top := by simp
#align add_circle.is_finite_measure AddCircle.isFiniteMeasure

instance : HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) ℝ where
  ExistsIsAddFundamentalDomain := ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩

instance : AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T)) := by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

/-- The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass `T`)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + T]. -/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := AddCircle T) ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioc t (t + T))) :=
  measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t+T)) (isAddFundamentalDomain_Ioc' hT.out _) _
#align add_circle.measure_preserving_mk AddCircle.measurePreserving_mk

lemma add_projection_respects_measure (t : ℝ) {U : Set (AddCircle T)} (meas_U : MeasurableSet U) :
    volume U = volume (QuotientAddGroup.mk ⁻¹' U ∩ (Ioc t (t + T))) :=
  (isAddFundamentalDomain_Ioc' hT.out _).addProjection_respects_measure_apply
    (volume : Measure (AddCircle T)) meas_U

theorem volume_closedBall {x : AddCircle T} (ε : ℝ) :
    volume (Metric.closedBall x ε) = ENNReal.ofReal (min T (2 * ε)) := by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 → Metric.closedBall (0 : ℝ) ε ∩ I = Metric.closedBall (0 : ℝ) ε := by
    intro hε
    rw [inter_eq_left, Real.closedBall_eq_Icc, zero_sub, zero_add]
    rintro y ⟨hy₁, hy₂⟩; constructor <;> linarith
  have h₂ : (↑) ⁻¹' Metric.closedBall (0 : AddCircle T) ε ∩ I =
      if ε < T / 2 then Metric.closedBall (0 : ℝ) ε else I := by
    conv_rhs => rw [← if_ctx_congr (Iff.rfl : ε < T / 2 ↔ ε < T / 2) h₁ fun _ => rfl, ← hT']
    apply coe_real_preimage_closedBall_inter_eq
    simpa only [hT', Real.closedBall_eq_Icc, zero_add, zero_sub] using Ioc_subset_Icc_self
  rw [addHaar_closedBall_center, add_projection_respects_measure T (-(T/2))
    measurableSet_closedBall, (by linarith : -(T / 2) + T = T / 2), h₂]
  by_cases hε : ε < T / 2
  · simp [hε, min_eq_right (by linarith : 2 * ε ≤ T)]
  · simp [I, hε, min_eq_left (by linarith : T ≤ 2 * ε)]
#align add_circle.volume_closed_ball AddCircle.volume_closedBall

instance : IsUnifLocDoublingMeasure (volume : Measure (AddCircle T)) := by
  refine ⟨⟨Real.toNNReal 2, Filter.eventually_of_forall fun ε x => ?_⟩⟩
  simp only [volume_closedBall]
  erw [← ENNReal.ofReal_mul zero_le_two]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
  exact min_le_min (by linarith [hT.out]) (le_refl _)

/-- The isomorphism `AddCircle T ≃ Ioc a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
noncomputable def measurableEquivIoc (a : ℝ) : AddCircle T ≃ᵐ Ioc a (a + T) where
  toEquiv := equivIoc T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_restrict.mp <| ContinuousAt.continuousOn fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe
#align add_circle.measurable_equiv_Ioc AddCircle.measurableEquivIoc

/-- The isomorphism `AddCircle T ≃ Ico a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
noncomputable def measurableEquivIco (a : ℝ) : AddCircle T ≃ᵐ Ico a (a + T) where
  toEquiv := equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_restrict.mp <| ContinuousAt.continuousOn fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe
#align add_circle.measurable_equiv_Ico AddCircle.measurableEquivIco

attribute [local instance] Subtype.measureSpace in
/-- The lower integral of a function over `AddCircle T` is equal to the lower integral over an
interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem lintegral_preimage (t : ℝ) (f : AddCircle T → ℝ≥0∞) :
    (∫⁻ a in Ioc t (t + T), f a) = ∫⁻ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := lintegral_map_equiv (μ := volume) f (measurableEquivIoc T t).symm
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq]
  convert this.symm using 1
  · rw [← map_comap_subtype_coe m _]
    exact MeasurableEmbedding.lintegral_map (MeasurableEmbedding.subtype_coe m) _
  · congr 1
    have : ((↑) : Ioc t (t + T) → AddCircle T) = ((↑) : ℝ → AddCircle T) ∘ ((↑) : _ → ℝ) := by
      ext1 x; rfl
    simp_rw [this]
    rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe, ← map_comap_subtype_coe m]
    rfl
#align add_circle.lintegral_preimage AddCircle.lintegral_preimage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

attribute [local instance] Subtype.measureSpace in
/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem integral_preimage (t : ℝ) (f : AddCircle T → E) :
    (∫ a in Ioc t (t + T), f a) = ∫ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := integral_map_equiv (μ := volume) (measurableEquivIoc T t).symm f
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq, ← integral_subtype m, ← this]
  have : ((↑) : Ioc t (t + T) → AddCircle T) = ((↑) : ℝ → AddCircle T) ∘ ((↑) : _ → ℝ) := by
    ext1 x; rfl
  simp_rw [this]
  rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe, ← map_comap_subtype_coe m]
  rfl
#align add_circle.integral_preimage AddCircle.integral_preimage

/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected theorem intervalIntegral_preimage (t : ℝ) (f : AddCircle T → E) :
    ∫ a in t..t + T, f a = ∫ b : AddCircle T, f b := by
  rw [integral_of_le, AddCircle.integral_preimage T t f]
  linarith [hT.out]
#align add_circle.interval_integral_preimage AddCircle.intervalIntegral_preimage

end AddCircle

namespace UnitAddCircle

attribute [local instance] Real.fact_zero_lt_one

protected theorem measure_univ : volume (Set.univ : Set UnitAddCircle) = 1 := by simp
#align unit_add_circle.measure_univ UnitAddCircle.measure_univ

/-- The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass 1)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + 1]. -/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := UnitAddCircle) ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ioc t (t + 1))) :=
  AddCircle.measurePreserving_mk 1 t
#align unit_add_circle.measure_preserving_mk UnitAddCircle.measurePreserving_mk

/-- The integral of a measurable function over `UnitAddCircle` is equal to the integral over an
interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem lintegral_preimage (t : ℝ) (f : UnitAddCircle → ℝ≥0∞) :
    (∫⁻ a in Ioc t (t + 1), f a) = ∫⁻ b : UnitAddCircle, f b :=
  AddCircle.lintegral_preimage 1 t f
#align unit_add_circle.lintegral_preimage UnitAddCircle.lintegral_preimage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem integral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    (∫ a in Ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t f
#align unit_add_circle.integral_preimage UnitAddCircle.integral_preimage

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected theorem intervalIntegral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    ∫ a in t..t + 1, f a = ∫ b : UnitAddCircle, f b :=
  AddCircle.intervalIntegral_preimage 1 t f
#align unit_add_circle.interval_integral_preimage UnitAddCircle.intervalIntegral_preimage

end UnitAddCircle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace Function

namespace Periodic

variable {f : ℝ → E} {T : ℝ}

/-- An auxiliary lemma for a more general `Function.Periodic.intervalIntegral_add_eq`. -/
theorem intervalIntegral_add_eq_of_pos (hf : Periodic f T) (hT : 0 < T) (t s : ℝ) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]
#align function.periodic.interval_integral_add_eq_of_pos Function.Periodic.intervalIntegral_add_eq_of_pos

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
theorem intervalIntegral_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  rcases lt_trichotomy (0 : ℝ) T with (hT | rfl | hT)
  · exact hf.intervalIntegral_add_eq_of_pos hT t s
  · simp
  · rw [← neg_inj, ← integral_symm, ← integral_symm]
    simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
      hf.neg.intervalIntegral_add_eq_of_pos (neg_pos.2 hT) (t + T) (s + T)
#align function.periodic.interval_integral_add_eq Function.Periodic.intervalIntegral_add_eq

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
theorem intervalIntegral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.intervalIntegral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]
#align function.periodic.interval_integral_add_eq_add Function.Periodic.intervalIntegral_add_eq_add

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
theorem intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in (0)..(n • T), f x) = n • ∫ x in (0)..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in (0)..m • T, f x) = m • ∫ x in (0)..T, f x := fun m ↦ by
    induction' m with m ih
    · simp
    · simp only [succ_nsmul, hf.intervalIntegral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  cases' n with n n
  · simp [← this n]
  · conv_rhs => rw [negSucc_zsmul]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by simp; linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.intervalIntegral_add_eq ((n + 1) • T) 0, zero_add]
#align function.periodic.interval_integral_add_zsmul_eq Function.Periodic.intervalIntegral_add_zsmul_eq

section RealValued

open Filter

variable {g : ℝ → ℝ}
variable (hg : Periodic g T) (h_int : ∀ t₁ t₂, IntervalIntegrable g MeasureSpace.volume t₁ t₂)

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem sInf_add_zsmul_le_integral_of_pos (hT : 0 < T) (t : ℝ) :
    (sInf ((fun t => ∫ x in (0)..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in (0)..T, g x) ≤
      ∫ x in (0)..t, g x := by
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t (by linarith), ←
      integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.intervalIntegral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact (continuous_primitive h_int 0).continuousOn.sInf_image_Icc_le <|
    mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT)
#align function.periodic.Inf_add_zsmul_le_integral_of_pos Function.Periodic.sInf_add_zsmul_le_integral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem integral_le_sSup_add_zsmul_of_pos (hT : 0 < T) (t : ℝ) :
    (∫ x in (0)..t, g x) ≤
      sSup ((fun t => ∫ x in (0)..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in (0)..T, g x := by
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t (by linarith), ←
      integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h_int, hg.intervalIntegral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact (continuous_primitive h_int 0).continuousOn.le_sSup_image_Icc
    (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))
#align function.periodic.integral_le_Sup_add_zsmul_of_pos Function.Periodic.integral_le_sSup_add_zsmul_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_atTop_intervalIntegral_of_pos (h₀ : 0 < ∫ x in (0)..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in (0)..t, g x) atTop atTop := by
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in (0)..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.comp (tendsto_id.atTop_mul_const (inv_pos.mpr hT))
#align function.periodic.tendsto_at_top_interval_integral_of_pos Function.Periodic.tendsto_atTop_intervalIntegral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_atBot_intervalIntegral_of_pos (h₀ : 0 < ∫ x in (0)..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in (0)..t, g x) atBot atBot := by
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in (0)..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.comp (tendsto_id.atBot_mul_const (inv_pos.mpr hT))
#align function.periodic.tendsto_at_bot_interval_integral_of_pos Function.Periodic.tendsto_atBot_intervalIntegral_of_pos

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_atTop_intervalIntegral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in (0)..t, g x) atTop atTop :=
  hg.tendsto_atTop_intervalIntegral_of_pos h_int (intervalIntegral_pos_of_pos (h_int 0 T) h₀ hT) hT
#align function.periodic.tendsto_at_top_interval_integral_of_pos' Function.Periodic.tendsto_atTop_intervalIntegral_of_pos'

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_atBot_intervalIntegral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in (0)..t, g x) atBot atBot :=
  hg.tendsto_atBot_intervalIntegral_of_pos h_int (intervalIntegral_pos_of_pos (h_int 0 T) h₀ hT) hT
#align function.periodic.tendsto_at_bot_interval_integral_of_pos' Function.Periodic.tendsto_atBot_intervalIntegral_of_pos'

end RealValued

end Periodic

end Function
