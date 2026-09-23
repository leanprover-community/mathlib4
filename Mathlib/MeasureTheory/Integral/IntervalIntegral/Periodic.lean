/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Instances.AddCircle.Real

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

@[expose] public section

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

/-!
## Measures and integrability on ℝ and on the circle
-/

@[fun_prop]
protected theorem AddCircle.measurable_mk' {a : ℝ} :
    Measurable (β := AddCircle a) ((↑) : ℝ → AddCircle a) :=
  Continuous.measurable <| AddCircle.continuous_mk' a

theorem isAddFundamentalDomain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa only [add_comm x] using existsUnique_add_zsmul_mem_Ioc hT x t

theorem isAddFundamentalDomain_Ioc' {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine (AddSubgroup.equivOp _).bijective.comp this |>.existsUnique_iff.2 ?_
  simpa using existsUnique_add_zsmul_mem_Ioc hT x t

namespace AddCircle

variable (T : ℝ) [hT : Fact (0 < T)]

/-- Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar measure of total
mass `T` -/
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }

@[simp]
protected theorem measure_univ : volume (Set.univ : Set (AddCircle T)) = ENNReal.ofReal T := by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]

instance : IsAddHaarMeasure (volume : Measure (AddCircle T)) :=
  IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top

instance isFiniteMeasure : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  measure_univ_lt_top := by simp

instance : HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) ℝ where
  ExistsIsAddFundamentalDomain := ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩

instance : AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T)) := by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

/-- The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass `T`)
on the additive circle, and with respect to the restriction of Lebesgue measure on `ℝ` to an
interval $(t, t + T]$. -/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := AddCircle T) ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioc t (t + T))) :=
  measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t + T)) (isAddFundamentalDomain_Ioc' hT.out _) _

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
  rw [addHaar_closedBall_center, add_projection_respects_measure T (-(T / 2))
    measurableSet_closedBall, (by linarith : -(T / 2) + T = T / 2), h₂]
  by_cases hε : ε < T / 2
  · simp [hε, min_eq_right (by linarith : 2 * ε ≤ T)]
  · simp [I, hε, min_eq_left (by linarith : T ≤ 2 * ε)]

instance : IsUnifLocDoublingMeasure (volume : Measure (AddCircle T)) := by
  refine ⟨⟨Real.toNNReal 2, Filter.Eventually.of_forall fun ε x => ?_⟩⟩
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
    (continuousOn_iff_continuous_restrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/-- The isomorphism `AddCircle T ≃ Ico a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
noncomputable def measurableEquivIco (a : ℝ) : AddCircle T ≃ᵐ Ico a (a + T) where
  toEquiv := equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_restrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/-- The equivalence `equivIoc` is measure preserving with respect to the natural volume measures. -/
lemma measurePreserving_equivIoc {a : ℝ} :
    MeasurePreserving (equivIoc T a) volume (Measure.comap Subtype.val volume) := by
  have h := (measurableEquivIoc T a).measurable
  refine ⟨h, ?_⟩
  ext s hs
  rw [comap_apply _ Subtype.val_injective (fun _ ↦ measurableSet_Ioc.subtype_image) _ hs,
    map_apply (by measurability) hs, add_projection_respects_measure T a (by exact h hs)]
  congr!
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  rw [and_comm, ← exists_prop]
  congr! with hx
  rw [equivIoc_coe_eq hx]

attribute [local instance] Subtype.measureSpace in
/-- The lower integral of a function over `AddCircle T` is equal to the lower integral over an
interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Subtype.measureSpace in
/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
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

/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
protected theorem intervalIntegral_preimage (t : ℝ) (f : AddCircle T → E) :
    ∫ a in t..t + T, f a = ∫ b : AddCircle T, f b := by
  rw [integral_of_le, AddCircle.integral_preimage T t f]
  linarith [hT.out]

/-- The integral of a function lifted to AddCircle from an interval `(t, t + T]` to `AddCircle T`
is equal to the intervalIntegral over the interval. -/
lemma integral_liftIoc_eq_intervalIntegral {t : ℝ} {f : ℝ → E} :
    ∫ a, liftIoc T t f a = ∫ a in t..t + T, f a := by
  rw [← AddCircle.intervalIntegral_preimage T t]
  apply intervalIntegral.integral_congr_ae
  refine .of_forall fun x hx ↦ ?_
  rw [uIoc_of_le (by linarith [hT.out])] at hx
  rw [liftIoc_coe_apply hx]

end AddCircle

/-- If a function satisfies `MemLp` on the interval `(t, t + T]`, then its lift to the AddCircle
also satisfies `MemLp` with respect to the Haar measure. -/
lemma MeasureTheory.MemLp.memLp_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ} {p : ℝ≥0∞}
    (hLp : MemLp f p (volume.restrict (Ioc t (t + T)))) :
      MemLp (AddCircle.liftIoc T t f) p := by
  simp only [AddCircle.liftIoc, Set.restrict_def, Function.comp_def]
  apply hLp.comp_measurePreserving
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

namespace UnitAddCircle

protected theorem measure_univ : volume (Set.univ : Set UnitAddCircle) = 1 := by simp

/-- The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass 1)
on the additive circle, and with respect to the restriction of Lebesgue measure on `ℝ` to an
interval $(t, t + 1]$. -/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := UnitAddCircle) ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ioc t (t + 1))) :=
  AddCircle.measurePreserving_mk 1 t

/-- The integral of a measurable function over `UnitAddCircle` is equal to the integral over an
interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
protected theorem lintegral_preimage (t : ℝ) (f : UnitAddCircle → ℝ≥0∞) :
    (∫⁻ a in Ioc t (t + 1), f a) = ∫⁻ b : UnitAddCircle, f b :=
  AddCircle.lintegral_preimage 1 t f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
protected theorem integral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    (∫ a in Ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t f

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
protected theorem intervalIntegral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    ∫ a in t..t + 1, f a = ∫ b : UnitAddCircle, f b :=
  AddCircle.intervalIntegral_preimage 1 t f

end UnitAddCircle

/-!
## Interval integrability of periodic functions
-/
namespace Function

namespace Periodic

variable {E : Type*} [NormedAddCommGroup E]

variable {f : ℝ → E} {T : ℝ}

/--
A periodic function is interval integrable over every interval if it is interval integrable over one
period.
-/
theorem intervalIntegrable {t : ℝ} (h₁f : Function.Periodic f T)
    (hT : T ≠ 0) (h₂f : IntervalIntegrable f volume t (t + T)) (a₁ a₂ : ℝ) :
    IntervalIntegrable f volume a₁ a₂ := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with h | h
    · tauto
    · have hnT : 0 < -T := by aesop
      nth_rw 1 [(by ring : t = (t + T) + (-T))] at h₂f
      apply this h₁f.neg hnT.ne' h₂f.symm _ _ hnT
  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are natural numbers
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((t - min a₁ a₂) / T)
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
  have : Set.uIcc a₁ a₂ ⊆ Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    rw [Set.uIcc_subset_uIcc_iff_le]
    constructor
    · calc min (t - n₁ * T) (t + n₂ * T)
      _ ≤ (t - n₁ * T) := by apply min_le_left
      _ ≤ min a₁ a₂ := by linarith [(div_le_iff₀ hT).1 hn₁]
    · calc max a₁ a₂
      _ ≤ t + n₂ * T := by linarith [(div_le_iff₀ hT).1 hn₂]
      _ ≤ max (t - n₁ * T) (t + n₂ * T) := by apply le_max_right
  apply IntervalIntegrable.mono_set _ this
  -- Suffices to show integrability over shifted periods
  let a : ℕ → ℝ := fun n ↦ t + (n - n₁) * T
  rw [(by ring : t - n₁ * T = a 0), (by simp [a] : t + n₂ * T = a (n₁ + n₂))]
  apply IntervalIntegrable.trans_iterate
  -- Show integrability over a shifted period
  intro k hk
  convert (IntervalIntegrable.comp_sub_right h₂f ((k - n₁) * T) (by aesop)) using 1
  · funext x
    simpa using (h₁f.sub_int_mul_eq (k - n₁)).symm
  · simp [a, Nat.cast_add]
    ring

/--
A periodic function is interval integrable over one full period if and only if it is interval
integrable over any other full period.

Special case of `Function.Periodic.intervalIntegrable`.
-/
theorem intervalIntegrable_iff {t₁ t₂ : ℝ} (hf : Periodic f T) :
    IntervalIntegrable f volume t₁ (t₁ + T) ↔ IntervalIntegrable f volume t₂ (t₂ + T) := by
  wlog hT : T ≠ 0
  · simp_all
  exact ⟨(hf.intervalIntegrable hT · t₂ (t₂ + T)), (hf.intervalIntegrable hT · t₁ (t₁ + T))⟩

/--
Special case of `Function.Periodic.intervalIntegrable`: A periodic function is interval integrable
over every interval if it is interval integrable over the period starting from zero.
-/
theorem intervalIntegrable₀ (h₁f : Function.Periodic f T) (hT : T ≠ 0)
    (h₂f : IntervalIntegrable f MeasureTheory.volume 0 T) (a₁ a₂ : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a₁ a₂ := by
  apply h₁f.intervalIntegrable hT (t := 0)
  simpa

/-!
## Interval integrals of periodic functions
-/

variable [NormedSpace ℝ E]

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
theorem intervalIntegral_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · aesop
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (by aesop : 0 < -T)
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
theorem intervalIntegral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.intervalIntegral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
theorem intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in 0..m • T, f x) = m • ∫ x in 0..T, f x := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [succ_nsmul, hf.intervalIntegral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  rcases n with n | n
  · simp [← this n]
  · conv_rhs => rw [negSucc_zsmul]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by simp; linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.intervalIntegral_add_eq ((n + 1) • T) 0, zero_add]

section RealValued

open Filter

variable {g : ℝ → ℝ}
variable (hg : Periodic g T)
include hg

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem sInf_add_zsmul_le_integral_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : ℝ) :
    (sInf ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x) ≤
      ∫ x in 0..t, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne',
      ← integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε (hg.intervalIntegrable₀ hT.ne' h_int),
    hg.intervalIntegral_add_eq ε 0, zero_add, add_le_add_iff_right]
  exact (continuous_primitive h'_int 0).continuousOn.sInf_image_Icc_le <|
    mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT)

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
theorem integral_le_sSup_add_zsmul_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : ℝ) :
    (∫ x in 0..t, g x) ≤
      sSup ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne', ←
      integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h'_int, hg.intervalIntegral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact (continuous_primitive h'_int 0).continuousOn.le_sSup_image_Icc
    (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_atTop_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.comp (tendsto_id.atTop_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_atBot_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.comp (tendsto_id.atBot_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
theorem tendsto_atTop_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop :=
  hg.tendsto_atTop_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
theorem tendsto_atBot_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  exact hg.tendsto_atBot_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

end RealValued

end Periodic

end Function
