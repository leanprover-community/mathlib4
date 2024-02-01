/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Prod.Basic

/-!


-/


open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {α β ι : Type*} [MeasurableSpace α]

section IsCDFLike

structure IsCDFLike (f : α → ℚ → ℝ) : Prop where
  mono : ∀ a, Monotone (f a)
  nonneg : ∀ a q, 0 ≤ f a q
  le_one : ∀ a q, f a q ≤ 1
  tendsto_atTop_one : ∀ a, Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : ∀ a, Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ a, ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t
  measurable : ∀ q, Measurable (fun a ↦ f a q)

end IsCDFLike

variable {f : α → ℚ → ℝ} (hf : IsCDFLike f)

/-- Conditional cdf of the measure given the value on `α`, as a plain function. This is an auxiliary
definition used to define `cond_cdf`. -/
noncomputable irreducible_def todo1 (f : α → ℚ → ℝ) : α → ℝ → ℝ :=
  fun a t ↦ ⨅ r : { r' : ℚ // t < r' }, f a r

lemma todo1_eq (a : α) (r : ℚ) :
    todo1 f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r, todo1]
  refine' Equiv.iInf_congr _ _
  · exact
      { toFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        invFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        left_inv := fun t ↦ by simp only [Subtype.coe_eta]
        right_inv := fun t ↦ by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]

theorem todo1_nonneg (a : α) (r : ℝ) : 0 ≤ todo1 f a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [todo1_def]
  exact le_ciInf fun r' ↦ hf.nonneg a _

theorem bddBelow_range_gt (a : α) (x : ℝ) :
    BddBelow (range fun r : { r' : ℚ // x < ↑r' } ↦ f a r) := by
  refine' ⟨0, fun z ↦ _⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _

theorem monotone_todo1 (a : α) : Monotone (todo1 f a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [todo1_def]
  refine' le_ciInf fun r ↦ (ciInf_le _ _).trans_eq _
  · exact bddBelow_range_gt hf a x
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl

theorem continuousWithinAt_todo1_Ici (a : α) (x : ℝ) :
    ContinuousWithinAt (todo1 f a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert Monotone.tendsto_nhdsWithin_Ioi (monotone_todo1 hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, todo1 f a r = ⨅ r : { r' : ℚ // x < r' }, todo1 f a r := by
    refine' Real.iInf_Ioi_eq_iInf_rat_gt x _ (monotone_todo1 hf a)
    refine' ⟨0, fun z ↦ _⟩
    rintro ⟨u, -, rfl⟩
    exact todo1_nonneg hf a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, todo1 f a r =
      ⨅ r : { r' : ℚ // x < r' }, f a r := by
    congr with r
    exact todo1_eq hf a r
  rw [h', h'', ContinuousWithinAt]
  congr!
  rw [todo1_def]

/-! ### Conditional cdf -/


/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable def todo2 (a : α) : StieltjesFunction where
  toFun := todo1 f a
  mono' := monotone_todo1 hf a
  right_continuous' x := continuousWithinAt_todo1_Ici hf a x

theorem todo2_eq (a : α) (r : ℚ) : todo2 hf a r = f a r := todo1_eq hf a r

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem todo2_nonneg (a : α) (r : ℝ) : 0 ≤ todo2 hf a r := todo1_nonneg hf a r

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem todo2_le_one (a : α) (x : ℝ) : todo2 hf a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [todo2_eq]
  refine ciInf_le_of_le (bddBelow_range_gt hf a x) ?_ (hf.le_one _ _)
  exact ⟨r, hrx⟩

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_todo2_atBot (a : α) :
    Tendsto (todo2 hf a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x ↦ exists_rat_btwn (lt_add_one x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q ↦ ⟨q - 1, fun y hy ↦ ?_⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hf.tendsto_atBot_zero a).comp hqs_tendsto) (todo2_nonneg hf a) fun x ↦ ?_
  rw [Function.comp_apply, ← todo2_eq hf]
  exact (todo2 hf a).mono (h_exists x).choose_spec.1.le

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_todo2_atTop (a : α) :
    Tendsto (todo2 hf a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x ↦ exists_rat_btwn (sub_one_lt x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q ↦ ⟨q + 1, fun y hy ↦ ?_⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hf.tendsto_atTop_one a).comp hqs_tendsto)
      tendsto_const_nhds ?_ (todo2_le_one hf a)
  intro x
  rw [Function.comp_apply, ← todo2_eq hf]
  exact (todo2 hf a).mono (le_of_lt (h_exists x).choose_spec.2)

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_todo2 (x : ℝ) : Measurable fun a ↦ todo2 hf a x := by
  have : (fun a ↦ todo2 hf a x) = fun a ↦ ⨅ r : { r' : ℚ // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [todo2_eq]
  rw [this]
  exact measurable_iInf (fun q ↦ hf.measurable q)

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_todo2 (x : ℝ) :
    StronglyMeasurable fun a ↦ todo2 hf a x :=
  (measurable_todo2 hf x).stronglyMeasurable

section Measure

theorem measure_todo2_Iic (a : α) (x : ℝ) :
    (todo2 hf a).measure (Iic x) = ENNReal.ofReal (todo2 hf a x) := by
  rw [← sub_zero (todo2 hf a x)]
  exact (todo2 hf a).measure_Iic (tendsto_todo2_atBot hf a) _

theorem measure_todo2_univ (a : α) : (todo2 hf a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_todo2_atBot hf a) (tendsto_todo2_atTop hf a)

instance instIsProbabilityMeasure_todo2 (a : α) :
    IsProbabilityMeasure (todo2 hf a).measure :=
  ⟨measure_todo2_univ hf a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
theorem measurable_measure_todo2 :
    Measurable fun a ↦ (todo2 hf a).measure := by
  rw [Measure.measurable_measure]
  refine' fun s hs ↦ ?_
  -- Porting note: supplied `C`
  refine' MeasurableSpace.induction_on_inter
    (C := fun s ↦ Measurable fun b ↦ StieltjesFunction.measure (todo2 hf b) s)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ hs
  · simp only [measure_empty, measurable_const]
  · rintro S ⟨u, rfl⟩
    simp_rw [measure_todo2_Iic hf _ u]
    exact (measurable_todo2 hf u).ennreal_ofReal
  · intro t ht ht_cd_meas
    have : (fun a ↦ (todo2 hf a).measure tᶜ) =
        (fun a ↦ (todo2 hf a).measure univ) - fun a ↦ (todo2 hf a).measure t := by
      ext1 a
      rw [measure_compl ht (measure_ne_top (todo2 hf a).measure _), Pi.sub_apply]
    simp_rw [this, measure_todo2_univ hf]
    exact Measurable.sub measurable_const ht_cd_meas
  · intro f hf_disj hf_meas hf_cd_meas
    simp_rw [measure_iUnion hf_disj hf_meas]
    exact Measurable.ennreal_tsum hf_cd_meas

end Measure

end ProbabilityTheory
