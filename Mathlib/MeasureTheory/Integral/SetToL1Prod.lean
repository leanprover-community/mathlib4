/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.SetToL1

/-!
# SetToL1 and products
-/

public section

open Function TopologicalSpace Set Filter
open scoped Topology

namespace MeasureTheory

variable {X Y E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {mX : MeasurableSpace X} {μ : Measure X}
  {mY : MeasurableSpace Y} {ν : Measure Y}
  {T : Set Y → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive ν T C)

omit [NormedSpace ℝ E] in
theorem measurableSet_integrable [SFinite ν] ⦃f : X → Y → E⦄
    (hf : StronglyMeasurable (uncurry f)) : MeasurableSet {x | Integrable (f x) ν} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_prod_right hf.enorm) measurable_const

/-
theorem stronglyMeasurable_prodMk_left (hT : DominatedFinMeasAdditive ν T C)
    {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simp [mk_preimage_prod_right_eq_if]
    have : (fun x ↦ T (if x ∈ s then t else ∅)) = fun x ↦ if x ∈ s then T t else T ∅ := by grind
    simp_rw [this, hT.1.map_empty_eq_zero]
    exact (stronglyMeasurable_const (b := T t)).indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i ↦ ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i ↦ measurable_prodMk_left (hfm i), hfd.mono fun _ _ ↦ .preimage _]
    exact StronglyMeasurable.hasSum ihf this
-/

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. This version has `f` in curried form. -/
theorem StronglyMeasurable.setToFun_prod_right [SFinite ν]
    (h'T : ∀ (s : Set (X × Y)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : X → Y → E⦄ (hf : StronglyMeasurable (uncurry f)) :
    StronglyMeasurable fun x => setToFun ν T hT (f x) := by
  classical
  by_cases hF : CompleteSpace F; swap;
  · simp [setToFun, hF, stronglyMeasurable_const]
  borelize E
  haveI : SeparableSpace (range (uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (X × Y) E :=
    SimpleFunc.approxOn _ hf.measurable (range (uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → X → SimpleFunc Y E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : ℕ → X → F := fun n =>
    {x | Integrable (f x) ν}.indicator fun x => (s' n x).setToSimpleFunc T
  have hf' n : StronglyMeasurable (f' n) := by
    refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    have : ∀ x, ((s' n x).range.filter fun x => x ≠ 0) ⊆ (s n).range := by
      intro x; refine Finset.Subset.trans (Finset.filter_subset _ _) ?_; intro y
      simp_rw [SimpleFunc.mem_range]; rintro ⟨z, rfl⟩; exact ⟨(x, z), rfl⟩
    simp_rw [SimpleFunc.setToSimpleFunc_eq_sum_of_subset T hT.1.map_empty_eq_zero (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply StronglyMeasurable.apply_continuousLinearMap
    apply h'T
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : X => setToFun ν T hT (f x)) := by
    rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable (f x) ν
    · have (n : _) : Integrable (s' n x) ν := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [mem_setOf_eq, hfx, indicator_of_mem, this,
        ← setToFun_simpleFunc_eq_setToSimpleFunc hT, f']
      refine
        tendsto_setToFun_of_dominated_convergence hT (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · refine fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le ?_ ?_ (x, y) n
        · exact hf.measurable
        · simp
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn ?_ ?_ ?_
        · exact hf.measurable.of_uncurry_left
        · simp
        apply subset_closure
        simp [-uncurry_apply_pair]
    · simp [f', hfx, setToFun_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) Fubini's theorem is measurable. -/
theorem StronglyMeasurable.setToFun_prod_right' [SFinite ν]
    (h'T : ∀ (s : Set (X × Y)), MeasurableSet s → StronglyMeasurable fun x => T (Prod.mk x ⁻¹' s))
    ⦃f : X × Y → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => setToFun ν T hT (fun y ↦ f (x, y)) := by
  rw [← uncurry_curry f] at hf
  apply hf.setToFun_prod_right hT h'T

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) the symmetric version of Fubini's theorem is measurable.
This version has `f` in curried form. -/
theorem StronglyMeasurable.setToFun_prod_left [SFinite μ]
    {T : Set X → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (X × Y)), MeasurableSet s → StronglyMeasurable fun y => T ((·, y) ⁻¹' s))
    ⦃f : X → Y → E⦄ (hf : StronglyMeasurable (uncurry f)) :
    StronglyMeasurable fun y => setToFun μ T hT (f · y) :=
  (hf.comp_measurable measurable_swap).setToFun_prod_right' hT
    (fun s hs ↦ h'T (Prod.swap ⁻¹' s) (measurable_swap hs))

/-- The `setToFun` operation is measurable. This shows that the integrand of (the right-hand-side
of) the symmetric version of Fubini's theorem is measurable. -/
theorem StronglyMeasurable.setToFun_prod_left' [SFinite μ]
    {T : Set X → E →L[ℝ] F} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (h'T : ∀ (s : Set (X × Y)), MeasurableSet s → StronglyMeasurable fun y => T ((·, y) ⁻¹' s))
    ⦃f : X × Y → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => setToFun μ T hT (fun x ↦ f (x, y)) := by
  rw [← uncurry_curry f] at hf
  apply hf.setToFun_prod_left hT h'T

end MeasureTheory
