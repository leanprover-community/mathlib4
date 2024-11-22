/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Kernel.Basic

/-!
# Measurability of the integral against a kernel

The Lebesgue integral of a measurable function against a kernel is measurable. The Bochner integral
is strongly measurable.

## Main statements

* `Measurable.lintegral_kernel_prod_right`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable,
  for an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` such that `uncurry f`
  is measurable.
* `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right`: the function
  `a ↦ ∫ b, f a b ∂(κ a)` is measurable, for an s-finite kernel `κ : Kernel α β` and a function
  `f : α → β → E` such that `uncurry f` is measurable.

-/


open MeasureTheory ProbabilityTheory Function Set Filter

open scoped MeasureTheory ENNReal Topology

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : Kernel α β} {η : Kernel (α × β) γ} {a : α}

namespace ProbabilityTheory

namespace Kernel

/-- This is an auxiliary lemma for `measurable_kernel_prod_mk_left`. -/
theorem measurable_kernel_prod_mk_left_of_finite {t : Set (α × β)} (ht : MeasurableSet t)
    (hκs : ∀ a, IsFiniteMeasure (κ a)) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) := by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  -- Porting note: added motive
  refine MeasurableSpace.induction_on_inter
    (C := fun t => Measurable fun a => κ a (Prod.mk a ⁻¹' t))
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ ht
  ·-- case `t = ∅`
    simp only [preimage_empty, measure_empty, measurable_const]
  · -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intro t' ht'
    simp only [Set.mem_image2, Set.mem_setOf_eq, exists_and_left] at ht'
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht'
    classical
    simp_rw [mk_preimage_prod_right_eq_if]
    have h_eq_ite : (fun a => κ a (ite (a ∈ t₁) t₂ ∅)) = fun a => ite (a ∈ t₁) (κ a t₂) 0 := by
      ext1 a
      split_ifs
      exacts [rfl, measure_empty]
    rw [h_eq_ite]
    exact Measurable.ite ht₁ (Kernel.measurable_coe κ ht₂) measurable_const
  · -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intro t' ht' h_meas
    have h_eq_sdiff : ∀ a, Prod.mk a ⁻¹' t'ᶜ = Set.univ \ Prod.mk a ⁻¹' t' := by
      intro a
      ext1 b
      simp only [mem_compl_iff, mem_preimage, mem_diff, mem_univ, true_and]
    simp_rw [h_eq_sdiff]
    have :
      (fun a => κ a (Set.univ \ Prod.mk a ⁻¹' t')) = fun a =>
        κ a Set.univ - κ a (Prod.mk a ⁻¹' t') := by
      ext1 a
      rw [← Set.diff_inter_self_eq_diff, Set.inter_univ, measure_diff (Set.subset_univ _)]
      · exact (measurable_prod_mk_left ht').nullMeasurableSet
      · exact measure_ne_top _ _
    rw [this]
    exact Measurable.sub (Kernel.measurable_coe κ MeasurableSet.univ) h_meas
  · -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intro f h_disj hf_meas hf
    have h_Union :
      (fun a => κ a (Prod.mk a ⁻¹' ⋃ i, f i)) = fun a => κ a (⋃ i, Prod.mk a ⁻¹' f i) := by
      ext1 a
      congr with b
      simp only [mem_iUnion, mem_preimage]
    rw [h_Union]
    have h_tsum :
      (fun a => κ a (⋃ i, Prod.mk a ⁻¹' f i)) = fun a => ∑' i, κ a (Prod.mk a ⁻¹' f i) := by
      ext1 a
      rw [measure_iUnion]
      · intro i j hij s hsi hsj b hbs
        have habi : {(a, b)} ⊆ f i := by rw [Set.singleton_subset_iff]; exact hsi hbs
        have habj : {(a, b)} ⊆ f j := by rw [Set.singleton_subset_iff]; exact hsj hbs
        simpa only [Set.bot_eq_empty, Set.le_eq_subset, Set.singleton_subset_iff,
          Set.mem_empty_iff_false] using h_disj hij habi habj
      · exact fun i => (@measurable_prod_mk_left α β _ _ a) (hf_meas i)
    rw [h_tsum]
    exact Measurable.ennreal_tsum hf

theorem measurable_kernel_prod_mk_left [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) := by
  rw [← Kernel.kernel_sum_seq κ]
  have : ∀ a, Kernel.sum (Kernel.seq κ) a (Prod.mk a ⁻¹' t) =
      ∑' n, Kernel.seq κ n a (Prod.mk a ⁻¹' t) := fun a =>
    Kernel.sum_apply' _ _ (measurable_prod_mk_left ht)
  simp_rw [this]
  refine Measurable.ennreal_tsum fun n => ?_
  exact measurable_kernel_prod_mk_left_of_finite ht inferInstance

theorem measurable_kernel_prod_mk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s)
    (a : α) : Measurable fun b => η (a, b) (Prod.mk b ⁻¹' s) := by
  have : ∀ b, Prod.mk b ⁻¹' s = {c | ((a, b), c) ∈ {p : (α × β) × γ | (p.1.2, p.2) ∈ s}} := by
    intro b; rfl
  simp_rw [this]
  refine (measurable_kernel_prod_mk_left ?_).comp measurable_prod_mk_left
  exact (measurable_fst.snd.prod_mk measurable_snd) hs

theorem measurable_kernel_prod_mk_right [IsSFiniteKernel κ] {s : Set (β × α)}
    (hs : MeasurableSet s) : Measurable fun y => κ y ((fun x => (x, y)) ⁻¹' s) :=
  measurable_kernel_prod_mk_left (measurableSet_swap_iff.mpr hs)

end Kernel

open ProbabilityTheory.Kernel

section Lintegral

variable [IsSFiniteKernel κ] [IsSFiniteKernel η]

/-- Auxiliary lemma for `Measurable.lintegral_kernel_prod_right`. -/
theorem Kernel.measurable_lintegral_indicator_const {t : Set (α × β)} (ht : MeasurableSet t)
    (c : ℝ≥0∞) : Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a := by
  -- Porting note: was originally by
  -- `simp_rw [lintegral_indicator_const_comp measurable_prod_mk_left ht _]`
  -- but this has no effect, so added the `conv` below
  conv =>
    congr
    ext
    erw [lintegral_indicator_const_comp measurable_prod_mk_left ht _]
  exact Measurable.const_mul (measurable_kernel_prod_mk_left ht) c

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `Measurable (uncurry f)`), the integral `a ↦ ∫⁻ b, f a b ∂(κ a)` is
measurable. -/
theorem _root_.Measurable.lintegral_kernel_prod_right {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox (uncurry f)
  have h : ∀ a, ⨆ n, F n a = uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prod_mk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox (uncurry f) hij _
  simp_rw [this]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (P := fun f => Measurable (fun (a : α) => ∫⁻ (b : β), f (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact Kernel.measurable_lintegral_indicator_const (κ := κ) ht c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext1 a
      rw [Pi.add_apply]
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): was `rw` (`Function.comp` reducibility)
      erw [lintegral_add_left (g₁.measurable.comp measurable_prod_mk_left)]
      simp_rw [Function.comp_apply]
    rw [h_add]
    exact Measurable.add hm₁ hm₂

theorem _root_.Measurable.lintegral_kernel_prod_right' {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f (a, b) ∂κ a := by
  refine Measurable.lintegral_kernel_prod_right ?_
  have : (uncurry fun (a : α) (b : β) => f (a, b)) = f := by
    ext x; rw [uncurry_apply_pair]
  rwa [this]

theorem _root_.Measurable.lintegral_kernel_prod_right'' {f : β × γ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ∫⁻ y, f (x, y) ∂η (a, x) := by
  -- Porting note: used `Prod.mk a` instead of `fun x => (a, x)` below
  change
    Measurable
      ((fun x => ∫⁻ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ Prod.mk a)
  -- Porting note: specified `κ`, `f`.
  refine (Measurable.lintegral_kernel_prod_right' (κ := η)
    (f := (fun u ↦ f (u.fst.snd, u.snd))) ?_).comp measurable_prod_mk_left
  exact hf.comp (measurable_fst.snd.prod_mk measurable_snd)

theorem _root_.Measurable.setLIntegral_kernel_prod_right {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f a b ∂κ a := by
  simp_rw [← lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_right

@[deprecated (since := "2024-06-29")]
alias _root_.Measurable.set_lintegral_kernel_prod_right :=
  _root_.Measurable.setLIntegral_kernel_prod_right

theorem _root_.Measurable.lintegral_kernel_prod_left' {f : β × α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂κ y :=
  (measurable_swap_iff.mpr hf).lintegral_kernel_prod_right'

theorem _root_.Measurable.lintegral_kernel_prod_left {f : β → α → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂κ y :=
  hf.lintegral_kernel_prod_left'

theorem _root_.Measurable.setLIntegral_kernel_prod_left {f : β → α → ℝ≥0∞}
    (hf : Measurable (uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun b => ∫⁻ a in s, f a b ∂κ b := by
  simp_rw [← lintegral_restrict κ hs]; exact hf.lintegral_kernel_prod_left

@[deprecated (since := "2024-06-29")]
alias _root_.Measurable.set_lintegral_kernel_prod_left :=
  _root_.Measurable.setLIntegral_kernel_prod_left

theorem _root_.Measurable.lintegral_kernel {f : β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f b ∂κ a :=
  Measurable.lintegral_kernel_prod_right (hf.comp measurable_snd)

theorem _root_.Measurable.setLIntegral_kernel {f : β → ℝ≥0∞} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) : Measurable fun a => ∫⁻ b in s, f b ∂κ a := by
  -- Porting note: was term mode proof (`Function.comp` reducibility)
  refine Measurable.setLIntegral_kernel_prod_right ?_ hs
  convert hf.comp measurable_snd

@[deprecated (since := "2024-06-29")]
alias _root_.Measurable.set_lintegral_kernel := _root_.Measurable.setLIntegral_kernel

end Lintegral

end ProbabilityTheory
