/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Notation

import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Chain rule for the Kullback-Leibler divergence

## Main statements

* `todo` :

-/

@[expose] public section

open Real MeasureTheory Set ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- Auxiliary lemma for `rnDeriv_measure_compProd_left`. -/
lemma rnDeriv_measure_compProd_left_of_ac (hμν : μ ≪ ν) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  have h_key t₁ t₂ : MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ x in t₁ ×ˢ t₂, (∂μ ⊗ₘ κ/∂ν ⊗ₘ κ) x ∂ν ⊗ₘ κ = ∫⁻ x in t₁ ×ˢ t₂, (∂μ/∂ν) x.1 ∂ν ⊗ₘ κ := by
    intro ht₁ ht₂
    rw [Measure.setLIntegral_rnDeriv (hμν.compProd_left _),
      Measure.setLIntegral_compProd (by fun_prop) ht₁ ht₂]
    simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter]
    rw [setLIntegral_rnDeriv_mul hμν (κ.measurable_coe ht₂).aemeasurable ht₁,
      Measure.compProd_apply_prod ht₁ ht₂]
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h_key t₁ t₂ ht₁ ht₂
  · intro t ht ht_eq
    rw [setLIntegral_compl ht, ht_eq, setLIntegral_compl ht]
    · congr 1
      specialize h_key .univ .univ .univ .univ
      simpa only [univ_prod_univ, Measure.restrict_univ] using h_key
    · rw [← ht_eq]
      exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
    · exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

lemma todo (μ ν : Measure α) (κ η : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
  conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
  rw [Measure.compProd_add_left]
  have h := Measure.rnDeriv_add' (μ.singularPart ν ⊗ₘ κ) (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)
    (ν ⊗ₘ η)
  have h2 : ∂μ.singularPart ν ⊗ₘ κ/∂ν ⊗ₘ η =ᵐ[ν ⊗ₘ η] 0 := by
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ ?_
    · exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart _) _ _
    · exact Measure.AbsolutelyContinuous.rfl
  filter_upwards [h, h2] with x hx hx2
  simp [hx, hx2]

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)` (with the same kernel) equals `∂μ/∂ν`. -/
lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  refine (todo μ ν κ κ).symm.trans ?_
  refine (rnDeriv_measure_compProd_left_of_ac
    (MeasureTheory.withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) κ).trans ?_
  refine Measure.ae_eq_compProd_of_ae_eq_fst _ (by fun_prop) (by fun_prop) ?_
  exact Measure.rnDeriv_withDensity ν (by fun_prop)

lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p)
      =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := by
  refine Filter.EventuallyEq.trans ?_ (Measure.rnDeriv_mul_rnDeriv h_ac)
  filter_upwards [rnDeriv_measure_compProd_left μ ν η] with p hp
  rw [Pi.mul_apply, hp, mul_comm]

section ConvexOn

variable {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

lemma _root_.ConvexOn.affine_le_of_mem_interior (hf : ConvexOn ℝ s f) {x y : ℝ}
    (hx : x ∈ interior s) (hy : y ∈ s) :
    derivWithin f (Set.Ioi x) x * y + (f x - derivWithin f (Set.Ioi x) x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : derivWithin f (Set.Ioi x) x ≤ slope f x y :=
      hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ derivWithin f (Set.Ioi x) x := by
      have := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
        (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
      rwa [slope_comm]
    rw [slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma _root_.Convex.subsingleton_of_interior_eq_empty (hs : Convex ℝ s) (h : interior s = ∅) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra h_ne
  wlog h_lt : x < y
  · refine this hs h hy hx (Ne.symm h_ne) ?_
    exact lt_of_le_of_ne (not_lt.mp h_lt) (Ne.symm h_ne)
  · have h_subset : Set.Icc x y ⊆ s := by
      rw [← segment_eq_Icc h_lt.le]
      exact hs.segment_subset hx hy
    have : Set.Ioo x y ⊆ interior s := by
      rw [← interior_Icc]
      exact interior_mono h_subset
    simp only [h, Set.subset_empty_iff, Set.Ioo_eq_empty_iff] at this
    exact this h_lt

lemma _root_.ConvexOn.exists_affine_le (hf : ConvexOn ℝ s f) (hs : Convex ℝ s) :
    ∃ c c', ∀ x ∈ s, c * x + c' ≤ f x := by
  cases Set.eq_empty_or_nonempty (interior s) with
  | inl h => -- there is at most one point in `s`
    have hs_sub : s.Subsingleton := hs.subsingleton_of_interior_eq_empty h
    cases Set.eq_empty_or_nonempty s with
    | inl h' => simp [h']
    | inr h' => -- there is exactly one point in `s`
      obtain ⟨x, hxs⟩ := h'
      refine ⟨0, f x, fun y hys ↦ ?_⟩
      simp [hs_sub hxs hys]
  | inr h => -- there is a point in the interior of `s`
    obtain ⟨x, hx⟩ := h
    refine ⟨derivWithin f (Set.Ioi x) x, f x - derivWithin f (Set.Ioi x) x * x, fun y hy ↦ ?_⟩
    exact hf.affine_le_of_mem_interior hx hy

end ConvexOn

lemma rnDeriv_add_self_right (ν μ : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x + 1)⁻¹ := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [μ.rnDeriv_add' ν ν, ν.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply, h1, Pi.add_apply, h2, inv_eq_iff_eq_inv] at h3
  rw [h3]

lemma rnDeriv_add_self_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x ↦ 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self_right ν μ] with a h4 h5 h6
    rw [h5, Pi.add_apply] at h4
    nth_rewrite 1 [h4]
    rw [h6]
    simp only [ne_eq, ENNReal.inv_eq_top, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      ENNReal.add_sub_cancel_right]
  filter_upwards [this, μ.rnDeriv_lt_top ν] with a ha ha_lt_top
  rw [ha, div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rw [ENNReal.mul_inv_cancel] at h
  · exact h
  · simp
  · simp [ha_lt_top.ne]

lemma _root_.MeasureTheory.Measure.rnDeriv_eq_div (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  filter_upwards [rnDeriv_add_self_right ν μ, rnDeriv_add_self_left μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1, ha2, ENNReal.div_eq_inv_mul, inv_inv, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel, one_mul]
  · simp
  · simp [ha_lt_top.ne]

lemma rnDeriv_div_rnDeriv {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    (fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x)
      =ᵐ[μ + ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv ?_
  swap; · rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h_ac : μ + ν ≪ ξ := by
    refine (Measure.AbsolutelyContinuous.add hμ hν).trans ?_
    have : ξ + ξ = (2 : ℝ≥0∞) • ξ := by
      ext
      simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [two_mul]
    rw [this]
    exact Measure.absolutelyContinuous_of_le_smul le_rfl
  filter_upwards [h_ac h1, h_ac h2, h_ac <| (μ + ν).rnDeriv_lt_top ξ, ν.rnDeriv_lt_top (μ + ν),
    Measure.rnDeriv_pos h_ac] with a h1 h2 h_lt_top1 h_lt_top2 h_pos
  rw [← h1, ← h2, Pi.mul_apply, Pi.mul_apply, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr h_lt_top1.ne) (Or.inl h_lt_top2.ne), div_eq_mul_inv, mul_assoc,
    mul_comm ((μ + ν).rnDeriv ξ a), mul_assoc, ENNReal.inv_mul_cancel h_pos.ne' h_lt_top1.ne,
    mul_one]

lemma rnDeriv_eq_div' {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x := by
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  filter_upwards [μ.rnDeriv_eq_div ν, hν_ac (rnDeriv_div_rnDeriv hμ hν)] with a h1 h2
  exact h1.trans h2.symm

/-- Singular part set of μ with respect to ν. -/
def singularPartSet (μ ν : Measure α) := {x | ν.rnDeriv (μ + ν) x = 0}

lemma measurableSet_singularPartSet : MeasurableSet (singularPartSet μ ν) :=
  Measure.measurable_rnDeriv _ _ (measurableSet_singleton _)

lemma measure_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ν (singularPartSet μ ν) = 0 := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h1 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = 0 := by
    calc ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν)
      = ∫⁻ _ in s, 0 ∂(μ + ν) := setLIntegral_congr_fun_ae hs (ae_of_all _ (fun _ hx ↦ hx))
    _ = 0 := lintegral_zero
  have h2 : ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) = ν s :=
    Measure.setLIntegral_rnDeriv hν_ac _
  exact h2.symm.trans h1

lemma measure_inter_compl_singularPartSet' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, μ.rnDeriv ν x ∂ν := by
  let s := singularPartSet μ ν
  have hs : MeasurableSet s := measurableSet_singularPartSet
  have hν_ac : ν ≪ μ + ν := by rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have : μ (t ∩ sᶜ) = ∫⁻ x in t ∩ sᶜ,
      ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
    have : ∫⁻ x in t ∩ sᶜ,
          ν.rnDeriv (μ + ν) x * (μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x) ∂(μ + ν)
        = ∫⁻ x in t ∩ sᶜ, μ.rnDeriv (μ + ν) x ∂(μ + ν) := by
      refine setLIntegral_congr_fun_ae (ht.inter hs.compl) ?_
      filter_upwards [ν.rnDeriv_lt_top (μ + ν)] with x hx_top hx
      rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
      · simp only [Set.mem_inter_iff, Set.mem_compl_iff, s] at hx
        exact hx.2
      · exact hx_top.ne
    rw [this, Measure.setLIntegral_rnDeriv (rfl.absolutelyContinuous.add_right _)]
  rw [this, setLIntegral_rnDeriv_mul hν_ac (by fun_prop) (ht.inter hs.compl)]
  refine setLIntegral_congr_fun_ae (ht.inter hs.compl) ?_
  filter_upwards [μ.rnDeriv_eq_div ν] with x hx
  exact hx ▸ fun _ ↦ rfl

lemma measure_inter_compl_singularPartSet (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {t : Set α} (ht : MeasurableSet t) :
    μ (t ∩ (singularPartSet μ ν)ᶜ) = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
  rw [measure_inter_compl_singularPartSet' _ _ ht]
  symm
  calc ∫⁻ x in t, μ.rnDeriv ν x ∂ν
    = ∫⁻ x in (singularPartSet μ ν) ∩ t, μ.rnDeriv ν x ∂ν
      + ∫⁻ x in (singularPartSet μ ν)ᶜ ∩ t, μ.rnDeriv ν x ∂ν := by
        rw [← Measure.restrict_restrict measurableSet_singularPartSet,
          ← Measure.restrict_restrict measurableSet_singularPartSet.compl,
          lintegral_add_compl _ measurableSet_singularPartSet]
  _ = ∫⁻ x in t ∩ (singularPartSet μ ν)ᶜ, μ.rnDeriv ν x ∂ν := by
        rw [setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left ?_),
          Set.inter_comm, zero_add]
        exact measure_singularPartSet _ _

lemma restrict_compl_singularPartSet_eq_withDensity
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν)ᶜ = ν.withDensity (μ.rnDeriv ν) := by
  ext t ht
  rw [Measure.restrict_apply ht, measure_inter_compl_singularPartSet μ ν ht, withDensity_apply _ ht]

lemma restrict_singularPartSet_eq_singularPart (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.restrict (singularPartSet μ ν) = μ.singularPart ν := by
  have h_add := μ.haveLebesgueDecomposition_add ν
  rw [← restrict_compl_singularPartSet_eq_withDensity μ ν] at h_add
  have : μ = μ.restrict (singularPartSet μ ν) + μ.restrict (singularPartSet μ ν)ᶜ := by
    rw [Measure.restrict_add_restrict_compl measurableSet_singularPartSet]
  conv_lhs at h_add => rw [this]
  exact (Measure.add_left_inj _ _ _).mp h_add

lemma ae_rnDeriv_ne_zero_imp_of_ae_aux [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) (hμν : μ ≪ ν) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  rw [ν.haveLebesgueDecomposition_add μ, ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : ∀ᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop)
        (fun s hs _ ↦ ?_)
      simp only [lintegral_const, Measure.restrict_apply .univ, Set.univ_inter, zero_mul]
      rw [← restrict_singularPartSet_eq_singularPart, Measure.restrict_restrict hs,
        Measure.setLIntegral_rnDeriv hμν]
      exact measure_mono_null Set.inter_subset_right (measure_singularPartSet ν _)
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  · have h_ac : μ.withDensity (ν.rnDeriv μ) ≪ μ := withDensity_absolutelyContinuous _ _
    rw [← ν.haveLebesgueDecomposition_add μ]
    suffices ∀ᵐx ∂μ, μ.rnDeriv ν x ≠ 0 → p x from h_ac this
    filter_upwards [h] with _ h _ using h

lemma ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  suffices ∀ᵐ a ∂ν, (ν.withDensity (μ.rnDeriv ν)).rnDeriv ν a ≠ 0 → p a by
    have h := ν.rnDeriv_withDensity (μ.measurable_rnDeriv ν)
    filter_upwards [this, h] with x hx1 hx2
    rwa [hx2] at hx1
  refine ae_rnDeriv_ne_zero_imp_of_ae_aux ?_ (withDensity_absolutelyContinuous _ _)
  exact (Measure.absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)) h

section Integrable

variable {E : Type*} {f g : ℝ → ℝ}

lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (fun a ↦ f ((∂μ/∂ν) a).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd : (fun p ↦ (∂μ/∂ν) p.1 * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p) =ᵐ[ν ⊗ₘ η]
      ∂μ ⊗ₘ κ/∂ν ⊗ₘ η := rnDeriv_compProd hκη ν
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have h_integrable := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at h_integrable h_int
  rotate_left
  · exact (hf.comp_measurable (by fun_prop)).aestronglyMeasurable
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  have h_ae1 : ∀ᵐ a ∂ν, (∂μ/∂ν) a * ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a) = (∂μ/∂ν) a := by
    suffices ∀ᵐ a ∂ν, (∂μ/∂ν) a ≠ 0 → ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a) = 1 by
      filter_upwards [this] with a ha
      by_cases h0 : (∂μ/∂ν) a = 0
      · simp [h0]
      · rw [ha h0, mul_one]
    refine ae_rnDeriv_ne_zero_imp_of_ae ?_
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) measurable_const ?_
    intro s hs hsμ
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
    calc ∫⁻ a in s, ∫⁻ b, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a ∂μ
    _ = ∫⁻ a in s, ∫⁻ b in univ, (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) (a, b) ∂η a ∂μ := by simp
    _ = μ s := by
      rw [← Measure.setLIntegral_compProd (by fun_prop) hs .univ, Measure.setLIntegral_rnDeriv hκη,
        Measure.compProd_apply_prod hs .univ]
      simp
  have h_ae2 : ∀ᵐ a ∂ν, ∀ᵐ b ∂(η a), (∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) =
      (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) := by
    rwa [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_compProd
    simp only [measurableSet_setOf]
    fun_prop
  filter_upwards [h_ae1, h_ae2, h_lt_top, h_integrable.1, h_int.1]
    with a h_eq_one h_mul_eq h_lt_top h_int' h_int
  calc f ((∂μ/∂ν) a).toReal
    = f ((∂μ/∂ν) a * ∫⁻ b, (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a)).toReal := by simp [h_eq_one]
  _ = f (∫⁻ b, (∂μ/∂ν) a * (∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) (a, b) ∂(η a)).toReal := by
    rw [lintegral_const_mul _ (by fun_prop)]
  _ = f (∫⁻ b, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b) ∂η a).toReal := by
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [h_mul_eq] with b hb using hb
  _ = f (∫ b, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a) := by
    rw [integral_toReal (by fun_prop) h_lt_top]
  _ ≤ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (a, b)).toReal ∂η a := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_int' h_int

lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun p ↦ f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    Integrable (fun a ↦ f ((∂μ/∂ν) a).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f ((∂μ/∂ν) a).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) (x, b)).toReal ∂(η x)) ?_ ?_ ?_ (by fun_prop) ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ h _ ENNReal.toReal_nonneg
  · exact hf_cvx.apply_rnDeriv_ae_le_integral hf hf_cont hf_int hκη
  · exact hf_int.integral_compProd

end Integrable

lemma integrable_llr_of_integrable_llr_compProd
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  replace h_int := convexOn_mul_log.integrable_apply_rnDeriv_of_integrable_compProd
    continuous_mul_log.stronglyMeasurable continuous_mul_log.continuousOn h_int hκη_ac
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int

lemma aux2 [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ p ∂(ν ⊗ₘ η), ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal =
      (((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * (log ((∂μ/∂ν) p.1).toReal +
        log ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) p).toReal)) := by
  filter_upwards [rnDeriv_compProd h_ac ν] with p hp
  simp_rw [← hp]
  simp only [ENNReal.toReal_mul]
  by_cases h_zero1 : ((∂μ/∂ν) p.1).toReal = 0
  · simp [h_zero1]
  by_cases h_zero2 : ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal = 0
  · simp [h_zero2]
  simp [log_mul h_zero1 h_zero2]

lemma aux [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
       Integrable (fun x ↦ log ((∂μ/∂ν) x.1).toReal +
         log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  have h_rnDeriv : (fun p ↦ (∂μ/∂ν) p.1 * (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p) =ᵐ[ν ⊗ₘ η]
      ∂μ ⊗ₘ κ/∂ν ⊗ₘ η := rnDeriv_compProd h_ac_κη ν
  rw [← integrable_rnDeriv_mul_log_iff h_ac, integrable_congr (aux2 h_ac_κη)]
  exact integrable_rnDeriv_smul_iff h_ac

lemma integrable_llr_compProd_iff [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac, integrable_congr (aux2 h_ac_κη)]
  have : Integrable (fun x ↦ ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal *
        (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal)) (ν ⊗ₘ η) ↔
      Integrable (fun x ↦ (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal))
        (μ ⊗ₘ κ) := integrable_rnDeriv_smul_iff h_ac
  rw [this]
  have h_iff_κ : Integrable (llr μ ν) μ ↔ Integrable (fun x ↦ llr μ ν x.1) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    swap; · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
    simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
      Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
      true_and]
    rw [← integrable_norm_iff (by fun_prop)]
    simp
  rw [h_iff_κ]
  -- goal of the form `Integrable (f + g) ↔ Integrable f ∧ Integrable g`
  refine ⟨fun h_int ↦ ?_, fun ⟨h_int1, h_int2⟩ ↦ h_int1.add h_int2⟩
  rw [← aux h_ac] at h_int
  have h_int1 := integrable_llr_of_integrable_llr_compProd h_ac h_int
  rw [h_iff_κ] at h_int1
  rw [aux h_ac, integrable_add_iff_integrable_right'] at h_int
  · refine ⟨h_int1, h_int⟩
  · exact h_int1

variable (μ ν κ η) in
/-- **Chain rule** for the Kullback-Leibler divergence, with conditional KL expressed using
composition-products.
This version holds without any assumption on the measurable spaces. -/
theorem klDiv_compProd_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
  have h_ac_iff : μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.absolutelyContinuous_compProd_iff
  -- first, if we don't have absolute continuity, both sides are `∞`
  by_cases h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac h_ac]
    rw [h_ac_iff] at h_ac
    simp only [not_and_or] at h_ac
    cases h_ac with
    | inl h => simp [h]
    | inr h => simp [h]
  -- same if we don't have integrability
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · rw [klDiv_of_not_integrable h_int]
    rw [integrable_llr_compProd_iff h_ac] at h_int
    simp only [not_and_or] at h_int
    cases h_int with
    | inl h => simp [h]
    | inr h => simp [h]
  -- now we can use the Radon-Nikodym derivatives to express the KL divergences
  have ⟨h_ac_μν, h_ac_κη⟩ := h_ac_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  rw [klDiv_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac_μν h_int_μν,
    klDiv_of_ac_of_integrable h_ac_κη h_int_κη]
  rw [← ENNReal.ofReal_add]
  rotate_left
  · exact integral_llr_add_sub_measure_univ_nonneg h_ac_μν h_int_μν
  · exact integral_llr_add_sub_measure_univ_nonneg h_ac_κη h_int_κη
  congr
  simp_rw [measureReal_def, Measure.compProd_apply_univ]
  rw [add_sub_cancel_right]
  suffices ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) by rw [this]; ring
  have h_int1 : Integrable (fun p ↦ log ((∂μ/∂ν) p.1).toReal) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    · simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
        Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
        true_and]
      rw [← integrable_norm_iff (by fun_prop)] at h_int_μν
      convert h_int_μν
    · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  calc ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η) := by
    rw [integral_rnDeriv_mul_log h_ac]
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
      (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η) :=
    integral_congr_ae (aux2 h_ac_κη)
  _ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ) :=
    integral_rnDeriv_smul h_ac
  _ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) +
      ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ) := by
    rw [integral_add h_int1]
    exact h_int_κη.ofReal
  _ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
    congr
    rw [Measure.integral_compProd h_int1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl

end InformationTheory
