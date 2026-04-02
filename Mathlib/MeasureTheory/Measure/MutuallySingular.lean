/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-! # Mutually singular measures

Two measures `μ`, `ν` are said to be mutually singular (`MeasureTheory.Measure.MutuallySingular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`MeasureTheory.Measure.MutuallySingular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `MeasureTheory.Measure.MutuallySingular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/

@[expose] public section


open Set

open MeasureTheory NNReal ENNReal Filter

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

/-- Two measures `μ`, `ν` are said to be mutually singular if there exists a measurable set `s`
such that `μ s = 0` and `ν sᶜ = 0`. -/
def MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0

@[inherit_doc MeasureTheory.Measure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

namespace MutuallySingular

theorem mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ ⊆ s ∪ t) :
    MutuallySingular μ ν := by
  use toMeasurable μ s, measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans hs
  refine measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx ?_) ht
  exact subset_toMeasurable _ _ hxs

/-- A set such that `μ h.nullSet = 0` and `ν h.nullSetᶜ = 0`. -/
def nullSet (h : μ ⟂ₘ ν) : Set α := h.choose

lemma measurableSet_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet := h.choose_spec.1

@[simp]
lemma measure_nullSet (h : μ ⟂ₘ ν) : μ h.nullSet = 0 := h.choose_spec.2.1

@[simp]
lemma measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0 := h.choose_spec.2.2

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
lemma restrict_nullSet (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0 := by simp

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
lemma restrict_compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0 := by simp

@[simp]
theorem zero_right : μ ⟂ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]
theorem symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
  let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

theorem comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]
theorem zero_left : 0 ⟂ₘ μ :=
  zero_right.symm

theorem mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂ :=
  let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩

lemma congr_ac (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν) :
    μ ⟂ₘ ν ↔ μ₂ ⟂ₘ ν₂ :=
  ⟨fun h ↦ h.mono_ac hμ₂μ hν₂ν, fun h ↦ h.mono_ac hμμ₂ hνν₂⟩

theorem mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
  h.mono_ac hμ.absolutelyContinuous hν.absolutelyContinuous

@[simp]
lemma self_iff (μ : Measure α) : μ ⟂ₘ μ ↔ μ = 0 := by
  refine ⟨?_, fun h ↦ by (rw [h]; exact zero_left)⟩
  rintro ⟨s, hs, hμs, hμs_compl⟩
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s, measure_union disjoint_compl_right hs.compl, hμs, hμs_compl,
    add_zero]

@[simp]
theorem sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α} : sum μ ⟂ₘ ν ↔ ∀ i, μ i ⟂ₘ ν := by
  refine ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => ?_⟩
  choose s hsm hsμ hsν using H
  refine ⟨⋂ i, s i, MeasurableSet.iInter hsm, ?_, ?_⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (iInter_subset _ _) (hsμ i)
  · rwa [compl_iInter, measure_iUnion_null_iff]

@[simp]
theorem sum_right {ι : Type*} [Countable ι] {ν : ι → Measure α} : μ ⟂ₘ sum ν ↔ ∀ i, μ ⟂ₘ ν i :=
  comm.trans <| sum_left.trans <| forall_congr' fun _ => comm

@[simp]
theorem add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν := by
  rw [← sum_cond, sum_left, Bool.forall_bool, cond, cond, and_comm]

@[simp]
theorem add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂ :=
  comm.trans <| add_left_iff.trans <| and_congr comm comm

theorem add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
  add_left_iff.2 ⟨h₁, h₂⟩

theorem add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
  add_right_iff.2 ⟨h₁, h₂⟩

theorem smul (r : ℝ≥0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.mono_ac (AbsolutelyContinuous.rfl.smul_left r) AbsolutelyContinuous.rfl

theorem smul_nnreal (r : ℝ≥0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.smul r

lemma restrict (h : μ ⟂ₘ ν) (s : Set α) : μ.restrict s ⟂ₘ ν := by
  refine ⟨h.nullSet, h.measurableSet_nullSet, ?_, h.measure_compl_nullSet⟩
  rw [Measure.restrict_apply h.measurableSet_nullSet]
  exact measure_mono_null Set.inter_subset_left h.measure_nullSet

end MutuallySingular

lemma eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α}
    (h_ac : μ ≪ ν) (h_ms : μ ⟂ₘ ν) :
    μ = 0 := by
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

lemma absolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α}
    (h : μ ≪ ν₁ + ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁ := by
  refine AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s ∩ tᶜ) := by
    conv_lhs => rw [← inter_union_compl s t]
    rw [measure_union, measure_inter_null_of_null_right _ htμ, zero_add]
    · exact (disjoint_compl_right.inter_right' _).inter_left' _
    · exact hs.inter ht.compl
  rw [this]
  refine h ?_
  simp only [Measure.coe_add, Pi.add_apply, add_eq_zero]
  exact ⟨measure_inter_null_of_null_left _ hs_zero, measure_inter_null_of_null_right _ htν₂⟩

lemma _root_.MeasurableEmbedding.mutuallySingular_map {β : Type*} {_ : MeasurableSpace β}
    {f : α → β} (hf : MeasurableEmbedding f) (hμν : μ ⟂ₘ ν) :
    μ.map f ⟂ₘ ν.map f := by
  refine ⟨f '' hμν.nullSet, hf.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hf.map_apply, hf.injective.preimage_image, hμν.measure_nullSet]
  · rw [hf.map_apply, Set.preimage_compl, hf.injective.preimage_image, hμν.measure_compl_nullSet]

set_option backward.isDefEq.respectTransparency false in
lemma exists_null_set_measure_lt_of_disjoint (h : Disjoint μ ν) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ s, μ s = 0 ∧ ν sᶜ ≤ 2 * ε := by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : ∀ n : ℕ, ∃ t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ :
        ∃ x ∈ {m | ∃ t, m = μ t + ν tᶜ}, x < ε * (1 / 2 : ℝ≥0∞) ^ n := by
      refine exists_lt_of_csInf_lt ⟨ν univ, ∅, by simp⟩ <| h₁ ▸ ENNReal.mul_pos ?_ (by simp)
      norm_cast
      exact hε.ne.symm
    exact ⟨t, hm₂⟩
  choose t ht₂ using h₂
  refine ⟨⋂ n, t n, ?_, ?_⟩
  · refine eq_zero_of_le_mul_pow (by simp)
      fun n ↦ ((measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans
      (le_add_right le_rfl)).trans (ht₂ n).le
  · rw [compl_iInter, (by simp [ENNReal.tsum_mul_left, mul_comm] :
      2 * (ε : ℝ≥0∞) = ∑' (n : ℕ), ε * (1 / 2 : ℝ≥0∞) ^ n)]
    refine (measure_iUnion_le _).trans ?_
    exact ENNReal.summable.tsum_le_tsum (fun n ↦ (le_add_left le_rfl).trans (ht₂ n).le)
      ENNReal.summable

set_option backward.isDefEq.respectTransparency false in
lemma mutuallySingular_of_disjoint (h : Disjoint μ ν) : μ ⟂ₘ ν := by
  have h' (n : ℕ) : ∃ s, μ s = 0 ∧ ν sᶜ ≤ (1 / 2) ^ n := by
    convert exists_null_set_measure_lt_of_disjoint h (ε := (1 / 2) ^ (n + 1))
      <| pow_pos (by simp) (n + 1)
    conv =>
      -- this tweak is needed due to the known issue of `norm_cast` with numeric fractions
      enter [1, 1]
      equals ((1:ℝ≥0) / (2:ℝ≥0)) => rfl
    norm_cast
    ring
  choose s hs₂ hs₃ using h'
  refine Measure.MutuallySingular.mk (t := (⋃ n, s n)ᶜ) (measure_iUnion_null hs₂) ?_ ?_
  · rw [compl_iUnion]
    refine eq_zero_of_le_mul_pow (ε := 1) (by simp : (1 / 2 : ℝ≥0∞) < 1) <| fun n ↦ ?_
    rw [ENNReal.coe_one, one_mul]
    exact (measure_mono <| iInter_subset_of_subset n fun _ ht ↦ ht).trans (hs₃ n)
  · rw [union_compl_self]

lemma MutuallySingular.disjoint (h : μ ⟂ₘ ν) : Disjoint μ ν := by
  have h_bot_iff (ξ : Measure α) : ξ ≤ ⊥ ↔ ξ = 0 := by
    rw [le_bot_iff]
    rfl
  intro ξ hξμ hξν
  rw [h_bot_iff]
  ext s hs
  simp only [Measure.coe_zero, Pi.zero_apply]
  rw [← inter_union_compl s h.nullSet, measure_union, add_eq_zero]
  · exact ⟨measure_inter_null_of_null_right _ <| absolutelyContinuous_of_le hξμ h.measure_nullSet,
      measure_inter_null_of_null_right _ <| absolutelyContinuous_of_le hξν h.measure_compl_nullSet⟩
  · exact Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right
  · exact hs.inter h.measurableSet_nullSet.compl

lemma MutuallySingular.disjoint_ae (h : μ ⟂ₘ ν) : Disjoint (ae μ) (ae ν) := by
  rw [disjoint_iff_inf_le]
  intro s _
  refine ⟨s ∪ h.nullSetᶜ, ?_, s ∪ h.nullSet, ?_, ?_⟩
  · rw [mem_ae_iff, compl_union, compl_compl]
    exact measure_inter_null_of_null_right _ h.measure_nullSet
  · rw [mem_ae_iff, compl_union]
    exact measure_inter_null_of_null_right _ h.measure_compl_nullSet
  · rw [union_eq_compl_compl_inter_compl, union_eq_compl_compl_inter_compl,
      ← compl_union, compl_compl, inter_union_compl, compl_compl]

lemma disjoint_of_disjoint_ae (h : Disjoint (ae μ) (ae ν)) : Disjoint μ ν := by
  simp_rw [Filter.disjoint_iff, mem_ae_iff] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  rw [disjoint_iff_inf_le]
  have : (⊥ : Measure α) = 0 := rfl
  refine Measure.le_intro fun u hu _ ↦ ?_
  simp only [Measure.inf_apply hu, this, coe_zero, Pi.zero_apply, nonpos_iff_eq_zero]
  refine csInf_eq_bot_of_bot_mem ⟨t, ?_⟩
  simp [measure_mono_null (inter_subset_left.trans hst.subset_compl_left) hs,
    measure_mono_null inter_subset_left ht]

lemma mutuallySingular_tfae : List.TFAE
    [ μ ⟂ₘ ν,
      Disjoint μ ν,
      Disjoint (ae μ) (ae ν) ] := by
  tfae_have 1 → 2
  | h => h.disjoint
  tfae_have 2 → 1
  | h => mutuallySingular_of_disjoint h
  tfae_have 1 → 3
  | h => h.disjoint_ae
  tfae_have 3 → 2
  | h => disjoint_of_disjoint_ae h
  tfae_finish

lemma mutuallySingular_iff_disjoint : μ ⟂ₘ ν ↔ Disjoint μ ν :=
  mutuallySingular_tfae.out 0 1

lemma mutuallySingular_iff_disjoint_ae : μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν) :=
  mutuallySingular_tfae.out 0 2

end Measure

end MeasureTheory
