/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.MinMax

/-!
# Interval properties in linear orders

Since every pair of elements are comparable in a linear order, intervals over them are
better behaved. This file collects their properties under this assumption.
-/

assert_not_exists RelIso

open Function

namespace Set

variable {α : Type*} [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

theorem notMem_Ici : c ∉ Ici a ↔ c < a :=
  not_le

@[deprecated (since := "2025-05-23")] alias not_mem_Ici := notMem_Ici

theorem notMem_Iic : c ∉ Iic b ↔ b < c :=
  not_le

@[deprecated (since := "2025-05-23")] alias not_mem_Iic := notMem_Iic

theorem notMem_Ioi : c ∉ Ioi a ↔ c ≤ a :=
  not_lt

@[deprecated (since := "2025-05-23")] alias not_mem_Ioi := notMem_Ioi

theorem notMem_Iio : c ∉ Iio b ↔ b ≤ c :=
  not_lt

@[deprecated (since := "2025-05-23")] alias not_mem_Iio := notMem_Iio

@[simp]
theorem compl_Iic : (Iic a)ᶜ = Ioi a :=
  ext fun _ => not_le

@[simp]
theorem compl_Ici : (Ici a)ᶜ = Iio a :=
  ext fun _ => not_le

@[simp]
theorem compl_Iio : (Iio a)ᶜ = Ici a :=
  ext fun _ => not_lt

@[simp]
theorem compl_Ioi : (Ioi a)ᶜ = Iic a :=
  ext fun _ => not_lt

@[simp]
theorem Ici_diff_Ici : Ici a \ Ici b = Ico a b := by rw [diff_eq, compl_Ici, Ici_inter_Iio]

@[simp]
theorem Ici_diff_Ioi : Ici a \ Ioi b = Icc a b := by rw [diff_eq, compl_Ioi, Ici_inter_Iic]

@[simp]
theorem Ioi_diff_Ioi : Ioi a \ Ioi b = Ioc a b := by rw [diff_eq, compl_Ioi, Ioi_inter_Iic]

@[simp]
theorem Ioi_diff_Ici : Ioi a \ Ici b = Ioo a b := by rw [diff_eq, compl_Ici, Ioi_inter_Iio]

@[simp]
theorem Iic_diff_Iic : Iic b \ Iic a = Ioc a b := by
  rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iic]

@[simp]
theorem Iio_diff_Iic : Iio b \ Iic a = Ioo a b := by
  rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iio]

@[simp]
theorem Iic_diff_Iio : Iic b \ Iio a = Icc a b := by
  rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iic]

@[simp]
theorem Iio_diff_Iio : Iio b \ Iio a = Ico a b := by
  rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iio]

theorem Ioi_injective : Injective (Ioi : α → Set α) := fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1

theorem Iio_injective : Injective (Iio : α → Set α) := fun _ _ =>
  eq_of_forall_lt_iff ∘ Set.ext_iff.1

theorem Ioi_inj : Ioi a = Ioi b ↔ a = b :=
  Ioi_injective.eq_iff

theorem Iio_inj : Iio a = Iio b ↔ a = b :=
  Iio_injective.eq_iff

theorem Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h =>
    have : a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_gt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩

theorem Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ b₁ ≤ b₂ ∧ a₂ ≤ a₁ := by
  convert @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ using 2 <;> exact (@Ico_toDual α _ _ _).symm

theorem Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) :
    Ioo a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine le_of_not_gt fun h' => ?_
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

theorem Ico_eq_Ico_iff (h : a₁ < b₁ ∨ a₂ < b₂) : Ico a₁ b₁ = Ico a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun e => by
      simp only [Subset.antisymm_iff] at e
      simp only [le_antisymm_iff]
      rcases h with h | h <;>
      simp only [gt_iff_lt, not_lt, Ico_subset_Ico_iff h] at e <;>
      [ rcases e with ⟨⟨h₁, h₂⟩, e'⟩; rcases e with ⟨e', ⟨h₁, h₂⟩⟩ ] <;>
      have hab := (Ico_subset_Ico_iff <| h₁.trans_lt <| h.trans_le h₂).1 e' <;>
      tauto,
    fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩

lemma Ici_eq_singleton_iff_isTop {x : α} : (Ici x = {x}) ↔ IsTop x := by
  refine ⟨fun h y ↦ ?_, fun h ↦ by ext y; simp [(h y).ge_iff_eq]⟩
  by_contra! H
  have : y ∈ Ici x := H.le
  rw [h, mem_singleton_iff] at this
  exact lt_irrefl y (this.le.trans_lt H)

@[simp]
theorem Ioi_subset_Ioi_iff : Ioi b ⊆ Ioi a ↔ a ≤ b := by
  refine ⟨fun h => ?_, Ioi_subset_Ioi⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[simp]
theorem Ioi_ssubset_Ioi_iff : Ioi b ⊂ Ioi a ↔ a < b := by
  refine ⟨fun h => ?_, Ioi_ssubset_Ioi⟩
  obtain ⟨_, c, ac, cb⟩ := ssubset_iff_exists.mp h
  exact ac.trans_le (le_of_not_gt cb)

@[simp]
theorem Ioi_subset_Ici_iff [DenselyOrdered α] : Ioi b ⊆ Ici a ↔ a ≤ b := by
  refine ⟨fun h => ?_, Ioi_subset_Ici⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : ∃ c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

@[simp]
theorem Iio_subset_Iio_iff : Iio a ⊆ Iio b ↔ a ≤ b := by
  refine ⟨fun h => ?_, Iio_subset_Iio⟩
  by_contra ab
  exact lt_irrefl _ (h (not_le.mp ab))

@[simp]
theorem Iio_ssubset_Iio_iff : Iio a ⊂ Iio b ↔ a < b := by
  refine ⟨fun h => ?_, Iio_ssubset_Iio⟩
  obtain ⟨_, c, cb, ac⟩ := ssubset_iff_exists.mp h
  exact (le_of_not_gt ac).trans_lt cb

@[simp]
theorem Iio_subset_Iic_iff [DenselyOrdered α] : Iio a ⊆ Iic b ↔ a ≤ b := by
  rw [← diff_eq_empty, Iio_diff_Iic, Ioo_eq_empty_iff, not_lt]

/-! ### Two infinite intervals -/

theorem Iic_union_Ioi_of_le (h : a ≤ b) : Iic b ∪ Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_le x).symm

theorem Iio_union_Ici_of_le (h : a ≤ b) : Iio b ∪ Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_lt x).symm

theorem Iic_union_Ici_of_le (h : a ≤ b) : Iic b ∪ Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_le x).symm

theorem Iio_union_Ioi_of_lt (h : a < b) : Iio b ∪ Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_lt x).symm

@[simp]
theorem Iic_union_Ici : Iic a ∪ Ici a = univ :=
  Iic_union_Ici_of_le le_rfl

@[simp]
theorem Iio_union_Ici : Iio a ∪ Ici a = univ :=
  Iio_union_Ici_of_le le_rfl

@[simp]
theorem Iic_union_Ioi : Iic a ∪ Ioi a = univ :=
  Iic_union_Ioi_of_le le_rfl

@[simp]
theorem Iio_union_Ioi : Iio a ∪ Ioi a = {a}ᶜ :=
  ext fun _ => lt_or_lt_iff_ne

/-! ### A finite and an infinite interval -/

theorem Ioo_union_Ioi' (h₁ : c < b) : Ioo a b ∪ Ioi c = Ioi (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, mem_Ioi, min_lt_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x < b := (le_of_not_gt hc).trans_lt h₁
    tauto

theorem Ioo_union_Ioi (h : c < max a b) : Ioo a b ∪ Ioi c = Ioi (min a c) := by
  rcases le_total a b with hab | hab <;> simp [hab] at h
  · exact Ioo_union_Ioi' h
  · rw [min_comm]
    simp [*, min_eq_left_of_lt]

theorem Ioi_subset_Ioo_union_Ici : Ioi a ⊆ Ioo a b ∪ Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b ∪ Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici

theorem Ici_subset_Ico_union_Ici : Ici a ⊆ Ico a b ∪ Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ico_union_Ici_eq_Ici (h : a ≤ b) : Ico a b ∪ Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici

theorem Ico_union_Ici' (h₁ : c ≤ b) : Ico a b ∪ Ici c = Ici (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, mem_Ici, min_le_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto

theorem Ico_union_Ici (h : c ≤ max a b) : Ico a b ∪ Ici c = Ici (min a c) := by
  rcases le_total a b with hab | hab <;> simp [hab] at h
  · exact Ico_union_Ici' h
  · simp [*]

theorem Ioi_subset_Ioc_union_Ioi : Ioi a ⊆ Ioc a b ∪ Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : Ioc a b ∪ Ioi b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi

theorem Ioc_union_Ioi' (h₁ : c ≤ b) : Ioc a b ∪ Ioi c = Ioi (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, mem_Ioi, min_lt_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto

theorem Ioc_union_Ioi (h : c ≤ max a b) : Ioc a b ∪ Ioi c = Ioi (min a c) := by
  rcases le_total a b with hab | hab <;> simp [hab] at h
  · exact Ioc_union_Ioi' h
  · simp [*]

theorem Ici_subset_Icc_union_Ioi : Ici a ⊆ Icc a b ∪ Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
theorem Icc_union_Ioi_eq_Ici (h : a ≤ b) : Icc a b ∪ Ioi b = Ici a :=
  Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi

theorem Ioi_subset_Ioc_union_Ici : Ioi a ⊆ Ioc a b ∪ Ici b :=
  Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]
theorem Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b ∪ Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici

theorem Ici_subset_Icc_union_Ici : Ici a ⊆ Icc a b ∪ Ici b :=
  Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]
theorem Icc_union_Ici_eq_Ici (h : a ≤ b) : Icc a b ∪ Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici

theorem Icc_union_Ici' (h₁ : c ≤ b) : Icc a b ∪ Ici c = Ici (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, mem_Ici, min_le_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto

theorem Icc_union_Ici (h : c ≤ max a b) : Icc a b ∪ Ici c = Ici (min a c) := by
  rcases le_or_gt a b with hab | hab <;> simp [hab] at h
  · exact Icc_union_Ici' h
  · rcases h with h | h
    · simp [*]
    · have hca : c ≤ a := h.trans hab.le
      simp [*]

/-! ### An infinite and a finite interval -/

theorem Iic_subset_Iio_union_Icc : Iic b ⊆ Iio a ∪ Icc a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc

theorem Iio_subset_Iio_union_Ico : Iio b ⊆ Iio a ∪ Ico a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iio_union_Ico_eq_Iio (h : a ≤ b) : Iio a ∪ Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico

theorem Iio_union_Ico' (h₁ : c ≤ b) : Iio b ∪ Ico c d = Iio (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iio, mem_Ico, lt_max_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto

theorem Iio_union_Ico (h : min c d ≤ b) : Iio b ∪ Ico c d = Iio (max b d) := by
  rcases le_total c d with hcd | hcd <;> simp [hcd] at h
  · exact Iio_union_Ico' h
  · simp [*]

theorem Iic_subset_Iic_union_Ioc : Iic b ⊆ Iic a ∪ Ioc a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc

theorem Iic_union_Ioc' (h₁ : c < b) : Iic b ∪ Ioc c d = Iic (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Ioc, le_max_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁.le
    tauto

theorem Iic_union_Ioc (h : min c d < b) : Iic b ∪ Ioc c d = Iic (max b d) := by
  rcases le_total c d with hcd | hcd <;> simp [hcd] at h
  · exact Iic_union_Ioc' h
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]

theorem Iio_subset_Iic_union_Ioo : Iio b ⊆ Iic a ∪ Ioo a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
theorem Iic_union_Ioo_eq_Iio (h : a < b) : Iic a ∪ Ioo a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo

theorem Iio_union_Ioo' (h₁ : c < b) : Iio b ∪ Ioo c d = Iio (max b d) := by
  ext x
  rcases lt_or_ge x b with hba | hba
  · simp [hba, h₁]
  · simp only [mem_Iio, mem_union, mem_Ioo, lt_max_iff]
    refine or_congr Iff.rfl ⟨And.right, ?_⟩
    exact fun h₂ => ⟨h₁.trans_le hba, h₂⟩

theorem Iio_union_Ioo (h : min c d < b) : Iio b ∪ Ioo c d = Iio (max b d) := by
  rcases le_total c d with hcd | hcd <;> simp [hcd] at h
  · exact Iio_union_Ioo' h
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]

theorem Iic_subset_Iic_union_Icc : Iic b ⊆ Iic a ∪ Icc a b :=
  Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Iic_union_Icc_eq_Iic (h : a ≤ b) : Iic a ∪ Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc

theorem Iic_union_Icc' (h₁ : c ≤ b) : Iic b ∪ Icc c d = Iic (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Icc, le_max_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto

theorem Iic_union_Icc (h : min c d ≤ b) : Iic b ∪ Icc c d = Iic (max b d) := by
  rcases le_or_gt c d with hcd | hcd <;> simp [hcd] at h
  · exact Iic_union_Icc' h
  · rcases h with h | h
    · have hdb : d ≤ b := hcd.le.trans h
      simp [*]
    · simp [*]

theorem Iio_subset_Iic_union_Ico : Iio b ⊆ Iic a ∪ Ico a b :=
  Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Iic_union_Ico_eq_Iio (h : a < b) : Iic a ∪ Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico

/-! ### Two finite intervals, `I?o` and `Ic?` -/

theorem Ioo_subset_Ioo_union_Ico : Ioo a c ⊆ Ioo a b ∪ Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico

theorem Ico_subset_Ico_union_Ico : Ico a c ⊆ Ico a b ∪ Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ico_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico

theorem Ico_union_Ico' (h₁ : c ≤ b) (h₂ : a ≤ d) : Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, min_le_iff, lt_max_iff]
  by_cases hc : c ≤ x <;> by_cases hd : x < d
  · tauto
  · have hax : a ≤ x := h₂.trans (le_of_not_gt hd)
    tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
  · tauto

theorem Ico_union_Ico (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd <;> simp [*] at h₁ h₂
  · exact Ico_union_Ico' h₂ h₁
  all_goals simp [*]

theorem Icc_subset_Ico_union_Icc : Icc a c ⊆ Ico a b ∪ Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ico_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc

theorem Ioc_subset_Ioo_union_Icc : Ioc a c ⊆ Ioo a b ∪ Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

/-! ### Two finite intervals, `I?c` and `Io?` -/

theorem Ioo_subset_Ioc_union_Ioo : Ioo a c ⊆ Ioc a b ∪ Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioc_union_Ioo_eq_Ioo (h₁ : a ≤ b) (h₂ : b < c) : Ioc a b ∪ Ioo b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

theorem Ico_subset_Icc_union_Ioo : Ico a c ⊆ Icc a b ∪ Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Icc_union_Ioo_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ioo b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo

theorem Icc_subset_Icc_union_Ioc : Icc a c ⊆ Icc a b ∪ Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Icc_union_Ioc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Ioc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc

theorem Ioc_subset_Ioc_union_Ioc : Ioc a c ⊆ Ioc a b ∪ Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
theorem Ioc_union_Ioc_eq_Ioc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc

theorem Ioc_union_Ioc' (h₁ : c ≤ b) (h₂ : a ≤ d) : Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, min_lt_iff, le_max_iff]
  by_cases hc : c < x <;> by_cases hd : x ≤ d
  · tauto
  · have hax : a < x := h₂.trans_lt (lt_of_not_ge hd)
    tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto
  · tauto

theorem Ioc_union_Ioc (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd <;> simp [*] at h₁ h₂
  · exact Ioc_union_Ioc' h₂ h₁
  all_goals simp [*]

/-! ### Two finite intervals with a common point -/

theorem Ioo_subset_Ioc_union_Ico : Ioo a c ⊆ Ioc a b ∪ Ico b c :=
  Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : Ioc a b ∪ Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico

theorem Ico_subset_Icc_union_Ico : Ico a c ⊆ Icc a b ∪ Ico b c :=
  Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
theorem Icc_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico

theorem Icc_subset_Icc_union_Icc : Icc a c ⊆ Icc a b ∪ Icc b c :=
  Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Icc_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc

theorem Icc_union_Icc' (h₁ : c ≤ b) (h₂ : a ≤ d) : Icc a b ∪ Icc c d = Icc (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, min_le_iff, le_max_iff]
  by_cases hc : c ≤ x <;> by_cases hd : x ≤ d
  · tauto
  · have hax : a ≤ x := h₂.trans (le_of_not_ge hd)
    tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
  · tauto

/-- We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
theorem Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Icc a b ∪ Icc c d = Icc (min a c) (max b d) := by
  rcases le_or_gt a b with hab | hab <;> rcases le_or_gt c d with hcd | hcd <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, min_eq_left_of_lt,
      min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt, hab, hcd] at h₁ h₂
  · exact Icc_union_Icc' h₂.le h₁.le
  all_goals simp [*, min_eq_left_of_lt, max_eq_left_of_lt, min_eq_right_of_lt, max_eq_right_of_lt]

theorem Ioc_subset_Ioc_union_Icc : Ioc a c ⊆ Ioc a b ∪ Icc b c :=
  Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
theorem Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioc a b ∪ Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc

theorem Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, min_lt_iff, lt_max_iff]
  by_cases hc : c < x <;> by_cases hd : x < d
  · tauto
  · have hax : a < x := h₂.trans_le (le_of_not_gt hd)
    tauto
  · have hxb : x < b := (le_of_not_gt hc).trans_lt h₁
    tauto
  · tauto

theorem Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hcd] at h₁ h₂
  · exact Ioo_union_Ioo' h₂ h₁
  all_goals
    simp [*, min_eq_left_of_lt, min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt,
      le_of_lt h₂, le_of_lt h₁]

theorem Ioo_subset_Ioo_union_Ioo (h₁ : a ≤ a₁) (h₂ : c < b) (h₃ : b₁ ≤ d) :
    Ioo a₁ b₁ ⊆ Ioo a b ∪ Ioo c d := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨lt_of_le_of_lt h₁ hx.1, hxb⟩)
    fun hxb => Or.inr ⟨lt_of_lt_of_le h₂ hxb, lt_of_lt_of_le hx.2 h₃⟩

/-! ### Intersection, difference, complement -/

@[simp]
theorem Ioi_inter_Ioi : Ioi a ∩ Ioi b = Ioi (a ⊔ b) :=
  ext fun _ => sup_lt_iff.symm

@[simp]
theorem Iio_inter_Iio : Iio a ∩ Iio b = Iio (a ⊓ b) :=
  ext fun _ => lt_inf_iff.symm

theorem Ico_inter_Ico : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iio.symm, Ici_inter_Ici.symm, Iio_inter_Iio.symm]; ac_rfl

theorem Ioc_inter_Ioc : Ioc a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iic.symm, Ioi_inter_Ioi.symm, Iic_inter_Iic.symm]; ac_rfl

theorem Ioo_inter_Ioo : Ioo a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iio.symm, Ioi_inter_Ioi.symm, Iio_inter_Iio.symm]; ac_rfl

theorem Ioo_inter_Iio : Ioo a b ∩ Iio c = Ioo a (min b c) := by
  ext
  simp_rw [mem_inter_iff, mem_Ioo, mem_Iio, lt_min_iff, and_assoc]

theorem Iio_inter_Ioo : Iio a ∩ Ioo b c = Ioo b (min a c) := by
  rw [Set.inter_comm, Set.Ioo_inter_Iio, min_comm]

theorem Ioo_inter_Ioi : Ioo a b ∩ Ioi c = Ioo (max a c) b := by
  ext
  simp_rw [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff, and_assoc, and_comm]

theorem Ioi_inter_Ioo : Set.Ioi a ∩ Set.Ioo b c = Set.Ioo (max a b) c := by
  rw [inter_comm, Ioo_inter_Ioi, max_comm]

theorem Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁ :=
  ext fun x => by
    simp [and_assoc, @and_left_comm (x ≤ _), and_iff_left_iff_imp.2 fun h' => lt_of_le_of_lt h' h]

theorem Ioc_inter_Ioo_of_right_le (h : b₂ ≤ b₁) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂ :=
  ext fun x => by
    simp [and_assoc, @and_left_comm (x ≤ _),
      and_iff_right_iff_imp.2 fun h' => (le_of_lt h').trans h]

theorem Ioo_inter_Ioc_of_left_le (h : b₁ ≤ b₂) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁ := by
  rw [inter_comm, Ioc_inter_Ioo_of_right_le h, max_comm]

theorem Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂ := by
  rw [inter_comm, Ioc_inter_Ioo_of_left_lt h, max_comm]

@[simp]
theorem Ico_diff_Iio : Ico a b \ Iio c = Ico (max a c) b := by
  rw [diff_eq, compl_Iio, Ico_inter_Ici]

@[simp]
theorem Ioc_diff_Ioi : Ioc a b \ Ioi c = Ioc a (min b c) :=
  ext <| by simp +contextual [iff_def]

@[simp]
theorem Ioc_inter_Ioi : Ioc a b ∩ Ioi c = Ioc (a ⊔ c) b := by
  rw [← Ioi_inter_Iic, inter_assoc, inter_comm, inter_assoc, Ioi_inter_Ioi, inter_comm,
    Ioi_inter_Iic, sup_comm]

@[simp]
theorem Ico_inter_Iio : Ico a b ∩ Iio c = Ico a (min b c) :=
  ext <| by simp +contextual [iff_def]

@[simp]
theorem Ioc_diff_Iic : Ioc a b \ Iic c = Ioc (max a c) b := by
  rw [diff_eq, compl_Iic, Ioc_inter_Ioi]

theorem compl_Ioc : (Ioc a b)ᶜ = Iic a ∪ Ioi b := by
  ext i
  rw [mem_compl_iff, mem_Ioc, mem_union, mem_Iic, mem_Ioi, not_and_or, not_lt, not_le]

theorem Iic_diff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  rw [diff_eq, compl_Ioc, inter_union_distrib_left, Iic_inter_Iic, ← compl_Iic, inter_compl_self,
    union_empty, min_comm]

theorem Iic_diff_Ioc_self_of_le (hab : a ≤ b) : Iic b \ Ioc a b = Iic a := by
  rw [Iic_diff_Ioc, min_eq_left hab]

@[simp]
theorem Ioc_union_Ioc_right : Ioc a b ∪ Ioc a c = Ioc a (max b c) := by
  rw [Ioc_union_Ioc, min_self] <;> exact (min_le_left _ _).trans (le_max_left _ _)

@[simp]
theorem Ioc_union_Ioc_left : Ioc a c ∪ Ioc b c = Ioc (min a b) c := by
  rw [Ioc_union_Ioc, max_self] <;> exact (min_le_right _ _).trans (le_max_right _ _)

@[simp]
theorem Ioc_union_Ioc_symm : Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b) := by
  rw [max_comm]
  apply Ioc_union_Ioc <;> rw [max_comm] <;> exact min_le_max

@[simp]
theorem Ioc_union_Ioc_union_Ioc_cycle :
    Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc (min a (min b c)) (max a (max b c)) := by
  rw [Ioc_union_Ioc, Ioc_union_Ioc]
  · ac_rfl
  all_goals
  solve_by_elim (config := { maxDepth := 5 }) [min_le_of_left_le, min_le_of_right_le,
       le_max_of_le_left, le_max_of_le_right, le_refl]

end Set
