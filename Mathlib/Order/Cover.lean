/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn
-/
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.WithBotTop
import Mathlib.Order.Antisymmetrization

/-!
# The covering relation

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. We say that `b` weakly covers `a` if `a ≤ b` and there is no element
between `a` and `b`. In a partial order this is equivalent to `a ⋖ b ∨ a = b`, in a preorder this
is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/


open Set OrderDual

variable {α β : Type*}

section WeaklyCovers

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

/-- `WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between.
-/
def WCovBy (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b

/-- Notation for `WCovBy a b`. -/
infixl:50 " ⩿ " => WCovBy

theorem WCovBy.le (h : a ⩿ b) : a ≤ b :=
  h.1

theorem WCovBy.refl (a : α) : a ⩿ a :=
  ⟨le_rfl, fun _ hc => hc.not_lt⟩

@[simp] lemma WCovBy.rfl : a ⩿ a := WCovBy.refl a

protected theorem Eq.wcovBy (h : a = b) : a ⩿ b :=
  h ▸ WCovBy.rfl

theorem wcovBy_of_le_of_le (h1 : a ≤ b) (h2 : b ≤ a) : a ⩿ b :=
  ⟨h1, fun _ hac hcb => (hac.trans hcb).not_le h2⟩

alias LE.le.wcovBy_of_le := wcovBy_of_le_of_le

theorem AntisymmRel.wcovBy (h : AntisymmRel (· ≤ ·) a b) : a ⩿ b :=
  wcovBy_of_le_of_le h.1 h.2

theorem WCovBy.wcovBy_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
  ⟨fun h => h.le, fun h => h.wcovBy_of_le hab.le⟩

theorem wcovBy_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

theorem AntisymmRel.trans_wcovBy (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⩿ c) : a ⩿ c :=
  ⟨hab.1.trans hbc.le, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

theorem wcovBy_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⩿ c ↔ b ⩿ c :=
  ⟨hab.symm.trans_wcovBy, hab.trans_wcovBy⟩

theorem WCovBy.trans_antisymm_rel (hab : a ⩿ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⩿ c :=
  ⟨hab.le.trans hbc.1, fun _ had hdc => hab.2 had <| hdc.trans_le hbc.2⟩

theorem wcovBy_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⩿ a ↔ c ⩿ b :=
  ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩

/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_wcovBy_iff (h : a ≤ b) : ¬a ⩿ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [WCovBy, h, true_and, not_forall, exists_prop, not_not]

instance WCovBy.isRefl : IsRefl α (· ⩿ ·) :=
  ⟨WCovBy.refl⟩

theorem WCovBy.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ hx => h.2 hx.1 hx.2

theorem wcovBy_iff_Ioo_eq : a ⩿ b ↔ a ≤ b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_not_mem]

lemma WCovBy.of_le_of_le (hac : a ⩿ c) (hab : a ≤ b) (hbc : b ≤ c) : b ⩿ c :=
  ⟨hbc, fun _x hbx hxc ↦ hac.2 (hab.trans_lt hbx) hxc⟩

lemma WCovBy.of_le_of_le' (hac : a ⩿ c) (hab : a ≤ b) (hbc : b ≤ c) : a ⩿ b :=
  ⟨hab, fun _x hax hxb ↦ hac.2 hax <| hxb.trans_le hbc⟩

theorem WCovBy.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
  ⟨f.le_iff_le.mp h.le, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

theorem WCovBy.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected) : f a ⩿ f b := by
  refine ⟨f.monotone hab.le, fun c ha hb => ?_⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb

theorem Set.OrdConnected.apply_wcovBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⩿ f b ↔ a ⩿ b :=
  ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩

@[simp]
theorem apply_wcovBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⩿ e b ↔ a ⩿ b :=
  (ordConnected_range (e : α ≃o β)).apply_wcovBy_apply_iff ((e : α ≃o β) : α ↪o β)

@[simp]
theorem toDual_wcovBy_toDual_iff : toDual b ⩿ toDual a ↔ a ⩿ b :=
  and_congr_right' <| forall_congr' fun _ => forall_swap

@[simp]
theorem ofDual_wcovBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a :=
  and_congr_right' <| forall_congr' fun _ => forall_swap

alias ⟨_, WCovBy.toDual⟩ := toDual_wcovBy_toDual_iff

alias ⟨_, WCovBy.ofDual⟩ := ofDual_wcovBy_ofDual_iff

theorem OrderEmbedding.wcovBy_of_apply {α β : Type*} [Preorder α] [Preorder β]
    (f : α ↪o β) {x y : α} (h : f x ⩿ f y) : x ⩿ y := by
  use f.le_iff_le.1 h.1
  intro a
  rw [← f.lt_iff_lt, ← f.lt_iff_lt]
  apply h.2

theorem OrderIso.map_wcovBy {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {x y : α} : f x ⩿ f y ↔ x ⩿ y := by
  use f.toOrderEmbedding.wcovBy_of_apply
  conv_lhs => rw [← f.symm_apply_apply x, ← f.symm_apply_apply y]
  exact f.symm.toOrderEmbedding.wcovBy_of_apply

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

theorem WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b := by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim

/-- An `iff` version of `WCovBy.eq_or_eq` and `wcovBy_of_eq_or_eq`. -/
theorem wcovBy_iff_le_and_eq_or_eq : a ⩿ b ↔ a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.le, fun _ => h.eq_or_eq⟩, And.rec wcovBy_of_eq_or_eq⟩

theorem WCovBy.le_and_le_iff (h : a ⩿ b) : a ≤ c ∧ c ≤ b ↔ c = a ∨ c = b := by
  refine ⟨fun h2 => h.eq_or_eq h2.1 h2.2, ?_⟩; rintro (rfl | rfl)
  exacts [⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]

theorem WCovBy.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} := by
  ext c
  exact h.le_and_le_iff

theorem WCovBy.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} := by
  rw [← Icc_diff_right, h.Icc_eq, diff_singleton_subset_iff, pair_comm]

theorem WCovBy.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} := by
  rw [← Icc_diff_left, h.Icc_eq, diff_singleton_subset_iff]

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

theorem WCovBy.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a ≠ b) : a ⊔ b = c :=
  (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

theorem WCovBy.inf_eq (hca : c ⩿ a) (hcb : c ⩿ b) (hab : a ≠ b) : a ⊓ b = c :=
  (le_inf hca.le hcb.le).eq_of_not_gt fun h => hab.inf_lt_or_inf_lt.elim (hca.2 h) (hcb.2 h)

end SemilatticeInf

end WeaklyCovers

section LT

variable [LT α] {a b : α}

/-- `CovBy a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def CovBy (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

/-- Notation for `CovBy a b`. -/
infixl:50 " ⋖ " => CovBy

theorem CovBy.lt (h : a ⋖ b) : a < b :=
  h.1

/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_covBy_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [CovBy, h, true_and, not_forall, exists_prop, not_not]

alias ⟨exists_lt_lt_of_not_covBy, _⟩ := not_covBy_iff

alias LT.lt.exists_lt_lt := exists_lt_lt_of_not_covBy

/-- In a dense order, nothing covers anything. -/
theorem not_covBy [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨_, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2

theorem denselyOrdered_iff_forall_not_covBy : DenselyOrdered α ↔ ∀ a b : α, ¬a ⋖ b :=
  ⟨fun h _ _ => @not_covBy _ _ _ _ h, fun h =>
    ⟨fun _ _ hab => exists_lt_lt_of_not_covBy hab <| h _ _⟩⟩

@[deprecated (since := "2024-04-04")]
alias densely_ordered_iff_forall_not_covBy := denselyOrdered_iff_forall_not_covBy

@[simp]
theorem toDual_covBy_toDual_iff : toDual b ⋖ toDual a ↔ a ⋖ b :=
  and_congr_right' <| forall_congr' fun _ => forall_swap

@[simp]
theorem ofDual_covBy_ofDual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a :=
  and_congr_right' <| forall_congr' fun _ => forall_swap

alias ⟨_, CovBy.toDual⟩ := toDual_covBy_toDual_iff

alias ⟨_, CovBy.ofDual⟩ := ofDual_covBy_ofDual_iff

end LT

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

theorem CovBy.le (h : a ⋖ b) : a ≤ b :=
  h.1.le

protected theorem CovBy.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.ne

theorem CovBy.ne' (h : a ⋖ b) : b ≠ a :=
  h.lt.ne'

protected theorem CovBy.wcovBy (h : a ⋖ b) : a ⩿ b :=
  ⟨h.le, h.2⟩

theorem WCovBy.covBy_of_not_le (h : a ⩿ b) (h2 : ¬b ≤ a) : a ⋖ b :=
  ⟨h.le.lt_of_not_le h2, h.2⟩

theorem WCovBy.covBy_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b :=
  ⟨h2, h.2⟩

lemma CovBy.of_le_of_lt (hac : a ⋖ c) (hab : a ≤ b) (hbc : b < c) : b ⋖ c :=
  ⟨hbc, fun _x hbx hxc ↦ hac.2 (hab.trans_lt hbx) hxc⟩

lemma CovBy.of_lt_of_le (hac : a ⋖ c) (hab : a < b) (hbc : b ≤ c) : a ⋖ b :=
  ⟨hab, fun _x hax hxb ↦ hac.2 hax <| hxb.trans_le hbc⟩

theorem not_covBy_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬a ⋖ c :=
  (not_covBy_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩

theorem covBy_iff_wcovBy_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
  ⟨fun h => ⟨h.wcovBy, h.lt⟩, fun h => h.1.covBy_of_lt h.2⟩

theorem covBy_iff_wcovBy_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b ≤ a :=
  ⟨fun h => ⟨h.wcovBy, h.lt.not_le⟩, fun h => h.1.covBy_of_not_le h.2⟩

theorem wcovBy_iff_covBy_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a ≤ b ∧ b ≤ a :=
  ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covBy_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.wcovBy) fun h => h.1.wcovBy_of_le h.2⟩

alias ⟨WCovBy.covBy_or_le_and_le, _⟩ := wcovBy_iff_covBy_or_le_and_le

theorem AntisymmRel.trans_covBy (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⋖ c) : a ⋖ c :=
  ⟨hab.1.trans_lt hbc.lt, fun _ had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩

theorem covBy_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⋖ c ↔ b ⋖ c :=
  ⟨hab.symm.trans_covBy, hab.trans_covBy⟩

theorem CovBy.trans_antisymmRel (hab : a ⋖ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⋖ c :=
  ⟨hab.lt.trans_le hbc.1, fun _ had hdb => hab.2 had <| hdb.trans_le hbc.2⟩

theorem covBy_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⋖ a ↔ c ⋖ b :=
  ⟨fun h => h.trans_antisymmRel hab, fun h => h.trans_antisymmRel hab.symm⟩

instance : IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·) :=
  ⟨fun _ _ =>
    covBy_iff_wcovBy_and_not_le.trans <| and_congr_right fun h => h.wcovBy_iff_le.not.symm⟩

instance CovBy.isIrrefl : IsIrrefl α (· ⋖ ·) :=
  ⟨fun _ ha => ha.ne rfl⟩

theorem CovBy.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  h.wcovBy.Ioo_eq

theorem covBy_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_not_mem]

theorem CovBy.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
  ⟨f.lt_iff_lt.mp h.lt, fun _ hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩

theorem CovBy.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected) : f a ⋖ f b :=
  (hab.wcovBy.image f h).covBy_of_lt <| f.strictMono hab.lt

theorem Set.OrdConnected.apply_covBy_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⋖ f b ↔ a ⋖ b :=
  ⟨CovBy.of_image f, fun hab => hab.image f h⟩

@[simp]
theorem apply_covBy_apply_iff {E : Type*} [EquivLike E α β] [OrderIsoClass E α β] (e : E) :
    e a ⋖ e b ↔ a ⋖ b :=
  (ordConnected_range (e : α ≃o β)).apply_covBy_apply_iff ((e : α ≃o β) : α ↪o β)

theorem covBy_of_eq_or_eq (hab : a < b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⋖ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.ne⟩

theorem OrderEmbedding.covBy_of_apply {α β : Type*} [Preorder α] [Preorder β]
    (f : α ↪o β) {x y : α} (h : f x ⋖ f y) : x ⋖ y := by
  use f.lt_iff_lt.1 h.1
  intro a
  rw [← f.lt_iff_lt, ← f.lt_iff_lt]
  apply h.2

theorem OrderIso.map_covBy {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {x y : α} : f x ⋖ f y ↔ x ⋖ y := by
  use f.toOrderEmbedding.covBy_of_apply
  conv_lhs => rw [← f.symm_apply_apply x, ← f.symm_apply_apply y]
  exact f.symm.toOrderEmbedding.covBy_of_apply

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

theorem WCovBy.covBy_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b :=
  ⟨h.le.lt_of_ne h2, h.2⟩

theorem covBy_iff_wcovBy_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.wcovBy, h.ne⟩, fun h => h.1.covBy_of_ne h.2⟩

theorem wcovBy_iff_covBy_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b := by
  rw [le_antisymm_iff, wcovBy_iff_covBy_or_le_and_le]

theorem wcovBy_iff_eq_or_covBy : a ⩿ b ↔ a = b ∨ a ⋖ b :=
  wcovBy_iff_covBy_or_eq.trans or_comm

alias ⟨WCovBy.covBy_or_eq, _⟩ := wcovBy_iff_covBy_or_eq

alias ⟨WCovBy.eq_or_covBy, _⟩ := wcovBy_iff_eq_or_covBy

theorem CovBy.eq_or_eq (h : a ⋖ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
  h.wcovBy.eq_or_eq h2 h3

/-- An `iff` version of `CovBy.eq_or_eq` and `covBy_of_eq_or_eq`. -/
theorem covBy_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.lt, fun _ => h.eq_or_eq⟩, And.rec covBy_of_eq_or_eq⟩

theorem CovBy.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Ioo_union_left h.lt, h.Ioo_eq, empty_union]

theorem CovBy.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} := by
  rw [← Ioo_union_right h.lt, h.Ioo_eq, empty_union]

theorem CovBy.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
  h.wcovBy.Icc_eq

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c : α}

theorem CovBy.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b := by
  rw [← Ioo_union_Ici_eq_Ioi h.lt, h.Ioo_eq, empty_union]

theorem CovBy.Iio_eq (h : a ⋖ b) : Iio b = Iic a := by
  rw [← Iic_union_Ioo_eq_Iio h.lt, h.Ioo_eq, union_empty]

theorem WCovBy.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c ≤ a :=
  not_lt.1 fun hac => hab.2 hac hcb

theorem WCovBy.ge_of_gt (hab : a ⩿ b) (hac : a < c) : b ≤ c :=
  not_lt.1 <| hab.2 hac

theorem CovBy.le_of_lt (hab : a ⋖ b) : c < b → c ≤ a :=
  hab.wcovBy.le_of_lt

theorem CovBy.ge_of_gt (hab : a ⋖ b) : a < c → b ≤ c :=
  hab.wcovBy.ge_of_gt

theorem CovBy.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (hb.le_of_lt ha.lt).antisymm <| ha.le_of_lt hb.lt

theorem CovBy.unique_right (hb : a ⋖ b) (hc : a ⋖ c) : b = c :=
  (hb.ge_of_gt hc.lt).antisymm <| hc.ge_of_gt hb.lt

/-- If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`. -/
theorem CovBy.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c) :
    x = b :=
  le_antisymm (le_of_not_lt fun h => hbc.2 h hxc) (le_of_not_lt <| hab.2 hax)

/-- If `a < b` then there exist `a' > a` and `b' < b` such that `Set.Iio a'` is strictly to the left
of `Set.Ioi b'`. -/
lemma LT.lt.exists_disjoint_Iio_Ioi (h : a < b) :
    ∃ a' > a, ∃ b' < b, ∀ x < a', ∀ y > b', x < y := by
  by_cases h' : a ⋖ b
  · exact ⟨b, h, a, h, fun x hx y hy => hx.trans_le <| h'.ge_of_gt hy⟩
  · rcases h.exists_lt_lt h' with ⟨c, ha, hb⟩
    exact ⟨c, ha, c, hb, fun _ h₁ _ => lt_trans h₁⟩

end LinearOrder

namespace Set
variable {s t : Set α} {a : α}

@[simp] lemma wcovBy_insert (x : α) (s : Set α) : s ⩿ insert x s := by
  refine wcovBy_of_eq_or_eq (subset_insert x s) fun t hst h2t => ?_
  by_cases h : x ∈ t
  · exact Or.inr (subset_antisymm h2t <| insert_subset_iff.mpr ⟨h, hst⟩)
  · refine Or.inl (subset_antisymm ?_ hst)
    rwa [← diff_singleton_eq_self h, diff_singleton_subset_iff]

@[simp] lemma sdiff_singleton_wcovBy (s : Set α) (a : α) : s \ {a} ⩿ s := by
  by_cases ha : a ∈ s
  · convert wcovBy_insert a _
    ext
    simp [ha]
  · simp [ha]

@[simp] lemma covBy_insert (ha : a ∉ s) : s ⋖ insert a s :=
  (wcovBy_insert _ _).covBy_of_lt <| ssubset_insert ha

@[simp] lemma sdiff_singleton_covBy (ha : a ∈ s) : s \ {a} ⋖ s :=
  ⟨sdiff_lt (singleton_subset_iff.2 ha) <| singleton_ne_empty _, (sdiff_singleton_wcovBy _ _).2⟩

lemma _root_.CovBy.exists_set_insert (h : s ⋖ t) : ∃ a ∉ s, insert a s = t :=
  let ⟨a, ha, hst⟩ := ssubset_iff_insert.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssuperset <| h.2 <| ssubset_insert ha).symm⟩

lemma _root_.CovBy.exists_set_sdiff_singleton (h : s ⋖ t) : ∃ a ∈ t, t \ {a} =  s :=
  let ⟨a, ha, hst⟩ := ssubset_iff_sdiff_singleton.1 h.lt
  ⟨a, ha, (hst.eq_of_not_ssubset fun h' ↦ h.2 h' <|
    sdiff_lt (singleton_subset_iff.2 ha) <| singleton_ne_empty _).symm⟩

lemma covBy_iff_exists_insert : s ⋖ t ↔ ∃ a ∉ s, insert a s = t :=
  ⟨CovBy.exists_set_insert, by rintro ⟨a, ha, rfl⟩; exact covBy_insert ha⟩

lemma covBy_iff_exists_sdiff_singleton : s ⋖ t ↔ ∃ a ∈ t, t \ {a} = s :=
  ⟨CovBy.exists_set_sdiff_singleton, by rintro ⟨a, ha, rfl⟩; exact sdiff_singleton_covBy ha⟩

end Set

section Relation

open Relation

lemma wcovBy_eq_reflGen_covBy [PartialOrder α] : ((· : α) ⩿ ·) = ReflGen (· ⋖ ·) := by
  ext x y; simp_rw [wcovBy_iff_eq_or_covBy, @eq_comm _ x, reflGen_iff]

lemma transGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    TransGen ((· : α) ⩿ ·) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy, transGen_reflGen]

lemma reflTransGen_wcovBy_eq_reflTransGen_covBy [PartialOrder α] :
    ReflTransGen ((· : α) ⩿ ·) = ReflTransGen (· ⋖ ·) := by
  rw [wcovBy_eq_reflGen_covBy, reflTransGen_reflGen]

end Relation

namespace Prod

variable [PartialOrder α] [PartialOrder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

@[simp]
theorem swap_wcovBy_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
  apply_wcovBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

@[simp]
theorem swap_covBy_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
  apply_covBy_apply_iff (OrderIso.prodComm : α × β ≃o β × α)

theorem fst_eq_or_snd_eq_of_wcovBy : x ⩿ y → x.1 = y.1 ∨ x.2 = y.2 := by
  refine fun h => of_not_not fun hab => ?_
  push_neg at hab
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨hab.1.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hab.2.lt_of_le h.1.2⟩)

theorem _root_.WCovBy.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
  ⟨h.1.1, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_le hc.1⟩⟩

theorem _root_.WCovBy.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
  ⟨h.1.2, fun _ h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_le hc.2⟩⟩

theorem mk_wcovBy_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ := by
  refine ⟨WCovBy.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => ?_⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c, this, mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂

theorem mk_wcovBy_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
  swap_wcovBy_swap.trans mk_wcovBy_mk_iff_left

theorem mk_covBy_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_left, mk_lt_mk_iff_left]

theorem mk_covBy_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ := by
  simp_rw [covBy_iff_wcovBy_and_lt, mk_wcovBy_mk_iff_right, mk_lt_mk_iff_right]

theorem mk_wcovBy_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h
    · exact Or.inr ⟨mk_wcovBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_wcovBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovBy_mk_iff_left.2 h
    · exact mk_wcovBy_mk_iff_right.2 h

theorem mk_covBy_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovBy h.wcovBy
    · exact Or.inr ⟨mk_covBy_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_covBy_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covBy_mk_iff_left.2 h
    · exact mk_covBy_mk_iff_right.2 h

theorem wcovBy_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_wcovBy_mk_iff

theorem covBy_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 := by
  cases x
  cases y
  exact mk_covBy_mk_iff

end Prod

namespace WithTop

variable [Preorder α] {a b : α}

@[simp, norm_cast] lemma coe_wcovBy_coe : (a : WithTop α) ⩿ b ↔ a ⩿ b :=
  Set.OrdConnected.apply_wcovBy_apply_iff OrderEmbedding.withTopCoe <| by
    simp [WithTop.range_coe, ordConnected_Iio]

@[simp, norm_cast] lemma coe_covBy_coe : (a : WithTop α) ⋖ b ↔ a ⋖ b :=
  Set.OrdConnected.apply_covBy_apply_iff OrderEmbedding.withTopCoe <| by
    simp [WithTop.range_coe, ordConnected_Iio]

@[simp] lemma coe_covBy_top : (a : WithTop α) ⋖ ⊤ ↔ IsMax a := by
  simp only [covBy_iff_Ioo_eq, ← image_coe_Ioi, coe_lt_top, image_eq_empty,
    true_and, Ioi_eq_empty_iff]

@[simp] lemma coe_wcovBy_top : (a : WithTop α) ⩿ ⊤ ↔ IsMax a := by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Ioi, le_top, image_eq_empty, true_and, Ioi_eq_empty_iff]

end WithTop

namespace WithBot

variable [Preorder α] {a b : α}

@[simp, norm_cast] lemma coe_wcovBy_coe : (a : WithBot α) ⩿ b ↔ a ⩿ b :=
  Set.OrdConnected.apply_wcovBy_apply_iff OrderEmbedding.withBotCoe <| by
    simp [WithBot.range_coe, ordConnected_Ioi]

@[simp, norm_cast] lemma coe_covBy_coe : (a : WithBot α) ⋖ b ↔ a ⋖ b :=
  Set.OrdConnected.apply_covBy_apply_iff OrderEmbedding.withBotCoe <| by
    simp [WithBot.range_coe, ordConnected_Ioi]

@[simp] lemma bot_covBy_coe : ⊥ ⋖ (a : WithBot α) ↔ IsMin a := by
  simp only [covBy_iff_Ioo_eq, ← image_coe_Iio, bot_lt_coe, image_eq_empty,
    true_and, Iio_eq_empty_iff]

@[simp] lemma bot_wcovBy_coe : ⊥ ⩿ (a : WithBot α) ↔ IsMin a := by
  simp only [wcovBy_iff_Ioo_eq, ← image_coe_Iio, bot_le, image_eq_empty, true_and, Iio_eq_empty_iff]

end WithBot
