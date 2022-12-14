/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Order.MinMax
import Mathlib.Data.Set.Prod

/-!
# Intervals

In any preorder `α`, we define intervals (which on each side can be either infinite, open, or
closed) using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side. For instance,
`Ioc a b` denotes the inverval `(a, b]`.

This file contains these definitions, and basic facts on inclusion, intersection, difference of
intervals (where the precise statements may depend on the properties of the order, in particular
for some statements it should be `linear_order` or `densely_ordered`).

TODO: This is just the beginning; a lot of rules are missing
-/


open Function

open OrderDual (toDual ofDual)

variable {α β : Type _}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

/-- Left-open right-open interval -/
def ioo (a b : α) :=
  { x | a < x ∧ x < b }
#align set.Ioo Set.ioo

/-- Left-closed right-open interval -/
def ico (a b : α) :=
  { x | a ≤ x ∧ x < b }
#align set.Ico Set.ico

/-- Left-infinite right-open interval -/
def iio (a : α) :=
  { x | x < a }
#align set.Iio Set.iio

/-- Left-closed right-closed interval -/
def icc (a b : α) :=
  { x | a ≤ x ∧ x ≤ b }
#align set.Icc Set.icc

/-- Left-infinite right-closed interval -/
def iic (b : α) :=
  { x | x ≤ b }
#align set.Iic Set.iic

/-- Left-open right-closed interval -/
def ioc (a b : α) :=
  { x | a < x ∧ x ≤ b }
#align set.Ioc Set.ioc

/-- Left-closed right-infinite interval -/
def ici (a : α) :=
  { x | a ≤ x }
#align set.Ici Set.ici

/-- Left-open right-infinite interval -/
def ioi (a : α) :=
  { x | a < x }
#align set.Ioi Set.ioi

theorem Ioo_def (a b : α) : { x | a < x ∧ x < b } = ioo a b :=
  rfl
#align set.Ioo_def Set.Ioo_def

theorem Ico_def (a b : α) : { x | a ≤ x ∧ x < b } = ico a b :=
  rfl
#align set.Ico_def Set.Ico_def

theorem Iio_def (a : α) : { x | x < a } = iio a :=
  rfl
#align set.Iio_def Set.Iio_def

theorem Icc_def (a b : α) : { x | a ≤ x ∧ x ≤ b } = icc a b :=
  rfl
#align set.Icc_def Set.Icc_def

theorem Iic_def (b : α) : { x | x ≤ b } = iic b :=
  rfl
#align set.Iic_def Set.Iic_def

theorem Ioc_def (a b : α) : { x | a < x ∧ x ≤ b } = ioc a b :=
  rfl
#align set.Ioc_def Set.Ioc_def

theorem Ici_def (a : α) : { x | a ≤ x } = ici a :=
  rfl
#align set.Ici_def Set.Ici_def

theorem Ioi_def (a : α) : { x | a < x } = ioi a :=
  rfl
#align set.Ioi_def Set.Ioi_def

@[simp]
theorem mem_Ioo : x ∈ ioo a b ↔ a < x ∧ x < b :=
  Iff.rfl
#align set.mem_Ioo Set.mem_Ioo

@[simp]
theorem mem_Ico : x ∈ ico a b ↔ a ≤ x ∧ x < b :=
  Iff.rfl
#align set.mem_Ico Set.mem_Ico

@[simp]
theorem mem_Iio : x ∈ iio b ↔ x < b :=
  Iff.rfl
#align set.mem_Iio Set.mem_Iio

@[simp]
theorem mem_Icc : x ∈ icc a b ↔ a ≤ x ∧ x ≤ b :=
  Iff.rfl
#align set.mem_Icc Set.mem_Icc

@[simp]
theorem mem_Iic : x ∈ iic b ↔ x ≤ b :=
  Iff.rfl
#align set.mem_Iic Set.mem_Iic

@[simp]
theorem mem_Ioc : x ∈ ioc a b ↔ a < x ∧ x ≤ b :=
  Iff.rfl
#align set.mem_Ioc Set.mem_Ioc

@[simp]
theorem mem_Ici : x ∈ ici a ↔ a ≤ x :=
  Iff.rfl
#align set.mem_Ici Set.mem_Ici

@[simp]
theorem mem_Ioi : x ∈ ioi a ↔ a < x :=
  Iff.rfl
#align set.mem_Ioi Set.mem_Ioi

instance decidableMemIoo [Decidable (a < x ∧ x < b)] : Decidable (x ∈ ioo a b) := by assumption
#align set.decidable_mem_Ioo Set.decidableMemIoo

instance decidableMemIco [Decidable (a ≤ x ∧ x < b)] : Decidable (x ∈ ico a b) := by assumption
#align set.decidable_mem_Ico Set.decidableMemIco

instance decidableMemIio [Decidable (x < b)] : Decidable (x ∈ iio b) := by assumption
#align set.decidable_mem_Iio Set.decidableMemIio

instance decidableMemIcc [Decidable (a ≤ x ∧ x ≤ b)] : Decidable (x ∈ icc a b) := by assumption
#align set.decidable_mem_Icc Set.decidableMemIcc

instance decidableMemIic [Decidable (x ≤ b)] : Decidable (x ∈ iic b) := by assumption
#align set.decidable_mem_Iic Set.decidableMemIic

instance decidableMemIoc [Decidable (a < x ∧ x ≤ b)] : Decidable (x ∈ ioc a b) := by assumption
#align set.decidable_mem_Ioc Set.decidableMemIoc

instance decidableMemIci [Decidable (a ≤ x)] : Decidable (x ∈ ici a) := by assumption
#align set.decidable_mem_Ici Set.decidableMemIci

instance decidableMemIoi [Decidable (a < x)] : Decidable (x ∈ ioi a) := by assumption
#align set.decidable_mem_Ioi Set.decidableMemIoi

@[simp]
theorem left_mem_Ioo : a ∈ ioo a b ↔ False := by simp [lt_irrefl]
#align set.left_mem_Ioo Set.left_mem_Ioo

@[simp]
theorem left_mem_Ico : a ∈ ico a b ↔ a < b := by simp [le_refl]
#align set.left_mem_Ico Set.left_mem_Ico

@[simp]
theorem left_mem_Icc : a ∈ icc a b ↔ a ≤ b := by simp [le_refl]
#align set.left_mem_Icc Set.left_mem_Icc

@[simp]
theorem left_mem_Ioc : a ∈ ioc a b ↔ False := by simp [lt_irrefl]
#align set.left_mem_Ioc Set.left_mem_Ioc

theorem left_mem_Ici : a ∈ ici a := by simp
#align set.left_mem_Ici Set.left_mem_Ici

@[simp]
theorem right_mem_Ioo : b ∈ ioo a b ↔ False := by simp [lt_irrefl]
#align set.right_mem_Ioo Set.right_mem_Ioo

@[simp]
theorem right_mem_Ico : b ∈ ico a b ↔ False := by simp [lt_irrefl]
#align set.right_mem_Ico Set.right_mem_Ico

@[simp]
theorem right_mem_Icc : b ∈ icc a b ↔ a ≤ b := by simp [le_refl]
#align set.right_mem_Icc Set.right_mem_Icc

@[simp]
theorem right_mem_Ioc : b ∈ ioc a b ↔ a < b := by simp [le_refl]
#align set.right_mem_Ioc Set.right_mem_Ioc

theorem right_mem_Iic : a ∈ iic a := by simp
#align set.right_mem_Iic Set.right_mem_Iic

@[simp]
theorem dual_Ici : ici (toDual a) = ofDual ⁻¹' iic a := rfl
#align set.dual_Ici Set.dual_Ici

@[simp]
theorem dual_Iic : iic (toDual a) = ofDual ⁻¹' ici a :=
  rfl
#align set.dual_Iic Set.dual_Iic

@[simp]
theorem dual_Ioi : ioi (toDual a) = ofDual ⁻¹' iio a :=
  rfl
#align set.dual_Ioi Set.dual_Ioi

@[simp]
theorem dual_Iio : iio (toDual a) = ofDual ⁻¹' ioi a :=
  rfl
#align set.dual_Iio Set.dual_Iio

@[simp]
theorem dual_Icc : icc (toDual a) (toDual b) = ofDual ⁻¹' icc b a :=
  Set.ext fun _ => @and_comm _ _
#align set.dual_Icc Set.dual_Icc

@[simp]
theorem dual_Ioc : ioc (toDual a) (toDual b) = ofDual ⁻¹' ico b a :=
  Set.ext fun _ => @and_comm _ _
#align set.dual_Ioc Set.dual_Ioc

@[simp]
theorem dual_Ico : ico (toDual a) (toDual b) = ofDual ⁻¹' ioc b a :=
  Set.ext fun _ => @and_comm _ _
#align set.dual_Ico Set.dual_Ico

@[simp]
theorem dual_Ioo : ioo (toDual a) (toDual b) = ofDual ⁻¹' ioo b a :=
  Set.ext fun _ => @and_comm _ _
#align set.dual_Ioo Set.dual_Ioo

@[simp]
theorem nonempty_Icc : (icc a b).Nonempty ↔ a ≤ b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩
#align set.nonempty_Icc Set.nonempty_Icc

@[simp]
theorem nonempty_Ico : (ico a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩
#align set.nonempty_Ico Set.nonempty_Ico

@[simp]
theorem nonempty_Ioc : (ioc a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_le hx.2, fun h => ⟨b, right_mem_Ioc.2 h⟩⟩
#align set.nonempty_Ioc Set.nonempty_Ioc

@[simp]
theorem nonempty_Ici : (ici a).Nonempty :=
  ⟨a, left_mem_Ici⟩
#align set.nonempty_Ici Set.nonempty_Ici

@[simp]
theorem nonempty_Iic : (iic a).Nonempty :=
  ⟨a, right_mem_Iic⟩
#align set.nonempty_Iic Set.nonempty_Iic

@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (ioo a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩
#align set.nonempty_Ioo Set.nonempty_Ioo

@[simp]
theorem nonempty_Ioi [NoMaxOrder α] : (ioi a).Nonempty :=
  exists_gt a
#align set.nonempty_Ioi Set.nonempty_Ioi

@[simp]
theorem nonempty_Iio [NoMinOrder α] : (iio a).Nonempty :=
  exists_lt a
#align set.nonempty_Iio Set.nonempty_Iio

theorem nonempty_Icc_subtype (h : a ≤ b) : Nonempty (icc a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)
#align set.nonempty_Icc_subtype Set.nonempty_Icc_subtype

theorem nonempty_Ico_subtype (h : a < b) : Nonempty (ico a b) :=
  Nonempty.to_subtype (nonempty_Ico.mpr h)
#align set.nonempty_Ico_subtype Set.nonempty_Ico_subtype

theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (ioc a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)
#align set.nonempty_Ioc_subtype Set.nonempty_Ioc_subtype

/-- An interval `Ici a` is nonempty. -/
instance nonempty_Ici_subtype : Nonempty (ici a) :=
  Nonempty.to_subtype nonempty_Ici
#align set.nonempty_Ici_subtype Set.nonempty_Ici_subtype

/-- An interval `Iic a` is nonempty. -/
instance nonempty_Iic_subtype : Nonempty (iic a) :=
  Nonempty.to_subtype nonempty_Iic
#align set.nonempty_Iic_subtype Set.nonempty_Iic_subtype

theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (ioo a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)
#align set.nonempty_Ioo_subtype Set.nonempty_Ioo_subtype

/-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/
instance nonempty_Ioi_subtype [NoMaxOrder α] : Nonempty (ioi a) :=
  Nonempty.to_subtype nonempty_Ioi
#align set.nonempty_Ioi_subtype Set.nonempty_Ioi_subtype

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (iio a) :=
  Nonempty.to_subtype nonempty_Iio
#align set.nonempty_Iio_subtype Set.nonempty_Iio_subtype

instance [NoMinOrder α] : NoMinOrder (iio a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

instance [NoMinOrder α] : NoMinOrder (iic a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

instance [NoMaxOrder α] : NoMaxOrder (ioi a) :=
  OrderDual.noMaxOrder (iio (toDual a))

instance [NoMaxOrder α] : NoMaxOrder (ici a) :=
  OrderDual.noMaxOrder (iic (toDual a))

@[simp]
theorem Icc_eq_empty (h : ¬a ≤ b) : icc a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)
#align set.Icc_eq_empty Set.Icc_eq_empty

@[simp]
theorem Ico_eq_empty (h : ¬a < b) : ico a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ ⟨ha, hb⟩ => h (ha.trans_lt hb)
#align set.Ico_eq_empty Set.Ico_eq_empty

@[simp]
theorem Ioc_eq_empty (h : ¬a < b) : ioc a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ ⟨ha, hb⟩ => h (ha.trans_le hb)
#align set.Ioc_eq_empty Set.Ioc_eq_empty

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)
#align set.Ioo_eq_empty Set.Ioo_eq_empty

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : icc a b = ∅ :=
  Icc_eq_empty h.not_le
#align set.Icc_eq_empty_of_lt Set.Icc_eq_empty_of_lt

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : ico a b = ∅ :=
  Ico_eq_empty h.not_lt
#align set.Ico_eq_empty_of_le Set.Ico_eq_empty_of_le

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : ioc a b = ∅ :=
  Ioc_eq_empty h.not_lt
#align set.Ioc_eq_empty_of_le Set.Ioc_eq_empty_of_le

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : ioo a b = ∅ :=
  Ioo_eq_empty h.not_lt
#align set.Ioo_eq_empty_of_le Set.Ioo_eq_empty_of_le

@[simp]
theorem Ico_self (a : α) : ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
#align set.Ico_self Set.Ico_self

@[simp]
theorem Ioc_self (a : α) : ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _
#align set.Ioc_self Set.Ioc_self

@[simp]
theorem Ioo_self (a : α) : ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _
#align set.Ioo_self Set.Ioo_self

theorem Ici_subset_Ici : ici a ⊆ ici b ↔ b ≤ a :=
  ⟨fun h => h <| left_mem_Ici, fun h _ hx => h.trans hx⟩
#align set.Ici_subset_Ici Set.Ici_subset_Ici

theorem Iic_subset_Iic : iic a ⊆ iic b ↔ a ≤ b :=
  @Ici_subset_Ici αᵒᵈ _ _ _
#align set.Iic_subset_Iic Set.Iic_subset_Iic

theorem Ici_subset_Ioi : ici a ⊆ ioi b ↔ b < a :=
  ⟨fun h => h left_mem_Ici, fun h _ hx => h.trans_le hx⟩
#align set.Ici_subset_Ioi Set.Ici_subset_Ioi

theorem Iic_subset_Iio : iic a ⊆ iio b ↔ a < b :=
  ⟨fun h => h right_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩
#align set.Iic_subset_Iio Set.Iic_subset_Iio

theorem Ioo_subset_Ioo (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : ioo a₁ b₁ ⊆ ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans_le h₂⟩
#align set.Ioo_subset_Ioo Set.Ioo_subset_Ioo

theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : ioo a₂ b ⊆ ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl
#align set.Ioo_subset_Ioo_left Set.Ioo_subset_Ioo_left

theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : ioo a b₁ ⊆ ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h
#align set.Ioo_subset_Ioo_right Set.Ioo_subset_Ioo_right

theorem Ico_subset_Ico (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : ico a₁ b₁ ⊆ ico a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, hx₂.trans_le h₂⟩
#align set.Ico_subset_Ico Set.Ico_subset_Ico

theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : ico a₂ b ⊆ ico a₁ b :=
  Ico_subset_Ico h le_rfl
#align set.Ico_subset_Ico_left Set.Ico_subset_Ico_left

theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : ico a b₁ ⊆ ico a b₂ :=
  Ico_subset_Ico le_rfl h
#align set.Ico_subset_Ico_right Set.Ico_subset_Ico_right

theorem Icc_subset_Icc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : icc a₁ b₁ ⊆ icc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, le_trans hx₂ h₂⟩
#align set.Icc_subset_Icc Set.Icc_subset_Icc

theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : icc a₂ b ⊆ icc a₁ b :=
  Icc_subset_Icc h le_rfl
#align set.Icc_subset_Icc_left Set.Icc_subset_Icc_left

theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : icc a b₁ ⊆ icc a b₂ :=
  Icc_subset_Icc le_rfl h
#align set.Icc_subset_Icc_right Set.Icc_subset_Icc_right

theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : icc a₁ b₁ ⊆ ioo a₂ b₂ := fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
#align set.Icc_subset_Ioo Set.Icc_subset_Ioo

theorem Icc_subset_Ici_self : icc a b ⊆ ici a := fun _ => And.left
#align set.Icc_subset_Ici_self Set.Icc_subset_Ici_self

theorem Icc_subset_Iic_self : icc a b ⊆ iic b := fun _ => And.right
#align set.Icc_subset_Iic_self Set.Icc_subset_Iic_self

theorem Ioc_subset_Iic_self : ioc a b ⊆ iic b := fun _ => And.right
#align set.Ioc_subset_Iic_self Set.Ioc_subset_Iic_self

theorem Ioc_subset_Ioc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : ioc a₁ b₁ ⊆ ioc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans h₂⟩
#align set.Ioc_subset_Ioc Set.Ioc_subset_Ioc

theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : ioc a₂ b ⊆ ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl
#align set.Ioc_subset_Ioc_left Set.Ioc_subset_Ioc_left

theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : ioc a b₁ ⊆ ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h
#align set.Ioc_subset_Ioc_right Set.Ioc_subset_Ioc_right

theorem Ico_subset_Ioo_left (h₁ : a₁ < a₂) : ico a₂ b ⊆ ioo a₁ b := fun _ =>
  And.imp_left h₁.trans_le
#align set.Ico_subset_Ioo_left Set.Ico_subset_Ioo_left

theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : ioc a b₁ ⊆ ioo a b₂ := fun _ =>
  And.imp_right fun h' => h'.trans_lt h
#align set.Ioc_subset_Ioo_right Set.Ioc_subset_Ioo_right

theorem Icc_subset_Ico_right (h₁ : b₁ < b₂) : icc a b₁ ⊆ ico a b₂ := fun _ =>
  And.imp_right fun h₂ => h₂.trans_lt h₁
#align set.Icc_subset_Ico_right Set.Icc_subset_Ico_right

theorem Ioo_subset_Ico_self : ioo a b ⊆ ico a b := fun _ => And.imp_left le_of_lt
#align set.Ioo_subset_Ico_self Set.Ioo_subset_Ico_self

theorem Ioo_subset_Ioc_self : ioo a b ⊆ ioc a b := fun _ => And.imp_right le_of_lt
#align set.Ioo_subset_Ioc_self Set.Ioo_subset_Ioc_self

theorem Ico_subset_Icc_self : ico a b ⊆ icc a b := fun _ => And.imp_right le_of_lt
#align set.Ico_subset_Icc_self Set.Ico_subset_Icc_self

theorem Ioc_subset_Icc_self : ioc a b ⊆ icc a b := fun _ => And.imp_left le_of_lt
#align set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self

theorem Ioo_subset_Icc_self : ioo a b ⊆ icc a b :=
  Subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self
#align set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

theorem Ico_subset_Iio_self : ico a b ⊆ iio b := fun _ => And.right
#align set.Ico_subset_Iio_self Set.Ico_subset_Iio_self

theorem Ioo_subset_Iio_self : ioo a b ⊆ iio b := fun _ => And.right
#align set.Ioo_subset_Iio_self Set.Ioo_subset_Iio_self

theorem Ioc_subset_Ioi_self : ioc a b ⊆ ioi a := fun _ => And.left
#align set.Ioc_subset_Ioi_self Set.Ioc_subset_Ioi_self

theorem Ioo_subset_Ioi_self : ioo a b ⊆ ioi a := fun _ => And.left
#align set.Ioo_subset_Ioi_self Set.Ioo_subset_Ioi_self

theorem Ioi_subset_Ici_self : ioi a ⊆ ici a := fun _ hx => le_of_lt hx
#align set.Ioi_subset_Ici_self Set.Ioi_subset_Ici_self

theorem Iio_subset_Iic_self : iio a ⊆ iic a := fun _ hx => le_of_lt hx
#align set.Iio_subset_Iic_self Set.Iio_subset_Iic_self

theorem Ico_subset_Ici_self : ico a b ⊆ ici a := fun _ => And.left
#align set.Ico_subset_Ici_self Set.Ico_subset_Ici_self

theorem Ioi_ssubset_Ici_self : ioi a ⊂ ici a :=
  ⟨Ioi_subset_Ici_self, fun h => lt_irrefl a (h le_rfl)⟩
#align set.Ioi_ssubset_Ici_self Set.Ioi_ssubset_Ici_self

theorem Iio_ssubset_Iic_self : iio a ⊂ iic a :=
  @Ioi_ssubset_Ici_self αᵒᵈ _ _
#align set.Iio_ssubset_Iic_self Set.Iio_ssubset_Iic_self

theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans hx, hx'.trans h'⟩⟩
#align set.Icc_subset_Icc_iff Set.Icc_subset_Icc_iff

theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans_le hx, hx'.trans_lt h'⟩⟩
#align set.Icc_subset_Ioo_iff Set.Icc_subset_Ioo_iff

theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans hx, hx'.trans_lt h'⟩⟩
#align set.Icc_subset_Ico_iff Set.Icc_subset_Ico_iff

theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans_le hx, hx'.trans h'⟩⟩
#align set.Icc_subset_Ioc_iff Set.Icc_subset_Ioc_iff

theorem Icc_subset_Iio_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ iio b₂ ↔ b₁ < b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h _ (_), hx'⟩ => hx'.trans_lt h⟩
#align set.Icc_subset_Iio_iff Set.Icc_subset_Iio_iff

theorem Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioi a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ ⟨hx, _⟩ => h.trans_le hx⟩
#align set.Icc_subset_Ioi_iff Set.Icc_subset_Ioi_iff

theorem Icc_subset_Iic_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ iic b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h _ ⟨_, hx'⟩ => hx'.trans h⟩
#align set.Icc_subset_Iic_iff Set.Icc_subset_Iic_iff

theorem Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ici a₂ ↔ a₂ ≤ a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ ⟨hx, _⟩ => h.trans hx⟩
#align set.Icc_subset_Ici_iff Set.Icc_subset_Ici_iff

theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : icc a₁ b₁ ⊂ icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr hI, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩
#align set.Icc_ssubset_Icc_left Set.Icc_ssubset_Icc_left

theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    icc a₁ b₁ ⊂ icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc ha (le_of_lt hb))).mpr
    ⟨b₂, right_mem_Icc.mpr hI, fun f => lt_irrefl b₁ (hb.trans_le f.2)⟩
#align set.Icc_ssubset_Icc_right Set.Icc_ssubset_Icc_right

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
theorem Ioi_subset_Ioi (h : a ≤ b) : ioi b ⊆ ioi a := fun _ hx => h.trans_lt hx
#align set.Ioi_subset_Ioi Set.Ioi_subset_Ioi

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
theorem Ioi_subset_Ici (h : a ≤ b) : ioi b ⊆ ici a :=
  Subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self
#align set.Ioi_subset_Ici Set.Ioi_subset_Ici

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
theorem Iio_subset_Iio (h : a ≤ b) : iio a ⊆ iio b := fun _ hx => lt_of_lt_of_le hx h
#align set.Iio_subset_Iio Set.Iio_subset_Iio

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
theorem Iio_subset_Iic (h : a ≤ b) : iio a ⊆ iic b :=
  Subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self
#align set.Iio_subset_Iic Set.Iio_subset_Iic

theorem Ici_inter_Iic : ici a ∩ iic b = icc a b :=
  rfl
#align set.Ici_inter_Iic Set.Ici_inter_Iic

theorem Ici_inter_Iio : ici a ∩ iio b = ico a b :=
  rfl
#align set.Ici_inter_Iio Set.Ici_inter_Iio

theorem Ioi_inter_Iic : ioi a ∩ iic b = ioc a b :=
  rfl
#align set.Ioi_inter_Iic Set.Ioi_inter_Iic

theorem Ioi_inter_Iio : ioi a ∩ iio b = ioo a b :=
  rfl
#align set.Ioi_inter_Iio Set.Ioi_inter_Iio

theorem Iic_inter_Ici : iic a ∩ ici b = icc b a :=
  inter_comm _ _
#align set.Iic_inter_Ici Set.Iic_inter_Ici

theorem Iio_inter_Ici : iio a ∩ ici b = ico b a :=
  inter_comm _ _
#align set.Iio_inter_Ici Set.Iio_inter_Ici

theorem Iic_inter_Ioi : iic a ∩ ioi b = ioc b a :=
  inter_comm _ _
#align set.Iic_inter_Ioi Set.Iic_inter_Ioi

theorem Iio_inter_Ioi : iio a ∩ ioi b = ioo b a :=
  inter_comm _ _
#align set.Iio_inter_Ioi Set.Iio_inter_Ioi

theorem mem_Icc_of_Ioo (h : x ∈ ioo a b) : x ∈ icc a b :=
  Ioo_subset_Icc_self h
#align set.mem_Icc_of_Ioo Set.mem_Icc_of_Ioo

theorem mem_Ico_of_Ioo (h : x ∈ ioo a b) : x ∈ ico a b :=
  Ioo_subset_Ico_self h
#align set.mem_Ico_of_Ioo Set.mem_Ico_of_Ioo

theorem mem_Ioc_of_Ioo (h : x ∈ ioo a b) : x ∈ ioc a b :=
  Ioo_subset_Ioc_self h
#align set.mem_Ioc_of_Ioo Set.mem_Ioc_of_Ioo

theorem mem_Icc_of_Ico (h : x ∈ ico a b) : x ∈ icc a b :=
  Ico_subset_Icc_self h
#align set.mem_Icc_of_Ico Set.mem_Icc_of_Ico

theorem mem_Icc_of_Ioc (h : x ∈ ioc a b) : x ∈ icc a b :=
  Ioc_subset_Icc_self h
#align set.mem_Icc_of_Ioc Set.mem_Icc_of_Ioc

theorem mem_Ici_of_Ioi (h : x ∈ ioi a) : x ∈ ici a :=
  Ioi_subset_Ici_self h
#align set.mem_Ici_of_Ioi Set.mem_Ici_of_Ioi

theorem mem_Iic_of_Iio (h : x ∈ iio a) : x ∈ iic a :=
  Iio_subset_Iic_self h
#align set.mem_Iic_of_Iio Set.mem_Iic_of_Iio

theorem Icc_eq_empty_iff : icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Icc]
#align set.Icc_eq_empty_iff Set.Icc_eq_empty_iff

theorem Ico_eq_empty_iff : ico a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ico]
#align set.Ico_eq_empty_iff Set.Ico_eq_empty_iff

theorem Ioc_eq_empty_iff : ioc a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioc]
#align set.Ioc_eq_empty_iff Set.Ioc_eq_empty_iff

theorem Ioo_eq_empty_iff [DenselyOrdered α] : ioo a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioo]
#align set.Ioo_eq_empty_iff Set.Ioo_eq_empty_iff

theorem IsTop.Iic_eq (h : IsTop a) : iic a = univ :=
  eq_univ_of_forall h
#align is_top.Iic_eq Set.IsTop.Iic_eq

theorem IsBot.Ici_eq (h : IsBot a) : ici a = univ :=
  eq_univ_of_forall h
#align is_bot.Ici_eq Set.IsBot.Ici_eq

theorem IsMax.Ioi_eq (h : IsMax a) : ioi a = ∅ :=
  eq_empty_of_subset_empty fun _ => h.not_lt
#align is_max.Ioi_eq Set.IsMax.Ioi_eq

theorem IsMin.Iio_eq (h : IsMin a) : iio a = ∅ :=
  eq_empty_of_subset_empty fun _ => h.not_lt
#align is_min.Iio_eq Set.IsMin.Iio_eq

theorem Iic_inter_Ioc_of_le (h : a ≤ c) : iic a ∩ ioc b c = ioc b a :=
  ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩
#align set.Iic_inter_Ioc_of_le Set.Iic_inter_Ioc_of_le

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : icc a a = {a} :=
  Set.ext <| by simp [icc, le_antisymm_iff, and_comm]
#align set.Icc_self Set.Icc_self

@[simp]
theorem Icc_eq_singleton_iff : icc a b = {c} ↔ a = c ∧ b = c := by
  refine' ⟨fun h => _, _⟩
  · have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
      ⟨eq_of_mem_singleton <| h.subst <| left_mem_Icc.2 hab,
        eq_of_mem_singleton <| h.subst <| right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _
#align set.Icc_eq_singleton_iff Set.Icc_eq_singleton_iff

@[simp]
theorem Icc_diff_left : icc a b \ {a} = ioc a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]
#align set.Icc_diff_left Set.Icc_diff_left

@[simp]
theorem Icc_diff_right : icc a b \ {b} = ico a b :=
  ext fun x => by simp [lt_iff_le_and_ne, and_assoc]
#align set.Icc_diff_right Set.Icc_diff_right

@[simp]
theorem Ico_diff_left : ico a b \ {a} = ioo a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]
#align set.Ico_diff_left Set.Ico_diff_left

@[simp]
theorem Ioc_diff_right : ioc a b \ {b} = ioo a b :=
  ext fun x => by simp [and_assoc, ← lt_iff_le_and_ne]
#align set.Ioc_diff_right Set.Ioc_diff_right

@[simp]
theorem Icc_diff_both : icc a b \ {a, b} = ioo a b := by
  rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]
#align set.Icc_diff_both Set.Icc_diff_both

@[simp]
theorem Ici_diff_left : ici a \ {a} = ioi a :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm]
#align set.Ici_diff_left Set.Ici_diff_left

@[simp]
theorem Iic_diff_right : iic a \ {a} = iio a :=
  ext fun x => by simp [lt_iff_le_and_ne]
#align set.Iic_diff_right Set.Iic_diff_right

@[simp]
theorem Ico_diff_Ioo_same (h : a < b) : ico a b \ ioo a b = {a} := by
  rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]
#align set.Ico_diff_Ioo_same Set.Ico_diff_Ioo_same

@[simp]
theorem Ioc_diff_Ioo_same (h : a < b) : ioc a b \ ioo a b = {b} := by
  rw [← Ioc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Ioc.2 h)]
#align set.Ioc_diff_Ioo_same Set.Ioc_diff_Ioo_same

@[simp]
theorem Icc_diff_Ico_same (h : a ≤ b) : icc a b \ ico a b = {b} := by
  rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]
#align set.Icc_diff_Ico_same Set.Icc_diff_Ico_same

@[simp]
theorem Icc_diff_Ioc_same (h : a ≤ b) : icc a b \ ioc a b = {a} := by
  rw [← Icc_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Icc.2 h)]
#align set.Icc_diff_Ioc_same Set.Icc_diff_Ioc_same

@[simp]
theorem Icc_diff_Ioo_same (h : a ≤ b) : icc a b \ ioo a b = {a, b} := by
  rw [← Icc_diff_both, diff_diff_cancel_left]
  simp [insert_subset, h]
#align set.Icc_diff_Ioo_same Set.Icc_diff_Ioo_same

@[simp]
theorem Ici_diff_Ioi_same : ici a \ ioi a = {a} := by
  rw [← Ici_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 left_mem_Ici)]
#align set.Ici_diff_Ioi_same Set.Ici_diff_Ioi_same

@[simp]
theorem Iic_diff_Iio_same : iic a \ iio a = {a} := by
  rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 right_mem_Iic)]
#align set.Iic_diff_Iio_same Set.Iic_diff_Iio_same

@[simp]
theorem Ioi_union_left : ioi a ∪ {a} = ici a :=
  ext fun _ => by simp [eq_comm, le_iff_eq_or_lt]
#align set.Ioi_union_left Set.Ioi_union_left

@[simp]
theorem Iio_union_right : iio a ∪ {a} = iic a :=
  ext fun _ => le_iff_lt_or_eq.symm
#align set.Iio_union_right Set.Iio_union_right

theorem Ioo_union_left (hab : a < b) : ioo a b ∪ {a} = ico a b := by
  rw [← Ico_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]
#align set.Ioo_union_left Set.Ioo_union_left

theorem Ioo_union_right (hab : a < b) : ioo a b ∪ {b} = ioc a b := by
  simpa only [dual_Ioo, dual_Ico] using Ioo_union_left hab.dual
#align set.Ioo_union_right Set.Ioo_union_right

theorem Ioc_union_left (hab : a ≤ b) : ioc a b ∪ {a} = icc a b := by
  rw [← Icc_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]
#align set.Ioc_union_left Set.Ioc_union_left

theorem Ico_union_right (hab : a ≤ b) : ico a b ∪ {b} = icc a b := by
  simpa only [dual_Ioc, dual_Icc] using Ioc_union_left hab.dual
#align set.Ico_union_right Set.Ico_union_right

@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (ico a b) = icc a b := by
  rw [insert_eq, union_comm, Ico_union_right h]
#align set.Ico_insert_right Set.Ico_insert_right

@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (ioc a b) = icc a b := by
  rw [insert_eq, union_comm, Ioc_union_left h]
#align set.Ioc_insert_left Set.Ioc_insert_left

@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (ioo a b) = ico a b := by
  rw [insert_eq, union_comm, Ioo_union_left h]
#align set.Ioo_insert_left Set.Ioo_insert_left

@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (ioo a b) = ioc a b := by
  rw [insert_eq, union_comm, Ioo_union_right h]
#align set.Ioo_insert_right Set.Ioo_insert_right

@[simp]
theorem Iio_insert : insert a (iio a) = iic a :=
  ext fun _ => le_iff_eq_or_lt.symm
#align set.Iio_insert Set.Iio_insert

@[simp]
theorem Ioi_insert : insert a (ioi a) = ici a :=
  ext fun _ => (or_congr_left eq_comm).trans le_iff_eq_or_lt.symm
#align set.Ioi_insert Set.Ioi_insert

theorem mem_Ici_Ioi_of_subset_of_subset {s : Set α} (ho : ioi a ⊆ s) (hc : s ⊆ ici a) :
    s ∈ ({ici a, ioi a} : Set (Set α)) :=
  Classical.byCases
    (fun h : a ∈ s =>
      Or.inl <| Subset.antisymm hc <| by rw [← Ioi_union_left, union_subset_iff] <;> simp [*])
    fun h =>
    Or.inr <| Subset.antisymm (fun x hx => lt_of_le_of_ne (hc hx) fun heq => h <| HEq.symm ▸ hx) ho
#align set.mem_Ici_Ioi_of_subset_of_subset Set.mem_Ici_Ioi_of_subset_of_subset

theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : iio a ⊆ s) (hc : s ⊆ iic a) :
    s ∈ ({iic a, iio a} : Set (Set α)) :=
  @mem_Ici_Ioi_of_subset_of_subset αᵒᵈ _ a s ho hc
#align set.mem_Iic_Iio_of_subset_of_subset Set.mem_Iic_Iio_of_subset_of_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:38: in apply_rules #[["[", expr subset_diff_singleton, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : ioo a b ⊆ s) (hc : s ⊆ icc a b) :
    s ∈ ({icc a b, ico a b, ioc a b, ioo a b} : Set (Set α)) := by
  classical
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · refine' Or.inl (Subset.antisymm hc _)
      rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_diff_right,
        diff_singleton_subset_iff, insert_eq_of_mem hb] at ho
    · refine' Or.inr <| Or.inl <| Subset.antisymm _ _
      · rw [← Icc_diff_right]
        exact subset_diff_singleton hc hb
      · rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha] at ho
    · refine' Or.inr <| Or.inr <| Or.inl <| Subset.antisymm _ _
      · rw [← Icc_diff_left]
        exact subset_diff_singleton hc ha
      · rwa [← Ioc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho
    · refine' Or.inr <| Or.inr <| Or.inr <| Subset.antisymm _ ho
      rw [← Ico_diff_left, ← Icc_diff_right]
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:38: in apply_rules #[[\"[\", expr subset_diff_singleton, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
#align set.mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset Set.mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset

theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x ∈ ico a b) : x = a ∨ x ∈ ioo a b :=
  hmem.1.eq_or_gt.imp_right fun h => ⟨h, hmem.2⟩
#align set.eq_left_or_mem_Ioo_of_mem_Ico Set.eq_left_or_mem_Ioo_of_mem_Ico

theorem eq_right_or_mem_Ioo_of_mem_Ioc {x : α} (hmem : x ∈ ioc a b) : x = b ∨ x ∈ ioo a b :=
  hmem.2.eq_or_lt.imp_right <| And.intro hmem.1
#align set.eq_right_or_mem_Ioo_of_mem_Ioc Set.eq_right_or_mem_Ioo_of_mem_Ioc

theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x ∈ icc a b) :
    x = a ∨ x = b ∨ x ∈ ioo a b :=
  hmem.1.eq_or_gt.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩
#align set.eq_endpoints_or_mem_Ioo_of_mem_Icc Set.eq_endpoints_or_mem_Ioo_of_mem_Icc

theorem IsMax.Ici_eq (h : IsMax a) : ici a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨left_mem_Ici, fun _ => h.eq_of_ge⟩
#align is_max.Ici_eq Set.IsMax.Ici_eq

theorem IsMin.Iic_eq (h : IsMin a) : iic a = {a} :=
  h.toDual.Ici_eq
#align is_min.Iic_eq Set.IsMin.Iic_eq

theorem Ici_injective : Injective (ici : α → Set α) := fun _ _ =>
  eq_of_forall_ge_iff ∘ Set.ext_iff.1
#align set.Ici_injective Set.Ici_injective

theorem Iic_injective : Injective (iic : α → Set α) := fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1
#align set.Iic_injective Set.Iic_injective

theorem Ici_inj : ici a = ici b ↔ a = b :=
  Ici_injective.eq_iff
#align set.Ici_inj Set.Ici_inj

theorem Iic_inj : iic a = iic b ↔ a = b :=
  Iic_injective.eq_iff
#align set.Iic_inj Set.Iic_inj

end PartialOrder

section OrderTop

@[simp]
theorem Ici_top [PartialOrder α] [OrderTop α] : ici (⊤ : α) = {⊤} :=
  isMax_top.Ici_eq
#align set.Ici_top Set.Ici_top

variable [Preorder α] [OrderTop α] {a : α}

@[simp]
theorem Ioi_top : ioi (⊤ : α) = ∅ :=
  isMax_top.Ioi_eq
#align set.Ioi_top Set.Ioi_top

@[simp]
theorem Iic_top : iic (⊤ : α) = univ :=
  isTop_top.Iic_eq
#align set.Iic_top Set.Iic_top

@[simp]
theorem Icc_top : icc a ⊤ = ici a := by simp [← Ici_inter_Iic]
#align set.Icc_top Set.Icc_top

@[simp]
theorem Ioc_top : ioc a ⊤ = ioi a := by simp [← Ioi_inter_Iic]
#align set.Ioc_top Set.Ioc_top

end OrderTop

section OrderBot

@[simp]
theorem Iic_bot [PartialOrder α] [OrderBot α] : iic (⊥ : α) = {⊥} :=
  isMin_bot.Iic_eq
#align set.Iic_bot Set.Iic_bot

variable [Preorder α] [OrderBot α] {a : α}

@[simp]
theorem Iio_bot : iio (⊥ : α) = ∅ :=
  isMin_bot.Iio_eq
#align set.Iio_bot Set.Iio_bot

@[simp]
theorem Ici_bot : ici (⊥ : α) = univ :=
  isBot_bot.Ici_eq
#align set.Ici_bot Set.Ici_bot

@[simp]
theorem Icc_bot : icc ⊥ a = iic a := by simp [← Ici_inter_Iic]
#align set.Icc_bot Set.Icc_bot

@[simp]
theorem Ico_bot : ico ⊥ a = iio a := by simp [← Ici_inter_Iio]
#align set.Ico_bot Set.Ico_bot

end OrderBot

theorem Icc_bot_top [PartialOrder α] [BoundedOrder α] : icc (⊥ : α) ⊤ = univ := by simp
#align set.Icc_bot_top Set.Icc_bot_top

section LinearOrder

variable [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

theorem not_mem_Ici : c ∉ ici a ↔ c < a :=
  not_le
#align set.not_mem_Ici Set.not_mem_Ici

theorem not_mem_Iic : c ∉ iic b ↔ b < c :=
  not_le
#align set.not_mem_Iic Set.not_mem_Iic

theorem not_mem_Icc_of_lt (ha : c < a) : c ∉ icc a b :=
  not_mem_subset Icc_subset_Ici_self <| not_mem_Ici.mpr ha
#align set.not_mem_Icc_of_lt Set.not_mem_Icc_of_lt

theorem not_mem_Icc_of_gt (hb : b < c) : c ∉ icc a b :=
  not_mem_subset Icc_subset_Iic_self <| not_mem_Iic.mpr hb
#align set.not_mem_Icc_of_gt Set.not_mem_Icc_of_gt

theorem not_mem_Ico_of_lt (ha : c < a) : c ∉ ico a b :=
  not_mem_subset Ico_subset_Ici_self <| not_mem_Ici.mpr ha
#align set.not_mem_Ico_of_lt Set.not_mem_Ico_of_lt

theorem not_mem_Ioc_of_gt (hb : b < c) : c ∉ ioc a b :=
  not_mem_subset Ioc_subset_Iic_self <| not_mem_Iic.mpr hb
#align set.not_mem_Ioc_of_gt Set.not_mem_Ioc_of_gt

theorem not_mem_Ioi : c ∉ ioi a ↔ c ≤ a :=
  not_lt
#align set.not_mem_Ioi Set.not_mem_Ioi

theorem not_mem_Iio : c ∉ iio b ↔ b ≤ c :=
  not_lt
#align set.not_mem_Iio Set.not_mem_Iio

@[simp]
theorem not_mem_Ioi_self : a ∉ ioi a :=
  lt_irrefl _
#align set.not_mem_Ioi_self Set.not_mem_Ioi_self

@[simp]
theorem not_mem_Iio_self : b ∉ iio b :=
  lt_irrefl _
#align set.not_mem_Iio_self Set.not_mem_Iio_self

theorem not_mem_Ioc_of_le (ha : c ≤ a) : c ∉ ioc a b :=
  not_mem_subset Ioc_subset_Ioi_self <| not_mem_Ioi.mpr ha
#align set.not_mem_Ioc_of_le Set.not_mem_Ioc_of_le

theorem not_mem_Ico_of_ge (hb : b ≤ c) : c ∉ ico a b :=
  not_mem_subset Ico_subset_Iio_self <| not_mem_Iio.mpr hb
#align set.not_mem_Ico_of_ge Set.not_mem_Ico_of_ge

theorem not_mem_Ioo_of_le (ha : c ≤ a) : c ∉ ioo a b :=
  not_mem_subset Ioo_subset_Ioi_self <| not_mem_Ioi.mpr ha
#align set.not_mem_Ioo_of_le Set.not_mem_Ioo_of_le

theorem not_mem_Ioo_of_ge (hb : b ≤ c) : c ∉ ioo a b :=
  not_mem_subset Ioo_subset_Iio_self <| not_mem_Iio.mpr hb
#align set.not_mem_Ioo_of_ge Set.not_mem_Ioo_of_ge

@[simp]
theorem compl_Iic : iic aᶜ = ioi a :=
  ext fun _ => not_le
#align set.compl_Iic Set.compl_Iic

@[simp]
theorem compl_Ici : ici aᶜ = iio a :=
  ext fun _ => not_le
#align set.compl_Ici Set.compl_Ici

@[simp]
theorem compl_Iio : iio aᶜ = ici a :=
  ext fun _ => not_lt
#align set.compl_Iio Set.compl_Iio

@[simp]
theorem compl_Ioi : ioi aᶜ = iic a :=
  ext fun _ => not_lt
#align set.compl_Ioi Set.compl_Ioi

@[simp]
theorem Ici_diff_Ici : ici a \ ici b = ico a b := by rw [diff_eq, compl_Ici, Ici_inter_Iio]
#align set.Ici_diff_Ici Set.Ici_diff_Ici

@[simp]
theorem Ici_diff_Ioi : ici a \ ioi b = icc a b := by rw [diff_eq, compl_Ioi, Ici_inter_Iic]
#align set.Ici_diff_Ioi Set.Ici_diff_Ioi

@[simp]
theorem Ioi_diff_Ioi : ioi a \ ioi b = ioc a b := by rw [diff_eq, compl_Ioi, Ioi_inter_Iic]
#align set.Ioi_diff_Ioi Set.Ioi_diff_Ioi

@[simp]
theorem Ioi_diff_Ici : ioi a \ ici b = ioo a b := by rw [diff_eq, compl_Ici, Ioi_inter_Iio]
#align set.Ioi_diff_Ici Set.Ioi_diff_Ici

@[simp]
theorem Iic_diff_Iic : iic b \ iic a = ioc a b := by
  rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iic]
#align set.Iic_diff_Iic Set.Iic_diff_Iic

@[simp]
theorem Iio_diff_Iic : iio b \ iic a = ioo a b := by
  rw [diff_eq, compl_Iic, inter_comm, Ioi_inter_Iio]
#align set.Iio_diff_Iic Set.Iio_diff_Iic

@[simp]
theorem Iic_diff_Iio : iic b \ iio a = icc a b := by
  rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iic]
#align set.Iic_diff_Iio Set.Iic_diff_Iio

@[simp]
theorem Iio_diff_Iio : iio b \ iio a = ico a b := by
  rw [diff_eq, compl_Iio, inter_comm, Ici_inter_Iio]
#align set.Iio_diff_Iio Set.Iio_diff_Iio

theorem Ioi_injective : Injective (ioi : α → Set α) := fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1
#align set.Ioi_injective Set.Ioi_injective

theorem Iio_injective : Injective (iio : α → Set α) := fun _ _ =>
  eq_of_forall_lt_iff ∘ Set.ext_iff.1
#align set.Iio_injective Set.Iio_injective

theorem Ioi_inj : ioi a = ioi b ↔ a = b :=
  Ioi_injective.eq_iff
#align set.Ioi_inj Set.Ioi_inj

theorem Iio_inj : iio a = iio b ↔ a = b :=
  Iio_injective.eq_iff
#align set.Iio_inj Set.Iio_inj

theorem Ico_subset_Ico_iff (h₁ : a₁ < b₁) : ico a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h =>
    have : a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_lt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩
#align set.Ico_subset_Ico_iff Set.Ico_subset_Ico_iff

theorem Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : ioc a₁ b₁ ⊆ ioc a₂ b₂ ↔ b₁ ≤ b₂ ∧ a₂ ≤ a₁ := by
  convert @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ <;> exact (@dual_Ico α _ _ _).symm
#align set.Ioc_subset_Ioc_iff Set.Ioc_subset_Ioc_iff

theorem Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) :
    ioo a₁ b₁ ⊆ ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine' le_of_not_lt fun h' => _
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩
#align set.Ioo_subset_Ioo_iff Set.Ioo_subset_Ioo_iff

theorem Ico_eq_Ico_iff (h : a₁ < b₁ ∨ a₂ < b₂) : ico a₁ b₁ = ico a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun e => by
    simp [Subset.antisymm_iff] at e; simp [le_antisymm_iff]
    cases  h <;> rename_i h <;> simp [Ico_subset_Ico_iff h] at e <;> [rcases e with ⟨⟨h₁, h₂⟩, e'⟩,
          rcases e with ⟨e', ⟨h₁, h₂⟩⟩] <;>
        have := (Ico_subset_Ico_iff <| h₁.trans_lt <| h.trans_le h₂).1 e' <;>
        sorry, --TODO porting notes: tauto
    fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩
#align set.Ico_eq_Ico_iff Set.Ico_eq_Ico_iff

open Classical

@[simp]
theorem Ioi_subset_Ioi_iff : ioi b ⊆ ioi a ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Ioi_subset_Ioi h⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))
#align set.Ioi_subset_Ioi_iff Set.Ioi_subset_Ioi_iff

@[simp]
theorem Ioi_subset_Ici_iff [DenselyOrdered α] : ioi b ⊆ ici a ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Ioi_subset_Ici h⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : ∃ c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))
#align set.Ioi_subset_Ici_iff Set.Ioi_subset_Ici_iff

@[simp]
theorem Iio_subset_Iio_iff : iio a ⊆ iio b ↔ a ≤ b := by
  refine' ⟨fun h => _, fun h => Iio_subset_Iio h⟩
  by_contra ab
  exact lt_irrefl _ (h (not_le.mp ab))
#align set.Iio_subset_Iio_iff Set.Iio_subset_Iio_iff

@[simp]
theorem Iio_subset_Iic_iff [DenselyOrdered α] : iio a ⊆ iic b ↔ a ≤ b := by
  rw [← diff_eq_empty, Iio_diff_Iic, Ioo_eq_empty_iff, not_lt]
#align set.Iio_subset_Iic_iff Set.Iio_subset_Iic_iff

/-! ### Unions of adjacent intervals -/


/-! #### Two infinite intervals -/


theorem Iic_union_Ioi_of_le (h : a ≤ b) : iic b ∪ ioi a = univ :=
  eq_univ_of_forall fun x => (h.lt_or_le x).symm
#align set.Iic_union_Ioi_of_le Set.Iic_union_Ioi_of_le

theorem Iio_union_Ici_of_le (h : a ≤ b) : iio b ∪ ici a = univ :=
  eq_univ_of_forall fun x => (h.le_or_lt x).symm
#align set.Iio_union_Ici_of_le Set.Iio_union_Ici_of_le

theorem Iic_union_Ici_of_le (h : a ≤ b) : iic b ∪ ici a = univ :=
  eq_univ_of_forall fun x => (h.le_or_le x).symm
#align set.Iic_union_Ici_of_le Set.Iic_union_Ici_of_le

theorem Iio_union_Ioi_of_lt (h : a < b) : iio b ∪ ioi a = univ :=
  eq_univ_of_forall fun x => (h.lt_or_lt x).symm
#align set.Iio_union_Ioi_of_lt Set.Iio_union_Ioi_of_lt

@[simp]
theorem Iic_union_Ici : iic a ∪ ici a = univ :=
  Iic_union_Ici_of_le le_rfl
#align set.Iic_union_Ici Set.Iic_union_Ici

@[simp]
theorem Iio_union_Ici : iio a ∪ ici a = univ :=
  Iio_union_Ici_of_le le_rfl
#align set.Iio_union_Ici Set.Iio_union_Ici

@[simp]
theorem Iic_union_Ioi : iic a ∪ ioi a = univ :=
  Iic_union_Ioi_of_le le_rfl
#align set.Iic_union_Ioi Set.Iic_union_Ioi

@[simp]
theorem Iio_union_Ioi : iio a ∪ ioi a = {a}ᶜ :=
  ext fun _ => lt_or_lt_iff_ne
#align set.Iio_union_Ioi Set.Iio_union_Ioi

/-! #### A finite and an infinite interval -/


theorem Ioo_union_Ioi' (h₁ : c < b) : ioo a b ∪ ioi c = ioi (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, mem_Ioi, min_lt_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x < b := (le_of_not_gt hc).trans_lt h₁
    tauto
#align set.Ioo_union_Ioi' Set.Ioo_union_Ioi'

theorem Ioo_union_Ioi (h : c < max a b) : ioo a b ∪ ioi c = ioi (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ioo_union_Ioi' h
  · rw [min_comm]
    simp [*, min_eq_left_of_lt]
#align set.Ioo_union_Ioi Set.Ioo_union_Ioi

theorem Ioi_subset_Ioo_union_Ici : ioi a ⊆ ioo a b ∪ ici b := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb
#align set.Ioi_subset_Ioo_union_Ici Set.Ioi_subset_Ioo_union_Ici

@[simp]
theorem Ioo_union_Ici_eq_Ioi (h : a < b) : ioo a b ∪ ici b = ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici
#align set.Ioo_union_Ici_eq_Ioi Set.Ioo_union_Ici_eq_Ioi

theorem Ici_subset_Ico_union_Ici : ici a ⊆ ico a b ∪ ici b := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb
#align set.Ici_subset_Ico_union_Ici Set.Ici_subset_Ico_union_Ici

@[simp]
theorem Ico_union_Ici_eq_Ici (h : a ≤ b) : ico a b ∪ ici b = ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici
#align set.Ico_union_Ici_eq_Ici Set.Ico_union_Ici_eq_Ici

theorem Ico_union_Ici' (h₁ : c ≤ b) : ico a b ∪ ici c = ici (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, mem_Ici, min_le_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
#align set.Ico_union_Ici' Set.Ico_union_Ici'

theorem Ico_union_Ici (h : c ≤ max a b) : ico a b ∪ ici c = ici (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ico_union_Ici' h
  · simp [*]
#align set.Ico_union_Ici Set.Ico_union_Ici

theorem Ioi_subset_Ioc_union_Ioi : ioi a ⊆ ioc a b ∪ ioi b := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb
#align set.Ioi_subset_Ioc_union_Ioi Set.Ioi_subset_Ioc_union_Ioi

@[simp]
theorem Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : ioc a b ∪ ioi b = ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi
#align set.Ioc_union_Ioi_eq_Ioi Set.Ioc_union_Ioi_eq_Ioi

theorem Ioc_union_Ioi' (h₁ : c ≤ b) : ioc a b ∪ ioi c = ioi (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, mem_Ioi, min_lt_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto
#align set.Ioc_union_Ioi' Set.Ioc_union_Ioi'

theorem Ioc_union_Ioi (h : c ≤ max a b) : ioc a b ∪ ioi c = ioi (min a c) := by
  cases' le_total a b with hab hab <;> simp [hab] at h
  · exact Ioc_union_Ioi' h
  · simp [*]
#align set.Ioc_union_Ioi Set.Ioc_union_Ioi

theorem Ici_subset_Icc_union_Ioi : ici a ⊆ icc a b ∪ ioi b := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb
#align set.Ici_subset_Icc_union_Ioi Set.Ici_subset_Icc_union_Ioi

@[simp]
theorem Icc_union_Ioi_eq_Ici (h : a ≤ b) : icc a b ∪ ioi b = ici a :=
  Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi
#align set.Icc_union_Ioi_eq_Ici Set.Icc_union_Ioi_eq_Ici

theorem Ioi_subset_Ioc_union_Ici : ioi a ⊆ ioc a b ∪ ici b :=
  Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)
#align set.Ioi_subset_Ioc_union_Ici Set.Ioi_subset_Ioc_union_Ici

@[simp]
theorem Ioc_union_Ici_eq_Ioi (h : a < b) : ioc a b ∪ ici b = ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici
#align set.Ioc_union_Ici_eq_Ioi Set.Ioc_union_Ici_eq_Ioi

theorem Ici_subset_Icc_union_Ici : ici a ⊆ icc a b ∪ ici b :=
  Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)
#align set.Ici_subset_Icc_union_Ici Set.Ici_subset_Icc_union_Ici

@[simp]
theorem Icc_union_Ici_eq_Ici (h : a ≤ b) : icc a b ∪ ici b = ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici
#align set.Icc_union_Ici_eq_Ici Set.Icc_union_Ici_eq_Ici

theorem Icc_union_Ici' (h₁ : c ≤ b) : icc a b ∪ ici c = ici (min a c) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, mem_Ici, min_le_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
#align set.Icc_union_Ici' Set.Icc_union_Ici'

theorem Icc_union_Ici (h : c ≤ max a b) : icc a b ∪ ici c = ici (min a c) := by
  cases' le_or_lt a b with hab hab <;> simp [hab] at h
  · exact Icc_union_Ici' h
  · cases h
    · simp [*]
    · rename_i h
      have hca : c ≤ a := h.trans hab.le
      simp [*]
#align set.Icc_union_Ici Set.Icc_union_Ici

/-! #### An infinite and a finite interval -/


theorem Iic_subset_Iio_union_Icc : iic b ⊆ iio a ∪ icc a b := fun x hx =>
  (lt_or_le x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩
#align set.Iic_subset_Iio_union_Icc Set.Iic_subset_Iio_union_Icc

@[simp]
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : iio a ∪ icc a b = iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc
#align set.Iio_union_Icc_eq_Iic Set.Iio_union_Icc_eq_Iic

theorem Iio_subset_Iio_union_Ico : iio b ⊆ iio a ∪ ico a b := fun x hx =>
  (lt_or_le x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩
#align set.Iio_subset_Iio_union_Ico Set.Iio_subset_Iio_union_Ico

@[simp]
theorem Iio_union_Ico_eq_Iio (h : a ≤ b) : iio a ∪ ico a b = iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico
#align set.Iio_union_Ico_eq_Iio Set.Iio_union_Ico_eq_Iio

theorem Iio_union_Ico' (h₁ : c ≤ b) : iio b ∪ ico c d = iio (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iio, mem_Ico, lt_max_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
#align set.Iio_union_Ico' Set.Iio_union_Ico'

theorem Iio_union_Ico (h : min c d ≤ b) : iio b ∪ ico c d = iio (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iio_union_Ico' h
  · simp [*]
#align set.Iio_union_Ico Set.Iio_union_Ico

theorem Iic_subset_Iic_union_Ioc : iic b ⊆ iic a ∪ ioc a b := fun x hx =>
  (le_or_lt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩
#align set.Iic_subset_Iic_union_Ioc Set.Iic_subset_Iic_union_Ioc

@[simp]
theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : iic a ∪ ioc a b = iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc
#align set.Iic_union_Ioc_eq_Iic Set.Iic_union_Ioc_eq_Iic

theorem Iic_union_Ioc' (h₁ : c < b) : iic b ∪ ioc c d = iic (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Ioc, le_max_iff]
  by_cases hc : c < x
  · tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁.le
    tauto
#align set.Iic_union_Ioc' Set.Iic_union_Ioc'

theorem Iic_union_Ioc (h : min c d < b) : iic b ∪ ioc c d = iic (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iic_union_Ioc' h
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]
#align set.Iic_union_Ioc Set.Iic_union_Ioc

theorem Iio_subset_Iic_union_Ioo : iio b ⊆ iic a ∪ ioo a b := fun x hx =>
  (le_or_lt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩
#align set.Iio_subset_Iic_union_Ioo Set.Iio_subset_Iic_union_Ioo

@[simp]
theorem Iic_union_Ioo_eq_Iio (h : a < b) : iic a ∪ ioo a b = iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo
#align set.Iic_union_Ioo_eq_Iio Set.Iic_union_Ioo_eq_Iio

theorem Iio_union_Ioo' (h₁ : c < b) : iio b ∪ ioo c d = iio (max b d) := by
  ext x
  cases' lt_or_le x b with hba hba
  · simp [hba, h₁]
  · simp only [mem_Iio, mem_union, mem_Ioo, lt_max_iff]
    refine' or_congr Iff.rfl ⟨And.right, _⟩
    exact fun h₂ => ⟨h₁.trans_le hba, h₂⟩
#align set.Iio_union_Ioo' Set.Iio_union_Ioo'

theorem Iio_union_Ioo (h : min c d < b) : iio b ∪ ioo c d = iio (max b d) := by
  cases' le_total c d with hcd hcd <;> simp [hcd] at h
  · exact Iio_union_Ioo' h
  · rw [max_comm]
    simp [*, max_eq_right_of_lt h]
#align set.Iio_union_Ioo Set.Iio_union_Ioo

theorem Iic_subset_Iic_union_Icc : iic b ⊆ iic a ∪ icc a b :=
  Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)
#align set.Iic_subset_Iic_union_Icc Set.Iic_subset_Iic_union_Icc

@[simp]
theorem Iic_union_Icc_eq_Iic (h : a ≤ b) : iic a ∪ icc a b = iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc
#align set.Iic_union_Icc_eq_Iic Set.Iic_union_Icc_eq_Iic

theorem Iic_union_Icc' (h₁ : c ≤ b) : iic b ∪ icc c d = iic (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Iic, mem_Icc, le_max_iff]
  by_cases hc : c ≤ x
  · tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
#align set.Iic_union_Icc' Set.Iic_union_Icc'

theorem Iic_union_Icc (h : min c d ≤ b) : iic b ∪ icc c d = iic (max b d) := by
  cases' le_or_lt c d with hcd hcd <;> simp [hcd] at h
  · exact Iic_union_Icc' h
  · cases h
    · rename_i h
      have hdb : d ≤ b := hcd.le.trans h
      simp [*]
    · simp [*]
#align set.Iic_union_Icc Set.Iic_union_Icc

theorem Iio_subset_Iic_union_Ico : iio b ⊆ iic a ∪ ico a b :=
  Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)
#align set.Iio_subset_Iic_union_Ico Set.Iio_subset_Iic_union_Ico

@[simp]
theorem Iic_union_Ico_eq_Iio (h : a < b) : iic a ∪ ico a b = iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico
#align set.Iic_union_Ico_eq_Iio Set.Iic_union_Ico_eq_Iio

/-! #### Two finite intervals, `I?o` and `Ic?` -/


theorem Ioo_subset_Ioo_union_Ico : ioo a c ⊆ ioo a b ∪ ico b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ioo_subset_Ioo_union_Ico Set.Ioo_subset_Ioo_union_Ico

@[simp]
theorem Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b ≤ c) : ioo a b ∪ ico b c = ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico
#align set.Ioo_union_Ico_eq_Ioo Set.Ioo_union_Ico_eq_Ioo

theorem Ico_subset_Ico_union_Ico : ico a c ⊆ ico a b ∪ ico b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ico_subset_Ico_union_Ico Set.Ico_subset_Ico_union_Ico

@[simp]
theorem Ico_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b ≤ c) : ico a b ∪ ico b c = ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico
#align set.Ico_union_Ico_eq_Ico Set.Ico_union_Ico_eq_Ico

theorem Ico_union_Ico' (h₁ : c ≤ b) (h₂ : a ≤ d) : ico a b ∪ ico c d = ico (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ico, min_le_iff, lt_max_iff]
  by_cases hc : c ≤ x <;> by_cases hd : x < d
  · tauto
  · have hax : a ≤ x := h₂.trans (le_of_not_gt hd)
    tauto
  · have hxb : x < b := (lt_of_not_ge hc).trans_le h₁
    tauto
  · tauto
#align set.Ico_union_Ico' Set.Ico_union_Ico'

theorem Ico_union_Ico (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    ico a b ∪ ico c d = ico (min a c) (max b d) := by
  cases' le_total a b with hab hab <;> cases' le_total c d with hcd hcd <;> simp [hab, hcd] at h₁ h₂
  · exact Ico_union_Ico' h₂ h₁
  all_goals simp [*]
#align set.Ico_union_Ico Set.Ico_union_Ico

theorem Icc_subset_Ico_union_Icc : icc a c ⊆ ico a b ∪ icc b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Icc_subset_Ico_union_Icc Set.Icc_subset_Ico_union_Icc

@[simp]
theorem Ico_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : ico a b ∪ icc b c = icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc
#align set.Ico_union_Icc_eq_Icc Set.Ico_union_Icc_eq_Icc

theorem Ioc_subset_Ioo_union_Icc : ioc a c ⊆ ioo a b ∪ icc b c := fun x hx =>
  (lt_or_le x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ioc_subset_Ioo_union_Icc Set.Ioc_subset_Ioo_union_Icc

@[simp]
theorem Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : ioo a b ∪ icc b c = ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc
#align set.Ioo_union_Icc_eq_Ioc Set.Ioo_union_Icc_eq_Ioc

/-! #### Two finite intervals, `I?c` and `Io?` -/


theorem Ioo_subset_Ioc_union_Ioo : ioo a c ⊆ ioc a b ∪ ioo b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ioo_subset_Ioc_union_Ioo Set.Ioo_subset_Ioc_union_Ioo

@[simp]
theorem Ioc_union_Ioo_eq_Ioo (h₁ : a ≤ b) (h₂ : b < c) : ioc a b ∪ ioo b c = ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo
#align set.Ioc_union_Ioo_eq_Ioo Set.Ioc_union_Ioo_eq_Ioo

theorem Ico_subset_Icc_union_Ioo : ico a c ⊆ icc a b ∪ ioo b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ico_subset_Icc_union_Ioo Set.Ico_subset_Icc_union_Ioo

@[simp]
theorem Icc_union_Ioo_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : icc a b ∪ ioo b c = ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo
#align set.Icc_union_Ioo_eq_Ico Set.Icc_union_Ioo_eq_Ico

theorem Icc_subset_Icc_union_Ioc : icc a c ⊆ icc a b ∪ ioc b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Icc_subset_Icc_union_Ioc Set.Icc_subset_Icc_union_Ioc

@[simp]
theorem Icc_union_Ioc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : icc a b ∪ ioc b c = icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc
#align set.Icc_union_Ioc_eq_Icc Set.Icc_union_Ioc_eq_Icc

theorem Ioc_subset_Ioc_union_Ioc : ioc a c ⊆ ioc a b ∪ ioc b c := fun x hx =>
  (le_or_lt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩
#align set.Ioc_subset_Ioc_union_Ioc Set.Ioc_subset_Ioc_union_Ioc

@[simp]
theorem Ioc_union_Ioc_eq_Ioc (h₁ : a ≤ b) (h₂ : b ≤ c) : ioc a b ∪ ioc b c = ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc
#align set.Ioc_union_Ioc_eq_Ioc Set.Ioc_union_Ioc_eq_Ioc

theorem Ioc_union_Ioc' (h₁ : c ≤ b) (h₂ : a ≤ d) : ioc a b ∪ ioc c d = ioc (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioc, min_lt_iff, le_max_iff]
  by_cases hc : c < x <;> by_cases hd : x ≤ d
  · tauto
  · have hax : a < x := h₂.trans_lt (lt_of_not_ge hd)
    tauto
  · have hxb : x ≤ b := (le_of_not_gt hc).trans h₁
    tauto
  · tauto
#align set.Ioc_union_Ioc' Set.Ioc_union_Ioc'

theorem Ioc_union_Ioc (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    ioc a b ∪ ioc c d = ioc (min a c) (max b d) := by
  cases' le_total a b with hab hab <;> cases' le_total c d with hcd hcd <;> simp [hab, hcd] at h₁ h₂
  · exact Ioc_union_Ioc' h₂ h₁
  all_goals simp [*]
#align set.Ioc_union_Ioc Set.Ioc_union_Ioc

/-! #### Two finite intervals with a common point -/


theorem Ioo_subset_Ioc_union_Ico : ioo a c ⊆ ioc a b ∪ ico b c :=
  Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)
#align set.Ioo_subset_Ioc_union_Ico Set.Ioo_subset_Ioc_union_Ico

@[simp]
theorem Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : ioc a b ∪ ico b c = ioo a c :=
  Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico
#align set.Ioc_union_Ico_eq_Ioo Set.Ioc_union_Ico_eq_Ioo

theorem Ico_subset_Icc_union_Ico : ico a c ⊆ icc a b ∪ ico b c :=
  Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)
#align set.Ico_subset_Icc_union_Ico Set.Ico_subset_Icc_union_Ico

@[simp]
theorem Icc_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : icc a b ∪ ico b c = ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico
#align set.Icc_union_Ico_eq_Ico Set.Icc_union_Ico_eq_Ico

theorem Icc_subset_Icc_union_Icc : icc a c ⊆ icc a b ∪ icc b c :=
  Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)
#align set.Icc_subset_Icc_union_Icc Set.Icc_subset_Icc_union_Icc

@[simp]
theorem Icc_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : icc a b ∪ icc b c = icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc
#align set.Icc_union_Icc_eq_Icc Set.Icc_union_Icc_eq_Icc

theorem Icc_union_Icc' (h₁ : c ≤ b) (h₂ : a ≤ d) : icc a b ∪ icc c d = icc (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Icc, min_le_iff, le_max_iff]
  by_cases hc : c ≤ x <;> by_cases hd : x ≤ d
  · tauto
  · have hax : a ≤ x := h₂.trans (le_of_not_ge hd)
    tauto
  · have hxb : x ≤ b := (le_of_not_ge hc).trans h₁
    tauto
  · tauto
#align set.Icc_union_Icc' Set.Icc_union_Icc'

/-- We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
theorem Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    icc a b ∪ icc c d = icc (min a c) (max b d) := by
  cases' le_or_lt a b with hab hab <;> cases' le_or_lt c d with hcd hcd <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, min_eq_left_of_lt,
      min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt, hab, hcd] at h₁ h₂
  · exact Icc_union_Icc' h₂.le h₁.le
  all_goals simp [*, min_eq_left_of_lt, max_eq_left_of_lt, min_eq_right_of_lt, max_eq_right_of_lt]
#align set.Icc_union_Icc Set.Icc_union_Icc

theorem Ioc_subset_Ioc_union_Icc : ioc a c ⊆ ioc a b ∪ icc b c :=
  Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)
#align set.Ioc_subset_Ioc_union_Icc Set.Ioc_subset_Ioc_union_Icc

@[simp]
theorem Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : ioc a b ∪ icc b c = ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc
#align set.Ioc_union_Icc_eq_Ioc Set.Ioc_union_Icc_eq_Ioc

theorem Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : ioo a b ∪ ioo c d = ioo (min a c) (max b d) := by
  ext1 x
  simp_rw [mem_union, mem_Ioo, min_lt_iff, lt_max_iff]
  by_cases hc : c < x <;> by_cases hd : x < d
  · tauto
  · have hax : a < x := h₂.trans_le (le_of_not_lt hd)
    tauto
  · have hxb : x < b := (le_of_not_lt hc).trans_lt h₁
    tauto
  · tauto
#align set.Ioo_union_Ioo' Set.Ioo_union_Ioo'

theorem Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    ioo a b ∪ ioo c d = ioo (min a c) (max b d) := by
  cases' le_total a b with hab hab <;> cases' le_total c d with hcd hcd <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hcd] at h₁ h₂
  · exact Ioo_union_Ioo' h₂ h₁
  all_goals
    simp [*, min_eq_left_of_lt, min_eq_right_of_lt, max_eq_left_of_lt, max_eq_right_of_lt,
      le_of_lt h₂, le_of_lt h₁]
#align set.Ioo_union_Ioo Set.Ioo_union_Ioo

end LinearOrder

section Lattice

section Inf

variable [SemilatticeInf α]

@[simp]
theorem Iic_inter_Iic {a b : α} : iic a ∩ iic b = iic (a ⊓ b) := by
  ext x
  simp [iic]
#align set.Iic_inter_Iic Set.Iic_inter_Iic

@[simp]
theorem Ioc_inter_Iic (a b c : α) : ioc a b ∩ iic c = ioc a (b ⊓ c) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_assoc, Iic_inter_Iic]
#align set.Ioc_inter_Iic Set.Ioc_inter_Iic

end Inf

section Sup

variable [SemilatticeSup α]

@[simp]
theorem Ici_inter_Ici {a b : α} : ici a ∩ ici b = ici (a ⊔ b) := by
  ext x
  simp [ici]
#align set.Ici_inter_Ici Set.Ici_inter_Ici

@[simp]
theorem Ico_inter_Ici (a b c : α) : ico a b ∩ ici c = ico (a ⊔ c) b := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio, ← Ici_inter_Ici, inter_right_comm]
#align set.Ico_inter_Ici Set.Ico_inter_Ici

end Sup

section Both

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

theorem Icc_inter_Icc : icc a₁ b₁ ∩ icc a₂ b₂ = icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm] ; ac_rfl
#align set.Icc_inter_Icc Set.Icc_inter_Icc

@[simp]
theorem Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) : icc a b ∩ icc b c = {b} := by
  rw [Icc_inter_Icc, sup_of_le_right hab, inf_of_le_left hbc, Icc_self]
#align set.Icc_inter_Icc_eq_singleton Set.Icc_inter_Icc_eq_singleton

end Both

end Lattice

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β} {a a₁ a₂ b b₁ b₂ c d : α}

@[simp]
theorem Ioi_inter_Ioi : ioi a ∩ ioi b = ioi (a ⊔ b) :=
  ext fun _ => sup_lt_iff.symm
#align set.Ioi_inter_Ioi Set.Ioi_inter_Ioi

@[simp]
theorem Iio_inter_Iio : iio a ∩ iio b = iio (a ⊓ b) :=
  ext fun _ => lt_inf_iff.symm
#align set.Iio_inter_Iio Set.Iio_inter_Iio

theorem Ico_inter_Ico : ico a₁ b₁ ∩ ico a₂ b₂ = ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iio.symm, Ici_inter_Ici.symm, Iio_inter_Iio.symm] ; ac_rfl
#align set.Ico_inter_Ico Set.Ico_inter_Ico

theorem Ioc_inter_Ioc : ioc a₁ b₁ ∩ ioc a₂ b₂ = ioc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iic.symm, Ioi_inter_Ioi.symm, Iic_inter_Iic.symm] ; ac_rfl
#align set.Ioc_inter_Ioc Set.Ioc_inter_Ioc

theorem Ioo_inter_Ioo : ioo a₁ b₁ ∩ ioo a₂ b₂ = ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ioi_inter_Iio.symm, Ioi_inter_Ioi.symm, Iio_inter_Iio.symm] ; ac_rfl
#align set.Ioo_inter_Ioo Set.Ioo_inter_Ioo

theorem Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : ioc a₁ b₁ ∩ ioo a₂ b₂ = ioc (max a₁ a₂) b₁ :=
  ext fun x => by
    simp [and_assoc, @and_left_comm (x ≤ _), and_iff_left_iff_imp.2 fun h' => lt_of_le_of_lt h' h]
#align set.Ioc_inter_Ioo_of_left_lt Set.Ioc_inter_Ioo_of_left_lt

theorem Ioc_inter_Ioo_of_right_le (h : b₂ ≤ b₁) : ioc a₁ b₁ ∩ ioo a₂ b₂ = ioo (max a₁ a₂) b₂ :=
  ext fun x => by
    simp [and_assoc, @and_left_comm (x ≤ _),
      and_iff_right_iff_imp.2 fun h' => (le_of_lt h').trans h]
#align set.Ioc_inter_Ioo_of_right_le Set.Ioc_inter_Ioo_of_right_le

theorem Ioo_inter_Ioc_of_left_le (h : b₁ ≤ b₂) : ioo a₁ b₁ ∩ ioc a₂ b₂ = ioo (max a₁ a₂) b₁ := by
  rw [inter_comm, Ioc_inter_Ioo_of_right_le h, max_comm]
#align set.Ioo_inter_Ioc_of_left_le Set.Ioo_inter_Ioc_of_left_le

theorem Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : ioo a₁ b₁ ∩ ioc a₂ b₂ = ioc (max a₁ a₂) b₂ := by
  rw [inter_comm, Ioc_inter_Ioo_of_left_lt h, max_comm]
#align set.Ioo_inter_Ioc_of_right_lt Set.Ioo_inter_Ioc_of_right_lt

@[simp]
theorem Ico_diff_Iio : ico a b \ iio c = ico (max a c) b := by
  rw [diff_eq, compl_Iio, Ico_inter_Ici, sup_eq_max]
#align set.Ico_diff_Iio Set.Ico_diff_Iio

@[simp]
theorem Ioc_diff_Ioi : ioc a b \ ioi c = ioc a (min b c) :=
  ext <| by simp (config := { contextual := true }) [iff_def]
#align set.Ioc_diff_Ioi Set.Ioc_diff_Ioi

@[simp]
theorem Ioc_inter_Ioi : ioc a b ∩ ioi c = ioc (a ⊔ c) b := by
  rw [← Ioi_inter_Iic, inter_assoc, inter_comm, inter_assoc, Ioi_inter_Ioi, inter_comm,
    Ioi_inter_Iic, sup_comm]
#align set.Ioc_inter_Ioi Set.Ioc_inter_Ioi

@[simp]
theorem Ico_inter_Iio : ico a b ∩ iio c = ico a (min b c) :=
  ext <| by simp (config := { contextual := true }) [iff_def]
#align set.Ico_inter_Iio Set.Ico_inter_Iio

@[simp]
theorem Ioc_diff_Iic : ioc a b \ iic c = ioc (max a c) b := by
  rw [diff_eq, compl_Iic, Ioc_inter_Ioi, sup_eq_max]
#align set.Ioc_diff_Iic Set.Ioc_diff_Iic

@[simp]
theorem Ioc_union_Ioc_right : ioc a b ∪ ioc a c = ioc a (max b c) := by
  rw [Ioc_union_Ioc, min_self] <;> exact (min_le_left _ _).trans (le_max_left _ _)
#align set.Ioc_union_Ioc_right Set.Ioc_union_Ioc_right

@[simp]
theorem Ioc_union_Ioc_left : ioc a c ∪ ioc b c = ioc (min a b) c := by
  rw [Ioc_union_Ioc, max_self] <;> exact (min_le_right _ _).trans (le_max_right _ _)
#align set.Ioc_union_Ioc_left Set.Ioc_union_Ioc_left

@[simp]
theorem Ioc_union_Ioc_symm : ioc a b ∪ ioc b a = ioc (min a b) (max a b) := by
  rw [max_comm]
  apply Ioc_union_Ioc <;> rw [max_comm] <;> exact min_le_max
#align set.Ioc_union_Ioc_symm Set.Ioc_union_Ioc_symm

@[simp]
theorem Ioc_union_Ioc_union_Ioc_cycle :
    ioc a b ∪ ioc b c ∪ ioc c a = ioc (min a (min b c)) (max a (max b c)) := by
  rw [Ioc_union_Ioc, Ioc_union_Ioc]
  ac_rfl
  all_goals
    solve_by_elim (config := { max_depth := 5 }) [min_le_of_left_le, min_le_of_right_le,
      le_max_of_le_left, le_max_of_le_right, le_refl]
#align set.Ioc_union_Ioc_union_Ioc_cycle Set.Ioc_union_Ioc_union_Ioc_cycle

end LinearOrder

/-!
### Closed intervals in `α × β`
-/


section Prod

variable [Preorder α] [Preorder β]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Iic_prod_Iic (a : α) (b : β) : iic a ×ˢ iic b = iic (a, b) :=
  rfl
#align set.Iic_prod_Iic Set.Iic_prod_Iic

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : ici a ×ˢ ici b = ici (a, b) :=
  rfl
#align set.Ici_prod_Ici Set.Ici_prod_Ici

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Ici_prod_eq (a : α × β) : ici a = ici a.1 ×ˢ ici a.2 :=
  rfl
#align set.Ici_prod_eq Set.Ici_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Iic_prod_eq (a : α × β) : iic a = iic a.1 ×ˢ iic a.2 :=
  rfl
#align set.Iic_prod_eq Set.Iic_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : icc a₁ a₂ ×ˢ icc b₁ b₂ = icc (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_comm, and_left_comm]
#align set.Icc_prod_Icc Set.Icc_prod_Icc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Icc_prod_eq (a b : α × β) : icc a b = icc a.1 b.1 ×ˢ icc a.2 b.2 := by simp
#align set.Icc_prod_eq Set.Icc_prod_eq

end Prod

end Set

/-! ### Lemmas about intervals in dense orders -/


section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

instance : NoMinOrder (Set.ioo x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.ioc x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.le.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.ioi x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

instance : NoMaxOrder (Set.ioo x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.ico x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁.le, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.iio x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₂⟩, hb₁⟩⟩

end Dense
