/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Interval.Set.Defs

/-!
# Intervals

In any preorder, we define intervals (which on each side can be either infinite, open or closed)
using the following naming conventions:

- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.
The definitions can be found in `Mathlib/Order/Interval/Set/Defs.lean`.

This file contains basic facts on inclusion of and set operations on intervals
(where the precise statements depend on the order's properties;
statements requiring `LinearOrder` are in `Mathlib/Order/Interval/Set/LinearOrder.lean`).

A conscious decision was made not to list all possible inclusion relations.
Monotonicity results and "self" results *are* included.
Most use cases can suffice with a transitive combination of those, for example:
```
theorem Ico_subset_Ici (h : a₂ ≤ a₁) : Ico a₁ b₁ ⊆ Ici a₂ :=
  (Ico_subset_Ico_left h).trans Ico_subset_Ici_self
```
Logical equivalences, such as `Icc_subset_Ici_iff`, are however stated.
-/

assert_not_exists RelIso

open Function

open OrderDual (toDual ofDual)

variable {α : Type*}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

instance decidableMemIoo [Decidable (a < x ∧ x < b)] : Decidable (x ∈ Ioo a b) := by assumption

instance decidableMemIco [Decidable (a ≤ x ∧ x < b)] : Decidable (x ∈ Ico a b) := by assumption

instance decidableMemIio [Decidable (x < b)] : Decidable (x ∈ Iio b) := by assumption

instance decidableMemIcc [Decidable (a ≤ x ∧ x ≤ b)] : Decidable (x ∈ Icc a b) := by assumption

instance decidableMemIic [Decidable (x ≤ b)] : Decidable (x ∈ Iic b) := by assumption

instance decidableMemIoc [Decidable (a < x ∧ x ≤ b)] : Decidable (x ∈ Ioc a b) := by assumption

instance decidableMemIci [Decidable (a ≤ x)] : Decidable (x ∈ Ici a) := by assumption

instance decidableMemIoi [Decidable (a < x)] : Decidable (x ∈ Ioi a) := by assumption

theorem left_mem_Ioo : a ∈ Ioo a b ↔ False := by simp

theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp [le_refl]

theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp [le_refl]

theorem left_mem_Ioc : a ∈ Ioc a b ↔ False := by simp

theorem left_mem_Ici : a ∈ Ici a := by simp

theorem right_mem_Ioo : b ∈ Ioo a b ↔ False := by simp

theorem right_mem_Ico : b ∈ Ico a b ↔ False := by simp

theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp [le_refl]

theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp [le_refl]

theorem right_mem_Iic : a ∈ Iic a := by simp

@[simp]
theorem Ici_toDual : Ici (toDual a) = ofDual ⁻¹' Iic a :=
  rfl

@[deprecated (since := "2025-03-20")]
alias dual_Ici := Ici_toDual

@[simp]
theorem Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a :=
  rfl

@[deprecated (since := "2025-03-20")]
alias dual_Iic := Iic_toDual

@[simp]
theorem Ioi_toDual : Ioi (toDual a) = ofDual ⁻¹' Iio a :=
  rfl

@[deprecated (since := "2025-03-20")]
alias dual_Ioi := Ioi_toDual

@[simp]
theorem Iio_toDual : Iio (toDual a) = ofDual ⁻¹' Ioi a :=
  rfl

@[deprecated (since := "2025-03-20")]
alias dual_Iio := Iio_toDual

@[simp]
theorem Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a :=
  Set.ext fun _ => and_comm

@[deprecated (since := "2025-03-20")]
alias dual_Icc := Icc_toDual

@[simp]
theorem Ioc_toDual : Ioc (toDual a) (toDual b) = ofDual ⁻¹' Ico b a :=
  Set.ext fun _ => and_comm

@[deprecated (since := "2025-03-20")]
alias dual_Ioc := Ioc_toDual

@[simp]
theorem Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a :=
  Set.ext fun _ => and_comm

@[deprecated (since := "2025-03-20")]
alias dual_Ico := Ico_toDual

@[simp]
theorem Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a :=
  Set.ext fun _ => and_comm

@[deprecated (since := "2025-03-20")]
alias dual_Ioo := Ioo_toDual

@[simp]
theorem Ici_ofDual {x : αᵒᵈ} : Ici (ofDual x) = toDual ⁻¹' Iic x :=
  rfl

@[simp]
theorem Iic_ofDual {x : αᵒᵈ} : Iic (ofDual x) = toDual ⁻¹' Ici x :=
  rfl

@[simp]
theorem Ioi_ofDual {x : αᵒᵈ} : Ioi (ofDual x) = toDual ⁻¹' Iio x :=
  rfl

@[simp]
theorem Iio_ofDual {x : αᵒᵈ} : Iio (ofDual x) = toDual ⁻¹' Ioi x :=
  rfl

@[simp]
theorem Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y :=
  Set.ext fun _ => and_comm

@[simp]
theorem Ico_ofDual {x y : αᵒᵈ} : Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y :=
  Set.ext fun _ => and_comm

@[simp]
theorem Ioc_ofDual {x y : αᵒᵈ} : Ioc (ofDual y) (ofDual x) = toDual ⁻¹' Ico x y :=
  Set.ext fun _ => and_comm

@[simp]
theorem Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y :=
  Set.ext fun _ => and_comm

@[simp]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[simp]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩

@[simp]
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_le hx.2, fun h => ⟨b, right_mem_Ioc.2 h⟩⟩

@[simp]
theorem nonempty_Ici : (Ici a).Nonempty :=
  ⟨a, left_mem_Ici⟩

@[simp]
theorem nonempty_Iic : (Iic a).Nonempty :=
  ⟨a, right_mem_Iic⟩

@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

@[simp]
theorem nonempty_Ioi [NoMaxOrder α] : (Ioi a).Nonempty :=
  exists_gt a

@[simp]
theorem nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty :=
  exists_lt a

theorem nonempty_Icc_subtype (h : a ≤ b) : Nonempty (Icc a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)

theorem nonempty_Ico_subtype (h : a < b) : Nonempty (Ico a b) :=
  Nonempty.to_subtype (nonempty_Ico.mpr h)

theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (Ioc a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)

/-- An interval `Ici a` is nonempty. -/
instance nonempty_Ici_subtype : Nonempty (Ici a) :=
  Nonempty.to_subtype nonempty_Ici

/-- An interval `Iic a` is nonempty. -/
instance nonempty_Iic_subtype : Nonempty (Iic a) :=
  Nonempty.to_subtype nonempty_Iic

theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (Ioo a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)

/-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/
instance nonempty_Ioi_subtype [NoMaxOrder α] : Nonempty (Ioi a) :=
  Nonempty.to_subtype nonempty_Ioi

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (Iio a) :=
  Nonempty.to_subtype nonempty_Iio

instance [NoMinOrder α] : NoMinOrder (Iio a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

instance [NoMinOrder α] : NoMinOrder (Iic a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

instance [NoMaxOrder α] : NoMaxOrder (Ioi a) :=
  OrderDual.noMaxOrder (α := Iio (toDual a))

instance [NoMaxOrder α] : NoMaxOrder (Ici a) :=
  OrderDual.noMaxOrder (α := Iic (toDual a))

@[simp]
theorem Icc_eq_empty (h : ¬a ≤ b) : Icc a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp]
theorem Ico_eq_empty (h : ¬a < b) : Ico a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans_lt hb)

@[simp]
theorem Ioc_eq_empty (h : ¬a < b) : Ioc a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans_le hb)

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_gt

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

theorem Ico_self (a : α) : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _

theorem Ioc_self (a : α) : Ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _

theorem Ioo_self (a : α) : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

@[simp]
theorem Ici_subset_Ici : Ici a ⊆ Ici b ↔ b ≤ a :=
  ⟨fun h => h <| left_mem_Ici, fun h _ hx => h.trans hx⟩

@[gcongr] alias ⟨_, _root_.GCongr.Ici_subset_Ici_of_le⟩ := Ici_subset_Ici

@[simp]
theorem Ici_ssubset_Ici : Ici a ⊂ Ici b ↔ b < a where
  mp h := by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Ici_subset_Ici.mp ab) (fun h' ↦ ac (h'.trans cb))
  mpr h := (ssubset_iff_of_subset (Ici_subset_Ici.mpr h.le)).mpr
    ⟨b, right_mem_Iic, fun h' => h.not_ge h'⟩

@[gcongr] alias ⟨_, _root_.GCongr.Ici_ssubset_Ici_of_le⟩ := Ici_ssubset_Ici

@[simp]
theorem Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b :=
  @Ici_subset_Ici αᵒᵈ _ _ _

@[gcongr] alias ⟨_, _root_.GCongr.Iic_subset_Iic_of_le⟩ := Iic_subset_Iic

@[simp]
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b :=
  @Ici_ssubset_Ici αᵒᵈ _ _ _

@[gcongr] alias ⟨_, _root_.GCongr.Iic_ssubset_Iic_of_le⟩ := Iic_ssubset_Iic

@[simp]
theorem Ici_subset_Ioi : Ici a ⊆ Ioi b ↔ b < a :=
  ⟨fun h => h left_mem_Ici, fun h _ hx => h.trans_le hx⟩

@[simp]
theorem Iic_subset_Iio : Iic a ⊆ Iio b ↔ a < b :=
  ⟨fun h => h right_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[gcongr]
theorem Ioo_subset_Ioo (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans_le h₂⟩

theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h

@[gcongr]
theorem Ico_subset_Ico (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, hx₂.trans_le h₂⟩

theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl

theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
  Ico_subset_Ico le_rfl h

@[gcongr]
theorem Icc_subset_Icc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans hx₁, le_trans hx₂ h₂⟩

theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl

theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
  Icc_subset_Icc le_rfl h

theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ hx =>
  ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩

theorem Icc_subset_Ici_self : Icc a b ⊆ Ici a := fun _ => And.left

theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := fun _ => And.right

theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := fun _ => And.right

@[gcongr]
theorem Ioc_subset_Ioc (h₁ : a₂ ≤ a₁) (h₂ : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨h₁.trans_lt hx₁, hx₂.trans h₂⟩

theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h

theorem Ico_subset_Ioo_left (h₁ : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b := fun _ =>
  And.imp_left h₁.trans_le

theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ := fun _ =>
  And.imp_right fun h' => h'.trans_lt h

theorem Icc_subset_Ico_right (h₁ : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ := fun _ =>
  And.imp_right fun h₂ => h₂.trans_lt h₁

theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := fun _ => And.imp_left le_of_lt

theorem Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b := fun _ => And.imp_right le_of_lt

theorem Ico_subset_Icc_self : Ico a b ⊆ Icc a b := fun _ => And.imp_right le_of_lt

theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := fun _ => And.imp_left le_of_lt

theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Subset.trans Ioo_subset_Ico_self Ico_subset_Icc_self

theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := fun _ => And.right

theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := fun _ => And.right

theorem Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := fun _ => And.left

theorem Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := fun _ => And.left

theorem Ioi_subset_Ici_self : Ioi a ⊆ Ici a := fun _ hx => le_of_lt hx

theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := fun _ hx => le_of_lt hx

theorem Ico_subset_Ici_self : Ico a b ⊆ Ici a := fun _ => And.left

theorem Ioi_ssubset_Ici_self : Ioi a ⊂ Ici a :=
  ⟨Ioi_subset_Ici_self, fun h => lt_irrefl a (h le_rfl)⟩

theorem Iio_ssubset_Iic_self : Iio a ⊂ Iic a :=
  @Ioi_ssubset_Ici_self αᵒᵈ _ _

theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans hx, hx'.trans h'⟩⟩

theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans_le hx, hx'.trans_lt h'⟩⟩

theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans hx, hx'.trans_lt h'⟩⟩

theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ ⟨hx, hx'⟩ =>
    ⟨h.trans_le hx, hx'.trans h'⟩⟩

theorem Icc_subset_Iio_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Iio b₂ ↔ b₁ < b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h _ ⟨_, hx'⟩ => hx'.trans_lt h⟩

theorem Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ ⟨hx, _⟩ => h.trans_le hx⟩

theorem Icc_subset_Iic_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Iic b₂ ↔ b₁ ≤ b₂ :=
  ⟨fun h => h ⟨h₁, le_rfl⟩, fun h _ ⟨_, hx'⟩ => hx'.trans h⟩

theorem Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ ⟨hx, _⟩ => h.trans hx⟩

theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr hI, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc ha (le_of_lt hb))).mpr
    ⟨b₂, right_mem_Icc.mpr hI, fun f => lt_irrefl b₁ (hb.trans_le f.2)⟩

/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/
@[gcongr]
theorem Ioi_subset_Ioi (h : a ≤ b) : Ioi b ⊆ Ioi a := fun _ hx => h.trans_lt hx

/-- If `a < b`, then `(b, +∞) ⊂ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_ssubset_Ioi_iff`. -/
@[gcongr]
theorem Ioi_ssubset_Ioi (h : a < b) : Ioi b ⊂ Ioi a :=
  (ssubset_iff_of_subset (Ioi_subset_Ioi h.le)).mpr ⟨b, h, lt_irrefl b⟩

/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/
theorem Ioi_subset_Ici (h : a ≤ b) : Ioi b ⊆ Ici a :=
  Subset.trans (Ioi_subset_Ioi h) Ioi_subset_Ici_self

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
@[gcongr]
theorem Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b := fun _ hx => lt_of_lt_of_le hx h

/-- If `a < b`, then `(-∞, a) ⊂ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_ssubset_Iio_iff`. -/
@[gcongr]
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b :=
  (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
theorem Iio_subset_Iic (h : a ≤ b) : Iio a ⊆ Iic b :=
  Subset.trans (Iio_subset_Iio h) Iio_subset_Iic_self

theorem Ici_inter_Iic : Ici a ∩ Iic b = Icc a b :=
  rfl

theorem Ici_inter_Iio : Ici a ∩ Iio b = Ico a b :=
  rfl

theorem Ioi_inter_Iic : Ioi a ∩ Iic b = Ioc a b :=
  rfl

theorem Ioi_inter_Iio : Ioi a ∩ Iio b = Ioo a b :=
  rfl

theorem Iic_inter_Ici : Iic a ∩ Ici b = Icc b a :=
  inter_comm _ _

theorem Iio_inter_Ici : Iio a ∩ Ici b = Ico b a :=
  inter_comm _ _

theorem Iic_inter_Ioi : Iic a ∩ Ioi b = Ioc b a :=
  inter_comm _ _

theorem Iio_inter_Ioi : Iio a ∩ Ioi b = Ioo b a :=
  inter_comm _ _

theorem mem_Icc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Icc a b :=
  Ioo_subset_Icc_self h

theorem mem_Ico_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ico a b :=
  Ioo_subset_Ico_self h

theorem mem_Ioc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ioc a b :=
  Ioo_subset_Ioc_self h

theorem mem_Icc_of_Ico (h : x ∈ Ico a b) : x ∈ Icc a b :=
  Ico_subset_Icc_self h

theorem mem_Icc_of_Ioc (h : x ∈ Ioc a b) : x ∈ Icc a b :=
  Ioc_subset_Icc_self h

theorem mem_Ici_of_Ioi (h : x ∈ Ioi a) : x ∈ Ici a :=
  Ioi_subset_Ici_self h

theorem mem_Iic_of_Iio (h : x ∈ Iio a) : x ∈ Iic a :=
  Iio_subset_Iic_self h

theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Icc]

theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ico]

theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioc]

theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← not_nonempty_iff_eq_empty, not_iff_not, nonempty_Ioo]

theorem _root_.IsTop.Iic_eq (h : IsTop a) : Iic a = univ :=
  eq_univ_of_forall h

theorem _root_.IsBot.Ici_eq (h : IsBot a) : Ici a = univ :=
  eq_univ_of_forall h

@[simp] theorem Ioi_eq_empty_iff : Ioi a = ∅ ↔ IsMax a := by
  simp only [isMax_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Ioi]

@[simp] theorem Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a := Ioi_eq_empty_iff (α := αᵒᵈ)

@[simp] alias ⟨_, _root_.IsMax.Ioi_eq⟩ := Ioi_eq_empty_iff
@[simp] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[simp] lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [nonempty_iff_ne_empty]
@[simp] lemma Ioi_nonempty : (Ioi a).Nonempty ↔ ¬ IsMax a := by simp [nonempty_iff_ne_empty]

theorem Iic_inter_Ioc_of_le (h : a ≤ c) : Iic a ∩ Ioc b c = Ioc b a :=
  ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

theorem notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b := fun h => ha.not_ge h.1

@[deprecated (since := "2025-05-23")] alias not_mem_Icc_of_lt := notMem_Icc_of_lt

theorem notMem_Icc_of_gt (hb : b < c) : c ∉ Icc a b := fun h => hb.not_ge h.2

@[deprecated (since := "2025-05-23")] alias not_mem_Icc_of_gt := notMem_Icc_of_gt

theorem notMem_Ico_of_lt (ha : c < a) : c ∉ Ico a b := fun h => ha.not_ge h.1

@[deprecated (since := "2025-05-23")] alias not_mem_Ico_of_lt := notMem_Ico_of_lt

theorem notMem_Ioc_of_gt (hb : b < c) : c ∉ Ioc a b := fun h => hb.not_ge h.2

@[deprecated (since := "2025-05-23")] alias not_mem_Ioc_of_gt := notMem_Ioc_of_gt

theorem notMem_Ioi_self : a ∉ Ioi a := lt_irrefl _

@[deprecated (since := "2025-05-23")] alias not_mem_Ioi_self := notMem_Ioi_self

theorem notMem_Iio_self : b ∉ Iio b := lt_irrefl _

@[deprecated (since := "2025-05-23")] alias not_mem_Iio_self := notMem_Iio_self

theorem notMem_Ioc_of_le (ha : c ≤ a) : c ∉ Ioc a b := fun h => lt_irrefl _ <| h.1.trans_le ha

@[deprecated (since := "2025-05-23")] alias not_mem_Ioc_of_le := notMem_Ioc_of_le

theorem notMem_Ico_of_ge (hb : b ≤ c) : c ∉ Ico a b := fun h => lt_irrefl _ <| h.2.trans_le hb

@[deprecated (since := "2025-05-23")] alias not_mem_Ico_of_ge := notMem_Ico_of_ge

theorem notMem_Ioo_of_le (ha : c ≤ a) : c ∉ Ioo a b := fun h => lt_irrefl _ <| h.1.trans_le ha

@[deprecated (since := "2025-05-23")] alias not_mem_Ioo_of_le := notMem_Ioo_of_le

theorem notMem_Ioo_of_ge (hb : b ≤ c) : c ∉ Ioo a b := fun h => lt_irrefl _ <| h.2.trans_le hb

@[deprecated (since := "2025-05-23")] alias not_mem_Ioo_of_ge := notMem_Ioo_of_ge

section matched_intervals

@[simp] theorem Icc_eq_Ioc_same_iff : Icc a b = Ioc a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]

@[simp] theorem Icc_eq_Ico_same_iff : Icc a b = Ico a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ico_eq_empty (mt le_of_lt h)]

@[simp] theorem Icc_eq_Ioo_same_iff : Icc a b = Ioo a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]

@[simp] theorem Ioc_eq_Ico_same_iff : Ioc a b = Ico a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]

@[simp] theorem Ioo_eq_Ioc_same_iff : Ioo a b = Ioc a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]

@[simp] theorem Ioo_eq_Ico_same_iff : Ioo a b = Ico a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioo_eq_empty h, Ico_eq_empty h]

-- Mirrored versions of the above for `simp`.

@[simp] theorem Ioc_eq_Icc_same_iff : Ioc a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioc_same_iff

@[simp] theorem Ico_eq_Icc_same_iff : Ico a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ico_same_iff

@[simp] theorem Ioo_eq_Icc_same_iff : Ioo a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioo_same_iff

@[simp] theorem Ico_eq_Ioc_same_iff : Ico a b = Ioc a b ↔ ¬a < b :=
  eq_comm.trans Ioc_eq_Ico_same_iff

@[simp] theorem Ioc_eq_Ioo_same_iff : Ioc a b = Ioo a b ↔ ¬a < b :=
  eq_comm.trans Ioo_eq_Ioc_same_iff

@[simp] theorem Ico_eq_Ioo_same_iff : Ico a b = Ioo a b ↔ ¬a < b :=
  eq_comm.trans Ioo_eq_Ico_same_iff

end matched_intervals

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} :=
  Set.ext <| by simp [Icc, le_antisymm_iff, and_comm]

instance instIccUnique : Unique (Set.Icc a a) where
  default := ⟨a, by simp⟩
  uniq y := Subtype.ext <| by simpa using y.2

@[simp]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
      ⟨eq_of_mem_singleton <| h ▸ left_mem_Icc.2 hab,
        eq_of_mem_singleton <| h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

lemma subsingleton_Icc_of_ge (hba : b ≤ a) : Set.Subsingleton (Icc a b) :=
  fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ ↦ le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp] lemma subsingleton_Icc_iff {α : Type*} [LinearOrder α] {a b : α} :
    Set.Subsingleton (Icc a b) ↔ b ≤ a := by
  refine ⟨fun h ↦ ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  simp only [not_subsingleton_iff]
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[simp]
theorem Icc_diff_left : Icc a b \ {a} = Ioc a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[simp]
theorem Icc_diff_right : Icc a b \ {b} = Ico a b :=
  ext fun x => by simp [lt_iff_le_and_ne, and_assoc]

@[simp]
theorem Ico_diff_left : Ico a b \ {a} = Ioo a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[simp]
theorem Ioc_diff_right : Ioc a b \ {b} = Ioo a b :=
  ext fun x => by simp [and_assoc, ← lt_iff_le_and_ne]

@[simp]
theorem Icc_diff_both : Icc a b \ {a, b} = Ioo a b := by
  rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]

@[simp]
theorem Ici_diff_left : Ici a \ {a} = Ioi a :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm]

@[simp]
theorem Iic_diff_right : Iic a \ {a} = Iio a :=
  ext fun x => by simp [lt_iff_le_and_ne]

@[simp]
theorem Ico_diff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} := by
  rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[simp]
theorem Ioc_diff_Ioo_same (h : a < b) : Ioc a b \ Ioo a b = {b} := by
  rw [← Ioc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Ioc.2 h)]

@[simp]
theorem Icc_diff_Ico_same (h : a ≤ b) : Icc a b \ Ico a b = {b} := by
  rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[simp]
theorem Icc_diff_Ioc_same (h : a ≤ b) : Icc a b \ Ioc a b = {a} := by
  rw [← Icc_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Icc.2 h)]

@[simp]
theorem Icc_diff_Ioo_same (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by
  rw [← Icc_diff_both, diff_diff_cancel_left]
  simp [insert_subset_iff, h]

@[simp]
theorem Ici_diff_Ioi_same : Ici a \ Ioi a = {a} := by
  rw [← Ici_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 left_mem_Ici)]

@[simp]
theorem Iic_diff_Iio_same : Iic a \ Iio a = {a} := by
  rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 right_mem_Iic)]

theorem Ioi_union_left : Ioi a ∪ {a} = Ici a :=
  ext fun x => by simp [eq_comm, le_iff_eq_or_lt]

theorem Iio_union_right : Iio a ∪ {a} = Iic a :=
  ext fun _ => le_iff_lt_or_eq.symm

theorem Ioo_union_left (hab : a < b) : Ioo a b ∪ {a} = Ico a b := by
  rw [← Ico_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

theorem Ioo_union_right (hab : a < b) : Ioo a b ∪ {b} = Ioc a b := by
  simpa only [Ioo_toDual, Ico_toDual] using Ioo_union_left hab.dual

theorem Ioo_union_both (h : a ≤ b) : Ioo a b ∪ {a, b} = Icc a b := by
  have : (Icc a b \ {a, b}) ∪ {a, b} = Icc a b := diff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this, Icc_diff_both]

theorem Ioc_union_left (hab : a ≤ b) : Ioc a b ∪ {a} = Icc a b := by
  rw [← Icc_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

theorem Ico_union_right (hab : a ≤ b) : Ico a b ∪ {b} = Icc a b := by
  simpa only [Ioc_toDual, Icc_toDual] using Ioc_union_left hab.dual

@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [insert_eq, union_comm, Ico_union_right h]

@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b := by
  rw [insert_eq, union_comm, Ioc_union_left h]

@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [insert_eq, union_comm, Ioo_union_left h]

@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b := by
  rw [insert_eq, union_comm, Ioo_union_right h]

@[simp]
theorem Iio_insert : insert a (Iio a) = Iic a :=
  ext fun _ => le_iff_eq_or_lt.symm

@[simp]
theorem Ioi_insert : insert a (Ioi a) = Ici a :=
  ext fun _ => (or_congr_left eq_comm).trans le_iff_eq_or_lt.symm

theorem mem_Ici_Ioi_of_subset_of_subset {s : Set α} (ho : Ioi a ⊆ s) (hc : s ⊆ Ici a) :
    s ∈ ({Ici a, Ioi a} : Set (Set α)) :=
  by_cases
    (fun h : a ∈ s =>
      Or.inl <| Subset.antisymm hc <| by rw [← Ioi_union_left, union_subset_iff]; simp [*])
    fun h =>
    Or.inr <| Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho

theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) :
    s ∈ ({Iic a, Iio a} : Set (Set α)) :=
  @mem_Ici_Ioi_of_subset_of_subset αᵒᵈ _ a s ho hc

theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : Ioo a b ⊆ s) (hc : s ⊆ Icc a b) :
    s ∈ ({Icc a b, Ico a b, Ioc a b, Ioo a b} : Set (Set α)) := by
  classical
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · refine Or.inl (Subset.antisymm hc ?_)
      rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_diff_right,
        diff_singleton_subset_iff, insert_eq_of_mem hb] at ho
    · refine Or.inr <| Or.inl <| Subset.antisymm ?_ ?_
      · rw [← Icc_diff_right]
        exact subset_diff_singleton hc hb
      · rwa [← Ico_diff_left, diff_singleton_subset_iff, insert_eq_of_mem ha] at ho
    · refine Or.inr <| Or.inr <| Or.inl <| Subset.antisymm ?_ ?_
      · rw [← Icc_diff_left]
        exact subset_diff_singleton hc ha
      · rwa [← Ioc_diff_right, diff_singleton_subset_iff, insert_eq_of_mem hb] at ho
    · refine Or.inr <| Or.inr <| Or.inr <| Subset.antisymm ?_ ho
      rw [← Ico_diff_left, ← Icc_diff_right]
      apply_rules [subset_diff_singleton]

theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x ∈ Ico a b) : x = a ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

theorem eq_right_or_mem_Ioo_of_mem_Ioc {x : α} (hmem : x ∈ Ioc a b) : x = b ∨ x ∈ Ioo a b :=
  hmem.2.eq_or_lt.imp_right <| And.intro hmem.1

theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x ∈ Icc a b) :
    x = a ∨ x = b ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

theorem _root_.IsMax.Ici_eq (h : IsMax a) : Ici a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨left_mem_Ici, fun _ => h.eq_of_ge⟩

theorem _root_.IsMin.Iic_eq (h : IsMin a) : Iic a = {a} :=
  h.toDual.Ici_eq

theorem Ici_injective : Injective (Ici : α → Set α) := fun _ _ =>
  eq_of_forall_ge_iff ∘ Set.ext_iff.1

theorem Iic_injective : Injective (Iic : α → Set α) := fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

theorem Ici_inj : Ici a = Ici b ↔ a = b :=
  Ici_injective.eq_iff

theorem Iic_inj : Iic a = Iic b ↔ a = b :=
  Iic_injective.eq_iff

@[simp]
theorem Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) : Icc a b ∩ Icc b c = {b} := by
  rw [← Ici_inter_Iic, ← Iic_inter_Ici, inter_inter_inter_comm, Iic_inter_Ici]
  simp [hab, hbc]

lemma Icc_eq_Icc_iff {d : α} (h : a ≤ b) :
    Icc a b = Icc c d ↔ a = c ∧ b = d := by
  refine ⟨fun heq ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h' : c ≤ d := by
    by_contra contra; rw [Icc_eq_empty_iff.mpr contra, Icc_eq_empty_iff] at heq; contradiction
  simp only [Set.ext_iff, mem_Icc] at heq
  obtain ⟨-, h₁⟩ := (heq b).mp ⟨h, le_refl _⟩
  obtain ⟨h₂, -⟩ := (heq a).mp ⟨le_refl _, h⟩
  obtain ⟨h₃, -⟩ := (heq c).mpr ⟨le_refl _, h'⟩
  obtain ⟨-, h₄⟩ := (heq d).mpr ⟨h', le_refl _⟩
  exact ⟨le_antisymm h₃ h₂, le_antisymm h₁ h₄⟩

end PartialOrder

section OrderTop

@[simp]
theorem Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤} :=
  isMax_top.Ici_eq

variable [Preorder α] [OrderTop α] {a : α}

theorem Ioi_top : Ioi (⊤ : α) = ∅ :=
  isMax_top.Ioi_eq

@[simp]
theorem Iic_top : Iic (⊤ : α) = univ :=
  isTop_top.Iic_eq

@[simp]
theorem Icc_top : Icc a ⊤ = Ici a := by simp [← Ici_inter_Iic]

@[simp]
theorem Ioc_top : Ioc a ⊤ = Ioi a := by simp [← Ioi_inter_Iic]

end OrderTop

section OrderBot

@[simp]
theorem Iic_bot [PartialOrder α] [OrderBot α] : Iic (⊥ : α) = {⊥} :=
  isMin_bot.Iic_eq

variable [Preorder α] [OrderBot α] {a : α}

theorem Iio_bot : Iio (⊥ : α) = ∅ :=
  isMin_bot.Iio_eq

@[simp]
theorem Ici_bot : Ici (⊥ : α) = univ :=
  isBot_bot.Ici_eq

@[simp]
theorem Icc_bot : Icc ⊥ a = Iic a := by simp [← Ici_inter_Iic]

@[simp]
theorem Ico_bot : Ico ⊥ a = Iio a := by simp [← Ici_inter_Iio]

end OrderBot

theorem Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α) ⊤ = univ := by simp

section Lattice

section Inf

variable [SemilatticeInf α]

@[simp]
theorem Iic_inter_Iic {a b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) := by
  ext x
  simp [Iic]

@[simp]
theorem Ioc_inter_Iic (a b c : α) : Ioc a b ∩ Iic c = Ioc a (b ⊓ c) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_assoc, Iic_inter_Iic]

end Inf

section Sup

variable [SemilatticeSup α]

@[simp]
theorem Ici_inter_Ici {a b : α} : Ici a ∩ Ici b = Ici (a ⊔ b) := by
  ext x
  simp [Ici]

@[simp]
theorem Ico_inter_Ici (a b c : α) : Ico a b ∩ Ici c = Ico (a ⊔ c) b := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio, ← Ici_inter_Ici, inter_right_comm]

end Sup

section Both

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

theorem Icc_inter_Icc : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

end Both

end Lattice

/-! ### Closed intervals in `α × β` -/

section Prod

variable {β : Type*} [Preorder α] [Preorder β]

@[simp]
theorem Iic_prod_Iic (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl

theorem Ici_prod_eq (a : α × β) : Ici a = Ici a.1 ×ˢ Ici a.2 :=
  rfl

theorem Iic_prod_eq (a : α × β) : Iic a = Iic a.1 ×ˢ Iic a.2 :=
  rfl

@[simp]
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

theorem Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2 := by simp

end Prod

end Set

/-! ### Lemmas about intervals in dense orders -/

section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

instance : NoMinOrder (Set.Ioo x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.Ioc x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₁ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁, hb₂.le.trans ha₂⟩, hb₂⟩⟩

instance : NoMinOrder (Set.Ioi x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

instance : NoMaxOrder (Set.Ioo x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.Ico x y) :=
  ⟨fun ⟨a, ha₁, ha₂⟩ => by
    rcases exists_between ha₂ with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, ha₁.trans hb₁.le, hb₂⟩, hb₁⟩⟩

instance : NoMaxOrder (Set.Iio x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₂⟩, hb₁⟩⟩

end Dense

/-! ### Intervals in `Prop` -/

namespace Set

@[simp] lemma Iic_False : Iic False = {False} := by aesop
@[simp] lemma Iic_True : Iic True = univ := by aesop
@[simp] lemma Ici_False : Ici False = univ := by aesop
@[simp] lemma Ici_True : Ici True = {True} := by aesop
lemma Iio_False : Iio False = ∅ := by aesop
@[simp] lemma Iio_True : Iio True = {False} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
@[simp] lemma Ioi_False : Ioi False = {True} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
lemma Ioi_True : Ioi True = ∅ := by aesop

end Set
