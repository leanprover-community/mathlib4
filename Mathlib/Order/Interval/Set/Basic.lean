/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Interval.Set.Defs

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

@[expose] public section

assert_not_exists RelIso

open Function

open OrderDual (toDual ofDual)

variable {α : Type*}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[to_dual]
instance decidableMemIio [Decidable (x < b)] : Decidable (x ∈ Iio b) := by assumption

@[to_dual]
instance decidableMemIic [Decidable (x ≤ b)] : Decidable (x ∈ Iic b) := by assumption

@[to_dual self (reorder := a b, 6 7)]
instance decidableMemIoo [Decidable (a < x)] [Decidable (x < b)] : Decidable (x ∈ Ioo a b) :=
  instDecidableAnd

instance decidableMemIco [Decidable (a ≤ x)] [Decidable (x < b)] : Decidable (x ∈ Ico a b) :=
  instDecidableAnd

@[to_dual self (reorder := a b, 6 7)]
instance decidableMemIcc [Decidable (a ≤ x)] [Decidable (x ≤ b)] : Decidable (x ∈ Icc a b) :=
  instDecidableAnd

@[to_dual existing (reorder := a b, 6 7)]
instance decidableMemIoc [Decidable (a < x)] [Decidable (x ≤ b)] : Decidable (x ∈ Ioc a b) :=
  instDecidableAnd

@[to_dual] theorem self_notMem_Iio : a ∉ Iio a := by simp
@[to_dual] theorem self_mem_Iic : a ∈ Iic a := by simp

@[to_dual right_notMem_Ioo]
theorem left_notMem_Ioo : a ∉ Ioo a b := by simp

@[to_dual right_notMem_Ico]
theorem left_notMem_Ioc : a ∉ Ioc a b := by simp

@[deprecated left_notMem_Ioo (since := "2025-12-26")]
theorem left_mem_Ioo : a ∈ Ioo a b ↔ False := by simp

@[deprecated left_notMem_Ioc (since := "2025-12-26")]
theorem left_mem_Ioc : a ∈ Ioc a b ↔ False := by simp

@[to_dual right_mem_Ioc] theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp
@[to_dual right_mem_Icc] theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp

@[deprecated (since := "2025-12-26")]
alias left_mem_Ici := self_mem_Ici

@[deprecated right_notMem_Ioo (since := "2025-12-26")]
theorem right_mem_Ioo : b ∈ Ioo a b ↔ False := by simp

@[deprecated right_notMem_Ico (since := "2025-12-26")]
theorem right_mem_Ico : b ∈ Ico a b ↔ False := by simp

@[deprecated (since := "2025-12-26")]
alias right_mem_Iic := self_mem_Iic

@[to_dual (attr := simp)]
theorem Iio_toDual : Iio (toDual a) = ofDual ⁻¹' Ioi a :=
  rfl

@[to_dual (attr := simp)]
theorem Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a :=
  rfl

@[simp, to_dual self]
theorem Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
theorem Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
theorem Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
theorem Iio_ofDual {x : αᵒᵈ} : Iio (ofDual x) = toDual ⁻¹' Ioi x :=
  rfl

@[to_dual (attr := simp)]
theorem Iic_ofDual {x : αᵒᵈ} : Iic (ofDual x) = toDual ⁻¹' Ici x :=
  rfl

@[simp, to_dual self]
theorem Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
theorem Ico_ofDual {x y : αᵒᵈ} : Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
theorem Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
theorem nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty :=
  exists_lt a

@[to_dual (attr := simp)]
theorem nonempty_Iic : (Iic a).Nonempty :=
  ⟨a, self_mem_Iic⟩

@[simp, to_dual self]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[to_dual (attr := simp)]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩


@[simp, to_dual self]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
@[to_dual /-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/]
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (Iio a) :=
  Nonempty.to_subtype nonempty_Iio

/-- An interval `Iic a` is nonempty. -/
@[to_dual /-- An interval `Ici a` is nonempty. -/]
instance nonempty_Iic_subtype : Nonempty (Iic a) :=
  Nonempty.to_subtype nonempty_Iic

@[to_dual self]
theorem nonempty_Icc_subtype (h : a ≤ b) : Nonempty (Icc a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)

@[to_dual]
theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (Ioc a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)

@[to_dual self]
theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (Ioo a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)

@[to_dual]
instance [NoMinOrder α] : NoMinOrder (Iio a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

@[to_dual]
instance [NoMinOrder α] : NoMinOrder (Iic a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

@[simp, to_dual self]
theorem Icc_eq_empty (h : ¬a ≤ b) : Icc a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[to_dual (attr := simp)]
theorem Ico_eq_empty (h : ¬a < b) : Ico a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hab => h (hab.1.trans_lt hab.2)

@[simp, to_dual self]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp, to_dual self]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[to_dual (attr := simp)]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp, to_dual self]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

@[to_dual]
theorem Ico_self (a : α) : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _

theorem Ioo_self (a : α) : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/]
theorem Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b := fun _ hx => lt_of_lt_of_le hx h

/-- If `a < b`, then `(-∞, a) ⊂ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_ssubset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a < b`, then `(b, +∞) ⊂ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_ssubset_Ioi_iff`. -/]
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b :=
  (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

@[to_dual (attr := simp, gcongr)]
theorem Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b :=
  ⟨fun h => h self_mem_Ici, fun h _ hx ↦ hx.trans h⟩

@[to_dual (attr := simp, gcongr)]
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b where
  mp h := by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Iic_subset_Iic.mp ab) (fun h' ↦ ac (cb.trans h'))
  mpr h := (ssubset_iff_of_subset (Iic_subset_Iic.mpr h.le)).mpr
    ⟨b, self_mem_Iic, fun h' => h.not_ge h'⟩

@[to_dual (attr := simp)]
theorem Iic_subset_Iio : Iic a ⊆ Iio b ↔ a < b :=
  ⟨fun h => h self_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[to_dual]
theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := fun _ hx => le_of_lt hx

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
@[to_dual
/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/]
theorem Iio_subset_Iic (h : a ≤ b) : Iio a ⊆ Iic b :=
  (Iio_subset_Iio h).trans Iio_subset_Iic_self

@[to_dual]
theorem Iio_ssubset_Iic_self : Iio a ⊂ Iic a :=
  ⟨Iio_subset_Iic_self, fun h => (h le_rfl).false⟩

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans_lt hx₁, hx₂.trans_le hb⟩

@[to_dual Ioo_subset_Ioo_right]
theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

@[to_dual (attr := gcongr) (reorder := ha hb)]
theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := fun _ hx =>
  ⟨ha.trans hx.1, hx.2.trans_le hb⟩

@[to_dual Ioc_subset_Ioc_right]
theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl

@[to_dual Ico_subset_Ico_right]
theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans hx₁, le_trans hx₂ hb⟩

@[to_dual Icc_subset_Icc_right]
theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl

@[to_dual (reorder := ha hb) Icc_ssubset_Icc_right]
theorem Icc_ssubset_Icc_left (h₂ : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr h₂, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

@[to_dual (reorder := ha hb)]
theorem Ico_subset_Ioo (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ hx ↦
  ⟨ha.trans_le hx.1, hx.2.trans_le hb⟩

@[to_dual Ioc_subset_Ioo_right]
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
  Ico_subset_Ioo h le_rfl

@[to_dual (reorder := ha hb)]
theorem Icc_subset_Ioc (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ := fun _ hx ↦
  ⟨ha.trans_le hx.1, hx.2.trans hb⟩

@[to_dual Icc_subset_Ico_right]
theorem Icc_subset_Ioc_left (h : a₁ < a₂) : Icc a₂ b ⊆ Ioc a₁ b :=
  Icc_subset_Ioc h le_rfl

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ :=
  (Icc_subset_Ioc_left ha).trans (Ioc_subset_Ioo_right hb)

@[to_dual] theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := fun _ => And.right
@[to_dual] theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := fun _ => And.right
@[to_dual] theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := fun _ => And.right
@[to_dual] theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := fun _ => And.right

@[to_dual] theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := fun _ => And.imp_left le_of_lt
@[to_dual] theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := fun _ => And.imp_left le_of_lt

@[to_dual self]
theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]
theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans h'⟩⟩

@[to_dual none]
theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans h'⟩⟩

@[to_dual]
theorem Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans_le hx.1⟩

@[to_dual]
theorem Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans hx.1⟩

@[to_dual] theorem Ici_inter_Iic : Ici a ∩ Iic b = Icc a b := rfl
@[to_dual] theorem Ici_inter_Iio : Ici a ∩ Iio b = Ico a b := rfl
@[to_dual] theorem Ioi_inter_Iic : Ioi a ∩ Iic b = Ioc a b := rfl
@[to_dual] theorem Ioi_inter_Iio : Ioi a ∩ Iio b = Ioo a b := rfl

@[to_dual self] theorem mem_Icc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Icc a b := Ioo_subset_Icc_self h
@[to_dual] theorem mem_Ico_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ico a b := Ioo_subset_Ico_self h
@[to_dual] theorem mem_Icc_of_Ioc (h : x ∈ Ioc a b) : x ∈ Icc a b := Ioc_subset_Icc_self h
@[to_dual] theorem mem_Iic_of_Iio (h : x ∈ Iio a) : x ∈ Iic a := Iio_subset_Iic_self h

@[to_dual self]
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  contrapose!; exact nonempty_Icc

@[to_dual]
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ico

@[to_dual self]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ioo

@[to_dual]
theorem _root_.IsTop.Iic_eq (h : IsTop a) : Iic a = univ :=
  eq_univ_of_forall h

@[to_dual (attr := simp)]
theorem Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a := by
  simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[to_dual (attr := simp)]
lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [nonempty_iff_ne_empty]

@[to_dual]
theorem Iic_inter_Ioc_of_le (h : a ≤ c) : Iic a ∩ Ioc b c = Ioc b a :=
  ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

@[to_dual notMem_Icc_of_gt]
theorem notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b := fun h => ha.not_ge h.1

@[to_dual notMem_Ioc_of_gt]
theorem notMem_Ico_of_lt (ha : c < a) : c ∉ Ico a b := fun h => ha.not_ge h.1

@[deprecated (since := "2026-02-10")] alias notMem_Ioi_self := self_notMem_Ioi

@[deprecated (since := "2026-02-10")] alias notMem_Iio_self := self_notMem_Iio

@[to_dual notMem_Ico_of_ge]
theorem notMem_Ioc_of_le (ha : c ≤ a) : c ∉ Ioc a b := fun h => lt_irrefl _ <| h.1.trans_le ha

@[to_dual notMem_Ioo_of_ge]
theorem notMem_Ioo_of_le (ha : c ≤ a) : c ∉ Ioo a b := fun h => lt_irrefl _ <| h.1.trans_le ha

section matched_intervals

@[to_dual (attr := simp)] theorem Icc_eq_Ioc_same_iff : Icc a b = Ioc a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]

@[to_dual (attr := simp)] theorem Ioc_eq_Icc_same_iff : Ioc a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioc_same_iff

@[simp, to_dual self] theorem Icc_eq_Ioo_same_iff : Icc a b = Ioo a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]

@[simp, to_dual self] theorem Ioo_eq_Icc_same_iff : Ioo a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioo_same_iff

@[to_dual (attr := simp)] theorem Ioc_eq_Ico_same_iff : Ioc a b = Ico a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]

@[to_dual (attr := simp)] theorem Ioo_eq_Ioc_same_iff : Ioo a b = Ioc a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]

@[to_dual (attr := simp)] theorem Ioc_eq_Ioo_same_iff : Ioc a b = Ioo a b ↔ ¬a < b :=
  eq_comm.trans Ioo_eq_Ioc_same_iff

end matched_intervals

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} :=
  Set.ext <| by simp [Icc, le_antisymm_iff, and_comm]

instance instIccUnique : Unique (Icc a a) where
  default := ⟨a, by simp⟩
  uniq y := Subtype.ext <| by simpa using y.2

@[simp, to_dual none]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
      ⟨eq_of_mem_singleton <| h ▸ left_mem_Icc.2 hab,
        eq_of_mem_singleton <| h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

@[to_dual self]
lemma subsingleton_Icc_of_ge (hba : b ≤ a) : Set.Subsingleton (Icc a b) :=
  fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ ↦ le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp, to_dual self]
lemma subsingleton_Icc_iff {α : Type*} [LinearOrder α] {a b : α} :
    Set.Subsingleton (Icc a b) ↔ b ≤ a := by
  refine ⟨fun h ↦ ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[to_dual (attr := simp) Icc_diff_right]
theorem Icc_diff_left : Icc a b \ {a} = Ioc a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[to_dual (attr := simp) Ioc_diff_right]
theorem Ico_diff_left : Ico a b \ {a} = Ioo a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[simp, to_dual none]
theorem Icc_diff_both : Icc a b \ {a, b} = Ioo a b := by
  rw [insert_eq, ← diff_diff, Icc_diff_left, Ioc_diff_right]

@[to_dual (attr := simp) Ici_diff_left]
theorem Iic_diff_right : Iic a \ {a} = Iio a :=
  ext fun x => by simp [lt_iff_le_and_ne]

@[to_dual (attr := simp)]
theorem Ico_diff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} := by
  rw [← Ico_diff_left, diff_diff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[to_dual (attr := simp)]
theorem Icc_diff_Ico_same (h : a ≤ b) : Icc a b \ Ico a b = {b} := by
  rw [← Icc_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[simp, to_dual none]
theorem Icc_diff_Ioo_same (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by
  rw [← Icc_diff_both, diff_diff_cancel_left]
  simp [insert_subset_iff, h]

@[to_dual (attr := simp)]
theorem Iic_diff_Iio_same : Iic a \ Iio a = {a} := by
  rw [← Iic_diff_right, diff_diff_cancel_left (singleton_subset_iff.2 self_mem_Iic)]

@[to_dual Ioi_union_left]
theorem Iio_union_right : Iio a ∪ {a} = Iic a :=
  ext fun _ => le_iff_lt_or_eq.symm

@[to_dual Ioo_union_right]
theorem Ioo_union_left (hab : a < b) : Ioo a b ∪ {a} = Ico a b := by
  rw [← Ico_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

@[to_dual none]
theorem Ioo_union_both (h : a ≤ b) : Ioo a b ∪ {a, b} = Icc a b := by
  have : (Icc a b \ {a, b}) ∪ {a, b} = Icc a b := diff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this, Icc_diff_both]

@[to_dual Ico_union_right]
theorem Ioc_union_left (hab : a ≤ b) : Ioc a b ∪ {a} = Icc a b := by
  rw [← Icc_diff_left, diff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

@[to_dual (attr := simp) Ioc_insert_left]
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [insert_eq, union_comm, Ico_union_right h]

@[to_dual (attr := simp) Ioo_insert_right]
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [insert_eq, union_comm, Ioo_union_left h]

@[to_dual (attr := simp)]
theorem Iio_insert : insert a (Iio a) = Iic a :=
  ext fun _ => le_iff_eq_or_lt.symm

@[to_dual]
theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) :
    s ∈ ({Iic a, Iio a} : Set (Set α)) :=
  by_cases
    (fun h : a ∈ s =>
      Or.inl <| Subset.antisymm hc <| by rw [← Iio_union_right, union_subset_iff]; simp [*])
    fun h =>
    Or.inr <| Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho

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

@[to_dual eq_right_or_mem_Ioo_of_mem_Ioc]
theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x ∈ Ico a b) : x = a ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

@[to_dual none]
theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x ∈ Icc a b) :
    x = a ∨ x = b ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

@[to_dual]
theorem _root_.IsMin.Iic_eq (h : IsMin a) : Iic a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨self_mem_Ici, fun _ => h.eq_of_le⟩

@[to_dual]
theorem Iic_injective : Injective (Iic : α → Set α) := fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

@[to_dual]
theorem Iic_inj : Iic a = Iic b ↔ a = b :=
  Iic_injective.eq_iff

@[simp, to_dual none]
theorem Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) : Icc a b ∩ Icc b c = {b} := by
  rw [← Ici_inter_Iic, ← Iic_inter_Ici, inter_inter_inter_comm, Iic_inter_Ici]
  simp [hab, hbc]

@[to_dual none]
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

@[to_dual (attr := simp)]
theorem Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤} :=
  isMax_top.Ici_eq

@[to_dual]
theorem Iio_top [PartialOrder α] [OrderTop α] : Iio (⊤ : α) = {⊤}ᶜ :=
  ext fun _ ↦ lt_top_iff_ne_top

variable [Preorder α] [OrderTop α] {a : α}

@[to_dual]
theorem Ioi_top : Ioi (⊤ : α) = ∅ :=
  isMax_top.Ioi_eq

@[to_dual (attr := simp)]
theorem Iic_top : Iic (⊤ : α) = univ :=
  isTop_top.Iic_eq

@[to_dual (attr := simp)]
theorem Icc_top : Icc a ⊤ = Ici a := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
theorem Ioc_top : Ioc a ⊤ = Ioi a := by simp [← Ioi_inter_Iic]

end OrderTop

theorem Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α) ⊤ = univ := by simp

section Lattice

section Inf

variable [SemilatticeInf α]

@[to_dual (attr := simp)]
theorem Iic_inter_Iic {a b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) := by
  ext x
  simp [Iic]

@[to_dual (reorder := a b) (attr := simp)]
theorem Ioc_inter_Iic (a b c : α) : Ioc a b ∩ Iic c = Ioc a (b ⊓ c) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_assoc, Iic_inter_Iic]

end Inf

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

@[to_dual self]
theorem Icc_inter_Icc : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

end Lattice

/-! ### Closed intervals in `α × β` -/

section Prod

variable {β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
theorem Iic_prod_Iic (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[to_dual]
theorem Iic_prod_eq (a : α × β) : Iic a = Iic a.1 ×ˢ Iic a.2 :=
  rfl

@[simp, to_dual self]
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

@[to_dual self]
theorem Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2 := by simp

end Prod

/-! ### Lemmas about intervals in dense orders -/

section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioo.mpr` in the proof.
instance : NoMinOrder (Ioo x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioo.mpr ⟨hb₁, hb₂.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioc.mpr` in the proof.
instance : NoMinOrder (Ioc x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioc.mpr ⟨hb₁, hb₂.le.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual]
instance : NoMinOrder (Ioi x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

end Dense

/-! ### Intervals in `Prop` -/

@[simp] lemma Iic_False : Iic False = {False} := by aesop
@[simp] lemma Iic_True : Iic True = univ := by aesop
@[simp] lemma Ici_False : Ici False = univ := by aesop
@[simp] lemma Ici_True : Ici True = {True} := by aesop
lemma Iio_False : Iio False = ∅ := by aesop
@[simp] lemma Iio_True : Iio True = {False} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
@[simp] lemma Ioi_False : Ioi False = {True} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
lemma Ioi_True : Ioi True = ∅ := by aesop

end Set
