/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Basic

#align_import algebra.order.sub.canonical from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

/-!
# Lemmas about subtraction in canonically ordered monoids
-/


variable {α : Type*}

section CanonicallyOrderedAddCommMonoid

variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩
#align add_tsub_cancel_iff_le add_tsub_cancel_iff_le

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le
#align tsub_add_cancel_iff_le tsub_add_cancel_iff_le

-- This was previously a `@[simp]` lemma, but it is not necessarily a good idea, e.g. in
-- `example (h : n - m = 0) : a + (n - m) = a := by simp_all`
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]
#align tsub_eq_zero_iff_le tsub_eq_zero_iff_le

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le
#align tsub_eq_zero_of_le tsub_eq_zero_of_le

attribute [simp] tsub_eq_zero_of_le

theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl
#align tsub_self tsub_self

theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl
#align tsub_le_self tsub_le_self

theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le <| zero_le a
#align zero_tsub zero_tsub

theorem tsub_self_add (a b : α) : a - (a + b) = 0 :=
  tsub_eq_zero_of_le <| self_le_add_right _ _
#align tsub_self_add tsub_self_add

theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne, tsub_eq_zero_iff_le]
#align tsub_pos_iff_not_le tsub_pos_iff_not_le

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_le
#align tsub_pos_of_lt tsub_pos_of_lt

theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_lt tsub_le_self h
#align tsub_lt_of_lt tsub_lt_of_lt

namespace AddLECancellable

protected theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha
#align add_le_cancellable.tsub_le_tsub_iff_left AddLECancellable.tsub_le_tsub_iff_left

protected theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]
#align add_le_cancellable.tsub_right_inj AddLECancellable.tsub_right_inj

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
  Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h
#align tsub_le_tsub_iff_left tsub_le_tsub_iff_left

theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
  Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca
#align tsub_right_inj tsub_right_inj

variable (α)

/-- A `CanonicallyOrderedAddCommMonoid` with ordered subtraction and order-reflecting addition is
cancellative. This is not an instance as it would form a typeclass loop.

See note [reducible non-instances]. -/
abbrev CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }
#align canonically_ordered_add_monoid.to_add_cancel_comm_monoid CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid

end Contra

end CanonicallyOrderedAddCommMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddCommMonoid

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]
#align tsub_pos_iff_lt tsub_pos_iff_lt

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]
#align tsub_eq_tsub_min tsub_eq_tsub_min

namespace AddLECancellable

protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩
#align add_le_cancellable.lt_tsub_iff_right AddLECancellable.lt_tsub_iff_right

protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩
#align add_le_cancellable.lt_tsub_iff_left AddLECancellable.lt_tsub_iff_left

protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c ≤ a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]
#align add_le_cancellable.tsub_lt_tsub_iff_right AddLECancellable.tsub_lt_tsub_iff_right

protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_le (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)
#align add_le_cancellable.tsub_lt_self AddLECancellable.tsub_lt_self

protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine
    ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false
#align add_le_cancellable.tsub_lt_self_iff AddLECancellable.tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b ≤ a) : a - b < a - c ↔ c < b :=
  lt_iff_lt_of_le_iff_le <| ha.tsub_le_tsub_iff_left hb h
#align add_le_cancellable.tsub_lt_tsub_iff_left_of_le AddLECancellable.tsub_lt_tsub_iff_left_of_le

end AddLECancellable

section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

/-- This lemma also holds for `ENNReal`, but we need a different proof for that. -/
theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h
#align tsub_lt_tsub_iff_right tsub_lt_tsub_iff_right

theorem tsub_lt_self : 0 < a → 0 < b → a - b < a :=
  Contravariant.AddLECancellable.tsub_lt_self
#align tsub_lt_self tsub_lt_self

@[simp] theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.AddLECancellable.tsub_lt_self_iff
#align tsub_lt_self_iff tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h
#align tsub_lt_tsub_iff_left_of_le tsub_lt_tsub_iff_left_of_le

lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end Contra

/-! ### Lemmas about `max` and `min`. -/


theorem tsub_add_eq_max : a - b + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]
#align tsub_add_eq_max tsub_add_eq_max

theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]
#align add_tsub_eq_max add_tsub_eq_max

theorem tsub_min : a - min a b = a - b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]
#align tsub_min tsub_min

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  apply min_le_left
#align tsub_add_min tsub_add_min

-- `Odd.tsub` requires `CanonicallyLinearOrderedSemiring`, which we don't have
lemma Even.tsub [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm
#align even.tsub Even.tsub

end CanonicallyLinearOrderedAddCommMonoid
