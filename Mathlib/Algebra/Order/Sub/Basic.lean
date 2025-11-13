/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Even
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

variable {α : Type*}

section CanonicallyOrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

-- This was previously a `@[simp]` lemma, but it is not necessarily a good idea, e.g. in
-- `example (h : n - m = 0) : a + (n - m) = a := by simp_all`
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le

@[simp]
theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl

theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl

@[simp]
theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le <| zero_le a

theorem tsub_self_add (a b : α) : a - (a + b) = 0 :=
  tsub_eq_zero_of_le <| self_le_add_right _ _

theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne, tsub_eq_zero_iff_le]

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_ge

theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_lt tsub_le_self h

namespace AddLECancellable

protected theorem tsub_le_tsub_iff_left (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b := by
  refine ⟨?_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha

protected theorem tsub_right_inj (ha : AddLECancellable a) (hb : AddLECancellable b)
    (hc : AddLECancellable c) (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iff, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca,
    and_comm]

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [AddLeftReflectLE α]

theorem tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
  Contravariant.AddLECancellable.tsub_le_tsub_iff_left Contravariant.AddLECancellable h

theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
  Contravariant.AddLECancellable.tsub_right_inj Contravariant.AddLECancellable
    Contravariant.AddLECancellable hba hca

variable (α)

/-- A `CanonicallyOrderedAddCommMonoid` with ordered subtraction and order-reflecting addition is
cancellative. This is not an instance as it would form a typeclass loop.

See note [reducible non-instances]. -/
abbrev CanonicallyOrderedAddCommMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }

end Contra

end CanonicallyOrderedAddCommMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddCommMonoid

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

namespace AddLECancellable

omit [CanonicallyOrderedAdd α] in
protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

omit [CanonicallyOrderedAdd α] in
protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c ≤ a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_ge (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine
    ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne ?_⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLECancellable a) (hb : AddLECancellable b)
    (h : b ≤ a) : a - b < a - c ↔ c < b :=
  lt_iff_lt_of_le_iff_le <| ha.tsub_le_tsub_iff_left hb h

end AddLECancellable

section Contra

variable [AddLeftReflectLE α]

/-- This lemma also holds for `ENNReal`, but we need a different proof for that. -/
theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_right h

theorem tsub_lt_self : 0 < a → 0 < b → a - b < a :=
  Contravariant.AddLECancellable.tsub_lt_self

@[simp] theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.AddLECancellable.tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h

lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b := by
  rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end Contra

/-! ### Lemmas about `max` and `min`. -/


theorem tsub_add_eq_max : a - b + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
  · rw [max_eq_left h, tsub_add_cancel_of_le h]

theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]

theorem tsub_min : a - min a b = a - b := (tsub_eq_tsub_min a b).symm

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  apply min_le_left

-- `Odd.tsub` requires `CanonicallyLinearOrderedSemiring`, which we don't have
lemma Even.tsub [AddLeftReflectLE α] {m n : α} (hm : Even m) (hn : Even n) :
    Even (m - n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  refine ⟨a - b, ?_⟩
  obtain h | h := le_total a b
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero]
  · exact (tsub_add_tsub_comm h h).symm

end CanonicallyLinearOrderedAddCommMonoid

/-! ### `Sub` structure in linearly canonically ordered monoid using choice. -/

namespace CanonicallyOrderedAdd

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- `Sub` structure in linearly canonically ordered monoid using choice. -/
noncomputable abbrev toSub : Sub α where
  sub x y := if h : y ≤ x then (exists_add_of_le h).choose else 0

attribute [local instance] toSub

/-- The `Sub` structure using choice satisfies `OrderedSub`. -/
theorem toOrderedSub [AddRightReflectLE α] : OrderedSub α where
  tsub_le_iff_right a b c := by
    change dite _ _ _ ≤ c ↔ _
    split_ifs with h
    · have := (exists_add_of_le h).choose_spec
      rw [this] at h
      conv_rhs => rw [this, add_comm]
      rw [add_le_add_iff_right]
    · rw [not_le] at h
      constructor <;> intro h'
      · simpa using add_le_add h' h.le
      · exact zero_le c

end CanonicallyOrderedAdd
