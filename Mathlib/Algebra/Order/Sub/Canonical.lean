/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs

/-!
# Lemmas about subtraction in canonically ordered monoids
-/


variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  exact add_le_add_left add_tsub_le_left a

theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_comm]
  exact add_tsub_cancel_of_le h

theorem add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
  (add_le_add_right h2 b).trans_eq <| tsub_add_cancel_of_le h

theorem add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
  (add_le_add_left h2 a).trans_eq <| add_tsub_cancel_of_le h

theorem tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b := by
  rw [tsub_le_iff_right, tsub_add_cancel_of_le h]

theorem tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b := by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

theorem tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) : b - a = c - a → b = c :=
  (tsub_left_inj h₁ h₂).1

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b := by
  refine ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne ?_
  rintro rfl
  exact h2.false

theorem tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub, add_tsub_cancel_of_le hcb]

theorem tsub_tsub_tsub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub, add_tsub_cancel_of_le h]

/-! #### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a = b - c ↔ a + c = b :=
  ⟨by
    rintro rfl
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩

protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLECancellable b) (h : b ≤ a) :
    a - b = c ↔ a = c + b := by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]

protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c ≤ b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]

protected theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b ≤ a) :
    a - b + c = a + c - b := by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]

protected theorem tsub_tsub_assoc (hbc : AddLECancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
    a - (b - c) = a - b + c :=
  hbc.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]

protected theorem tsub_add_tsub_comm (hb : AddLECancellable b) (hd : AddLECancellable d)
    (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba, ← hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_comm d]

protected theorem le_tsub_iff_left (ha : AddLECancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩

protected theorem le_tsub_iff_right (ha : AddLECancellable a) (h : a ≤ c) :
    b ≤ c - a ↔ b + a ≤ c := by
  rw [add_comm]
  exact ha.le_tsub_iff_left h

protected theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < b + c := by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)

protected theorem tsub_lt_iff_right (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < c + b := by
  rw [add_comm]
  exact hb.tsub_lt_iff_left hba

protected theorem tsub_lt_iff_tsub_lt (hb : AddLECancellable b) (hc : AddLECancellable c)
    (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]

protected theorem le_tsub_iff_le_tsub (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a := by
  rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]

protected theorem lt_tsub_iff_right_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ a + c < b := by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right

protected theorem lt_tsub_iff_left_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ c + a < b := by
  rw [add_comm]
  exact hc.lt_tsub_iff_right_of_le h

protected theorem tsub_inj_right (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
    (h₃ : a - b = a - c) : b = c := by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂]

protected theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)

protected theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b ≤ a)
    (h : c < b) : a - b < a - c :=
  (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' <| hab.tsub_inj_right h₁ (h.le.trans h₁) h'

protected theorem tsub_lt_tsub_right_of_le (hc : AddLECancellable c) (h : c ≤ a) (h2 : a < b) :
    a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]

protected theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]
protected theorem add_tsub_tsub_cancel (hac : AddLECancellable (a - c)) (h : c ≤ a) :
    a + b - (a - c) = b + c :=
  hac.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]

protected theorem tsub_tsub_cancel_of_le (hba : AddLECancellable (b - a)) (h : a ≤ b) :
    b - (b - a) = a :=
  hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm

protected theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b ≤ a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]

end AddLECancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
  Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h

theorem tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
  Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h

/-- See `add_tsub_le_assoc` for an inequality. -/
theorem add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.AddLECancellable.add_tsub_assoc_of_le h a

theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
  Contravariant.AddLECancellable.tsub_add_eq_add_tsub h

theorem tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
  Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂

theorem tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc

theorem le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_left h

theorem le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_right h

theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc

theorem tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
  Contravariant.AddLECancellable.tsub_lt_iff_right hbc

theorem tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
  Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂

theorem le_tsub_iff_le_tsub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
  Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂

/-- See `lt_tsub_iff_right` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h

/-- See `lt_tsub_iff_left` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h

/-- See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)] (hca : c ≤ a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

theorem tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

theorem tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2

theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)] (h₁ : b ≤ a)
    (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]
theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c :=
  Contravariant.AddLECancellable.add_tsub_tsub_cancel h

/-- See `tsub_tsub_le` for an inequality. -/
theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h

theorem tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c :=
  Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h

-- note: not generalized to `AddLECancellable` because `add_tsub_add_eq_tsub_left` isn't
/-- The `tsub` version of `sub_sub_eq_add_sub`. -/
theorem tsub_tsub_eq_add_tsub_of_le [ContravariantClass α α HAdd.hAdd LE.le]
    (h : c ≤ b) : a - (b - c) = a + c - b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c, add_comm a c, add_tsub_add_eq_tsub_left]

end Contra

end ExistsAddOfLE

/-! ### Lemmas in a canonically ordered monoid. -/


section CanonicallyOrderedAddCommMonoid

variable [CanonicallyOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

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

attribute [simp] tsub_eq_zero_of_le

theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_of_le le_rfl

theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl

theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_of_le <| zero_le a

theorem tsub_self_add (a b : α) : a - (a + b) = 0 :=
  tsub_eq_zero_of_le <| self_le_add_right _ _

theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne, tsub_eq_zero_iff_le]

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_le

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

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

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

variable [CanonicallyLinearOrderedAddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

namespace AddLECancellable

protected theorem lt_tsub_iff_right (hc : AddLECancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

protected theorem lt_tsub_iff_left (hc : AddLECancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

protected theorem tsub_lt_tsub_iff_right (hc : AddLECancellable c) (h : c ≤ a) :
    a - c < b - c ↔ a < b := by rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine tsub_le_self.lt_of_ne fun h => ?_
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_le (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

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

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

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

theorem tsub_min : a - min a b = a - b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
  · rw [min_eq_right h]

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  apply min_le_left

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

end CanonicallyLinearOrderedAddCommMonoid
