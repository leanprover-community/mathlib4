/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Lemmas about subtraction in an unbundled canonically ordered monoids
-/

-- These are about *unbundled* canonically ordered monoids
assert_not_exists OrderedCommMonoid

variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine le_antisymm ?_ le_add_tsub
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  grw [add_tsub_le_left]

theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_comm]
  exact add_tsub_cancel_of_le h

theorem add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c := by
  grw [h2, tsub_add_cancel_of_le h]

theorem add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c := by
  grw [h2, add_tsub_cancel_of_le h]

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

protected theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α]
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

protected theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩

@[simp]
protected lemma add_add_tsub_cancel (hc : AddLECancellable c) (hcb : c ≤ b) :
    a + c + (b - c) = a + b := by
  rw [← hc.add_tsub_assoc_of_le hcb, add_right_comm, hc.add_tsub_cancel_right]

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


variable [AddLeftReflectLE α]

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
theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α] (hca : c ≤ a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

theorem tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le

theorem tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2

theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α] (h₁ : b ≤ a)
    (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

@[simp]
lemma add_add_tsub_cancel (hcb : c ≤ b) : a + c + (b - c) = a + b :=
  Contravariant.AddLECancellable.add_add_tsub_cancel hcb

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
theorem tsub_tsub_eq_add_tsub_of_le
    (h : c ≤ b) : a - (b - c) = a + c - b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c, add_comm a c, add_tsub_add_eq_tsub_left]

end Contra

end ExistsAddOfLE
