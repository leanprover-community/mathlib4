/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs

#align_import algebra.order.sub.canonical from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

/-!
# Lemmas about subtraction in canonically ordered monoids
-/


variable {α : Type*}

section ExistsAddOfLE

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine' le_antisymm _ le_add_tsub
  -- ⊢ a + (b - a) ≤ b
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  -- ⊢ a + (a + c - a) ≤ a + c
  exact add_le_add_left add_tsub_le_left a
  -- 🎉 no goals
#align add_tsub_cancel_of_le add_tsub_cancel_of_le

theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_comm]
  -- ⊢ a + (b - a) = b
  exact add_tsub_cancel_of_le h
  -- 🎉 no goals
#align tsub_add_cancel_of_le tsub_add_cancel_of_le

theorem add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
  (add_le_add_right h2 b).trans_eq <| tsub_add_cancel_of_le h
#align add_le_of_le_tsub_right_of_le add_le_of_le_tsub_right_of_le

theorem add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
  (add_le_add_left h2 a).trans_eq <| add_tsub_cancel_of_le h
#align add_le_of_le_tsub_left_of_le add_le_of_le_tsub_left_of_le

theorem tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b := by
  rw [tsub_le_iff_right, tsub_add_cancel_of_le h]
  -- 🎉 no goals
#align tsub_le_tsub_iff_right tsub_le_tsub_iff_right

theorem tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b := by
  simp_rw [le_antisymm_iff, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]
  -- 🎉 no goals
#align tsub_left_inj tsub_left_inj

theorem tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) : b - a = c - a → b = c :=
  (tsub_left_inj h₁ h₂).1
#align tsub_inj_left tsub_inj_left

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b := by
  refine' ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne _
  -- ⊢ a ≠ b
  rintro rfl
  -- ⊢ False
  exact h2.false
  -- 🎉 no goals
#align lt_of_tsub_lt_tsub_right_of_le lt_of_tsub_lt_tsub_right_of_le

theorem tsub_add_tsub_cancel (hab : b ≤ a) (hcb : c ≤ b) : a - b + (b - c) = a - c := by
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  -- ⊢ a - b = a - c - (b - c)
  rw [tsub_tsub, add_tsub_cancel_of_le hcb]
  -- 🎉 no goals
#align tsub_add_tsub_cancel tsub_add_tsub_cancel

theorem tsub_tsub_tsub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub, add_tsub_cancel_of_le h]
  -- 🎉 no goals
#align tsub_tsub_tsub_cancel_right tsub_tsub_tsub_cancel_right

/-! #### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a = b - c ↔ a + c = b :=
  ⟨by
    rintro rfl
    -- ⊢ b - c + c = b
    exact tsub_add_cancel_of_le h, hc.eq_tsub_of_add_eq⟩
    -- 🎉 no goals
#align add_le_cancellable.eq_tsub_iff_add_eq_of_le AddLECancellable.eq_tsub_iff_add_eq_of_le

protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLECancellable b) (h : b ≤ a) :
    a - b = c ↔ a = c + b := by rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]
                                -- 🎉 no goals
#align add_le_cancellable.tsub_eq_iff_eq_add_of_le AddLECancellable.tsub_eq_iff_eq_add_of_le

protected theorem add_tsub_assoc_of_le (hc : AddLECancellable c) (h : c ≤ b) (a : α) :
    a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_comm c, ← add_assoc, hc.add_tsub_cancel_right]
  -- 🎉 no goals
#align add_le_cancellable.add_tsub_assoc_of_le AddLECancellable.add_tsub_assoc_of_le

protected theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b ≤ a) :
    a - b + c = a + c - b := by rw [add_comm a, hb.add_tsub_assoc_of_le h, add_comm]
                                -- 🎉 no goals
#align add_le_cancellable.tsub_add_eq_add_tsub AddLECancellable.tsub_add_eq_add_tsub

protected theorem tsub_tsub_assoc (hbc : AddLECancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
    a - (b - c) = a - b + c :=
  hbc.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h₂, tsub_add_cancel_of_le h₁]
                              -- 🎉 no goals
#align add_le_cancellable.tsub_tsub_assoc AddLECancellable.tsub_tsub_assoc

protected theorem tsub_add_tsub_comm (hb : AddLECancellable b) (hd : AddLECancellable d)
    (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba, ← hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_comm d]
  -- 🎉 no goals
#align add_le_cancellable.tsub_add_tsub_comm AddLECancellable.tsub_add_tsub_comm

protected theorem le_tsub_iff_left (ha : AddLECancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩
#align add_le_cancellable.le_tsub_iff_left AddLECancellable.le_tsub_iff_left

protected theorem le_tsub_iff_right (ha : AddLECancellable a) (h : a ≤ c) :
    b ≤ c - a ↔ b + a ≤ c := by
  rw [add_comm]
  -- ⊢ b ≤ c - a ↔ a + b ≤ c
  exact ha.le_tsub_iff_left h
  -- 🎉 no goals
#align add_le_cancellable.le_tsub_iff_right AddLECancellable.le_tsub_iff_right

protected theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < b + c := by
  refine' ⟨hb.lt_add_of_tsub_lt_left, _⟩
  -- ⊢ a < b + c → a - b < c
  intro h; refine' (tsub_le_iff_left.mpr h.le).lt_of_ne _
  -- ⊢ a - b < c
           -- ⊢ a - b ≠ c
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)
  -- ⊢ False
              -- 🎉 no goals
#align add_le_cancellable.tsub_lt_iff_left AddLECancellable.tsub_lt_iff_left

protected theorem tsub_lt_iff_right (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < c + b := by
  rw [add_comm]
  -- ⊢ a - b < c ↔ a < b + c
  exact hb.tsub_lt_iff_left hba
  -- 🎉 no goals
#align add_le_cancellable.tsub_lt_iff_right AddLECancellable.tsub_lt_iff_right

protected theorem tsub_lt_iff_tsub_lt (hb : AddLECancellable b) (hc : AddLECancellable c)
    (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]
  -- 🎉 no goals
#align add_le_cancellable.tsub_lt_iff_tsub_lt AddLECancellable.tsub_lt_iff_tsub_lt

protected theorem le_tsub_iff_le_tsub (ha : AddLECancellable a) (hc : AddLECancellable c)
    (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a := by
  rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]
  -- 🎉 no goals
#align add_le_cancellable.le_tsub_iff_le_tsub AddLECancellable.le_tsub_iff_le_tsub

protected theorem lt_tsub_iff_right_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ a + c < b := by
  refine' ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne _, hc.lt_tsub_of_add_lt_right⟩
  -- ⊢ a + c ≠ b
  rintro rfl
  -- ⊢ False
  exact h'.ne' hc.add_tsub_cancel_right
  -- 🎉 no goals
#align add_le_cancellable.lt_tsub_iff_right_of_le AddLECancellable.lt_tsub_iff_right_of_le

protected theorem lt_tsub_iff_left_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ c + a < b := by
  rw [add_comm]
  -- ⊢ a < b - c ↔ a + c < b
  exact hc.lt_tsub_iff_right_of_le h
  -- 🎉 no goals
#align add_le_cancellable.lt_tsub_iff_left_of_le AddLECancellable.lt_tsub_iff_left_of_le

protected theorem tsub_inj_right (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a)
    (h₃ : a - b = a - c) : b = c := by
  rw [← hab.inj]
  -- ⊢ a - b + b = a - b + c
  rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂]
  -- 🎉 no goals
#align add_le_cancellable.tsub_inj_right AddLECancellable.tsub_inj_right

protected theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hca : c ≤ a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  -- ⊢ c < b
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)
  -- 🎉 no goals
#align add_le_cancellable.lt_of_tsub_lt_tsub_left_of_le AddLECancellable.lt_of_tsub_lt_tsub_left_of_le

protected theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b ≤ a)
    (h : c < b) : a - b < a - c :=
  (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' <| hab.tsub_inj_right h₁ (h.le.trans h₁) h'
#align add_le_cancellable.tsub_lt_tsub_left_of_le AddLECancellable.tsub_lt_tsub_left_of_le

protected theorem tsub_lt_tsub_right_of_le (hc : AddLECancellable c) (h : c ≤ a) (h2 : a < b) :
    a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  -- ⊢ c + (a - c) < b
  rwa [add_tsub_cancel_of_le h]
  -- 🎉 no goals
#align add_le_cancellable.tsub_lt_tsub_right_of_le AddLECancellable.tsub_lt_tsub_right_of_le

protected theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, hab.tsub_lt_tsub_left_of_le h₁⟩
#align add_le_cancellable.tsub_lt_tsub_iff_left_of_le_of_le AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le

@[simp]
protected theorem add_tsub_tsub_cancel (hac : AddLECancellable (a - c)) (h : c ≤ a) :
    a + b - (a - c) = b + c :=
  hac.tsub_eq_of_eq_add <| by rw [add_assoc, add_tsub_cancel_of_le h, add_comm]
                              -- 🎉 no goals
#align add_le_cancellable.add_tsub_tsub_cancel AddLECancellable.add_tsub_tsub_cancel

protected theorem tsub_tsub_cancel_of_le (hba : AddLECancellable (b - a)) (h : a ≤ b) :
    b - (b - a) = a :=
  hba.tsub_eq_of_eq_add (add_tsub_cancel_of_le h).symm
#align add_le_cancellable.tsub_tsub_cancel_of_le AddLECancellable.tsub_tsub_cancel_of_le

protected theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b ≤ a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, hab.tsub_tsub_cancel_of_le h]
                                  -- 🎉 no goals
#align add_le_cancellable.tsub_tsub_tsub_cancel_left AddLECancellable.tsub_tsub_tsub_cancel_left

end AddLECancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
  Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h
#align eq_tsub_iff_add_eq_of_le eq_tsub_iff_add_eq_of_le

theorem tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
  Contravariant.AddLECancellable.tsub_eq_iff_eq_add_of_le h
#align tsub_eq_iff_eq_add_of_le tsub_eq_iff_eq_add_of_le

/-- See `add_tsub_le_assoc` for an inequality. -/
theorem add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.AddLECancellable.add_tsub_assoc_of_le h a
#align add_tsub_assoc_of_le add_tsub_assoc_of_le

theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
  Contravariant.AddLECancellable.tsub_add_eq_add_tsub h
#align tsub_add_eq_add_tsub tsub_add_eq_add_tsub

theorem tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
  Contravariant.AddLECancellable.tsub_tsub_assoc h₁ h₂
#align tsub_tsub_assoc tsub_tsub_assoc

theorem tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.AddLECancellable.tsub_add_tsub_comm Contravariant.AddLECancellable hba hdc
#align tsub_add_tsub_comm tsub_add_tsub_comm

theorem le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_left h
#align le_tsub_iff_left le_tsub_iff_left

theorem le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
  Contravariant.AddLECancellable.le_tsub_iff_right h
#align le_tsub_iff_right le_tsub_iff_right

theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.AddLECancellable.tsub_lt_iff_left hbc
#align tsub_lt_iff_left tsub_lt_iff_left

theorem tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
  Contravariant.AddLECancellable.tsub_lt_iff_right hbc
#align tsub_lt_iff_right tsub_lt_iff_right

theorem tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
  Contravariant.AddLECancellable.tsub_lt_iff_tsub_lt Contravariant.AddLECancellable h₁ h₂
#align tsub_lt_iff_tsub_lt tsub_lt_iff_tsub_lt

theorem le_tsub_iff_le_tsub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
  Contravariant.AddLECancellable.le_tsub_iff_le_tsub Contravariant.AddLECancellable h₁ h₂
#align le_tsub_iff_le_tsub le_tsub_iff_le_tsub

/-- See `lt_tsub_iff_right` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_right_of_le h
#align lt_tsub_iff_right_of_le lt_tsub_iff_right_of_le

/-- See `lt_tsub_iff_left` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
  Contravariant.AddLECancellable.lt_tsub_iff_left_of_le h
#align lt_tsub_iff_left_of_le lt_tsub_iff_left_of_le

/-- See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)] (hca : c ≤ a)
    (h : a - b < a - c) : c < b :=
  Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h
#align lt_of_tsub_lt_tsub_left_of_le lt_of_tsub_lt_tsub_left_of_le

theorem tsub_lt_tsub_left_of_le : b ≤ a → c < b → a - b < a - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_left_of_le
#align tsub_lt_tsub_left_of_le tsub_lt_tsub_left_of_le

theorem tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
  Contravariant.AddLECancellable.tsub_lt_tsub_right_of_le h h2
#align tsub_lt_tsub_right_of_le tsub_lt_tsub_right_of_le

theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.AddLECancellable.tsub_inj_right h₁ h₂ h₃
#align tsub_inj_right tsub_inj_right

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)] (h₁ : b ≤ a)
    (h₂ : c ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂
#align tsub_lt_tsub_iff_left_of_le_of_le tsub_lt_tsub_iff_left_of_le_of_le

@[simp]
theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c :=
  Contravariant.AddLECancellable.add_tsub_tsub_cancel h
#align add_tsub_tsub_cancel add_tsub_tsub_cancel

/-- See `tsub_tsub_le` for an inequality. -/
theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h
#align tsub_tsub_cancel_of_le tsub_tsub_cancel_of_le

theorem tsub_tsub_tsub_cancel_left (h : b ≤ a) : a - c - (a - b) = b - c :=
  Contravariant.AddLECancellable.tsub_tsub_tsub_cancel_left h
#align tsub_tsub_tsub_cancel_left tsub_tsub_tsub_cancel_left

end Contra

end ExistsAddOfLE

/-! ### Lemmas in a canonically ordered monoid. -/


section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩
#align add_tsub_cancel_iff_le add_tsub_cancel_iff_le

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  -- ⊢ a + (b - a) = b ↔ a ≤ b
  exact add_tsub_cancel_iff_le
  -- 🎉 no goals
#align tsub_add_cancel_iff_le tsub_add_cancel_iff_le

@[simp]
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]
  -- 🎉 no goals
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
  rw [pos_iff_ne_zero, Ne.def, tsub_eq_zero_iff_le]
  -- 🎉 no goals
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
  refine' ⟨_, fun h => tsub_le_tsub_left h a⟩
  -- ⊢ a - b ≤ a - c → c ≤ b
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self),
    add_comm b]
  apply ha
  -- 🎉 no goals
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

/-- A `CanonicallyOrderedAddMonoid` with ordered subtraction and order-reflecting addition is
cancellative. This is not an instance as it would form a typeclass loop.

See note [reducible non-instances]. -/
@[reducible]
def CanonicallyOrderedAddMonoid.toAddCancelCommMonoid : AddCancelCommMonoid α :=
  { (by infer_instance : AddCommMonoid α) with
        -- 🎉 no goals
    add_left_cancel := fun a b c h => by
      simpa only [add_tsub_cancel_left] using congr_arg (fun x => x - a) h }
      -- 🎉 no goals
#align canonically_ordered_add_monoid.to_add_cancel_comm_monoid CanonicallyOrderedAddMonoid.toAddCancelCommMonoid

end Contra

end CanonicallyOrderedAddMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddMonoid

variable [CanonicallyLinearOrderedAddMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by rw [tsub_pos_iff_not_le, not_le]
                                                  -- 🎉 no goals
#align tsub_pos_iff_lt tsub_pos_iff_lt

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  cases' le_total a b with h h
  -- ⊢ a - b = a - min a b
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
    -- 🎉 no goals
  · rw [min_eq_right h]
    -- 🎉 no goals
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
                                -- 🎉 no goals
#align add_le_cancellable.tsub_lt_tsub_iff_right AddLECancellable.tsub_lt_tsub_iff_right

protected theorem tsub_lt_self (ha : AddLECancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine' tsub_le_self.lt_of_ne fun h => _
  -- ⊢ False
  rw [← h, tsub_pos_iff_lt] at h₁
  -- ⊢ False
  exact h₂.not_le (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)
  -- 🎉 no goals
#align add_le_cancellable.tsub_lt_self AddLECancellable.tsub_lt_self

protected theorem tsub_lt_self_iff (ha : AddLECancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine'
    ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  -- ⊢ False
  rw [tsub_zero] at h
  -- ⊢ False
  exact h.false
  -- 🎉 no goals
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

theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.AddLECancellable.tsub_lt_self_iff
#align tsub_lt_self_iff tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le Contravariant.AddLECancellable h
#align tsub_lt_tsub_iff_left_of_le tsub_lt_tsub_iff_left_of_le

end Contra

/-! ### Lemmas about `max` and `min`. -/


theorem tsub_add_eq_max : a - b + b = max a b := by
  cases' le_total a b with h h
  -- ⊢ a - b + b = max a b
  · rw [max_eq_right h, tsub_eq_zero_of_le h, zero_add]
    -- 🎉 no goals
  · rw [max_eq_left h, tsub_add_cancel_of_le h]
    -- 🎉 no goals
#align tsub_add_eq_max tsub_add_eq_max

theorem add_tsub_eq_max : a + (b - a) = max a b := by rw [add_comm, max_comm, tsub_add_eq_max]
                                                      -- 🎉 no goals
#align add_tsub_eq_max add_tsub_eq_max

theorem tsub_min : a - min a b = a - b := by
  cases' le_total a b with h h
  -- ⊢ a - min a b = a - b
  · rw [min_eq_left h, tsub_self, tsub_eq_zero_of_le h]
    -- 🎉 no goals
  · rw [min_eq_right h]
    -- 🎉 no goals
#align tsub_min tsub_min

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, @tsub_add_cancel_of_le]
  -- ⊢ min a b ≤ a
  apply min_le_left
  -- 🎉 no goals
#align tsub_add_min tsub_add_min

end CanonicallyLinearOrderedAddMonoid
