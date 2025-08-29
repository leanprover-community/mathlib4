/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Principal upper/lower sets

The results in this file all assume that the underlying type is equipped with at least a preorder.

## Main declarations

* `UpperSet.Ici`: Principal upper set. `Set.Ici` as an upper set.
* `UpperSet.Ioi`: Strict principal upper set. `Set.Ioi` as an upper set.
* `LowerSet.Iic`: Principal lower set. `Set.Iic` as a lower set.
* `LowerSet.Iio`: Strict principal lower set. `Set.Iio` as a lower set.
-/

open Function Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- Principal upper set. `Set.Ici` as an upper set. The smallest upper set containing a given
element. -/
nonrec def Ici (a : α) : UpperSet α :=
  ⟨Ici a, isUpperSet_Ici a⟩

/-- Strict principal upper set. `Set.Ioi` as an upper set. -/
nonrec def Ioi (a : α) : UpperSet α :=
  ⟨Ioi a, isUpperSet_Ioi a⟩

@[simp]
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl

@[simp]
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl

@[simp]
theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b :=
  Iff.rfl

@[simp]
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by
  ext
  simp

@[simp]
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by
  ext
  simp

theorem Ici_le_Ioi (a : α) : Ici a ≤ Ioi a :=
  Ioi_subset_Ici_self

@[simp]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[simp]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[simp] lemma Ici_ne_top : Ici a ≠ ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty
@[simp] lemma Ici_lt_top : Ici a < ⊤ := lt_top_iff_ne_top.2 Ici_ne_top
@[simp] lemma le_Ici : s ≤ Ici a ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.upper.Ici_subset ha⟩

variable (α) in
theorem Ici_strictMono : StrictMono (Ici (α := α)) := fun _ _ h ↦ (Set.Ici_ssubset_Ici).mpr h

variable (α) in
theorem Ioi_strictMono : StrictMono (Ioi (α := α)) := fun _ _ h ↦ Set.Ioi_ssubset_Ioi h

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

nonrec lemma Ici_injective : Injective (Ici : α → UpperSet α) := fun _a _b hab ↦
  Ici_injective <| congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

lemma Ici_ne_Ici : Ici a ≠ Ici b ↔ a ≠ b := Ici_inj.not

@[simp]
theorem Ioi_eq_top [OrderTop α] {a : α} : Ioi a = ⊤ ↔ a = ⊤ := by
  simp [UpperSet.ext_iff]

end PartialOrder

@[simp]
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a ∈ S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[simp]
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorder

variable [Preorder α] [Preorder β] {s : LowerSet α} {a b : α}

/-- Principal lower set. `Set.Iic` as a lower set. The smallest lower set containing a given
element. -/
nonrec def Iic (a : α) : LowerSet α :=
  ⟨Iic a, isLowerSet_Iic a⟩

/-- Strict principal lower set. `Set.Iio` as a lower set. -/
nonrec def Iio (a : α) : LowerSet α :=
  ⟨Iio a, isLowerSet_Iio a⟩

@[simp]
theorem coe_Iic (a : α) : ↑(Iic a) = Set.Iic a :=
  rfl

@[simp]
theorem coe_Iio (a : α) : ↑(Iio a) = Set.Iio a :=
  rfl

@[simp]
theorem mem_Iic_iff : b ∈ Iic a ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem mem_Iio_iff : b ∈ Iio a ↔ b < a :=
  Iff.rfl

@[simp]
theorem map_Iic (f : α ≃o β) (a : α) : map f (Iic a) = Iic (f a) := by
  ext
  simp

@[simp]
theorem map_Iio (f : α ≃o β) (a : α) : map f (Iio a) = Iio (f a) := by
  ext
  simp

theorem Ioi_le_Ici (a : α) : Ioi a ≤ Ici a :=
  Ioi_subset_Ici_self

@[simp]
nonrec theorem Iic_top [OrderTop α] : Iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top

@[simp]
nonrec theorem Iio_bot [OrderBot α] : Iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot

@[simp] lemma Iic_ne_bot : Iic a ≠ ⊥ := SetLike.coe_ne_coe.1 nonempty_Iic.ne_empty
@[simp] lemma bot_lt_Iic : ⊥ < Iic a := bot_lt_iff_ne_bot.2 Iic_ne_bot
@[simp] lemma Iic_le : Iic a ≤ s ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.lower.Iic_subset ha⟩

variable (α) in
theorem Iic_strictMono : StrictMono (Iic (α := α)) := fun _ _ h ↦ (Set.Iic_ssubset_Iic).mpr h

variable (α) in
theorem Iio_strictMono : StrictMono (Iio (α := α)) := fun _ _ h ↦ Set.Iio_ssubset_Iio h

end Preorder

section PartialOrder
variable [PartialOrder α] {a b : α}

nonrec lemma Iic_injective : Injective (Iic : α → LowerSet α) := fun _a _b hab ↦
  Iic_injective <| congr_arg ((↑) : _ → Set α) hab

@[simp] lemma Iic_inj : Iic a = Iic b ↔ a = b := Iic_injective.eq_iff

lemma Iic_ne_Iic : Iic a ≠ Iic b ↔ a ≠ b := Iic_inj.not

@[simp]
theorem Iio_eq_bot [OrderBot α] {a : α} : Iio a = ⊥ ↔ a = ⊥ := by
  simp [LowerSet.ext_iff]

end PartialOrder

@[simp]
theorem Iic_inf [SemilatticeInf α] (a b : α) : Iic (a ⊓ b) = Iic a ⊓ Iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Iic_sInf (S : Set α) : Iic (sInf S) = ⨅ a ∈ S, Iic a :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_iInf₂_iff, le_sInf_iff]

@[simp]
theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⨅ i, Iic (f i) :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_iInf_iff, le_iInf_iff]

theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⨅ (i) (j), Iic (f i j) := by
  simp

end CompleteLattice

end LowerSet
