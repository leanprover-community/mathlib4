/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Principal upper/lower sets

The results in this file all assume that the underlying type is equipped with at least a preorder.

## Main declarations

* `UpperSet.Ici`: Principal upper set. `Set.Ici` as an upper set.
* `UpperSet.Ioi`: Strict principal upper set. `Set.Ioi` as an upper set.
* `LowerSet.Iic`: Principal lower set. `Set.Iic` as a lower set.
* `LowerSet.Iio`: Strict principal lower set. `Set.Iio` as a lower set.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Function Set

variable {α β : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- Principal upper set. `Set.Ici` as an upper set. The smallest upper set containing a given
element. -/
@[to_dual
/-- Principal lower set. `Set.Iic` as a lower set. The smallest lower set containing a given
element. -/]
def Ici (a : α) : UpperSet α :=
  ⟨Set.Ici a, isUpperSet_Ici a⟩

/-- Strict principal upper set. `Set.Ioi` as an upper set. -/
@[to_dual
/-- Strict principal lower set. `Set.Iio` as a lower set. -/]
def Ioi (a : α) : UpperSet α :=
  ⟨Set.Ioi a, isUpperSet_Ioi a⟩

@[to_dual (attr := simp)]
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl

@[to_dual (attr := simp)]
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl

@[to_dual (attr := simp)]
theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by
  ext
  simp

@[to_dual (attr := simp)]
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by
  ext
  simp

@[to_dual Ioi_le_Ici]
theorem Ici_le_Ioi (a : α) : Ici a ≤ Ioi a :=
  Ioi_subset_Ici_self

@[to_dual (attr := simp)]
nonrec theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

@[to_dual (attr := simp)]
nonrec theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[to_dual (attr := simp)]
lemma Ici_ne_top : Ici a ≠ ⊤ := SetLike.coe_ne_coe.1 nonempty_Ici.ne_empty

@[to_dual (attr := simp) bot_lt_Iic]
lemma Ici_lt_top : Ici a < ⊤ := lt_top_iff_ne_top.2 Ici_ne_top

@[to_dual (attr := simp) Iic_le]
lemma le_Ici : s ≤ Ici a ↔ a ∈ s := ⟨fun h ↦ h le_rfl, fun ha ↦ s.upper.Ici_subset ha⟩

variable (α) in
@[to_dual]
theorem Ici_strictMono : StrictMono (Ici (α := α)) := fun _ _ h ↦ (Set.Ici_ssubset_Ici).mpr h

variable (α) in
@[to_dual]
theorem Ioi_strictMono : StrictMono (Ioi (α := α)) := fun _ _ h ↦ Set.Ioi_ssubset_Ioi h

end Preorder

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual]
lemma Ici_injective : Injective (Ici : α → UpperSet α) := fun _a _b hab ↦
  Set.Ici_injective <| congr_arg ((↑) : _ → Set α) hab

@[to_dual (attr := simp)]
lemma Ici_inj : Ici a = Ici b ↔ a = b := Ici_injective.eq_iff

@[to_dual]
lemma Ici_ne_Ici : Ici a ≠ Ici b ↔ a ≠ b := Ici_inj.not

@[to_dual (attr := simp)]
theorem Ioi_eq_top [OrderTop α] {a : α} : Ioi a = ⊤ ↔ a = ⊤ := by
  simp [UpperSet.ext_iff]

end PartialOrder

@[to_dual (attr := simp)]
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm

section CompleteLattice

variable [CompleteLattice α]

@[to_dual (attr := simp)]
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a ∈ S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, sSup_le_iff]

@[to_dual (attr := simp)]
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_iSup_iff, iSup_le_iff]

@[to_dual]
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp

end CompleteLattice

end UpperSet
