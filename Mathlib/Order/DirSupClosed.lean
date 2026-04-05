/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.UpperLower.Basic

import Mathlib.Data.Set.Lattice

/-!
# Sets closed under directed suprema

We say that a set `s` is closed under directed suprema whenever it contains all least upper bounds
for nonempty, directed subsets. Conversely, a set `s` is inaccessible by directed suprema whenever
its complement is closed under directed suprema. Equivalently, if the least upper bound of a
nonempty directed set `t` is contained in `s`, then `t` and `s` must have nonempty intersection.

## Main definitions

- `DirSupClosed`: sets closed under directed suprema.
- `DirSupInacc`: sets inaccessible by directed suprema.
-/

@[expose] public section

variable {α : Type*} {s t : Set α} {D D₁ D₂ : Set (Set α)}

open Set

section Preorder
variable [Preorder α]

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInaccOn` set. -/
def DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets in `D`.
This is the complement of a `DirSupClosedOn` set. -/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInacc` set. -/
def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets.
This is the complement of a `DirSupClosed` set. -/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

@[simp] lemma dirSupClosedOn_univ : DirSupClosedOn univ s ↔ DirSupClosed s := by
  simp [DirSupClosedOn, DirSupClosed]

@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]

@[simp] lemma DirSupClosed.dirSupClosedOn : DirSupClosed s → DirSupClosedOn D s := @fun h _ _ ↦ @h _
@[simp] lemma DirSupInacc.dirSupInaccOn : DirSupInacc s → DirSupInaccOn D s := @fun h _ _ ↦ @h _

@[simp]
theorem DirSupClosed.of_isEmpty [IsEmpty α] (s : Set α) : DirSupClosed s :=
  fun _ _ ⟨a, _⟩ ↦ isEmptyElim a

@[simp]
theorem DirSupClosedOn.of_isEmpty [IsEmpty α] (s : Set α) : DirSupClosedOn D s := by
  simp

@[simp]
theorem DirSupInacc.of_isEmpty [IsEmpty α] (s : Set α) : DirSupInacc s :=
  fun _ ⟨a, _⟩ ↦ isEmptyElim a

@[simp]
theorem DirSupInaccOn.of_isEmpty [IsEmpty α] (s : Set α) : DirSupInaccOn D s := by
  simp

@[gcongr]
lemma DirSupClosedOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupClosedOn D₂ s) : DirSupClosedOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[gcongr]
lemma DirSupInaccOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) : DirSupInaccOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[simp]
lemma dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s := by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]
lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupClosedOn_univ, dirSupClosedOn_compl, dirSupInaccOn_univ]

@[simp]
lemma dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s := by
  rw [← dirSupClosedOn_compl, compl_compl]

@[simp]
lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  rw [← dirSupClosed_compl, compl_compl]

alias ⟨DirSupClosedOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupInaccOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupClosed.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupInacc.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl

@[simp] theorem DirSupClosed.empty : DirSupClosed (∅ : Set α) := by simp [DirSupClosed]
@[simp] theorem DirSupInacc.empty : DirSupInacc (∅ : Set α) := by simp [DirSupInacc]
theorem DirSupClosedOn.empty : DirSupClosedOn D ∅ := by simp
theorem DirSupInaccOn.empty : DirSupInaccOn D ∅ := by simp

@[simp] theorem DirSupClosed.univ : DirSupClosed (univ : Set α) := by simp [DirSupClosed]
@[simp] theorem DirSupInacc.univ : DirSupInacc (univ : Set α) := by simp [← compl_empty]
theorem DirSupClosedOn.univ : DirSupClosedOn D univ := by simp
theorem DirSupInaccOn.univ : DirSupInaccOn D univ := by simp

theorem DirSupClosedOn.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosedOn D x) :
    DirSupClosedOn D (⋂₀ s) :=
  fun _d hD hds hd hd' _a ha t ht ↦ hs t ht hD (hds.trans fun _x hx ↦ hx _ ht) hd hd' ha

theorem DirSupClosed.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosed x) :
    DirSupClosed (⋂₀ s) := by
  simpa using DirSupClosedOn.sInter fun x hx ↦ (hs x hx).dirSupClosedOn (D := .univ)

theorem DirSupInaccOn.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInaccOn D x) :
    DirSupInaccOn D (⋃₀ s) := by
  rw [← dirSupClosedOn_compl, Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl

theorem DirSupInacc.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInacc x) :
    DirSupInacc (⋃₀ s) := by
  simpa using DirSupInaccOn.sUnion fun x hx ↦ (hs x hx).dirSupInaccOn (D := .univ)

theorem DirSupClosedOn.iInter {ι} {f : ι → Set α} (hs : ∀ i, DirSupClosedOn D (f i)) :
    DirSupClosedOn D (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosedOn.sInter (by simpa)

theorem DirSupClosed.iInter {ι} {f : ι → Set α} (hs : ∀ i, DirSupClosed (f i)) :
    DirSupClosed (⋂ i, f i) := by
  rw [← sInter_range f]
  exact DirSupClosed.sInter (by simpa)

theorem DirSupInaccOn.iUnion {ι} {f : ι → Set α} (hs : ∀ i, DirSupInaccOn D (f i)) :
    DirSupInaccOn D (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInaccOn.sUnion (by simpa)

theorem DirSupInacc.iUnion {ι} {f : ι → Set α} (hs : ∀ i, DirSupInacc (f i)) :
    DirSupInacc (⋃ i, f i) := by
  rw [← sUnion_range f]
  exact DirSupInacc.sUnion (by simpa)

lemma DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) :
    DirSupClosedOn D (s ∩ t) := by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]

lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∩ t) := by
  simpa using hs.dirSupClosedOn.inter ht.dirSupClosedOn (D := .univ)

lemma DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) :
    DirSupInaccOn D (s ∪ t) := by
  rw [← dirSupClosedOn_compl, compl_union]; exact hs.compl.inter ht.compl

lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  simpa using hs.dirSupInaccOn.union ht.dirSupInaccOn (D := .univ)

lemma IsUpperSet.dirSupClosedOn (hs : IsUpperSet s) : DirSupClosedOn D s :=
  fun _d _ hds ⟨_b, hb⟩ _ _a ha ↦ hs (ha.1 hb) <| hds hb

lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
  by simpa using hs.dirSupClosedOn (D := univ)

lemma IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) : DirSupInaccOn D s :=
  hs.compl.dirSupClosedOn.of_compl

lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s :=
  hs.compl.dirSupClosed.of_compl

theorem isLUB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· ≤ ·) a b) :
    IsLUB s a ↔ IsLUB s b := by
  simp [isLUB_iff_le_iff, h.le_congr_left]

private theorem DirSupClosed.mem_imp_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) (ha : a ∈ s) : b ∈ s := by
  apply hs (singleton_subset_iff.2 ha) ⟨a, rfl⟩ (directedOn_singleton Std.Refl.refl a)
  rw [← isLUB_congr_of_antisymmRel h]
  exact isLUB_singleton

theorem DirSupClosed.mem_iff_of_antisymmRel (hs : DirSupClosed s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) : a ∈ s ↔ b ∈ s :=
  ⟨hs.mem_imp_of_antisymmRel h, hs.mem_imp_of_antisymmRel h.symm⟩

theorem DirSupInacc.mem_iff_of_antisymmRel (hs : DirSupInacc s) {a b : α}
    (h : AntisymmRel (· ≤ ·) a b) : a ∈ s ↔ b ∈ s := by
  simpa [not_iff_not] using hs.compl.mem_iff_of_antisymmRel h

lemma dirSupClosedOn_Iic (a : α) : DirSupClosedOn D (Iic a) :=
  fun _d _ h _ _ _a ha ↦ (isLUB_le_iff ha).2 h

lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) := by
  simpa using dirSupClosedOn_Iic a (D := .univ)

lemma dirSupInaccOn_Iic (a : α) : DirSupInaccOn D (Iic a) :=
  (isLowerSet_Iic a).dirSupInaccOn

lemma dirSupInacc_Iic (a : α) : DirSupInacc (Iic a) := by
  simpa using dirSupInaccOn_Iic a (D := .univ)

end Preorder

namespace PartialOrder
variable [PartialOrder α]

theorem dirSupClosedOn_singleton (a : α) : DirSupClosedOn D {a} := by
  intro d hD hdu hd₀ hd₁ b hb
  rw [subset_singleton_iff_eq] at hdu
  obtain rfl | rfl := hdu
  · simp at hd₀
  · exact hb.unique isLUB_singleton

theorem dirSupClosed_singleton (a : α) : DirSupClosed {a} := by
  simpa using dirSupClosedOn_singleton a (D := .univ)

end PartialOrder

section CompleteLattice
variable [CompleteLattice α]

lemma dirSupClosedOn_iff_forall_sSup : DirSupClosedOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]

lemma dirSupInaccOn_iff_forall_sSup : DirSupInaccOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]

lemma dirSupClosed_iff_forall_sSup : DirSupClosed s ↔
    ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

lemma dirSupInacc_iff_forall_sSup : DirSupInacc s ↔
    ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

end CompleteLattice
