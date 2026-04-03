/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.UpperLower.Basic

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

variable {α : Type*}

open Set

section Preorder
variable [Preorder α] {s t : Set α}

/--
A set `s` is said to be closed under directed joins if, whenever a directed set `d` has a least
upper bound `a` and is a subset of `s` then `a` also lies in `s`.
-/
def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A set `s` is said to be inaccessible by directed joins on `D` if, when the least upper bound of
a directed set `d` in `D` lies in `s` then `d` has non-empty intersection with `s`. -/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/-- A set `s` is said to be inaccessible by directed joins if, when the least upper bound of a
directed set `d` lies in `s` then `d` has non-empty intersection with `s`. -/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]

@[simp] lemma DirSupInacc.dirSupInaccOn {D : Set (Set α)} :
    DirSupInacc s → DirSupInaccOn D s := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

lemma DirSupInaccOn.mono {D₁ D₂ : Set (Set α)} (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) :
    DirSupInaccOn D₁ s := fun _ a ↦ hf (hD a)

@[simp] lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  simp [DirSupInacc, ← not_disjoint_iff_nonempty_inter, disjoint_compl_right_iff, not_imp_not]
  tauto

@[simp] lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupInacc_compl, compl_compl]

alias ⟨DirSupInacc.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl
alias ⟨DirSupClosed.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl

lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∩ t) :=
  fun _d hds hd hd' _a ha ↦
    ⟨hs (hds.trans inter_subset_left) hd hd' ha, ht (hds.trans inter_subset_right) hd hd' ha⟩

lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  rw [← dirSupClosed_compl, compl_union]; exact hs.compl.inter ht.compl

lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
  fun _d hds ⟨_b, hb⟩ _ _a ha ↦ hs (ha.1 hb) <| hds hb

lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s := hs.compl.dirSupClosed.of_compl

lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) := fun _d h _ _ _a ha ↦ (isLUB_le_iff ha).2 h

end Preorder

section CompleteLattice
variable [CompleteLattice α] {s : Set α}

lemma dirSupClosed_iff_forall_sSup :
    DirSupClosed s ↔ ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

lemma dirSupInacc_iff_forall_sSup :
    DirSupInacc s ↔ ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

end CompleteLattice
