/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.FinsetOps

/-!
# Lattice structure on finite sets

This file puts a lattice structure on finite sets using the union and intersection operators.

For `Finset α`, where `α` is a lattice, see also `Mathlib/Data/Finset/Lattice/Fold.lean`.

## Main declarations

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`Mathlib/Order/Lattice.lean`. For the lattice structure on finsets, `⊥` is called `bot` with
`⊥ = ∅` and `⊤` is called `top` with `⊤ = univ`.

* `Finset.instHasSubset`: Lots of API about lattices, otherwise behaves as one would expect.
* `Finset.instUnion`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `Finset.sup`/`Finset.biUnion` for finite unions.
* `Finset.instInter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `Finset.inf` for finite intersections.

## Implementation Notes

All the theorems and instances expect `DecidableEq` instance for `α`

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a : α}

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : Union (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : Inter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

instance : Lattice (Finset α) :=
  { Finset.partialOrder with
    sup := (· ∪ ·)
    sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
    le_sup_left := fun _ _ _ h => mem_ndunion.2 <| Or.inl h
    le_sup_right := fun _ _ _ h => mem_ndunion.2 <| Or.inr h
    inf := (· ∩ ·)
    le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
    inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
    inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2 }

@[simp]
theorem sup_eq_union' : (Max.max : Finset α → Finset α → Finset α) = Union.union :=
  rfl

@[grind =]
theorem sup_eq_union {s t : Finset α} : s ⊔ t = s ∪ t :=
  rfl

@[simp]
theorem inf_eq_inter' : (Min.min : Finset α → Finset α → Finset α) = Inter.inter :=
  rfl

@[grind =]
theorem inf_eq_inter {s t : Finset α} : s ⊓ t = s ∩ t :=
  rfl

/-! #### union -/

theorem union_val_nd (s t : Finset α) : (s ∪ t).1 = ndunion s.1 t.1 :=
  rfl

@[simp]
theorem union_val (s t : Finset α) : (s ∪ t).1 = s.1 ∪ t.1 :=
  ndunion_eq_union s.2

@[simp, grind =]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  mem_ndunion

theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inl h

theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inr h

theorem forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a := by
  grind

theorem notMem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or]

@[simp, norm_cast]
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext fun _ => mem_union

theorem union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u :=
  sup_le <| le_iff_subset.2 hs

@[simp] lemma subset_union_left : s₁ ⊆ s₁ ∪ s₂ := fun _ ↦ mem_union_left _
@[simp] lemma subset_union_right : s₂ ⊆ s₁ ∪ s₂ := fun _ ↦ mem_union_right _

@[gcongr]
theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup (le_iff_subset.2 hsu) htv

theorem union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl

theorem union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h

theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := sup_comm _ _

instance : Std.Commutative (α := Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc _ _ _

instance : Std.Associative (α := Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s := sup_idem _

instance : Std.IdempotentOp (α := Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  subset_union_left.trans h

theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans subset_union_right h

theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]

theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by simp only [mem_union, or_assoc, @or_comm (x ∈ t)]

theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s

@[simp] lemma union_eq_left : s ∪ t = s ↔ t ⊆ s := sup_eq_left

@[simp] lemma left_eq_union : s = s ∪ t ↔ t ⊆ s := by rw [eq_comm, union_eq_left]

@[simp] lemma union_eq_right : s ∪ t = t ↔ s ⊆ t := sup_eq_right

@[simp] lemma right_eq_union : s = t ∪ s ↔ t ⊆ s := by rw [eq_comm, union_eq_right]

theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right

theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl

@[simp]
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2

@[simp, grind =]
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2

@[simp] lemma inter_subset_left : s₁ ∩ s₂ ⊆ s₁ := fun _ ↦ mem_of_mem_inter_left
@[simp] lemma inter_subset_right : s₁ ∩ s₂ ⊆ s₂ := fun _ ↦ mem_of_mem_inter_right

theorem subset_inter {s₁ s₂ u : Finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u := by grind

@[simp, norm_cast]
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter

@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by grind

@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by grind

theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by grind

@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by grind

theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) := by grind

theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ := by grind

@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_self_iff

@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]

@[mono, gcongr]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t := by grind

theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h

theorem inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter h Subset.rfl

theorem inter_subset_union : s ∩ t ⊆ s ∪ t :=
  le_iff_subset.1 inf_le_sup

instance : DistribLattice (Finset α) :=
  { le_sup_inf := fun a b c => by
      simp +contextual only
        [sup_eq_union, inf_eq_inter, le_eq_subset, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or, imp_true_iff, true_and, or_true] }

@[simp]
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem _ _

theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem _ _

@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem _ _

theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem _ _

theorem inter_union_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left _ _ _

theorem union_inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right _ _ _

theorem union_inter_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left _ _ _

theorem inter_union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right _ _ _

theorem union_union_distrib_left (s t u : Finset α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _

theorem union_union_distrib_right (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _

theorem inter_inter_distrib_left (s t u : Finset α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _

theorem inter_inter_distrib_right (s t u : Finset α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _

theorem union_union_union_comm (s t u v : Finset α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _

theorem inter_inter_inter_comm (s t u v : Finset α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _

theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)

theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)

@[simp] lemma inter_eq_left : s ∩ t = s ↔ s ⊆ t := inf_eq_left

@[simp] lemma inter_eq_right : t ∩ s = s ↔ s ⊆ t := inf_eq_right

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right

theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' ⊆ s ∪ s' :=
  ite_le_sup s s' P

theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s ∩ s' ⊆ ite P s s' :=
  inf_le_ite s s' P

end Lattice

end Finset
