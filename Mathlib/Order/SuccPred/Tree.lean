/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/

import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Atoms
import Mathlib.Data.SetLike.Basic

/-!
# Rooted trees

This file proves basic results about rooted trees, represented using the ancestorship order.
This is a `PartialOrder`, with `PredOrder` with the immediate parent as a predecessor, and an
`OrderBot` which is the root. We also have an `IsPredArchimedean` assumption to prevent infinite
dangling chains.

--/

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]

namespace IsPredArchimedean

lemma le_total_of_le {r v₁ v₂ : α} (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_pred_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_pred_iterate
  clear h₁ h₂
  wlog h : n ≤ m
  · rw [Or.comm]
    apply this
    omega
  right
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add, Function.comp_apply]
  apply Order.pred_iterate_le

lemma lt_or_le_of_le {r v₁ v₂ : α} (h₁ : v₁ ≤ r) (h₂ : v₂ ≤ r) :
    v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_le h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

variable [OrderBot α]

section DecidableEq

variable [DecidableEq α]

/--
The unique atom less than an element in an `OrderBot` with archimedean predecessor.
-/
def find_atom (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

@[simp]
lemma find_atom_le (r : α) : find_atom r ≤ r :=
  Order.pred_iterate_le _ _

@[simp]
lemma find_atom_bot : find_atom (⊥ : α) = ⊥ := by
  apply Function.iterate_fixed
  simp

@[simp]
lemma pred_find_atom (r : α) : Order.pred (find_atom r) = ⊥ := by
  unfold find_atom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [Nat.add_sub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [← h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

lemma find_atom_ne_bot {r : α} (hr : r ≠ ⊥) :
    find_atom r ≠ ⊥ := by
  unfold find_atom
  intro nh
  have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate nh
  replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by omega
  simp [this, hr] at nh

@[simp]
lemma find_atom_eq_bot_iff {r : α} :
    find_atom r = ⊥ ↔ r = ⊥ where
  mp h := by_contra fun nh ↦ find_atom_ne_bot nh h
  mpr h := by simp [h]

@[simp]
lemma find_atom_is_atom (r : α) (hr : r ≠ ⊥) :
    IsAtom (find_atom r) := by
  constructor
  · simp [hr]
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb

end DecidableEq

instance instIsAtomic : IsAtomic α where
  eq_bot_or_exists_atom_le b := by classical
    rw [Classical.or_iff_not_imp_left]
    intro hb
    use find_atom b, find_atom_is_atom b hb, find_atom_le b

end IsPredArchimedean

/--
The type of rooted trees.
-/
structure RootedTree where
  /-- The type representing the elements in the tree. -/
  α : Type*
  /-- The type should be a `SemilatticeInf`, where `inf` is LCA in the tree. -/
  [order : SemilatticeInf α]
  /-- The type should have a bottom, the root. -/
  [bot : OrderBot α]
  /-- The type should have a predecessor for every element, its parent. -/
  [pred : PredOrder α]
  /-- The predecessor relationship should be archimedean. -/
  [pred_archimedean : IsPredArchimedean α]

attribute [coe] RootedTree.α

instance coeSort : CoeSort RootedTree (Type*) := ⟨RootedTree.α⟩


instance (t : RootedTree) : SemilatticeInf t := t.order
instance (t : RootedTree) : PredOrder t := t.pred
instance (t : RootedTree) : OrderBot t := t.bot
instance (t : RootedTree) : IsPredArchimedean t := t.pred_archimedean

/--
A subtree is represented by its root, therefore this is a type synonym.
-/
def SubRootedTree (t : RootedTree) : Type* := t

/--
The root of a `SubRootedTree`.
-/
def SubRootedTree.root {t : RootedTree} (v : SubRootedTree t) : t := v

/--
The `SubRootedTree` rooted at a given node.
-/
def RootedTree.subtree (t : RootedTree) (r : t) : SubRootedTree t := r


@[simp]
lemma RootedTree.root_subtree (t : RootedTree) (r : t) : (t.subtree r).root = r := rfl

@[simp]
lemma RootedTree.subtree_root (t : RootedTree) (v : SubRootedTree t) : t.subtree v.root = v := rfl

@[ext]
lemma SubRootedTree.ext {t : RootedTree} (v₁ v₂ : SubRootedTree t)
    (h : v₁.root = v₂.root) : v₁ = v₂ := h

instance (t : RootedTree) : SetLike (SubRootedTree t) t where
  coe v := Set.Ici v.root
  coe_injective' a₁ a₂ h := by
    simpa only [Set.Ici_inj, ← SubRootedTree.ext_iff] using h

lemma mem_iff {t : RootedTree} {r : SubRootedTree t} {v : t} :
    v ∈ r ↔ r.root ≤ v := Iff.rfl

/--
The coersion from a `SubRootedTree` to a `RootedTree`.
-/
@[coe, reducible]
noncomputable def coeTree {t : RootedTree} (r : SubRootedTree t) : RootedTree where
  α := r
  pred := inferInstanceAs (PredOrder (Set.Ici r.root))

noncomputable instance (t : RootedTree) : CoeOut (SubRootedTree t) RootedTree :=
  ⟨coeTree⟩

@[simp]
lemma bot_mem_iff {t : RootedTree} (r : SubRootedTree t) :
    ⊥ ∈ r ↔ r.root = ⊥ := by
  simp [mem_iff]

/--
All of the immediate subtrees of a given rooted tree.
-/
def RootedTree.subtrees (t : RootedTree) : Set (SubRootedTree t) :=
  {x | IsAtom x.root}

variable {t : RootedTree}

lemma root_ne_bot_of_mem_subtrees (r : SubRootedTree t) (hr : r ∈ t.subtrees) :
    r.root ≠ ⊥ := by
  simp only [RootedTree.subtrees, Set.mem_setOf_eq] at hr
  exact hr.1

lemma subtrees_inf_eq_bot_iff {t₁ t₂ : SubRootedTree t}
    (ht₁ : t₁ ∈ t.subtrees) (ht₂ : t₂ ∈ t.subtrees) (v₁ v₂ : t) (h₁ : v₁ ∈ t₁)
    (h₂ : v₂ ∈ t₂) :
    v₁ ⊓ v₂ = ⊥ ↔ t₁ ≠ t₂ where
  mp h := by
    intro nh
    have : t₁.root ≤ (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h] at this
    simp only [le_bot_iff] at this
    exact root_ne_bot_of_mem_subtrees t₁ ht₁ this
  mpr h := by
    rw [mem_iff] at h₁ h₂
    contrapose! h
    rw [← bot_lt_iff_ne_bot] at h
    rcases IsPredArchimedean.lt_or_le_of_le (by simp : v₁ ⊓ v₂ ≤ v₁) h₁ with oh | oh
    · simp_all [RootedTree.subtrees, IsAtom.lt_iff]
    rw [le_inf_iff] at oh
    have := IsPredArchimedean.le_total_of_le oh.2 h₂
    simp only [ht₂.le_iff_eq ht₁.1, ht₁.le_iff_eq ht₂.1, eq_comm, or_self] at this
    ext
    exact this

-- An alternative spelling is the contrapositive, `v ∈ t₁ → v ∈ t₂ → t₁ = t₂`. Which is better?
lemma subtrees_disjoint {t₁ t₂ : SubRootedTree t}
    (ht₁ : t₁ ∈ t.subtrees) (ht₂ : t₂ ∈ t.subtrees) (h : t₁ ≠ t₂) :
    Disjoint (t₁ : Set t) (t₂ : Set t) := by
  rw [Set.disjoint_left]
  intro a ha hb
  rw [← subtrees_inf_eq_bot_iff ht₁ ht₂ a a ha hb] at h
  simp only [le_refl, inf_of_le_left] at h
  subst h
  simp only [SetLike.mem_coe, bot_mem_iff] at ha
  exact root_ne_bot_of_mem_subtrees t₁ ht₁ ha

/--
The subtree of `t` containing `r`, or all of `t` if `r` is the root.
-/
def RootedTree.subtreeOf (t : RootedTree) [DecidableEq t] (r : t) : SubRootedTree t :=
  t.subtree (IsPredArchimedean.find_atom r)

@[simp]
lemma RootedTree.mem_subtreeOf [DecidableEq t] {r : t} :
    r ∈ t.subtreeOf r := by
  simp [mem_iff, RootedTree.subtreeOf]

lemma RootedTree.subtreeOf_mem_subtrees [DecidableEq t] {r : t} (hr : r ≠ ⊥) :
    t.subtreeOf r ∈ t.subtrees := by
  simp [RootedTree.subtrees, RootedTree.subtreeOf, IsPredArchimedean.find_atom_is_atom r hr]
