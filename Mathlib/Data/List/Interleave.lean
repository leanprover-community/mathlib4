/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Batteries.Data.List.Lemmas
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Unbundled

import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Simproc.ExistsAndEq
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Interleaving lists

This file defines interleaving of lists, both as an operation and as a relation.
-/

public section

namespace List
variable {α : Type*} {r s : α → α → Prop} {l l₁ l₂ l₃ l₄ : List α} {a b c : α}

/-- Interleaves two lists `l₁` and `l₂`, starting with an element of `l₁`.

This operation fully interleaves the two lists when the length of `l₁` is either the length of `l₂`
or one more. If one of the lists runs out early, the remainder of the other list is kept without
further interleaving, so that `l₁.interleave l₂` is always a permutation of `l₁ ++ l₂`.
See `interleaves_perm_append`.

```
#eval interleave [0, 2, 4] [1] -- [0, 1, 2, 4] -- The second list is too short
#eval interleave [0, 2, 4] [1, 3] -- [0, 1, 2, 3, 4]
#eval interleave [0, 2] [1, 3] -- [0, 1, 2, 3]
#eval interleave [0] [1, 3] -- [0, 1, 3] -- The first list is too short
```
-/
@[expose]
def interleave : List α → List α → List α
  | [], l₂ => l₂
  | a :: l₁, l₂ => a :: interleave l₂ l₁
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp] lemma nil_interleave (l₂ : List α) : [].interleave l₂ = l₂ := by rw [interleave]
@[simp] lemma interleave_nil (l₁ : List α) : l₁.interleave [] = l₁ := by
  cases l₁ <;> simp [interleave]

@[simp]
lemma cons_interleave (a : α) (l₁ : List α) (l₂ : List α) :
    (a :: l₁).interleave l₂ = a :: interleave l₂ l₁ := by rw [interleave]

@[simp] lemma interleaves_perm_append : ∀ {l₁ l₂ : List α}, l₁.interleave l₂ ~ l₁ ++ l₂
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    rw [cons_interleave]
    exact ((interleaves_perm_append ..).trans perm_append_comm).cons _
termination_by l₁ l₂ => l₁.length + l₂.length

protected lemma Perm.interleaves (h₁₃ : l₁ ~ l₃) (h₂₄ : l₂ ~ l₄) :
    l₁.interleave l₂ ~ l₃.interleave l₄ :=
  interleaves_perm_append.trans <| (h₁₃.append h₂₄).trans interleaves_perm_append.symm

@[simp] lemma length_interleaves (l₁ l₂ : List α) :
    (l₁.interleave l₂).length = l₁.length + l₂.length := by simp [interleaves_perm_append.length_eq]

@[simp] lemma countP_interleaves (l₁ l₂ : List α) (p : α → Bool) :
    (l₁.interleave l₂).countP p = l₁.countP p + l₂.countP p := by
  simp [interleaves_perm_append.countP_eq]

@[simp] lemma count_interleaves [BEq α] (l₁ l₂ : List α) (a : α) :
    (l₁.interleave l₂).count a = l₁.count a + l₂.count a := by
  simp [interleaves_perm_append.count_eq]

@[simp]
lemma interleave_append_append_of_length_eq_length :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length = l₂.length) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₃.interleave l₄
  | [], [], _, l₃, l₄ => by simp
  | a :: l₁, b :: l₂, _, l₃, l₄ => by simp_all [interleave_append_append_of_length_eq_length]

@[simp]
lemma interleave_append_left_of_length_eq_length (h₁₂ : l₁.length = l₂.length) (l₃ : List α) :
    (l₁ ++ l₃).interleave l₂ = l₁.interleave l₂ ++ l₃.interleave [] := by
  simpa using interleave_append_append_of_length_eq_length h₁₂ _ []

@[simp]
lemma interleave_append_right_of_length_eq_length (h₁₂ : l₁.length = l₂.length) (l₃ : List α) :
    l₁.interleave (l₂ ++ l₃) = l₁.interleave l₂ ++ [].interleave l₃ := by
  simpa using interleave_append_append_of_length_eq_length h₁₂ [] _

@[simp]
lemma interleave_append_append_of_length_eq_length_add_one :
    ∀ {l₁ l₂ : List α} (_h₁₂ : l₁.length = l₂.length + 1) (l₃ l₄ : List α),
      (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₄.interleave l₃
  | a :: l₁, l₂, _, l₃, l₄ => by simp_all

@[simp]
lemma interleave_append_left_of_length_eq_length_add_one (h₁₂ : l₁.length = l₂.length + 1)
    (l₃ : List α) : (l₁ ++ l₃).interleave l₂ = l₁.interleave l₂ ++ [].interleave l₃ := by
  simpa using interleave_append_append_of_length_eq_length_add_one h₁₂ _ []

@[simp]
lemma interleave_append_right_of_length_eq_length_add_one (h₁₂ : l₁.length = l₂.length + 1)
    (l₃ : List α) : l₁.interleave (l₂ ++ l₃) = l₁.interleave l₂ ++ l₃.interleave [] := by
  simpa using interleave_append_append_of_length_eq_length_add_one h₁₂ [] _

@[simp]
lemma reverse_interleave_of_length_eq_length :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
      (l₁.interleave l₂).reverse = l₂.reverse.interleave l₁.reverse
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleave_of_length_eq_length]

@[simp]
lemma reverse_interleave_of_length_eq_length_add_one :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length + 1 →
      (l₁.interleave l₂).reverse = l₁.reverse.interleave l₂.reverse
  | a :: l₁, [], _ => by simp
  | a :: l₁, b :: l₂, _ => by simp_all [reverse_interleave_of_length_eq_length_add_one]

@[simp]
lemma interleave_ofFn_ofFn :
    ∀ {n : ℕ} {f g : Fin n → α},
      interleave (ofFn f) (ofFn g) =
        ofFn (n := 2 * n) (fun i ↦ if i.val % 2 = 0 then f ⟨i / 2, by lia⟩ else g ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by simp_all [interleave_ofFn_ofFn]; grind

lemma interleave_ofFn_ofFn' :
    ∀ {n : ℕ} {f : Fin (n + 1) → α} {g : Fin n → α},
      interleave (ofFn f) (ofFn g) =
        ofFn (n := 2 * n + 1)
          (fun i ↦ if hi : i.val % 2 = 0 then f ⟨i / 2, by lia⟩ else g ⟨i / 2, by lia⟩)
  | 0, f, g  => by simp
  | n + 1, f, g => by simp_all [interleave_ofFn_ofFn]; grind

@[simp]
lemma right_sublist_interleave : ∀ {l₁ l₂ : List α}, l₂.length ≤ l₁.length → l₂ <+ l₁.interleave l₂
  | _, [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [cons_interleave]
    exact .cons _ <| .cons_cons _ <| right_sublist_interleave <| by simpa using h

@[simp]
lemma left_sublist_interleave {l₁ l₂ : List α} (hl : l₁.length ≤ l₂.length + 1) :
    l₁ <+ l₁.interleave l₂ := by cases l₁ <;> simp_all

variable (r) in
/-- Relation for interleaving lists. `l₁` `r`-interleaves `l₂` if the length of `l₂` is either the
length of `l₁` or one more and if the `i`-th rightmost element of `l₁` is `r`-related to both the
`i`-th and `i + 1`-st rightmost elements of `l₂`, except possibly when `i = l₁.length`.

For example, `[1, 3]` `(· ≥ ·)`-interleaves `[0, 2, 4]`.

See `interleaves_iff_length_isChain_interleave` for the connection with `List.interleave`. -/
@[mk_iff]
inductive Interleaves : List α → List α → Prop
  /-- The empty list interleaves itself. -/
  | nil_nil : Interleaves [] []
  /-- The empty list interleaves any singleton list. -/
  | nil_singleton (a : α) : Interleaves [] [a]
  /-- If `l₁` interleaves `b :: l₂` and `a` is related to `b`, then `b :: l₂` interleaves
  `a :: l₁`. -/
  | cons_symm ⦃l₁ l₂ : List α⦄ ⦃b : α⦄ (hl : Interleaves l₁ (b :: l₂)) ⦃a : α⦄ (hab : r a b) :
      Interleaves (b :: l₂) (a :: l₁)

attribute [simp] Interleaves.nil_nil
attribute [simp high] Interleaves.nil_singleton

@[simp]
lemma interleaves_nil_cons : Interleaves r [] (a :: l) ↔ l = [] := by grind [interleaves_iff]

@[simp]
lemma not_interleaves_cons_nil : ¬ Interleaves r (a :: l) [] := by grind [interleaves_iff]

@[simp]
lemma interleaves_cons_cons :
    Interleaves r (a :: l₁) (b :: l₂) ↔ r b a ∧ Interleaves r l₂ (a :: l₁) := by
  grind [interleaves_iff]

@[simp high]
lemma interleaves_singleton_singleton : Interleaves r [a] [b] ↔ r b a := by simp

@[gcongr]
lemma Interleaves.mono (hrs : ∀ ⦃a b⦄, r a b → s a b) :
    ∀ l₁ l₂ : List α, Interleaves r l₁ l₂ → Interleaves s l₁ l₂
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton _
  | _, _, .cons_symm hl hab => .cons_symm (hl.mono hrs) <| hrs hab

lemma interleaves_iff_length_isChain_interleave :
    ∀ {l₁ l₂ : List α},
    Interleaves r l₁ l₂ ↔
      (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) ∧ (l₂.interleave l₁).IsChain r
  | [], [] => by simp
  | [], b :: l₂ => by simp +contextual
  | a :: l₁, [] => by simp
  | a :: l₁, [b] => by rw [interleaves_iff]; simp +contextual
  | a :: l₁, b :: l₂ => by
    rw [interleaves_iff]
    simp [interleaves_iff_length_isChain_interleave (l₁ := l₂) (l₂ := a :: l₁), or_comm, eq_comm,
      and_comm, and_assoc]
termination_by l₁ l₂ => l₁.length + l₂.length

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_eq_length
    (h : l₁.length = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r b a ∧ Interleaves r l₁ (l₂ ++ [b]) := by
  simp [interleaves_iff_length_isChain_interleave, and_comm, *]

@[simp]
lemma interleaves_append_singleton_append_singleton_of_length_eq_length_add_one
    (h : l₁.length + 1 = l₂.length) :
    Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r a b ∧ Interleaves r (l₁ ++ [a]) l₂ := by
  simp [interleaves_iff_length_isChain_interleave, and_comm, *]

lemma interleaves_reverse_reverse_of_length_eq_length (h : l₁.length = l₂.length) :
    Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (Function.swap r) l₂ l₁ := by
  simp [interleaves_iff_length_isChain_interleave, ← reverse_interleave_of_length_eq_length,
    isChain_reverse, *]

lemma interleaves_reverse_reverse_of_length_eq_length_add_one (h : l₁.length + 1 = l₂.length) :
    Interleaves r l₁.reverse l₂.reverse ↔ Interleaves (fun a b ↦ r b a) l₁ l₂ := by
  simp [interleaves_iff_length_isChain_interleave, ← reverse_interleave_of_length_eq_length_add_one,
    isChain_reverse, *]

lemma interleaves_ofFn {n : ℕ} {f g : Fin n → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i, r (g i) (f i)) ∧ ∀ (i : ℕ) (hi : i + 1 < n), r (f ⟨i, by lia⟩) (g ⟨i + 1, hi⟩) := by
  simp only [interleaves_iff_length_isChain_interleave, length_ofFn, Nat.succ_ne_self, or_false,
    interleave_ofFn_ofFn, isChain_ofFn, true_and]
  refine ⟨fun h ↦ ?_, by grind⟩
  exact ⟨fun i ↦ by have := h (2 * i); grind, fun i hi ↦ by have := h (2 * i + 1); grind⟩

lemma interleaves_ofFn' {n : ℕ} {f : Fin n → α} {g : Fin (n + 1) → α} :
    Interleaves r (ofFn f) (ofFn g) ↔
      (∀ i : Fin n, r (f i) (g i.succ)) ∧ ∀ i : Fin n, r (g i.castSucc) (f i) := by
  simp only [interleaves_iff_length_isChain_interleave, length_ofFn, Nat.left_eq_add,
    interleave_ofFn_ofFn', isChain_ofFn, Nat.succ_ne_self, or_true, true_and]
  -- FIXME: Why doesn't `grind unfold these?
  unfold Fin.castSucc Fin.castAdd Fin.castLE
  refine ⟨fun h ↦ ?_, fun h i hi ↦ by grind⟩
  exact ⟨fun i ↦ by have := h (2 * i + 1); grind, fun i ↦ by have := h (2 * i); grind⟩

variable [IsTrans α r]

lemma Interleaves.pairwise_left (hl : Interleaves r l₁ l₂) : l₁.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist <| right_sublist_interleave <| by lia

lemma Interleaves.pairwise_right (hl : Interleaves r l₁ l₂) : l₂.Pairwise r := by
  rw [interleaves_iff_length_isChain_interleave] at hl
  exact hl.2.pairwise.sublist <| left_sublist_interleave <| by lia

end List
