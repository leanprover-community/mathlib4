/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Intervals as finsets

This file provides basic results about all the `Finset.Ixx`, which are defined in
`Order.Interval.Finset.Defs`.

In addition, it shows that in a locally finite order `≤` and `<` are the transitive closures of,
respectively, `⩿` and `⋖`, which then leads to a characterization of monotone and strictly
functions whose domain is a locally finite order. In particular, this file proves:

* `le_iff_transGen_wcovBy`: `≤` is the transitive closure of `⩿`
* `lt_iff_transGen_covBy`: `<` is the transitive closure of `⋖`
* `monotone_iff_forall_wcovBy`: Characterization of monotone functions
* `strictMono_iff_forall_covBy`: Characterization of strictly monotone functions

## TODO

This file was originally only about `Finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `Data.X.Intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/

@[expose] public section

assert_not_exists MonoidWithZero Finset.sum

open Function OrderDual

open scoped FinsetInterval

variable {ι α : Type*} {a a₁ a₂ b b₁ b₂ c x : α}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[to_dual self, simp]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]

@[to_dual self, aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Icc_of_le⟩ := nonempty_Icc

@[to_dual (attr := simp) (rename := a ↔ b)]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]

@[to_dual (rename := a ↔ b) (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
alias ⟨_, Aesop.nonempty_Ico_of_lt⟩ := nonempty_Ico

-- TODO: This is nonsense. A locally finite order is never densely ordered;
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[to_dual self, simp]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]

@[to_dual self, simp]
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]

@[to_dual (attr := simp) (rename := a ↔ b)]
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]

-- TODO: This is nonsense. A locally finite order is never densely ordered
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[to_dual self, simp]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]

@[to_dual self] alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff
@[to_dual (rename := a ↔ b)] alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff

@[to_dual self, simp]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[to_dual self, simp]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[to_dual (attr := simp) (rename := a ↔ b)]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[to_dual self, simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

@[to_dual (rename := a ↔ b) right_mem_Icc]
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and, le_rfl]

@[to_dual (rename := a ↔ b) right_mem_Ioc]
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico, true_and, le_refl]

@[to_dual (rename := a ↔ b) right_notMem_Ico]
theorem left_notMem_Ioc : a ∉ Ioc a b := fun h => lt_irrefl _ (mem_Ioc.1 h).1

@[to_dual (rename := a ↔ b) right_notMem_Ioo]
theorem left_notMem_Ioo : a ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).1

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb), gcongr]
theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb

@[to_dual (rename := a₁ ↔ b₁, a₂ ↔ b₂, ha ↔ hb) (reorder := ha hb) (attr := gcongr)]
theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb), gcongr]
theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Icc_subset_Icc_right]
theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Ioc_subset_Ioc_right]
theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Ico_subset_Ico_right]
theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Ioo_subset_Ioo_right]
theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Ioc_subset_Ioo_right]
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b := by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h

@[to_dual (rename := a₁ → b₂, a₂ → b₁, b → a) Icc_subset_Ico_right]
theorem Icc_subset_Ioc_left (h : a₂ < a₁) : Icc a₁ b ⊆ Ioc a₂ b := by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Icc_subset_Ioc_left h

@[to_dual (rename := a ↔ b)]
theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self

@[to_dual (rename := a ↔ b)]
theorem Ico_subset_Icc_self : Ico a b ⊆ Icc a b := by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self

@[to_dual self]
theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]
theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]

@[to_dual none]
theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]

@[to_dual none]
theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]

@[to_dual none]
theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans and_comm

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`

@[to_dual (rename := a₁ ↔ b₁, a₂ ↔ b₂, ha ↔ hb) (reorder := ha hb) Icc_ssubset_Icc_right]
theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb

@[to_dual (attr := simp)]
theorem Ioc_disjoint_Ioc_of_le {d : α} (hbc : b ≤ c) : Disjoint (Ioc a b) (Ioc c d) :=
  disjoint_left.2 fun _ h1 h2 ↦ not_and_of_not_left _
    ((mem_Ioc.1 h1).2.trans hbc).not_gt (mem_Ioc.1 h2)

@[to_dual self]
lemma _root_.not_lt_of_denselyOrdered_of_locallyFinite [DenselyOrdered α] (a b : α) :
    ¬ a < b := by
  intro h
  induction hs : Finset.Icc a b using Finset.strongInduction generalizing b with | H i ih
  subst hs
  obtain ⟨c, hac, hcb⟩ := exists_between h
  refine ih _ ?_ c hac rfl
  exact Finset.Icc_ssubset_Icc_right (hac.trans hcb).le le_rfl hcb

variable (a)

@[to_dual]
theorem Ico_self : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _

theorem Ioo_self : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
@[to_dual self (reorder := a b, ha hb), instance_reducible]
def _root_.Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· ∈ s)]
    (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩

section Filter

@[to_dual (rename := a ↔ b) Ioc_filter_lt_of_right_le]
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    {x ∈ Ico a b | x < c} = ∅ :=
  filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_gt

@[to_dual (rename := a ↔ b) Ioc_filter_lt_of_le_left]
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    {x ∈ Ico a b | x < c} = Ico a b :=
  filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc

@[to_dual (rename := a ↔ b) Ioc_filter_lt_of_left_le]
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    {x ∈ Ico a b | x < c} = Ico a c := by
  grind

@[to_dual (rename := a ↔ b) Ioc_filter_le_of_right_le]
theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred (c ≤ ·)] (hca : c ≤ a) :
    {x ∈ Ico a b | c ≤ x} = Ico a b :=
  filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1

@[to_dual (rename := a ↔ b) Ioc_filter_le_of_le_left]
theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred (b ≤ ·)] :
    {x ∈ Ico a b | b ≤ x} = ∅ :=
  filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_ge

@[to_dual (rename := a ↔ b) Ioc_filter_le_of_le_right]
theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred (c ≤ ·)] (hac : a ≤ c) :
    {x ∈ Ico a b | c ≤ x} = Ico c b := by
  grind

@[to_dual (rename := a ↔ b) Icc_filter_lt_of_right_lt]
theorem Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x ∈ Icc a b | x < c} = Icc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h

@[to_dual (rename := a ↔ b) Ico_filter_lt_of_right_lt]
theorem Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x ∈ Ioc a b | x < c} = Ioc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h

@[to_dual]
theorem Iic_filter_lt_of_lt {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : {x ∈ Iic a | x < c} = Iic a :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h

@[deprecated (since := "2026-11-04")] alias Iic_filter_lt_of_lt_right := Iic_filter_lt_of_lt

variable (a b) [Fintype α]

@[to_dual none]
theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] :
    ({j | a < j ∧ j < b} : Finset _) = Ioo a b := by ext; simp

@[to_dual none]
theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j ≤ b] :
    ({j | a < j ∧ j ≤ b} : Finset _) = Ioc a b := by ext; simp

@[to_dual none]
theorem filter_le_lt_eq_Ico [DecidablePred fun j => a ≤ j ∧ j < b] :
    ({j | a ≤ j ∧ j < b} : Finset _) = Ico a b := by ext; simp

@[to_dual none]
theorem filter_le_le_eq_Icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] :
    ({j | a ≤ j ∧ j ≤ b} : Finset _) = Icc a b := by ext; simp

end Filter

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

@[to_dual (attr := simp)]
theorem Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a := by
  rw [← coe_eq_empty, coe_Ioi, Set.Ioi_eq_empty_iff]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMax.finsetIoi_eq⟩ := Ioi_eq_empty

@[to_dual (attr := simp)]
lemma Ioi_nonempty : (Ioi a).Nonempty ↔ ¬ IsMax a := by
  contrapose!; exact Ioi_eq_empty

@[to_dual]
theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ∅ := Ioi_eq_empty.mpr isMax_top

@[to_dual (attr := simp)]
theorem Ici_bot [OrderBot α] [Fintype α] : Ici (⊥ : α) = univ := by
  ext a; simp only [mem_Ici, bot_le, mem_univ]

@[to_dual (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
lemma nonempty_Ici : (Ici a).Nonempty := ⟨a, mem_Ici.2 le_rfl⟩
@[to_dual]
lemma nonempty_Ioi : (Ioi a).Nonempty ↔ ¬ IsMax a := by simp [Finset.Nonempty]

@[to_dual (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
alias ⟨_, Aesop.nonempty_Ioi_of_not_isMax⟩ := nonempty_Ioi

@[to_dual (attr := simp, gcongr)]
theorem Ici_subset_Ici : Ici a ⊆ Ici b ↔ b ≤ a := by
  simp [← coe_subset]

@[to_dual (attr := simp, gcongr)]
theorem Ici_ssubset_Ici : Ici a ⊂ Ici b ↔ b < a := by
  simp [← coe_ssubset]

@[to_dual (attr := gcongr)]
theorem Ioi_subset_Ioi (h : b ≤ a) : Ioi a ⊆ Ioi b := by
  simpa [← coe_subset] using Set.Ioi_subset_Ioi h

@[to_dual (attr := gcongr)]
theorem Ioi_ssubset_Ioi (h : b < a) : Ioi a ⊂ Ioi b := by
  simpa [← coe_ssubset] using Set.Ioi_ssubset_Ioi h

-- See note [lower instance priority]
instance (priority := low) : WellFoundedGT α :=
  StrictAnti.wellFoundedGT fun _ _ ↦ Finset.Ici_ssubset_Ici.mpr

variable [LocallyFiniteOrder α]

@[to_dual (rename := a ↔ b)]
theorem Icc_subset_Ici_self : Icc a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self

@[to_dual (rename := a ↔ b)]
theorem Ico_subset_Ici_self : Ico a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self

@[to_dual (rename := a ↔ b)]
theorem Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self

@[to_dual (rename := a ↔ b)]
theorem Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self

@[to_dual (rename := a ↔ b)]
theorem Ioc_subset_Ici_self : Ioc a b ⊆ Ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self

@[to_dual (rename := a ↔ b)]
theorem Ioo_subset_Ici_self : Ioo a b ⊆ Ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

-- See note [lower instance priority]
@[to_dual existing]
instance (priority := low) : WellFoundedLT α :=
  StrictMono.wellFoundedLT fun _ _ ↦ Finset.Iic_ssubset_Iic.mpr

theorem sup_Iic_of_monotone {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α → β}
    (hf : Monotone f) : (Iic a).sup f = f a :=
  le_antisymm (Finset.sup_le_iff.mpr fun _ h ↦ hf (by simpa using h)) (le_sup (by simp))

variable [LocallyFiniteOrder α]

@[to_dual]
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  disjoint_left.2 fun _ hax hbcx ↦ (mem_Iic.1 hax).not_gt <| lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

/-- An equivalence between `Finset.Iic a` and `Set.Iic a`. -/
@[to_dual
/-- An equivalence between `Finset.Ici a` and `Set.Ici a`. -/]
def _root_.Equiv.IicFinsetSet (a : α) : Iic a ≃ Set.Iic a where
  toFun b := ⟨b.1, coe_Iic a ▸ mem_coe.2 b.2⟩
  invFun b := ⟨b.1, by rw [← mem_coe, coe_Iic a]; exact b.2⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

@[to_dual]
theorem Ioi_subset_Ici_self : Ioi a ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self

@[to_dual]
theorem _root_.BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 <| ha hx

@[to_dual]
theorem _root_.Set.Infinite.not_bddBelow {s : Set α} : s.Infinite → ¬BddBelow s :=
  mt BddBelow.finite

variable [Fintype α]

@[to_dual filter_gt_eq_Iio]
theorem filter_lt_eq_Ioi [DecidablePred (a < ·)] : ({x | a < x} : Finset _) = Ioi a := by ext; simp
@[to_dual filter_ge_eq_Iic]
theorem filter_le_eq_Ici [DecidablePred (a ≤ ·)] : ({x | a ≤ x} : Finset _) = Ici a := by ext; simp

end LocallyFiniteOrderTop

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[to_dual (attr := simp)]
theorem Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a := rfl

@[to_dual (attr := simp)]
theorem Ico_bot [OrderBot α] : Ico (⊥ : α) a = Iio a := rfl

theorem Icc_bot_top [BoundedOrder α] [Fintype α] : Icc (⊥ : α) (⊤ : α) = univ := by
  rw [Icc_bot, Iic_top]

end LocallyFiniteOrder

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

@[to_dual]
theorem disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a) :=
  disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_gt <| mem_Iio.1 hba

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[to_dual none, simp]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]

@[to_dual]
theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_ge (mem_Ico.mp hbc).1

section DecidableEq

variable [DecidableEq α]

@[to_dual (attr := simp) (rename := a ↔ b) Icc_erase_right]
theorem Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b := by simp [← coe_inj]

@[to_dual (attr := simp) (rename := a ↔ b) Ioc_erase_right]
theorem Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b := by simp [← coe_inj]

@[to_dual none, simp]
theorem Icc_sdiff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [← coe_inj]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[to_dual (attr := simp) (rename := a ↔ b) Ico_insert_right]
theorem Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]

@[to_dual (attr := simp) (rename := a ↔ b) Ioo_insert_right]
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]

@[to_dual (attr := simp) (rename := a ↔ b)]
theorem Icc_sdiff_Ico_self (h : a ≤ b) : Icc a b \ Ico a b = {b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_self := Icc_sdiff_Ico_self
@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioc_self := Icc_sdiff_Ioc_self

@[to_dual none, simp]
theorem Icc_sdiff_Ioo_self (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_self := Icc_sdiff_Ioo_self

@[to_dual (attr := simp) (rename := a ↔ b)]
theorem Ico_sdiff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_self := Ico_sdiff_Ioo_self
@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioo_self := Ioc_sdiff_Ioo_self

@[to_dual none, simp]
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
  (Ico_disjoint_Ico_consecutive a b c).eq_bot

end DecidableEq

-- Those lemmas are purposefully the other way around

/-- `Finset.cons` version of `Finset.Ico_insert_right`. -/
@[to_dual (rename := a ↔ b)
/-- `Finset.cons` version of `Finset.Ioc_insert_left`. -/]
theorem Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_notMem_Ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]

/-- `Finset.cons` version of `Finset.Ioo_insert_right`. -/
@[to_dual (rename := a ↔ b)
/-- `Finset.cons` version of `Finset.Ioo_insert_left`. -/]
theorem Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_notMem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_right h]

@[to_dual (rename := a ↔ b) Ioc_filter_right_le]
theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    {x ∈ Ico a b | x ≤ a} = {a} := by
  grind

@[to_dual (rename := a ↔ b)]
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : #(Ico a b) = #(Icc a b) - 1 := by
  by_cases h : a ≤ b
  · rw [Icc_eq_cons_Ico h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]

@[to_dual (rename := a ↔ b)]
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : #(Ioo a b) = #(Ico a b) - 1 := by
  by_cases h : a < b
  · rw [Ico_eq_cons_Ioo h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]

@[to_dual self]
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : #(Ioo a b) = #(Icc a b) - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl

end PartialOrder

section Prod

variable {β : Type*}

section sectL

lemma uIcc_map_sectL [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (a b : α) (c : β) :
    (uIcc a b).map (.sectL _ c) = uIcc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (a b : α) (c : β)

@[to_dual self]
lemma Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])

@[to_dual (rename := a ↔ b)]
lemma Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

@[to_dual self]
lemma Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectL

section sectR

lemma uIcc_map_sectR [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (c : α) (a b : β) :
    (uIcc a b).map (.sectR c _) = uIcc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (c : α) (a b : β)

@[to_dual self]
lemma Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])

@[to_dual (rename := a ↔ b)]
lemma Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

@[to_dual self]
lemma Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectR

end Prod

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

@[to_dual (attr := simp)]
theorem Ici_erase [DecidableEq α] (a : α) : (Ici a).erase a = Ioi a := by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]

@[to_dual (attr := simp)]
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a := by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]

@[to_dual]
theorem notMem_Ioi_self {b : α} : b ∉ Ioi b := fun h => lt_irrefl _ (mem_Ioi.1 h)

-- Purposefully written the other way around
/-- `Finset.cons` version of `Finset.Ioi_insert`. -/
@[to_dual
/-- `Finset.cons` version of `Finset.Iio_insert`. -/]
theorem Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a notMem_Ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]

@[to_dual]
theorem card_Ioi_eq_card_Ici_sub_one (a : α) : #(Ioi a) = #(Ici a) - 1 := by
  rw [Ici_eq_cons_Ioi, card_cons, Nat.add_sub_cancel_right]

@[to_dual (attr := simp)]
theorem Ici_top [OrderTop α] : Ici (⊤ : α) = {⊤} := by ext; simp

@[to_dual]
instance [OrderTop α] : Unique (Ici (⊤ : α)) where
  default := ⟨⊤, by simp⟩
  uniq := by simp

end OrderTop

end BoundedPartialOrder

section SemilatticeSup
variable [SemilatticeSup α] [LocallyFiniteOrderBot α]

-- TODO: Why does `id_eq` simplify the LHS here but not the LHS of `Finset.sup_Iic`?
@[to_dual]
lemma sup'_Iic (a : α) : (Iic a).sup' nonempty_Iic id = a :=
  le_antisymm (sup'_le _ _ fun _ ↦ mem_Iic.1) <| le_sup' (f := id) <| mem_Iic.2 <| le_refl a

@[to_dual (attr := simp)]
lemma sup_Iic [OrderBot α] (a : α) : (Iic a).sup id = a :=
  le_antisymm (Finset.sup_le fun _ ↦ mem_Iic.1) <| le_sup (f := id) <| mem_Iic.2 <| le_refl a

@[to_dual]
lemma image_subset_Iic_sup [OrderBot α] [DecidableEq α] (f : ι → α) (s : Finset ι) :
    s.image f ⊆ Iic (s.sup f) := by
  refine fun i hi ↦ mem_Iic.2 ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact le_sup hj

@[to_dual]
lemma subset_Iic_sup_id [OrderBot α] (s : Finset α) : s ⊆ Iic (s.sup id) :=
  fun _ h ↦ mem_Iic.2 <| le_sup (f := id) h

end SemilatticeSup

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]

theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b ∪ Ico b c = Ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Ioc a b ∪ Ioc b c = Ioc a c := by
  rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]

theorem Ico_subset_Ico_union_Ico {a b c : α} : Ico a c ⊆ Ico a b ∪ Ico b c := by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico

theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]

/-- This is a special case of `Ico_union_Ico` -/
theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]

theorem Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, Set.Ico_inter_Ico]

theorem Ioc_inter_Ioc {a b c d : α} : Ioc a b ∩ Ioc c d = Ioc (max a c) (min b d) := by grind

@[simp]
theorem Ico_filter_lt (a b c : α) : {x ∈ Ico a b | x < c} = Ico a (min b c) := by grind

@[simp]
theorem Ico_filter_le (a b c : α) : {x ∈ Ico a b | c ≤ x} = Ico (max a c) b := by grind

@[simp]
theorem Ioo_filter_lt (a b c : α) : {x ∈ Ioo a b | x < c} = Ioo a (min b c) := by grind

@[simp]
theorem Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    {x ∈ Iio a | x < b} = Iio (min a b) := by grind

@[simp]
theorem Ico_sdiff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_left := Ico_sdiff_Ico_left

@[simp]
theorem Ico_sdiff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_right := Ico_sdiff_Ico_right

@[simp]
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [disjoint_iff_inter_eq_empty, Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

theorem Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

theorem Iic_sdiff_Ioc_self_of_le (hab : a ≤ b) : Iic b \ Ioc a b = Iic a := by
  rw [Iic_sdiff_Ioc, min_eq_left hab]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b := by
  grind

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α] {s : Set α}

theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove

theorem _root_.Set.infinite_iff_exists_gt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, a < b :=
  ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] {s : Set α}

theorem _root_.Set.Infinite.exists_lt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, b < a :=
  not_bddBelow_iff.1 hs.not_bddBelow

theorem _root_.Set.infinite_iff_exists_lt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩

end LocallyFiniteOrderTop

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem Ioi_disjUnion_Iio (a : α) :
    (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ := by
  ext
  simp [eq_comm]

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ x : α}

theorem uIcc_toDual (a b : α) : [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding :=
  Icc_toDual (a ⊔ b) (a ⊓ b)

@[simp]
theorem uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by
  rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
theorem uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by
  rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

theorem uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by
  rw [uIcc, uIcc, inf_comm, sup_comm]

theorem uIcc_self : [[a, a]] = {a} := by simp [uIcc]

@[simp]
theorem nonempty_uIcc : Finset.Nonempty [[a, b]] :=
  nonempty_Icc.2 inf_le_sup

theorem Icc_subset_uIcc : Icc a b ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_left le_sup_right

theorem Icc_subset_uIcc' : Icc b a ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_right le_sup_left

theorem left_mem_uIcc : a ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_left, le_sup_left⟩

theorem right_mem_uIcc : b ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_right, le_sup_right⟩

theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [[a, b]] :=
  Icc_subset_uIcc <| mem_Icc.2 ⟨ha, hb⟩

theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [[a, b]] :=
  Icc_subset_uIcc' <| mem_Icc.2 ⟨hb, ha⟩

theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [[a₂, b₂]]) (h₂ : b₁ ∈ [[a₂, b₂]]) :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] := by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)

theorem uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [[a₁, b₁]] ⊆ Icc a₂ b₂ := by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)

theorem uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₁ ∈ [[a₂, b₂]] ∧ b₁ ∈ [[a₂, b₂]] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩

theorem uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup

theorem uIcc_subset_uIcc_right (h : x ∈ [[a, b]]) : [[x, b]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc

theorem uIcc_subset_uIcc_left (h : x ∈ [[a, b]]) : [[a, x]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a b c : α}

theorem eq_of_mem_uIcc_of_mem_uIcc : a ∈ [[b, c]] → b ∈ [[a, c]] → a = b := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc

theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [[a, c]] → c ∈ [[a, b]] → b = c := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'

theorem uIcc_injective_right (a : α) : Injective fun b => [[b, a]] := fun b c h => by
  rw [Finset.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c : α}

theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl

theorem uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a :=
  uIcc_of_ge <| le_of_not_ge h

theorem uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b :=
  uIcc_of_le <| le_of_not_ge h

theorem uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a :=
  coe_injective <| by
    push_cast
    exact Set.uIcc_eq_union

theorem mem_uIcc' : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]

theorem notMem_uIcc_of_lt : c < a → c < b → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_lt

theorem notMem_uIcc_of_gt : a < c → b < c → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_gt

theorem uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
theorem uIcc_subset_uIcc_union_uIcc : [[a, c]] ⊆ [[a, b]] ∪ [[b, c]] :=
  coe_subset.1 <| by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc

end LinearOrder
end Finset

/-! ### `⩿`, `⋖` and monotonicity -/

section Cover

open Finset Relation

set_option linter.style.whitespace false in -- manual alignment is not recognised
lemma transGen_wcovBy_of_le [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x ≤ y) :
    TransGen (· ⩿ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
  have : #(Ico x y) < #(Icc x y) := card_lt_card
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_notMem_Ico⟩⟩⟩
  by_cases hxy' : y ≤ x
  -- If `y ≤ x`, then `x ⩿ y`
  · exact .single <| wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · obtain ⟨z, hxz, hz⟩ :=
      (Set.finite_Ico x y).exists_le_maximal <| Set.left_mem_Ico.2 <| hxy.lt_of_not_ge hxy'
    have z_card := calc
      #(Icc x z) ≤ #(Ico x y) := card_le_card <| Icc_subset_Ico_right hz.1.2
      _          < #(Icc x y) := this
    have h₁ := transGen_wcovBy_of_le hz.1.1
    have h₂ : z ⩿ y :=
      ⟨hz.1.2.le, fun c hzc hcy ↦ hzc.not_ge <| hz.2 ⟨hz.1.1.trans hzc.le, hcy⟩ hzc.le⟩
    exact .tail h₁ h₂
termination_by #(Icc x y)

/-- In a locally finite preorder, `≤` is the transitive closure of `⩿`. -/
lemma le_iff_transGen_wcovBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ TransGen (· ⩿ ·) x y := by
  refine ⟨transGen_wcovBy_of_le, fun h ↦ ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

/-- In a locally finite partial order, `≤` is the reflexive transitive closure of `⋖`. -/
lemma le_iff_reflTransGen_covBy [PartialOrder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ ReflTransGen (· ⋖ ·) x y := by
  rw [le_iff_transGen_wcovBy, wcovBy_eq_reflGen_covBy, transGen_reflGen]

lemma transGen_covBy_of_lt [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x < y) :
    TransGen (· ⋖ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
  obtain ⟨z, hxz, hz⟩ := (Set.finite_Ico x y).exists_le_maximal <| Set.left_mem_Ico.2 hxy
  have z_card : #(Ico x z) < #(Ico x y) := card_lt_card <| ssubset_iff_of_subset
    (Ico_subset_Ico_right hz.1.2.le) |>.mpr ⟨z, mem_Ico.2 hz.1, right_notMem_Ico⟩
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y :=
    ⟨hz.1.2, fun c hc hcy ↦ hc.not_ge <| hz.2 (⟨(hz.1.1.trans_lt hc).le, hcy⟩) hc.le⟩
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y`, then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_ge, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz hz.1.1) hxy)
termination_by #(Ico x y)

/-- In a locally finite preorder, `<` is the transitive closure of `⋖`. -/
lemma lt_iff_transGen_covBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x < y ↔ TransGen (· ⋖ ·) x y := by
  refine ⟨transGen_covBy_of_lt, fun h ↦ ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

variable {β : Type*}

/-- A function from a locally finite preorder is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⩿ b`. -/
lemma monotone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⩿ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [transGen_eq_self] using TransGen.lift f h a b <| le_iff_transGen_wcovBy.mp hab

/-- A function from a locally finite partial order is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⋖ b`. -/
lemma monotone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⋖ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [reflTransGen_eq_self] using ReflTransGen.lift f h a b <| le_iff_reflTransGen_covBy.mp hab

/-- A function from a locally finite preorder is strictly monotone if and only if it is strictly
monotone when restricted to pairs satisfying `a ⋖ b`. -/
lemma strictMono_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictMono f ↔ ∀ a b : α, a ⋖ b → f a < f b := by
  refine ⟨fun hf _ _ h ↦ hf h.lt, fun h a b hab ↦ ?_⟩
  have := Relation.TransGen.lift f h a b
  rw [← lt_iff_transGen_covBy, transGen_eq_self] at this
  exact this hab

/-- A function from a locally finite preorder is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⩿ b`. -/
lemma antitone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⩿ b → f b ≤ f a :=
  monotone_iff_forall_wcovBy (β := βᵒᵈ) f

/-- A function from a locally finite partial order is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⋖ b`. -/
lemma antitone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⋖ b → f b ≤ f a :=
  monotone_iff_forall_covBy (β := βᵒᵈ) f

/-- A function from a locally finite preorder is strictly antitone if and only if it is strictly
antitone when restricted to pairs satisfying `a ⋖ b`. -/
lemma strictAnti_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictAnti f ↔ ∀ a b : α, a ⋖ b → f b < f a :=
  strictMono_iff_forall_covBy (β := βᵒᵈ) f

end Cover
