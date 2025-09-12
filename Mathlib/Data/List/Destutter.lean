/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import Mathlib.Data.List.Chain

/-!
# Destuttering of Lists

This file proves theorems about `List.destutter` (in `Data.List.Defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `List.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `List.destutter_is_chain'`: `l.destutter` satisfies `Chain' R`.
* Analogies of these theorems for `List.destutter'`, which is the `destutter` equivalent of `Chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/

open Function

variable {α β : Type*} (l l₁ l₂ : List α) (R : α → α → Prop) [DecidableRel R] {a b : α}

variable {R₂ : β → β → Prop} [DecidableRel R₂]

namespace List

@[simp]
theorem destutter'_nil : destutter' R a [] = [a] :=
  rfl

theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

variable {R}

@[simp]
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter', if_pos h]

@[simp]
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter', if_neg h]

variable (R)

@[simp]
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]

theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · exact Sublist.cons₂ a (hl b)
    · exact (hl a).trans ((l.sublist_cons_self b).cons_cons a)

theorem mem_destutter' (a) : a ∈ l.destutter' R a := by
  induction l with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs
    · simp
    · assumption

theorem destutter'_is_chain : ∀ l : List α, ∀ {a b}, R a b → (l.destutter' R b).Chain R a
  | [], _, _, h => chain_singleton.mpr h
  | c :: l, a, b, h => by
    rw [destutter']
    split_ifs with hbc
    · rw [chain_cons]
      exact ⟨h, destutter'_is_chain l hbc⟩
    · exact destutter'_is_chain l h

theorem destutter'_is_chain' (a) : (l.destutter' R a).Chain' R := by
  induction l generalizing a with
  | nil => simp
  | cons b l hl =>
    rw [destutter']
    split_ifs with h
    · exact destutter'_is_chain R l h
    · exact hl a

theorem destutter'_of_chain (h : l.Chain R a) : l.destutter' R a = a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons b l hb =>
    obtain ⟨h, hc⟩ := chain_cons.mp h
    rw [l.destutter'_cons_pos h, hb hc]

@[simp]
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ l.Chain R a :=
  ⟨fun h => by
    suffices Chain' R (a::l) by
      assumption
    rw [← h]
    exact l.destutter'_is_chain' R a, destutter'_of_chain _ _⟩

theorem destutter'_ne_nil : l.destutter' R a ≠ [] :=
  ne_nil_of_mem <| l.mem_destutter' R a

@[simp]
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl

theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl

theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

@[simp]
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl

@[simp]
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R

theorem destutter_sublist : ∀ l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h

theorem destutter_is_chain' : ∀ l : List α, (l.destutter R).Chain' R
  | [] => List.chain'_nil
  | h :: l => l.destutter'_is_chain' R h

theorem destutter_of_chain' : ∀ l : List α, l.Chain' R → l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_chain _ h

@[simp]
theorem destutter_eq_self_iff : ∀ l : List α, l.destutter R = l ↔ l.Chain' R
  | [] => by simp
  | a :: l => l.destutter'_eq_self_iff R a

theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
  destutter_of_chain' R _ <| l.destutter_is_chain' R

@[simp]
theorem destutter_eq_nil : ∀ {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
  | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R, fun h => nomatch h⟩

variable {R}

/-- For a relation-preserving map, `destutter` commutes with `map`. -/
theorem map_destutter {f : α → β} : ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, R a b ↔ R₂ (f a) (f b)) →
    (l.destutter R).map f = (l.map f).destutter R₂
  | [], hl => by simp
  | [a], hl => by simp
  | a :: b :: l, hl => by
    have := hl a (by simp) b (by simp)
    simp_rw [map_cons, destutter_cons_cons, ← this]
    by_cases hr : R a b <;>
      simp [hr, ← destutter_cons', map_destutter fun c hc d hd ↦ hl _ (cons_subset_cons _
        (subset_cons_self _ _) hc) _ (cons_subset_cons _ (subset_cons_self _ _) hd),
        map_destutter fun c hc d hd ↦ hl _ (subset_cons_self _ _ hc) _ (subset_cons_self _ _ hd)]

/-- For a injective function `f`, `destutter' (·≠·)` commutes with `map f`. -/
theorem map_destutter_ne {f : α → β} (h : Injective f) [DecidableEq α] [DecidableEq β] :
    (l.destutter (·≠·)).map f = (l.map f).destutter (·≠·) :=
  map_destutter fun _ _ _ _ ↦ h.ne_iff.symm

/-- `destutter'` on a relation like ≠ or <, whose negation is transitive, has length monotone
under a `¬R` changing of the first element. -/
theorem length_destutter'_cotrans_ge [i : IsTrans α Rᶜ] :
    ∀ {a} {l : List α}, ¬R b a → (l.destutter' R b).length ≤ (l.destutter' R a).length
  | a, [], hba => by simp
  | a, c :: l, hba => by
    by_cases hbc : R b c
    case pos =>
      have hac : ¬Rᶜ a c := (mt (_root_.trans hba)) (not_not.2 hbc)
      simp_rw [destutter', if_pos (not_not.1 hac), if_pos hbc, length_cons, le_refl]
    case neg =>
      simp only [destutter', if_neg hbc]
      by_cases hac : R a c
      case pos =>
        simp only [if_pos hac, length_cons]
        exact Nat.le_succ_of_le (length_destutter'_cotrans_ge hbc)
      case neg =>
        simp only [if_neg hac]
        exact length_destutter'_cotrans_ge hba

/-- `List.destutter'` on a relation like `≠`, whose negation is an equivalence, gives the same
length if the first elements are not related. -/
theorem length_destutter'_congr [IsEquiv α Rᶜ] (hab : ¬R a b) :
    (l.destutter' R a).length = (l.destutter' R b).length :=
  (length_destutter'_cotrans_ge hab).antisymm <| length_destutter'_cotrans_ge (symm hab : Rᶜ b a)

/-- `List.destutter'` on a relation like ≠, whose negation is an equivalence, has length
monotonic under List.cons -/
/-
TODO: Replace this lemma by the more general version:
theorem Sublist.length_destutter'_mono [IsEquiv α Rᶜ] (h : a :: l₁ <+ b :: l₂) :
    (List.destutter' R a l₁).length ≤ (List.destutter' R b l₂).length
-/
theorem le_length_destutter'_cons [IsEquiv α Rᶜ] :
    ∀ {l : List α}, (l.destutter' R b).length ≤ ((b :: l).destutter' R a).length
  | [] => by by_cases hab : (R a b) <;> simp_all [Nat.le_succ]
  | c :: cs => by
    by_cases hab : R a b
    case pos => simp [destutter', if_pos hab, Nat.le_succ]
    obtain hac | hac : R a c ∨ Rᶜ a c := em _
    · have hbc : ¬Rᶜ b c := mt (_root_.trans hab) (not_not.2 hac)
      simp [destutter', if_pos hac, if_pos (not_not.1 hbc), if_neg hab]
    · have hbc : ¬R b c := trans (symm hab) hac
      simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
      exact (length_destutter'_congr cs hab).ge

/-- `List.destutter` on a relation like ≠, whose negation is an equivalence, has length
monotone under List.cons -/
theorem length_destutter_le_length_destutter_cons [IsEquiv α Rᶜ] :
    ∀ {l : List α}, (l.destutter R).length ≤ ((a :: l).destutter R).length
  | [] => by simp [destutter]
  | b :: l => le_length_destutter'_cons

variable {l l₁ l₂}

/-- `destutter ≠` has length monotone under `List.cons`. -/
theorem length_destutter_ne_le_length_destutter_cons [DecidableEq α] :
    (l.destutter (· ≠ ·)).length ≤ ((a :: l).destutter (· ≠ ·)).length :=
  length_destutter_le_length_destutter_cons

/-- `destutter` of relations like `≠`, whose negation is an equivalence relation,
gives a list of maximal length over any chain.

In other words, `l.destutter R` is an `R`-chain sublist of `l`, and is at least as long as any other
`R`-chain sublist. -/
lemma Chain'.length_le_length_destutter [IsEquiv α Rᶜ] :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → l₁.Chain' R → l₁.length ≤ (l₂.destutter R).length
  -- `l₁ := []`, `l₂ := []`
  | [], [], _, _ => by simp
  -- `l₁ := l₁`, `l₂ := a :: l₂`
  | l₁, _, .cons (l₂ := l₂) a hl, hl₁ =>
    (hl₁.length_le_length_destutter hl).trans length_destutter_le_length_destutter_cons
  -- `l₁ := [a]`, `l₂ := a :: l₂`
  | _, _, .cons₂ (l₁ := []) (l₂ := l₁) a hl, hl₁ => by simp [Nat.one_le_iff_ne_zero]
  -- `l₁ := a :: l₁`, `l₂ := a :: b :: l₂`
  | _, _, .cons₂ a <| .cons (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    by_cases hab : R a b
    · simpa [destutter_cons_cons, hab] using hl₁.tail.length_le_length_destutter (hl.cons _)
    · simpa [destutter_cons_cons, hab] using hl₁.length_le_length_destutter (hl.cons₂ _)
  -- `l₁ := a :: b :: l₁`, `l₂ := a :: b :: l₂`
  | _, _, .cons₂ a <| .cons₂ (l₁ := l₁) (l₂ := l₂) b hl, hl₁ => by
    simpa [destutter_cons_cons, rel_of_chain_cons hl₁]
      using hl₁.tail.length_le_length_destutter (hl.cons₂ _)

/-- `destutter` of `≠` gives a list of maximal length over any chain.

In other words, `l.destutter (· ≠ ·)` is a `≠`-chain sublist of `l`, and is at least as long as any
other `≠`-chain sublist. -/
lemma Chain'.length_le_length_destutter_ne [DecidableEq α] (hl : l₁ <+ l₂)
    (hl₁ : l₁.Chain' (· ≠ ·)) : l₁.length ≤ (l₂.destutter (· ≠ ·)).length :=
  hl₁.length_le_length_destutter hl

end List
