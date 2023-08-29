/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Order

#align_import combinatorics.double_counting from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Double countings

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : Finset α` and `t : Finset β` by the minimum/maximum of edges over all `a ∈ s` times the
size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartiteBelow`: `s.bipartiteBelow r b` are the elements of `s` below `b` wrt to `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartiteAbove`: `t.bipartite_Above r a` are the elements of `t` above `a` wrt to `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.
-/


open Finset Function Relator

open BigOperators

variable {α β : Type*}

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a a' : α) (b b' : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

/-- Elements of `s` which are "below" `b` according to relation `r`. -/
def bipartiteBelow : Finset α := s.filter fun a ↦ r a b
#align finset.bipartite_below Finset.bipartiteBelow

/-- Elements of `t` which are "above" `a` according to relation `r`. -/
def bipartiteAbove : Finset β := t.filter (r a)
#align finset.bipartite_above Finset.bipartiteAbove

theorem bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a := rfl
#align finset.bipartite_below_swap Finset.bipartiteBelow_swap

theorem bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b := rfl
#align finset.bipartite_above_swap Finset.bipartiteAbove_swap

@[simp, norm_cast]
theorem coe_bipartiteBelow : (s.bipartiteBelow r b : Set α) = { a ∈ s | r a b } := coe_filter _ _
#align finset.coe_bipartite_below Finset.coe_bipartiteBelow

@[simp, norm_cast]
theorem coe_bipartiteAbove : (t.bipartiteAbove r a : Set β) = { b ∈ t | r a b } := coe_filter _ _
#align finset.coe_bipartite_above Finset.coe_bipartiteAbove

variable {s t a a' b b'}

@[simp]
theorem mem_bipartiteBelow {a : α} : a ∈ s.bipartiteBelow r b ↔ a ∈ s ∧ r a b := mem_filter
#align finset.mem_bipartite_below Finset.mem_bipartiteBelow

@[simp]
theorem mem_bipartiteAbove {b : β} : b ∈ t.bipartiteAbove r a ↔ b ∈ t ∧ r a b := mem_filter
#align finset.mem_bipartite_above Finset.mem_bipartiteAbove

theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [∀ a b, Decidable (r a b)] :
    (∑ a in s, (t.bipartiteAbove r a).card) = ∑ b in t, (s.bipartiteBelow r b).card := by
  simp_rw [card_eq_sum_ones, bipartiteAbove, bipartiteBelow, sum_filter]
  -- ⊢ (∑ x in s, ∑ a in t, if r x a then 1 else 0) = ∑ x in t, ∑ a in s, if r a x  …
  exact sum_comm
  -- 🎉 no goals
#align finset.sum_card_bipartite_above_eq_sum_card_bipartite_below Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow

/-- Double counting argument. Considering `r` as a bipartite graph, the LHS is a lower bound on the
number of edges while the RHS is an upper bound. -/
theorem card_mul_le_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove r a).card)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card ≤ n) : s.card * m ≤ t.card * n :=
  calc
    _ ≤ ∑ a in s, (t.bipartiteAbove r a).card := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (s.bipartiteBelow r b).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn
#align finset.card_mul_le_card_mul Finset.card_mul_le_card_mul

theorem card_mul_le_card_mul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ (s.bipartiteBelow r b).card)
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card ≤ m) : t.card * n ≤ s.card * m :=
  card_mul_le_card_mul (swap r) hn hm
#align finset.card_mul_le_card_mul' Finset.card_mul_le_card_mul'

theorem card_mul_eq_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card = m)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card = n) : s.card * m = t.card * n :=
  (card_mul_le_card_mul _ (fun a ha ↦ (hm a ha).ge) fun b hb ↦ (hn b hb).le).antisymm <|
    card_mul_le_card_mul' _ (fun a ha ↦ (hn a ha).ge) fun b hb ↦ (hm b hb).le
#align finset.card_mul_eq_card_mul Finset.card_mul_eq_card_mul

theorem card_le_card_of_forall_subsingleton (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : s.card ≤ t.card := by
  classical
    rw [← mul_one s.card, ← mul_one t.card]
    exact card_mul_le_card_mul r
      (fun a h ↦ card_pos.2 (by
        rw [← coe_nonempty, coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h ↦ card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))
#align finset.card_le_card_of_forall_subsingleton Finset.card_le_card_of_forall_subsingleton

theorem card_le_card_of_forall_subsingleton' (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b)
    (hs : ∀ a ∈ s, ({ b ∈ t | r a b } : Set β).Subsingleton) : t.card ≤ s.card :=
  card_le_card_of_forall_subsingleton (swap r) ht hs
#align finset.card_le_card_of_forall_subsingleton' Finset.card_le_card_of_forall_subsingleton'

end Bipartite

end Finset

open Finset

namespace Fintype

variable [Fintype α] [Fintype β] {r : α → β → Prop}

theorem card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) :
    Fintype.card α ≤ Fintype.card β :=
  card_le_card_of_forall_subsingleton r (by simpa using h₁) fun b _ a₁ ha₁ a₂ ha₂ ↦ h₂ ha₁.2 ha₂.2
                                            -- 🎉 no goals
#align fintype.card_le_card_of_left_total_unique Fintype.card_le_card_of_leftTotal_unique

theorem card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r) :
    Fintype.card β ≤ Fintype.card α :=
  card_le_card_of_forall_subsingleton' r (by simpa using h₁) fun b _ a₁ ha₁ a₂ ha₂ ↦ h₂ ha₁.2 ha₂.2
                                             -- 🎉 no goals
#align fintype.card_le_card_of_right_total_unique Fintype.card_le_card_of_rightTotal_unique

end Fintype
