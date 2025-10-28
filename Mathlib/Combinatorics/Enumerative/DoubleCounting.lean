/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Double countings

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : Finset α` and `t : Finset β` by the minimum/maximum of edges over all `a ∈ s` times the
size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartiteBelow`: `s.bipartiteBelow r b` are the elements of `s` below `b` w.r.t. `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartiteAbove`: `t.bipartite_Above r a` are the elements of `t` above `a` w.r.t. `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
bipartite simple graph `G : SimpleGraph V`, see `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.
-/

assert_not_exists Field

open Finset Function Relator

variable {R α β : Type*}

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

/-- Elements of `s` which are "below" `b` according to relation `r`. -/
def bipartiteBelow : Finset α := {a ∈ s | r a b}

/-- Elements of `t` which are "above" `a` according to relation `r`. -/
def bipartiteAbove : Finset β := {b ∈ t | r a b}

theorem bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a := rfl

theorem bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b := rfl

@[simp, norm_cast]
theorem coe_bipartiteBelow : s.bipartiteBelow r b = ({a ∈ s | r a b} : Set α) := coe_filter _ _

@[simp, norm_cast]
theorem coe_bipartiteAbove : t.bipartiteAbove r a = ({b ∈ t | r a b} : Set β) := coe_filter _ _

variable {s t a b}

@[simp]
theorem mem_bipartiteBelow {a : α} : a ∈ s.bipartiteBelow r b ↔ a ∈ s ∧ r a b := mem_filter

@[simp]
theorem mem_bipartiteAbove {b : β} : b ∈ t.bipartiteAbove r a ↔ b ∈ t ∧ r a b := mem_filter

@[to_additive]
theorem prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
    [CommMonoid R] (f : α → β → R) [∀ a b, Decidable (r a b)] :
    ∏ a ∈ s, ∏ b ∈ t.bipartiteAbove r a, f a b = ∏ b ∈ t, ∏ a ∈ s.bipartiteBelow r b, f a b := by
  simp_rw [bipartiteAbove, bipartiteBelow, prod_filter]
  exact prod_comm

theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [∀ a b, Decidable (r a b)] :
    (∑ a ∈ s, #(t.bipartiteAbove r a)) = ∑ b ∈ t, #(s.bipartiteBelow r b) := by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
theorem card_nsmul_le_card_nsmul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s • m ≤ #t • n :=
  calc
    _ ≤ ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
theorem card_nsmul_le_card_nsmul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t • n ≤ #s • m :=
  card_nsmul_le_card_nsmul (swap r) hn hm

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] (r : α → β → Prop)
  {s : Finset α} {t : Finset β} (a b) {m n : R}

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hm : ∀ a ∈ s, m < #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s • m < #t • n :=
  calc
    _ = ∑ _a ∈ s, m := by rw [sum_const]
    _ < ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) < n) : #s • m < #t • n :=
  calc
    _ ≤ ∑ a ∈ s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b ∈ t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b ∈ t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a strict lower bound on the number of edges while
the RHS is an upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le' [∀ a b, Decidable (r a b)] (ht : t.Nonempty)
    (hn : ∀ b ∈ t, n < #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is a strict upper bound. -/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt' [∀ a b, Decidable (r a b)] (hs : s.Nonempty)
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) < m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm

end StrictOrderedSemiring

/-- **Double counting** argument.

Considering `r` as a bipartite graph, the LHS is a lower bound on the number of edges while the RHS
is an upper bound. -/
theorem card_mul_le_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ #(t.bipartiteAbove r a))
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) ≤ n) : #s * m ≤ #t * n :=
  card_nsmul_le_card_nsmul _ hm hn

theorem card_mul_le_card_mul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ #(s.bipartiteBelow r b))
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) ≤ m) : #t * n ≤ #s * m :=
  card_nsmul_le_card_nsmul' _ hn hm

theorem card_mul_eq_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, #(t.bipartiteAbove r a) = m)
    (hn : ∀ b ∈ t, #(s.bipartiteBelow r b) = n) : #s * m = #t * n :=
  (card_mul_le_card_mul _ (fun a ha ↦ (hm a ha).ge) fun b hb ↦ (hn b hb).le).antisymm <|
    card_mul_le_card_mul' _ (fun a ha ↦ (hn a ha).ge) fun b hb ↦ (hm b hb).le

theorem card_le_card_of_forall_subsingleton (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : #s ≤ #t := by
  classical
    rw [← mul_one #s, ← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h ↦ card_pos.2 (by
        rw [← coe_nonempty, coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h ↦ card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))

theorem card_le_card_of_forall_subsingleton' (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b)
    (hs : ∀ a ∈ s, ({ b ∈ t | r a b } : Set β).Subsingleton) : #t ≤ #s :=
  card_le_card_of_forall_subsingleton (swap r) ht hs

end Bipartite

end Finset

namespace Fintype

variable [Fintype α] [Fintype β] {r : α → β → Prop}

theorem card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) :
    Fintype.card α ≤ Fintype.card β :=
  card_le_card_of_forall_subsingleton r (by simpa using h₁) fun _ _ _ ha₁ _ ha₂ ↦ h₂ ha₁.2 ha₂.2

theorem card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r) :
    Fintype.card β ≤ Fintype.card α :=
  card_le_card_of_forall_subsingleton' r (by simpa using h₁) fun _ _ _ ha₁ _ ha₂ ↦ h₂ ha₁.2 ha₂.2

end Fintype
