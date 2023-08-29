/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Order.GameAdd

#align_import logic.hydra from "leanprover-community/mathlib"@"48085f140e684306f9e7da907cd5932056d1aded"

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `CutExpand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `CutExpand r` on `Multiset α`:
`CutExpand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

We follow the proof by Peter LeFanu Lumsdaine at https://mathoverflow.net/a/229084/3332.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/


namespace Relation

open Multiset Prod

variable {α : Type*}

/-- The relation that specifies valid moves in our hydra game. `CutExpand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `Multiset.erase` requires
  `DecidableEq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `Relation.cutExpand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
def CutExpand (r : α → α → Prop) (s' s : Multiset α) : Prop :=
  ∃ (t : Multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ s' + {a} = s + t
#align relation.cut_expand Relation.CutExpand

variable {r : α → α → Prop}

theorem cutExpand_le_invImage_lex [DecidableEq α] [IsIrrefl α r] :
    CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ (· ≠ ·)) (· < ·)) toFinsupp := by
  rintro s t ⟨u, a, hr, he⟩
  -- ⊢ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) (↑to …
  replace hr := fun a' ↦ mt (hr a')
  -- ⊢ InvImage (Finsupp.Lex (rᶜ ⊓ fun x x_1 => x ≠ x_1) fun x x_1 => x < x_1) (↑to …
  classical
  refine ⟨a, fun b h ↦ ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, if_neg h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _
#align relation.cut_expand_le_inv_image_lex Relation.cutExpand_le_invImage_lex

theorem cutExpand_singleton {s x} (h : ∀ x' ∈ s, r x' x) : CutExpand r s {x} :=
  ⟨s, x, h, add_comm s _⟩
#align relation.cut_expand_singleton Relation.cutExpand_singleton

theorem cutExpand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x} :=
  cutExpand_singleton fun a h ↦ by rwa [mem_singleton.1 h]
                                   -- 🎉 no goals
#align relation.cut_expand_singleton_singleton Relation.cutExpand_singleton_singleton

theorem cutExpand_add_left {t u} (s) : CutExpand r (s + t) (s + u) ↔ CutExpand r t u :=
  exists₂_congr fun _ _ ↦ and_congr Iff.rfl <| by rw [add_assoc, add_assoc, add_left_cancel_iff]
                                                  -- 🎉 no goals
#align relation.cut_expand_add_left Relation.cutExpand_add_left

theorem cutExpand_iff [DecidableEq α] [IsIrrefl α r] {s' s : Multiset α} :
    CutExpand r s' s ↔
      ∃ (t : Multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t := by
  simp_rw [CutExpand, add_singleton_eq_iff]
  -- ⊢ (∃ t a, (∀ (a' : α), a' ∈ t → r a' a) ∧ a ∈ s + t ∧ s' = erase (s + t) a) ↔  …
  refine' exists₂_congr fun t a ↦ ⟨_, _⟩
  -- ⊢ (∀ (a' : α), a' ∈ t → r a' a) ∧ a ∈ s + t ∧ s' = erase (s + t) a → (∀ (a' :  …
  · rintro ⟨ht, ha, rfl⟩
    -- ⊢ (∀ (a' : α), a' ∈ t → r a' a) ∧ a ∈ s ∧ erase (s + t) a = erase s a + t
    obtain h | h := mem_add.1 ha
    -- ⊢ (∀ (a' : α), a' ∈ t → r a' a) ∧ a ∈ s ∧ erase (s + t) a = erase s a + t
    exacts [⟨ht, h, erase_add_left_pos t h⟩, (@irrefl α r _ a (ht a h)).elim]
    -- 🎉 no goals
  · rintro ⟨ht, h, rfl⟩
    -- ⊢ (∀ (a' : α), a' ∈ t → r a' a) ∧ a ∈ s + t ∧ erase s a + t = erase (s + t) a
    exact ⟨ht, mem_add.2 (Or.inl h), (erase_add_left_pos t h).symm⟩
    -- 🎉 no goals
#align relation.cut_expand_iff Relation.cutExpand_iff

theorem not_cutExpand_zero [IsIrrefl α r] (s) : ¬CutExpand r s 0 := by
  classical
  rw [cutExpand_iff]
  rintro ⟨_, _, _, ⟨⟩, _⟩
#align relation.not_cut_expand_zero Relation.not_cutExpand_zero

/-- For any relation `r` on `α`, multiset addition `Multiset α × Multiset α → Multiset α` is a
  fibration between the game sum of `CutExpand r` with itself and `CutExpand r` itself. -/
theorem cutExpand_fibration (r : α → α → Prop) :
    Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s ↦ s.1 + s.2 := by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩; dsimp at he ⊢
  -- ⊢ ∃ a', GameAdd (CutExpand r) (CutExpand r) a' (s₁, s₂) ∧ (fun s => s.fst + s. …
                                    -- ⊢ ∃ a', GameAdd (CutExpand r) (CutExpand r) a' (s₁, s₂) ∧ a'.fst + a'.snd = s
  classical
  -- Porting note: Originally `obtain ⟨ha, rfl⟩`
  -- This is https://github.com/leanprover/std4/issues/62
  obtain ⟨ha, hb⟩ := add_singleton_eq_iff.1 he
  rw [hb]
  rw [add_assoc, mem_add] at ha
  obtain h | h := ha
  · refine' ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, hr, _⟩, _⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc]
  · refine' ⟨(s₁, (s₂ + t).erase a), GameAdd.snd ⟨t, a, hr, _⟩, _⟩
    · rw [add_comm, singleton_add, cons_erase h]
    · rw [add_assoc, erase_add_right_pos _ h]
#align relation.cut_expand_fibration Relation.cutExpand_fibration

/-- A multiset is accessible under `CutExpand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
theorem acc_of_singleton [IsIrrefl α r] {s : Multiset α} (hs : ∀ a ∈ s, Acc (CutExpand r) {a}) :
    Acc (CutExpand r) s := by
  induction s using Multiset.induction
  -- ⊢ Acc (CutExpand r) 0
  case empty => exact Acc.intro 0 fun s h ↦ (not_cutExpand_zero s h).elim
  -- ⊢ Acc (CutExpand r) (a✝¹ ::ₘ s✝)
  -- 🎉 no goals
  case cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha ↦ hs.2 a ha).of_fibration _ (cutExpand_fibration r)
#align relation.acc_of_singleton Relation.acc_of_singleton

/-- A singleton `{a}` is accessible under `CutExpand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
theorem _root_.Acc.cutExpand [IsIrrefl α r] {a : α} (hacc : Acc r a) : Acc (CutExpand r) {a} := by
  induction' hacc with a h ih
  -- ⊢ Acc (CutExpand r) {a}
  refine' Acc.intro _ fun s ↦ _
  -- ⊢ CutExpand r s {a} → Acc (CutExpand r) s
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine' acc_of_singleton fun a' ↦ _
  rw [erase_singleton, zero_add]
  exact ih a' ∘ hr a'
#align acc.cut_expand Acc.cutExpand

/-- `CutExpand r` is well-founded when `r` is. -/
theorem _root_.WellFounded.cutExpand (hr : WellFounded r) : WellFounded (CutExpand r) :=
  ⟨have := hr.isIrrefl; fun _ ↦ acc_of_singleton fun a _ ↦ (hr.apply a).cutExpand⟩
#align well_founded.cut_expand WellFounded.cutExpand

end Relation
