/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Order.GameAdd

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

@[expose] public section


namespace Relation

open Multiset Prod

variable {α : Type*}

/-- The relation that specifies valid moves in our hydra game. `CutExpand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `Multiset.erase` requires
  `DecidableEq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  The lemma `Relation.cutExpand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
def CutExpand (r : α → α → Prop) (s' s : Multiset α) : Prop :=
  ∃ (t : Multiset α) (a : α), a ∈ s ∧ (∀ a' ∈ t, r a' a) ∧ s' + {a} = s + t

variable {r : α → α → Prop}

theorem cutExpand_le_invImage_lex [DecidableEq α] [Std.Irrefl r] :
    CutExpand r ≤ InvImage (Finsupp.Lex (rᶜ ⊓ (· ≠ ·)) (· < ·)) toFinsupp := by
  rintro s t ⟨u, a, ha, hr, he⟩
  replace hr := fun a' ↦ mt (hr a')
  refine ⟨a, fun b h ↦ ?_, ?_⟩ <;> simp_rw [toFinsupp_apply]
  · apply_fun count b at he
    simpa only [count_add, count_singleton, ite_eq_right h.2, add_zero, count_eq_zero.2 (hr b h.1)]
      using he
  · apply_fun count a at he
    simp only [count_add, count_singleton_self, count_eq_zero.2 (hr _ (irrefl_of r a)),
      add_zero] at he
    exact he ▸ Nat.lt_succ_self _

theorem cutExpand_singleton {s x} (h : ∀ x' ∈ s, r x' x) : CutExpand r s {x} :=
  ⟨s, x, mem_singleton_self x, h, add_comm s _⟩

theorem cutExpand_singleton_singleton {x' x} (h : r x' x) : CutExpand r {x'} {x} :=
  cutExpand_singleton fun a h ↦ by rwa [mem_singleton.1 h]

theorem CutExpand.add_left {t u} (s) (h : CutExpand r t u) :
    CutExpand r (s + t) (s + u) := by
  obtain ⟨k, a, ha, hk, h⟩ := h
  refine ⟨k, a, mem_add.2 (.inr ha), hk, ?_⟩
  rw [add_assoc, add_assoc, h]

theorem CutExpand.add_right {t u} (s) (h : CutExpand r t u) :
    CutExpand r (t + s) (u + s) := by
  rw [add_comm t s, add_comm u s]
  exact h.add_left s

theorem cutExpand_add_left [Std.Irrefl r] {t u} (s) :
    CutExpand r (s + t) (s + u) ↔ CutExpand r t u := by
  refine ⟨fun h => ?_, fun h => h.add_left s⟩
  obtain ⟨k, a, ha, hk, h⟩ := h
  rw [add_assoc, add_assoc, add_right_inj] at h
  refine ⟨k, a, ?_, hk, h⟩
  refine (mem_add.1 ?_).resolve_right fun hak => irrefl_of r a (hk a hak)
  rw [← h]
  simp

lemma cutExpand_add_right [Std.Irrefl r] {s' s} (t) :
    CutExpand r (s' + t) (s + t) ↔ CutExpand r s' s := by
  rw [add_comm s' t, add_comm s t, cutExpand_add_left]

theorem cutExpand_add_singleton_single {a' a : α} (s : Multiset α) (h : r a' a) :
    CutExpand r (s + {a'}) (s + {a}) :=
  ⟨{a'}, a, mem_add.2 (.inr (mem_singleton_self a)), by simpa using h, by ac_rfl⟩

@[deprecated (since := "2026-08-16")]
alias cutExpand_add_single := cutExpand_add_singleton_single

theorem cutExpand_singleton_add_single {a' a : α} (h : r a' a) (s : Multiset α) :
    CutExpand r ({a'} + s) ({a} + s) := by
  rw [add_comm {a'} s, add_comm {a} s]
  exact cutExpand_add_singleton_single s h

@[deprecated (since := "2026-08-16")]
alias cutExpand_single_add := cutExpand_singleton_add_single

theorem cutExpand_iff [DecidableEq α] {s' s : Multiset α} :
    CutExpand r s' s ↔
      ∃ (t : Multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t := by
  simp_rw [CutExpand, add_singleton_eq_iff, mem_add]
  refine exists₂_congr fun t a ↦ ?_
  rw [and_left_comm, and_congr_right_iff]
  intro ht
  rw [← and_assoc, and_iff_left_of_imp Or.inl, and_congr_right_iff]
  intro has
  rw [erase_add_left_pos t has]

theorem not_cutExpand_zero (s) : ¬CutExpand r s 0 := by simp [CutExpand]

lemma cutExpand_zero_singleton {x} : CutExpand r 0 {x} :=
  ⟨0, x, mem_singleton_self x, by simp, add_comm 0 _⟩

@[deprecated (since := "2026-08-16")] alias cutExpand_zero := cutExpand_zero_singleton

/-- For any relation `r` on `α`, multiset addition `Multiset α × Multiset α → Multiset α` is a
  fibration between the game sum of `CutExpand r` with itself and `CutExpand r` itself. -/
theorem cutExpand_fibration (r : α → α → Prop) :
    Fibration (GameAdd (CutExpand r) (CutExpand r)) (CutExpand r) fun s ↦ s.1 + s.2 := by
  rintro ⟨s₁, s₂⟩ s ⟨t, a, ha, hr, he⟩; dsimp at ha he ⊢
  classical
  rw [← cons_erase ha, ← singleton_add, add_comm s {a}, add_assoc, add_right_inj] at he
  subst he
  rw [mem_add] at ha
  obtain h | h := ha
  · refine ⟨(s₁.erase a + t, s₂), GameAdd.fst ⟨t, a, h, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [add_right_comm, erase_add_left_pos _ h]
  · refine ⟨(s₁, s₂.erase a + t), GameAdd.snd ⟨t, a, h, hr, ?_⟩, ?_⟩
    · rw [add_comm, ← add_assoc, singleton_add, cons_erase h]
    · rw [← add_assoc, erase_add_right_pos _ h]

/-- `CutExpand` preserves leftward-closedness under a relation. -/
lemma cutExpand_closed (p : α → Prop)
    (h : ∀ {a' a}, r a' a → p a → p a') {s' s : Multiset α} :
    CutExpand r s' s → (∀ a ∈ s, p a) → ∀ a ∈ s', p a := by
  classical
  rw [cutExpand_iff]
  rintro ⟨t, a, hr, ha, rfl⟩ hsp a' h'
  obtain (h' | h') := mem_add.1 h'
  exacts [hsp a' (mem_of_mem_erase h'), h (hr a' h') (hsp a ha)]

lemma cutExpand_double {a a₁ a₂} (h₁ : r a₁ a) (h₂ : r a₂ a) : CutExpand r {a₁, a₂} {a} :=
  cutExpand_singleton <| by
    simp only [insert_eq_cons, mem_cons, mem_singleton, forall_eq_or_imp, forall_eq]
    tauto

lemma cutExpand_pair_pair_left {a' a b} (hr : r a' a) : CutExpand r {a', b} {a, b} := by
  rw [insert_eq_cons, insert_eq_cons, ← singleton_add, ← singleton_add]
  exact cutExpand_singleton_add_single hr {b}

@[deprecated (since := "2026-08-16")]
alias cutExpand_pair_left := cutExpand_pair_pair_left

lemma cutExpand_pair_pair_right {a b' b} (hr : r b' b) : CutExpand r {a, b'} {a, b} := by
  rw [insert_eq_cons, insert_eq_cons, ← singleton_add, ← singleton_add]
  exact cutExpand_add_singleton_single {a} hr

@[deprecated (since := "2026-08-16")]
alias cutExpand_pair_right := cutExpand_pair_pair_right

lemma cutExpand_triple_pair_left {a a₁ a₂ b} (h₁ : r a₁ a) (h₂ : r a₂ a) :
    CutExpand r {a₁, a₂, b} {a, b} := by
  simp_rw [insert_eq_cons, ← singleton_add, ← add_assoc]
  exact (cutExpand_singleton (by simp [h₁, h₂])).add_right {b}

@[deprecated (since := "2026-08-16")]
alias cutExpand_double_left := cutExpand_triple_pair_left

/-- A multiset is accessible under `CutExpand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
private theorem acc_of_singleton {s : Multiset α} (hs : ∀ a ∈ s, Acc (CutExpand r) {a}) :
    Acc (CutExpand r) s := by
  induction s using Multiset.induction with
  | empty => exact Acc.intro 0 fun s h ↦ (not_cutExpand_zero s h).elim
  | cons a s ihs =>
    rw [← s.singleton_add a]
    rw [forall_mem_cons] at hs
    exact (hs.1.prod_gameAdd <| ihs fun a ha ↦ hs.2 a ha).of_fibration _ (cutExpand_fibration r)

/-- A singleton `{a}` is accessible under `CutExpand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
theorem _root_.Acc.cutExpand_singleton {a : α} (hacc : Acc r a) : Acc (CutExpand r) {a} := by
  induction hacc with | _ a h ih
  refine Acc.intro _ fun s ↦ ?_
  classical
  simp only [cutExpand_iff, mem_singleton]
  rintro ⟨t, a, hr, rfl, rfl⟩
  refine acc_of_singleton fun a' ↦ ?_
  rw [erase_singleton, zero_add]
  exact ih a' ∘ hr a'

@[deprecated (since := "2026-08-16")]
alias _root_.Acc.cutExpand := Acc.cutExpand_singleton

theorem acc_cutExpand {s} (hs : ∀ a ∈ s, Acc r a) : Acc (CutExpand r) s :=
  acc_of_singleton fun a ha => (hs a ha).cutExpand_singleton

theorem acc_cutExpand_iff {s} : Acc (CutExpand r) s ↔ ∀ a ∈ s, Acc r a := by
  refine ⟨fun h a ha => ?_, acc_cutExpand⟩
  classical
  induction h generalizing a with
  | intro s h ih =>
    refine .intro _ fun b hb => ?_
    refine ih (s.erase a + {b}) ?_ b (mem_add.2 (.inr (mem_singleton_self b)))
    rw [cutExpand_iff]
    exact ⟨{b}, a, by simp [hb], ha, rfl⟩

/-- `CutExpand r` is well-founded when `r` is. -/
theorem _root_.WellFounded.cutExpand (hr : WellFounded r) : WellFounded (CutExpand r) :=
  ⟨fun _ ↦ acc_cutExpand fun _ _ => hr.apply _⟩

instance [h : IsWellFounded α r] : IsWellFounded _ (CutExpand r) :=
  ⟨h.wf.cutExpand⟩

end Relation
