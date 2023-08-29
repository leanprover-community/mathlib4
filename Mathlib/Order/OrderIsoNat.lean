/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Hom.Basic

#align_import order.order_iso_nat from "leanprover-community/mathlib"@"210657c4ea4a4a7b234392f70a3a2a83346dfa90"

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `natLT`/`natGT`: Make an order embedding `Nat ↪ α` from
   an increasing/decreasing function `Nat → α`.
* `monotonicSequenceLimit`: The limit of an eventually-constant monotone sequence `Nat →o α`.
* `monotonicSequenceLimitIndex`: The index of the first occurrence of `monotonicSequenceLimit`
  in the sequence.
-/


variable {α : Type*}

namespace RelEmbedding

variable {r : α → α → Prop} [IsStrictOrder α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def natLT (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((· < ·) : ℕ → ℕ → Prop) ↪r r :=
  ofMonotone f <| Nat.rel_of_forall_rel_succ_of_lt r H
#align rel_embedding.nat_lt RelEmbedding.natLT

@[simp]
theorem coe_natLT {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} : ⇑(natLT f H) = f :=
  rfl
#align rel_embedding.coe_nat_lt RelEmbedding.coe_natLT

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def natGT (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  haveI := IsStrictOrder.swap r
  RelEmbedding.swap (natLT f H)
#align rel_embedding.nat_gt RelEmbedding.natGT

@[simp]
theorem coe_natGT {f : ℕ → α} {H : ∀ n : ℕ, r (f (n + 1)) (f n)} : ⇑(natGT f H) = f :=
  rfl
#align rel_embedding.coe_nat_gt RelEmbedding.coe_natGT

theorem exists_not_acc_lt_of_not_acc {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a := by
  contrapose! h
  -- ⊢ Acc r a
  refine' ⟨_, fun b hr => _⟩
  -- ⊢ Acc r b
  by_contra hb
  -- ⊢ False
  exact h b hb hr
  -- 🎉 no goals
#align rel_embedding.exists_not_acc_lt_of_not_acc RelEmbedding.exists_not_acc_lt_of_not_acc

/-- A value is accessible iff it isn't contained in any infinite decreasing sequence. -/
theorem acc_iff_no_decreasing_seq {x} :
    Acc r x ↔ IsEmpty { f : ((· > ·) : ℕ → ℕ → Prop) ↪r r // x ∈ Set.range f } := by
  constructor
  -- ⊢ Acc r x → IsEmpty { f // x ∈ Set.range ↑f }
  · refine' fun h => h.recOn fun x _ IH => _
    -- ⊢ IsEmpty { f // x ∈ Set.range ↑f }
    constructor
    -- ⊢ { f // x ∈ Set.range ↑f } → False
    rintro ⟨f, k, hf⟩
    -- ⊢ False
    exact IsEmpty.elim' (IH (f (k + 1)) (hf ▸ f.map_rel_iff.2 (lt_add_one k))) ⟨f, _, rfl⟩
    -- 🎉 no goals
  · have : ∀ x : { a // ¬Acc r a }, ∃ y : { a // ¬Acc r a }, r y.1 x.1 := by
      rintro ⟨x, hx⟩
      cases exists_not_acc_lt_of_not_acc hx with
      | intro w h => exact ⟨⟨w, h.1⟩, h.2⟩
    obtain ⟨f, h⟩ := Classical.axiom_of_choice this
    -- ⊢ IsEmpty { f // x ∈ Set.range ↑f } → Acc r x
    refine' fun E =>
      by_contradiction fun hx => E.elim' ⟨natGT (fun n => (f^[n] ⟨x, hx⟩).1) fun n => _, 0, rfl⟩
    simp only [Function.iterate_succ']
    -- ⊢ r ↑((f ∘ f^[n]) { val := x, property := hx }) ↑(f^[n] { val := x, property : …
    apply h
    -- 🎉 no goals
#align rel_embedding.acc_iff_no_decreasing_seq RelEmbedding.acc_iff_no_decreasing_seq

theorem not_acc_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) (k : ℕ) : ¬Acc r (f k) := by
  rw [acc_iff_no_decreasing_seq, not_isEmpty_iff]
  -- ⊢ Nonempty { f_1 // ↑f k ∈ Set.range ↑f_1 }
  exact ⟨⟨f, k, rfl⟩⟩
  -- 🎉 no goals
#align rel_embedding.not_acc_of_decreasing_seq RelEmbedding.not_acc_of_decreasing_seq

/-- A relation is well-founded iff it doesn't have any infinite decreasing sequence. -/
theorem wellFounded_iff_no_descending_seq :
    WellFounded r ↔ IsEmpty (((· > ·) : ℕ → ℕ → Prop) ↪r r) := by
  constructor
  -- ⊢ WellFounded r → IsEmpty ((fun x x_1 => x > x_1) ↪r r)
  · rintro ⟨h⟩
    -- ⊢ IsEmpty ((fun x x_1 => x > x_1) ↪r r)
    exact ⟨fun f => not_acc_of_decreasing_seq f 0 (h _)⟩
    -- 🎉 no goals
  · intro h
    -- ⊢ WellFounded r
    exact ⟨fun x => acc_iff_no_decreasing_seq.2 inferInstance⟩
    -- 🎉 no goals
#align rel_embedding.well_founded_iff_no_descending_seq RelEmbedding.wellFounded_iff_no_descending_seq

theorem not_wellFounded_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) : ¬WellFounded r := by
  rw [wellFounded_iff_no_descending_seq, not_isEmpty_iff]
  -- ⊢ Nonempty ((fun x x_1 => x > x_1) ↪r r)
  exact ⟨f⟩
  -- 🎉 no goals
#align rel_embedding.not_well_founded_of_decreasing_seq RelEmbedding.not_wellFounded_of_decreasing_seq

end RelEmbedding

namespace Nat

variable (s : Set ℕ) [Infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)
#align nat.order_embedding_of_set Nat.orderEmbeddingOfSet

/-- `Nat.Subtype.ofNat` as an order isomorphism between `ℕ` and an infinite subset. See also
`Nat.Nth` for a version where the subset may be finite. -/
noncomputable def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective
#align nat.subtype.order_iso_of_nat Nat.Subtype.orderIsoOfNat

variable {s}

@[simp]
theorem coe_orderEmbeddingOfSet [DecidablePred (· ∈ s)] :
    ⇑(orderEmbeddingOfSet s) = (↑) ∘ Subtype.ofNat s :=
  rfl
#align nat.coe_order_embedding_of_set Nat.coe_orderEmbeddingOfSet

theorem orderEmbeddingOfSet_apply [DecidablePred (· ∈ s)] {n : ℕ} :
    orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl
#align nat.order_embedding_of_set_apply Nat.orderEmbeddingOfSet_apply

@[simp]
theorem Subtype.orderIsoOfNat_apply [dP : DecidablePred (· ∈ s)] {n : ℕ} :
    Subtype.orderIsoOfNat s n = Subtype.ofNat s n := by
  simp [orderIsoOfNat]; congr!
  -- ⊢ ofNat s n = ofNat s n
                        -- 🎉 no goals
#align nat.subtype.order_iso_of_nat_apply Nat.Subtype.orderIsoOfNat_apply

variable (s)

theorem orderEmbeddingOfSet_range [DecidablePred (· ∈ s)] :
    Set.range (Nat.orderEmbeddingOfSet s) = s :=
  Subtype.coe_comp_ofNat_range
#align nat.order_embedding_of_set_range Nat.orderEmbeddingOfSet_range

theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
    ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ ∀ n, e (g n) ∈ t := by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]
#align nat.exists_subseq_of_forall_mem_union Nat.exists_subseq_of_forall_mem_union

end Nat

theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  classical
    let bad : Set ℕ := { m | ∀ n, m < n → ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · haveI := hbad
      refine' ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => _⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → ¬n ∈ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine'
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : ∀ n : ℕ, ∃ n' : ℕ, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (le_add_of_nonneg_left n.zero_le)
        simp only [exists_prop, not_not, Set.mem_setOf_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        obtain ⟨x, hpos, rfl⟩ := exists_pos_add_of_lt hn1
        refine' ⟨n + x, add_lt_add_left hpos n, _⟩
        rw [add_assoc, add_comm x m, ← add_assoc]
        exact hn2
      let g' : ℕ → ℕ := @Nat.rec (fun _ => ℕ) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩
#align exists_increasing_or_nonincreasing_subseq' exists_increasing_or_nonincreasing_subseq'

/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
    Bolzano-Weierstrass for `ℝ`. -/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  -- ⊢ ∃ g, (∀ (m n : ℕ), m < n → r (f (↑g m)) (f (↑g n))) ∨ ∀ (m n : ℕ), m < n → ¬ …
  · refine' ⟨g, Or.intro_left _ fun m n mn => _⟩
    -- ⊢ r (f (↑g m)) (f (↑g n))
    obtain ⟨x, rfl⟩ := exists_add_of_le (Nat.succ_le_iff.2 mn)
    -- ⊢ r (f (↑g m)) (f (↑g (Nat.succ m + x)))
    induction' x with x ih
    -- ⊢ r (f (↑g m)) (f (↑g (Nat.succ m + Nat.zero)))
    · apply hr
      -- 🎉 no goals
    · apply IsTrans.trans _ _ _ _ (hr _)
      -- ⊢ r (f (↑g m)) (f (↑g (Nat.add (Nat.succ m) x)))
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
      -- 🎉 no goals
  · exact ⟨g, Or.intro_right _ hnr⟩
    -- 🎉 no goals
#align exists_increasing_or_nonincreasing_subseq exists_increasing_or_nonincreasing_subseq

theorem WellFounded.monotone_chain_condition' [Preorder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m := by
  refine' ⟨fun h a => _, fun h => _⟩
  -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → ¬↑a n < ↑a m
  · have hne : (Set.range a).Nonempty := ⟨a 0, by simp⟩
    -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → ¬↑a n < ↑a m
    obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.has_min _ hne
    -- ⊢ ∃ n, ∀ (m : ℕ), n ≤ m → ¬↑a n < ↑a m
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
    -- 🎉 no goals
  · refine' RelEmbedding.wellFounded_iff_no_descending_seq.2 ⟨fun a => _⟩
    -- ⊢ False
    obtain ⟨n, hn⟩ := h (a.swap : ((· < ·) : ℕ → ℕ → Prop) →r ((· < ·) : α → α → Prop)).toOrderHom
    -- ⊢ False
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)
    -- 🎉 no goals
#align well_founded.monotone_chain_condition' WellFounded.monotone_chain_condition'

/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
theorem WellFounded.monotone_chain_condition [PartialOrder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m :=
  WellFounded.monotone_chain_condition'.trans <| by
  congrm ∀ a, ∃ n, ∀ m h, ?_
  -- ⊢ ¬↑a n < ↑a m ↔ ↑a n = ↑a m
  rw [lt_iff_le_and_ne]
  -- ⊢ ¬(↑a n ≤ ↑a m ∧ ↑a n ≠ ↑a m) ↔ ↑a n = ↑a m
  simp [a.mono h]
  -- 🎉 no goals
#align well_founded.monotone_chain_condition WellFounded.monotone_chain_condition

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonicSequenceLimitIndex a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonicSequenceLimitIndex a`
is defined, but is a junk value. -/
noncomputable def monotonicSequenceLimitIndex [Preorder α] (a : ℕ →o α) : ℕ :=
  sInf { n | ∀ m, n ≤ m → a n = a m }
#align monotonic_sequence_limit_index monotonicSequenceLimitIndex

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonicSequenceLimit [Preorder α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)
#align monotonic_sequence_limit monotonicSequenceLimit

theorem WellFounded.iSup_eq_monotonicSequenceLimit [CompleteLattice α]
    (h : WellFounded ((· > ·) : α → α → Prop)) (a : ℕ →o α) :
    iSup a = monotonicSequenceLimit a := by
  refine' (iSup_le fun m => _).antisymm (le_iSup a _)
  -- ⊢ ↑a m ≤ monotonicSequenceLimit a
  cases' le_or_lt m (monotonicSequenceLimitIndex a) with hm hm
  -- ⊢ ↑a m ≤ monotonicSequenceLimit a
  · exact a.monotone hm
    -- 🎉 no goals
  · cases' WellFounded.monotone_chain_condition'.1 h a with n hn
    -- ⊢ ↑a m ≤ monotonicSequenceLimit a
    have : n ∈ {n | ∀ m, n ≤ m → a n = a m} := fun k hk => (a.mono hk).eq_of_not_lt (hn k hk)
    -- ⊢ ↑a m ≤ monotonicSequenceLimit a
    exact (Nat.sInf_mem ⟨n, this⟩ m hm.le).ge
    -- 🎉 no goals
#align well_founded.supr_eq_monotonic_sequence_limit WellFounded.iSup_eq_monotonicSequenceLimit
