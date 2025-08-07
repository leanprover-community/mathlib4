/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Set.Subsingleton

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

@[simp]
theorem coe_natLT {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} : ⇑(natLT f H) = f :=
  rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def natGT (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((· > ·) : ℕ → ℕ → Prop) ↪r r :=
  haveI := IsStrictOrder.swap r
  RelEmbedding.swap (natLT f H)

@[simp]
theorem coe_natGT {f : ℕ → α} {H : ∀ n : ℕ, r (f (n + 1)) (f n)} : ⇑(natGT f H) = f :=
  rfl

theorem exists_not_acc_lt_of_not_acc {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a := by
  contrapose! h
  refine ⟨_, fun b hr => ?_⟩
  by_contra hb
  exact h b hb hr

/-- A value is accessible iff it isn't contained in any infinite decreasing sequence. -/
theorem acc_iff_no_decreasing_seq {x} :
    Acc r x ↔ IsEmpty { f : ((· > ·) : ℕ → ℕ → Prop) ↪r r // x ∈ Set.range f } := by
  constructor
  · refine fun h => h.recOn fun x _ IH => ?_
    constructor
    rintro ⟨f, k, hf⟩
    exact IsEmpty.elim' (IH (f (k + 1)) (hf ▸ f.map_rel_iff.2 (Nat.lt_succ_self _))) ⟨f, _, rfl⟩
  · have : ∀ x : { a // ¬Acc r a }, ∃ y : { a // ¬Acc r a }, r y.1 x.1 := by
      rintro ⟨x, hx⟩
      cases exists_not_acc_lt_of_not_acc hx with
      | intro w h => exact ⟨⟨w, h.1⟩, h.2⟩
    choose f h using this
    refine fun E =>
      by_contradiction fun hx => E.elim' ⟨natGT (fun n => (f^[n] ⟨x, hx⟩).1) fun n => ?_, 0, rfl⟩
    simp only [Function.iterate_succ']
    apply h

theorem not_acc_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) (k : ℕ) : ¬Acc r (f k) := by
  rw [acc_iff_no_decreasing_seq, not_isEmpty_iff]
  exact ⟨⟨f, k, rfl⟩⟩

/-- A strict order relation is well-founded iff it doesn't have any infinite decreasing sequence.

See `wellFounded_iff_no_descending_seq` for a version which works on any relation. -/
theorem wellFounded_iff_no_descending_seq :
    WellFounded r ↔ IsEmpty (((· > ·) : ℕ → ℕ → Prop) ↪r r) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun f => not_acc_of_decreasing_seq f 0 (h _)⟩
  · intro h
    exact ⟨fun x => acc_iff_no_decreasing_seq.2 inferInstance⟩

theorem not_wellFounded_of_decreasing_seq (f : ((· > ·) : ℕ → ℕ → Prop) ↪r r) : ¬WellFounded r := by
  rw [wellFounded_iff_no_descending_seq, not_isEmpty_iff]
  exact ⟨f⟩

end RelEmbedding

theorem not_strictAnti_of_wellFoundedLT [Preorder α] [WellFoundedLT α] (f : ℕ → α) :
    ¬ StrictAnti f := fun hf ↦
  (RelEmbedding.natGT f (fun n ↦ hf (by simp))).not_wellFounded_of_decreasing_seq wellFounded_lt

theorem not_strictMono_of_wellFoundedGT [Preorder α] [WellFoundedGT α] (f : ℕ → α) :
    ¬ StrictMono f :=
  not_strictAnti_of_wellFoundedLT (α := αᵒᵈ) f

namespace Nat

variable (s : Set ℕ) [Infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def orderEmbeddingOfSet [DecidablePred (· ∈ s)] : ℕ ↪o ℕ :=
  (RelEmbedding.orderEmbeddingOfLTEmbedding
    (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun _ => Nat.Subtype.lt_succ_self _)).trans
    (OrderEmbedding.subtype s)

/-- `Nat.Subtype.ofNat` as an order isomorphism between `ℕ` and an infinite subset. See also
`Nat.Nth` for a version where the subset may be finite. -/
noncomputable def Subtype.orderIsoOfNat : ℕ ≃o s := by
  classical
  exact
    RelIso.ofSurjective
      (RelEmbedding.orderEmbeddingOfLTEmbedding
        (RelEmbedding.natLT (Nat.Subtype.ofNat s) fun n => Nat.Subtype.lt_succ_self _))
      Nat.Subtype.ofNat_surjective

variable {s}

@[simp]
theorem coe_orderEmbeddingOfSet [DecidablePred (· ∈ s)] :
    ⇑(orderEmbeddingOfSet s) = (↑) ∘ Subtype.ofNat s :=
  rfl

theorem orderEmbeddingOfSet_apply [DecidablePred (· ∈ s)] {n : ℕ} :
    orderEmbeddingOfSet s n = Subtype.ofNat s n :=
  rfl

@[simp]
theorem Subtype.orderIsoOfNat_apply [dP : DecidablePred (· ∈ s)] {n : ℕ} :
    Subtype.orderIsoOfNat s n = Subtype.ofNat s n := by
  simp [orderIsoOfNat]; congr!

variable (s)

theorem orderEmbeddingOfSet_range [DecidablePred (· ∈ s)] :
    Set.range (Nat.orderEmbeddingOfSet s) = s :=
  Subtype.coe_comp_ofNat_range

theorem exists_subseq_of_forall_mem_union {s t : Set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
    ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ ∀ n, e (g n) ∈ t := by
  classical
    have : Infinite (e ⁻¹' s) ∨ Infinite (e ⁻¹' t) := by
      simp only [Set.infinite_coe_iff, ← Set.infinite_union, ← Set.preimage_union,
        Set.eq_univ_of_forall fun n => Set.mem_preimage.2 (he n), Set.infinite_univ]
    cases this
    exacts [⟨Nat.orderEmbeddingOfSet (e ⁻¹' s), Or.inl fun n => (Nat.Subtype.ofNat (e ⁻¹' s) _).2⟩,
      ⟨Nat.orderEmbeddingOfSet (e ⁻¹' t), Or.inr fun n => (Nat.Subtype.ofNat (e ⁻¹' t) _).2⟩]

end Nat

theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  classical
    let bad : Set ℕ := { m | ∀ n, m < n → ¬r (f m) (f n) }
    by_cases hbad : Infinite bad
    · refine ⟨Nat.orderEmbeddingOfSet bad, Or.intro_right _ fun m n mn => ?_⟩
      have h := @Set.mem_range_self _ _ ↑(Nat.orderEmbeddingOfSet bad) m
      rw [Nat.orderEmbeddingOfSet_range bad] at h
      exact h _ ((OrderEmbedding.lt_iff_lt _).2 mn)
    · rw [Set.infinite_coe_iff, Set.Infinite, not_not] at hbad
      obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → n ∉ bad := by
        by_cases he : hbad.toFinset.Nonempty
        · refine
            ⟨(hbad.toFinset.max' he).succ, fun n hn nbad =>
              Nat.not_succ_le_self _
                (hn.trans (hbad.toFinset.le_max' n (hbad.mem_toFinset.2 nbad)))⟩
        · exact ⟨0, fun n _ nbad => he ⟨n, hbad.mem_toFinset.2 nbad⟩⟩
      have h : ∀ n : ℕ, ∃ n' : ℕ, n < n' ∧ r (f (n + m)) (f (n' + m)) := by
        intro n
        have h := hm _ (Nat.le_add_left m n)
        simp only [bad, exists_prop, not_not, Set.mem_setOf_eq, not_forall] at h
        obtain ⟨n', hn1, hn2⟩ := h
        refine ⟨n + n' - n - m, by omega, ?_⟩
        convert hn2
        omega
      let g' : ℕ → ℕ := @Nat.rec (fun _ => ℕ) m fun n gn => Nat.find (h gn)
      exact
        ⟨(RelEmbedding.natLT (fun n => g' n + m) fun n =>
              Nat.add_lt_add_right (Nat.find_spec (h (g' n))).1 m).orderEmbeddingOfLTEmbedding,
          Or.intro_left _ fun n => (Nat.find_spec (h (g' n))).2⟩

/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
Bolzano-Weierstrass for `ℝ`. -/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [IsTrans α r] (f : ℕ → α) :
    ∃ g : ℕ ↪o ℕ,
      (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨ ∀ m n : ℕ, m < n → ¬r (f (g m)) (f (g n)) := by
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f
  · refine ⟨g, Or.intro_left _ fun m n mn => ?_⟩
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 mn)
    induction x with
    | zero => apply hr
    | succ x ih =>
      apply IsTrans.trans _ _ _ _ (hr _)
      exact ih (lt_of_lt_of_le m.lt_succ_self (Nat.le_add_right _ _))
  · exact ⟨g, Or.intro_right _ hnr⟩

/-- The **monotone chain condition**: a preorder is co-well-founded iff every increasing sequence
contains two non-increasing indices.

See `wellFoundedGT_iff_monotone_chain_condition` for a stronger version on partial orders. -/
theorem wellFoundedGT_iff_monotone_chain_condition' [Preorder α] :
    WellFoundedGT α ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m := by
  refine ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.wf.has_min _ (Set.range_nonempty a)
    exact ⟨n, fun m _ => H _ (Set.mem_range_self _)⟩
  · rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_no_descending_seq]
    refine ⟨fun a => ?_⟩
    obtain ⟨n, hn⟩ := h (a.swap : _ →r _).toOrderHom
    exact hn n.succ n.lt_succ_self.le ((RelEmbedding.map_rel_iff _).2 n.lt_succ_self)

theorem WellFoundedGT.monotone_chain_condition' [Preorder α] [h : WellFoundedGT α] (a : ℕ →o α) :
    ∃ n, ∀ m, n ≤ m → ¬a n < a m :=
  wellFoundedGT_iff_monotone_chain_condition'.1 h a

/-- A stronger version of the **monotone chain** condition for partial orders.

See `wellFoundedGT_iff_monotone_chain_condition'` for a version on preorders. -/
theorem wellFoundedGT_iff_monotone_chain_condition [PartialOrder α] :
    WellFoundedGT α ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m :=
  wellFoundedGT_iff_monotone_chain_condition'.trans <| by
  congrm ∀ a, ∃ n, ∀ m h, ?_
  rw [lt_iff_le_and_ne]
  simp [a.mono h]

theorem WellFoundedGT.monotone_chain_condition [PartialOrder α] [h : WellFoundedGT α] (a : ℕ →o α) :
    ∃ n, ∀ m, n ≤ m → a n = a m :=
  wellFoundedGT_iff_monotone_chain_condition.1 h a

@[deprecated wellFoundedGT_iff_monotone_chain_condition' (since := "2025-01-15")]
theorem WellFounded.monotone_chain_condition' [Preorder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → ¬a n < a m := by
  rw [← isWellFounded_iff]
  exact wellFoundedGT_iff_monotone_chain_condition'

@[deprecated wellFoundedGT_iff_monotone_chain_condition (since := "2025-01-15")]
theorem WellFounded.monotone_chain_condition [PartialOrder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔ ∀ a : ℕ →o α, ∃ n, ∀ m, n ≤ m → a n = a m := by
  rw [← isWellFounded_iff]
  exact wellFoundedGT_iff_monotone_chain_condition

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonicSequenceLimitIndex a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonicSequenceLimitIndex a`
is defined, but is a junk value. -/
noncomputable def monotonicSequenceLimitIndex [Preorder α] (a : ℕ →o α) : ℕ :=
  sInf { n | ∀ m, n ≤ m → a n = a m }

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonicSequenceLimit [Preorder α] (a : ℕ →o α) :=
  a (monotonicSequenceLimitIndex a)

theorem le_monotonicSequenceLimit [PartialOrder α] [WellFoundedGT α] (a : ℕ →o α) (m : ℕ) :
    a m ≤ monotonicSequenceLimit a := by
  rcases le_or_gt m (monotonicSequenceLimitIndex a) with hm | hm
  · exact a.monotone hm
  · obtain h := WellFoundedGT.monotone_chain_condition a
    exact (Nat.sInf_mem (s := {n | ∀ m, n ≤ m → a n = a m}) h m hm.le).ge

theorem WellFoundedGT.iSup_eq_monotonicSequenceLimit [CompleteLattice α]
    [WellFoundedGT α] (a : ℕ →o α) : iSup a = monotonicSequenceLimit a :=
  (iSup_le (le_monotonicSequenceLimit a)).antisymm (le_iSup a _)

theorem WellFoundedGT.ciSup_eq_monotonicSequenceLimit [ConditionallyCompleteLattice α]
    [WellFoundedGT α] (a : ℕ →o α) (ha : BddAbove (Set.range a)) :
    iSup a = monotonicSequenceLimit a :=
  (ciSup_le (le_monotonicSequenceLimit a)).antisymm (le_ciSup ha _)

@[deprecated WellFoundedGT.iSup_eq_monotonicSequenceLimit (since := "2025-01-15")]
theorem WellFounded.iSup_eq_monotonicSequenceLimit [CompleteLattice α]
    (h : WellFounded ((· > ·) : α → α → Prop)) (a : ℕ →o α) :
    iSup a = monotonicSequenceLimit a := by
  have : WellFoundedGT α := ⟨h⟩
  exact WellFoundedGT.iSup_eq_monotonicSequenceLimit a

theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (α) [Preorder α]
    [Nonempty α] [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] :
    ∃ a : ℕ → α, IsMin (a 0) ∧ ∃ n, IsMax (a n) ∧ ∀ i < n, a i ⋖ a (i + 1) := by
  choose next hnext using exists_covBy_of_wellFoundedLT (α := α)
  have hα := Set.nonempty_iff_univ_nonempty.mp ‹_›
  classical
  let a : ℕ → α := Nat.rec (wfl.wf.min _ hα) fun _n a ↦ if ha : IsMax a then a else next ha
  refine ⟨a, isMin_iff_forall_not_lt.mpr fun _ ↦ wfl.wf.not_lt_min _ hα trivial, ?_⟩
  have cov n (hn : ¬ IsMax (a n)) : a n ⋖ a (n + 1) := by
    change a n ⋖ if ha : IsMax (a n) then a n else _
    rw [dif_neg hn]
    exact hnext hn
  have H : ∃ n, IsMax (a n) := by
    by_contra!
    exact (RelEmbedding.natGT a fun n ↦ (cov n (this n)).1).not_wellFounded_of_decreasing_seq wfg.wf
  exact ⟨_, wellFounded_lt.min_mem _ H, fun i h ↦ cov _ fun h' ↦ wellFounded_lt.not_lt_min _ H h' h⟩

theorem exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le {α : Type*} [PartialOrder α]
    [wfl : WellFoundedLT α] [wfg : WellFoundedGT α] {x y : α} (h : x ≤ y) :
    ∃ a : ℕ → α, a 0 = x ∧ ∃ n, a n = y ∧ ∀ i < n, a i ⋖ a (i + 1) := by
  let S := Set.Icc x y
  let hS : BoundedOrder S :=
    { top := ⟨y, h, le_rfl⟩, le_top x := x.2.2, bot := ⟨x, le_rfl, h⟩, bot_le x := x.2.1 }
  obtain ⟨a, h₁, n, h₂, e⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT S
  simp only [isMin_iff_eq_bot, Subtype.ext_iff, isMax_iff_eq_top] at h₁ h₂
  exact ⟨Subtype.val ∘ a, h₁, n, h₂, fun i hi ↦ ⟨(e i hi).1, fun c hc h ↦ (e i hi).2
    (c := ⟨c, (a i).2.1.trans hc.le, h.le.trans (a _).2.2⟩) hc h⟩⟩
