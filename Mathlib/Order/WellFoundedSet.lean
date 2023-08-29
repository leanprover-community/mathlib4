/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Init.Data.Sigma.Lex
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.Antichain
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.WellFounded
import Mathlib.Tactic.TFAE

#align_import order.well_founded_set from "leanprover-community/mathlib"@"2c84c2c5496117349007d97104e7bbb471381592"

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `Set.WellFoundedOn s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `Set.IsWf s` indicates that `<` is well-founded when restricted to `s`.
 * `Set.PartiallyWellOrderedOn s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
 * `Set.IsPwo s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results
 * Higman's Lemma, `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`,
  shows that if `r` is partially well-ordered on `s`, then `List.SublistForall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
 * `Set.wellFoundedOn_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `Set.IsWf.mono` shows that a subset of a well-founded subset is well-founded.
 * `Set.IsWf.union` shows that the union of two well-founded subsets is well-founded.
 * `Finset.isWf` shows that all `Finset`s are well-founded.

## TODO

Prove that `s` is partial well ordered iff it has no infinite descending chain or antichain.

## References
 * [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
 * [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/


variable {ι α β γ : Type*} {π : ι → Type*}

namespace Set

/-! ### Relations well-founded on sets -/


/-- `s.WellFoundedOn r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded fun a b : s => r a b
#align set.well_founded_on Set.WellFoundedOn

@[simp]
theorem wellFoundedOn_empty (r : α → α → Prop) : WellFoundedOn ∅ r :=
  wellFounded_of_isEmpty _
#align set.well_founded_on_empty Set.wellFoundedOn_empty

section WellFoundedOn

variable {r r' : α → α → Prop}

section AnyRel

variable {f : β → α} {s t : Set α} {x y : α}

theorem wellFoundedOn_iff :
    s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s := by
  have f : RelEmbedding (fun (a : s) (b : s) => r a b) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine' ⟨fun h => _, f.wellFounded⟩
  -- ⊢ WellFounded fun a b => r a b ∧ a ∈ s ∧ b ∈ s
  rw [WellFounded.wellFounded_iff_has_min]
  -- ⊢ ∀ (s_1 : Set α), Set.Nonempty s_1 → ∃ m, m ∈ s_1 ∧ ∀ (x : α), x ∈ s_1 → ¬(r  …
  intro t ht
  -- ⊢ ∃ m, m ∈ t ∧ ∀ (x : α), x ∈ t → ¬(r x m ∧ x ∈ s ∧ m ∈ s)
  by_cases hst : (s ∩ t).Nonempty
  -- ⊢ ∃ m, m ∈ t ∧ ∀ (x : α), x ∈ t → ¬(r x m ∧ x ∈ s ∧ m ∈ s)
  · rw [← Subtype.preimage_coe_nonempty] at hst
    -- ⊢ ∃ m, m ∈ t ∧ ∀ (x : α), x ∈ t → ¬(r x m ∧ x ∈ s ∧ m ∈ s)
    rcases h.has_min (Subtype.val ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    -- ⊢ ∃ m, m ∈ t ∧ ∀ (x : α), x ∈ t → ¬(r x m ∧ x ∈ s ∧ m ∈ s)
    exact ⟨m, mt, fun x xt ⟨xm, xs, _⟩ => hm ⟨x, xs⟩ xt xm⟩
    -- 🎉 no goals
  · rcases ht with ⟨m, mt⟩
    -- ⊢ ∃ m, m ∈ t ∧ ∀ (x : α), x ∈ t → ¬(r x m ∧ x ∈ s ∧ m ∈ s)
    exact ⟨m, mt, fun x _ ⟨_, _, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩
    -- 🎉 no goals
#align set.well_founded_on_iff Set.wellFoundedOn_iff

@[simp]
theorem wellFoundedOn_univ : (univ : Set α).WellFoundedOn r ↔ WellFounded r := by
  simp [wellFoundedOn_iff]
  -- 🎉 no goals
#align set.well_founded_on_univ Set.wellFoundedOn_univ

theorem _root_.WellFounded.wellFoundedOn : WellFounded r → s.WellFoundedOn r :=
  InvImage.wf _
#align well_founded.well_founded_on WellFounded.wellFoundedOn

@[simp]
theorem wellFoundedOn_range : (range f).WellFoundedOn r ↔ WellFounded (r on f) := by
  let f' : β → range f := fun c => ⟨f c, c, rfl⟩
  -- ⊢ WellFoundedOn (range f) r ↔ WellFounded (r on f)
  refine' ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨_⟩⟩
  -- ⊢ ∀ (a : ↑(range f)), Acc (fun a b => r ↑a ↑b) a
  rintro ⟨_, c, rfl⟩
  -- ⊢ Acc (fun a b => r ↑a ↑b) { val := f c, property := (_ : ∃ y, f y = f c) }
  refine' Acc.of_downward_closed f' _ _ _
  -- ⊢ ∀ {a : β} {b : ↑(range f)}, r ↑b ↑(f' a) → ∃ c, f' c = b
  · rintro _ ⟨_, c', rfl⟩ -
    -- ⊢ ∃ c, f' c = { val := f c', property := (_ : ∃ y, f y = f c') }
    exact ⟨c', rfl⟩
    -- 🎉 no goals
  · exact h.apply _
    -- 🎉 no goals
#align set.well_founded_on_range Set.wellFoundedOn_range

@[simp]
theorem wellFoundedOn_image {s : Set β} : (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f) := by
  rw [image_eq_range]; exact wellFoundedOn_range
  -- ⊢ WellFoundedOn (range fun x => f ↑x) r ↔ WellFoundedOn s (r on f)
                       -- 🎉 no goals
#align set.well_founded_on_image Set.wellFoundedOn_image

namespace WellFoundedOn

protected theorem induction (hs : s.WellFoundedOn r) (hx : x ∈ s) {P : α → Prop}
    (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x := by
  let Q : s → Prop := fun y => P y
  -- ⊢ P x
  change Q ⟨x, hx⟩
  -- ⊢ Q { val := x, property := hx }
  refine' WellFounded.induction hs ⟨x, hx⟩ _
  -- ⊢ ∀ (x : ↑s), (∀ (y : ↑s), r ↑y ↑x → Q y) → Q x
  simpa only [Subtype.forall]
  -- 🎉 no goals
#align set.well_founded_on.induction Set.WellFoundedOn.induction

protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) :
    s.WellFoundedOn r := by
  rw [wellFoundedOn_iff] at *
  -- ⊢ WellFounded fun a b => r a b ∧ a ∈ s ∧ b ∈ s
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h
  -- 🎉 no goals
#align set.well_founded_on.mono Set.WellFoundedOn.mono

theorem mono' (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), r' a b → r a b) :
    s.WellFoundedOn r → s.WellFoundedOn r' :=
  Subrelation.wf @fun a b => h _ a.2 _ b.2
#align set.well_founded_on.mono' Set.WellFoundedOn.mono'

theorem subset (h : t.WellFoundedOn r) (hst : s ⊆ t) : s.WellFoundedOn r :=
  h.mono le_rfl hst
#align set.well_founded_on.subset Set.WellFoundedOn.subset

open Relation

open List in
/-- `a` is accessible under the relation `r` iff `r` is well-founded on the downward transitive
closure of `a` under `r` (including `a` or not). -/
theorem acc_iff_wellFoundedOn {α} {r : α → α → Prop} {a : α} :
    TFAE [Acc r a,
      WellFoundedOn { b | ReflTransGen r b a } r,
      WellFoundedOn { b | TransGen r b a } r] := by
  tfae_have 1 → 2
  -- ⊢ Acc r a → WellFoundedOn {b | ReflTransGen r b a} r
  · refine fun h => ⟨fun b => InvImage.accessible _ ?_⟩
    -- ⊢ Acc r ↑b
    rw [← acc_transGen_iff] at h ⊢
    -- ⊢ Acc (TransGen r) ↑b
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    -- ⊢ Acc (TransGen r) ↑b
    · rwa [h'] at h
      -- 🎉 no goals
    · exact h.inv h'
      -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ WellFoundedOn {b | ReflTransGen r b a} r → WellFoundedOn {b | TransGen r b a …
  · exact fun h => h.subset fun _ => TransGen.to_reflTransGen
    -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ WellFoundedOn {b | TransGen r b a} r → Acc r a
  · refine fun h => Acc.intro _ (fun b hb => (h.apply ⟨b, .single hb⟩).of_fibration Subtype.val ?_)
    -- ⊢ Fibration (fun a_1 b => r ↑a_1 ↑b) r Subtype.val
    exact fun ⟨c, hc⟩ d h => ⟨⟨d, .head h hc⟩, h, rfl⟩
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align set.well_founded_on.acc_iff_well_founded_on Set.WellFoundedOn.acc_iff_wellFoundedOn

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s where
  toIsIrrefl := ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩
#align set.is_strict_order.subset Set.IsStrictOrder.subset

theorem wellFoundedOn_iff_no_descending_seq :
    s.WellFoundedOn r ↔ ∀ f : ((· > ·) : ℕ → ℕ → Prop) ↪r r, ¬∀ n, f n ∈ s := by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_no_descending_seq, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  -- ⊢ Nonempty ((fun x x_1 => x > x_1) ↪r fun a b => r a b ∧ a ∈ s ∧ b ∈ s) → ∃ x, …
  · rintro ⟨⟨f, hf⟩⟩
    -- ⊢ ∃ x, ∀ (n : ℕ), ↑x n ∈ s
    have H : ∀ n, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
    -- ⊢ ∃ x, ∀ (n : ℕ), ↑x n ∈ s
    refine' ⟨⟨f, _⟩, H⟩
    -- ⊢ ∀ {a b : ℕ}, r (↑f a) (↑f b) ↔ a > b
    simpa only [H, and_true_iff] using @hf
    -- 🎉 no goals
  · rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩
    -- ⊢ Nonempty ((fun x x_1 => x > x_1) ↪r fun a b => r a b ∧ a ∈ s ∧ b ∈ s)
    refine' ⟨⟨f, _⟩⟩
    -- ⊢ ∀ {a b : ℕ}, r (↑f a) (↑f b) ∧ ↑f a ∈ s ∧ ↑f b ∈ s ↔ a > b
    simpa only [hfs, and_true_iff] using @hf
    -- 🎉 no goals
#align set.well_founded_on_iff_no_descending_seq Set.wellFoundedOn_iff_no_descending_seq

theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) :
    (s ∪ t).WellFoundedOn r := by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  -- ⊢ ∀ (f : (fun x x_1 => x > x_1) ↪r r), ¬∀ (n : ℕ), ↑f n ∈ s ∪ t
  rintro f hf
  -- ⊢ False
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  -- ⊢ False
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]
  -- 🎉 no goals
#align set.well_founded_on.union Set.WellFoundedOn.union

@[simp]
theorem wellFoundedOn_union : (s ∪ t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.subset <| subset_union_left _ _, h.subset <| subset_union_right _ _⟩, fun h =>
    h.1.union h.2⟩
#align set.well_founded_on_union Set.wellFoundedOn_union

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/

section LT

variable [LT α] {s t : Set α}

/-- `s.IsWf` indicates that `<` is well-founded when restricted to `s`. -/
def IsWf (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)
#align set.is_wf Set.IsWf

@[simp]
theorem isWf_empty : IsWf (∅ : Set α) :=
  wellFounded_of_isEmpty _
#align set.is_wf_empty Set.isWf_empty

theorem isWf_univ_iff : IsWf (univ : Set α) ↔ WellFounded ((· < ·) : α → α → Prop) := by
  simp [IsWf, wellFoundedOn_iff]
  -- 🎉 no goals
#align set.is_wf_univ_iff Set.isWf_univ_iff

theorem IsWf.mono (h : IsWf t) (st : s ⊆ t) : IsWf s := h.subset st
#align set.is_wf.mono Set.IsWf.mono

end LT

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

protected nonrec theorem IsWf.union (hs : IsWf s) (ht : IsWf t) : IsWf (s ∪ t) := hs.union ht
#align set.is_wf.union Set.IsWf.union

@[simp] theorem isWf_union : IsWf (s ∪ t) ↔ IsWf s ∧ IsWf t := wellFoundedOn_union
#align set.is_wf_union Set.isWf_union

end Preorder

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

theorem isWf_iff_no_descending_seq :
    IsWf s ↔ ∀ f : ℕ → α, StrictAnti f → ¬∀ n, f (OrderDual.toDual n) ∈ s :=
  wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_lt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩
#align set.is_wf_iff_no_descending_seq Set.isWf_iff_no_descending_seq

end Preorder

/-!
### Partially well-ordered sets

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `IsAntichain`) is
finite, see `Set.partiallyWellOrderedOn_iff_finite_antichains`.
-/


/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def PartiallyWellOrderedOn (s : Set α) (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n : ℕ, m < n ∧ r (f m) (f n)
#align set.partially_well_ordered_on Set.PartiallyWellOrderedOn

section PartiallyWellOrderedOn

variable {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α} {t : Set α} {a : α}

theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) :
    s.PartiallyWellOrderedOn r := fun f hf => ht f fun n => h <| hf n
#align set.partially_well_ordered_on.mono Set.PartiallyWellOrderedOn.mono

@[simp]
theorem partiallyWellOrderedOn_empty (r : α → α → Prop) : PartiallyWellOrderedOn ∅ r := fun _ h =>
  (h 0).elim
#align set.partially_well_ordered_on_empty Set.partiallyWellOrderedOn_empty

theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r)
    (ht : t.PartiallyWellOrderedOn r) : (s ∪ t).PartiallyWellOrderedOn r := by
  rintro f hf
  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hgs | hgt⟩
  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  · rcases hs _ hgs with ⟨m, n, hlt, hr⟩
    -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
    -- 🎉 no goals
  · rcases ht _ hgt with ⟨m, n, hlt, hr⟩
    -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
    -- 🎉 no goals
#align set.partially_well_ordered_on.union Set.PartiallyWellOrderedOn.union

@[simp]
theorem partiallyWellOrderedOn_union :
    (s ∪ t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h => ⟨h.mono <| subset_union_left _ _, h.mono <| subset_union_right _ _⟩, fun h =>
    h.1.union h.2⟩
#align set.partially_well_ordered_on_union Set.partiallyWellOrderedOn_union

theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : ∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' := by
  intro g' hg'
  -- ⊢ ∃ m n, m < n ∧ r' (g' m) (g' n)
  choose g hgs heq using hg'
  -- ⊢ ∃ m n, m < n ∧ r' (g' m) (g' n)
  obtain rfl : f ∘ g = g'; exact funext heq
  -- ⊢ f ∘ g = g'
                           -- ⊢ ∃ m n, m < n ∧ r' ((f ∘ g) m) ((f ∘ g) n)
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  -- ⊢ ∃ m n, m < n ∧ r' ((f ∘ g) m) ((f ∘ g) n)
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩
  -- 🎉 no goals
#align set.partially_well_ordered_on.image_of_monotone_on Set.PartiallyWellOrderedOn.image_of_monotone_on

theorem _root_.IsAntichain.finite_of_partiallyWellOrderedOn (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite := by
  refine' not_infinite.1 fun hi => _
  -- ⊢ False
  obtain ⟨m, n, hmn, h⟩ := hp (fun n => hi.natEmbedding _ n) fun n => (hi.natEmbedding _ n).2
  -- ⊢ False
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)
#align is_antichain.finite_of_partially_well_ordered_on IsAntichain.finite_of_partiallyWellOrderedOn

section IsRefl

variable [IsRefl α r]

protected theorem Finite.partiallyWellOrderedOn (hs : s.Finite) : s.PartiallyWellOrderedOn r := by
  intro f hf
  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  obtain ⟨m, n, hmn, h⟩ := hs.exists_lt_map_eq_of_forall_mem hf
  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  exact ⟨m, n, hmn, h.subst <| refl (f m)⟩
  -- 🎉 no goals
#align set.finite.partially_well_ordered_on Set.Finite.partiallyWellOrderedOn

theorem _root_.IsAntichain.partiallyWellOrderedOn_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩
#align is_antichain.partially_well_ordered_on_iff IsAntichain.partiallyWellOrderedOn_iff

@[simp]
theorem partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).partiallyWellOrderedOn
#align set.partially_well_ordered_on_singleton Set.partiallyWellOrderedOn_singleton

@[nontriviality]
theorem Subsingleton.partiallyWellOrderedOn (hs : s.Subsingleton) : PartiallyWellOrderedOn s r :=
  hs.finite.partiallyWellOrderedOn

@[simp]
theorem partiallyWellOrderedOn_insert :
    PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and_iff]
#align set.partially_well_ordered_on_insert Set.partiallyWellOrderedOn_insert

protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partiallyWellOrderedOn_insert.2 h
#align set.partially_well_ordered_on.insert Set.PartiallyWellOrderedOn.insert

theorem partiallyWellOrderedOn_iff_finite_antichains [IsSymm α r] :
    s.PartiallyWellOrderedOn r ↔ ∀ t, t ⊆ s → IsAntichain r t → t.Finite := by
  refine' ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), _⟩
  -- ⊢ (∀ (t : Set α), t ⊆ s → IsAntichain r t → Set.Finite t) → PartiallyWellOrder …
  rintro hs f hf
  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  by_contra' H
  -- ⊢ False
  refine' infinite_range_of_injective (fun m n hmn => _) (hs _ (range_subset_iff.2 hf) _)
  -- ⊢ m = n
  · obtain h | h | h := lt_trichotomy m n
    · refine' (H _ _ h _).elim
      -- ⊢ r (f m) (f n)
      rw [hmn]
      -- ⊢ r (f n) (f n)
      exact refl _
      -- 🎉 no goals
    · exact h
      -- 🎉 no goals
    · refine' (H _ _ h _).elim
      -- ⊢ r (f n) (f m)
      rw [hmn]
      -- ⊢ r (f n) (f n)
      exact refl _
      -- 🎉 no goals
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  -- ⊢ rᶜ ((fun y => f y) m) ((fun y => f y) n)
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_lt
  -- ⊢ rᶜ ((fun y => f y) m) ((fun y => f y) n)
  · exact H _ _ h
    -- 🎉 no goals
  · exact mt symm (H _ _ h)
    -- 🎉 no goals
#align set.partially_well_ordered_on_iff_finite_antichains Set.partiallyWellOrderedOn_iff_finite_antichains

variable [IsTrans α r]

theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) (f : ℕ → α)
    (hf : ∀ n, f n ∈ s) : ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  -- ⊢ ∃ g, ∀ (m n : ℕ), m ≤ n → r (f (↑g m)) (f (↑g n))
  · refine' ⟨g, fun m n hle => _⟩
    -- ⊢ r (f (↑g m)) (f (↑g n))
    obtain hlt | rfl := hle.lt_or_eq
    -- ⊢ r (f (↑g m)) (f (↑g n))
    exacts [h1 m n hlt, refl_of r _]
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) fun n => hf _
    -- ⊢ False
    exact h2 m n hlt hle
    -- 🎉 no goals
#align set.partially_well_ordered_on.exists_monotone_subseq Set.PartiallyWellOrderedOn.exists_monotone_subseq

theorem partiallyWellOrderedOn_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔
      ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  constructor <;> intro h f hf
  -- ⊢ PartiallyWellOrderedOn s r → ∀ (f : ℕ → α), (∀ (n : ℕ), f n ∈ s) → ∃ g, ∀ (m …
                  -- ⊢ ∃ g, ∀ (m n : ℕ), m ≤ n → r (f (↑g m)) (f (↑g n))
                  -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
  · exact h.exists_monotone_subseq f hf
    -- 🎉 no goals
  · obtain ⟨g, gmon⟩ := h f hf
    -- ⊢ ∃ m n, m < n ∧ r (f m) (f n)
    exact ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩
    -- 🎉 no goals
#align set.partially_well_ordered_on_iff_exists_monotone_subseq Set.partiallyWellOrderedOn_iff_exists_monotone_subseq

protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') :
    PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 := by
  intro f hf
  -- ⊢ ∃ m n, m < n ∧ (fun x y => r x.fst y.fst ∧ r' x.snd y.snd) (f m) (f n)
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq (Prod.fst ∘ f) fun n => (hf n).1
  -- ⊢ ∃ m n, m < n ∧ (fun x y => r x.fst y.fst ∧ r' x.snd y.snd) (f m) (f n)
  obtain ⟨m, n, hlt, hle⟩ := ht (Prod.snd ∘ f ∘ g₁) fun n => (hf _).2
  -- ⊢ ∃ m n, m < n ∧ (fun x y => r x.fst y.fst ∧ r' x.snd y.snd) (f m) (f n)
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩
  -- 🎉 no goals
#align set.partially_well_ordered_on.prod Set.PartiallyWellOrderedOn.prod

end IsRefl

theorem PartiallyWellOrderedOn.wellFoundedOn [IsPreorder α r] (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬r b a := by
  letI : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  change s.WellFoundedOn (· < ·)
  -- ⊢ WellFoundedOn s fun x x_1 => x < x_1
  replace h : s.PartiallyWellOrderedOn (· ≤ ·) := h -- porting note: was `change _ at h`
  -- ⊢ WellFoundedOn s fun x x_1 => x < x_1
  rw [wellFoundedOn_iff_no_descending_seq]
  -- ⊢ ∀ (f : (fun x x_1 => x > x_1) ↪r fun x x_1 => x < x_1), ¬∀ (n : ℕ), ↑f n ∈ s
  intro f hf
  -- ⊢ False
  obtain ⟨m, n, hlt, hle⟩ := h f hf
  -- ⊢ False
  exact (f.map_rel_iff.2 hlt).not_le hle
  -- 🎉 no goals
#align set.partially_well_ordered_on.well_founded_on Set.PartiallyWellOrderedOn.wellFoundedOn

end PartiallyWellOrderedOn

section IsPwo

variable [Preorder α] [Preorder β] {s t : Set α}

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def IsPwo (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· ≤ ·)
#align set.is_pwo Set.IsPwo

nonrec theorem IsPwo.mono (ht : t.IsPwo) : s ⊆ t → s.IsPwo := ht.mono
#align set.is_pwo.mono Set.IsPwo.mono

nonrec theorem IsPwo.exists_monotone_subseq (h : s.IsPwo) (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf
#align set.is_pwo.exists_monotone_subseq Set.IsPwo.exists_monotone_subseq

theorem isPwo_iff_exists_monotone_subseq :
    s.IsPwo ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partiallyWellOrderedOn_iff_exists_monotone_subseq
#align set.is_pwo_iff_exists_monotone_subseq Set.isPwo_iff_exists_monotone_subseq

protected theorem IsPwo.isWf (h : s.IsPwo) : s.IsWf := by
  simpa only [← lt_iff_le_not_le] using h.wellFoundedOn
  -- 🎉 no goals
#align set.is_pwo.is_wf Set.IsPwo.isWf

nonrec theorem IsPwo.prod {t : Set β} (hs : s.IsPwo) (ht : t.IsPwo) : IsPwo (s ×ˢ t) :=
  hs.prod ht
#align set.is_pwo.prod Set.IsPwo.prod

theorem IsPwo.image_of_monotoneOn (hs : s.IsPwo) {f : α → β} (hf : MonotoneOn f s) :
    IsPwo (f '' s) :=
  hs.image_of_monotone_on hf
#align set.is_pwo.image_of_monotone_on Set.IsPwo.image_of_monotoneOn

theorem IsPwo.image_of_monotone (hs : s.IsPwo) {f : α → β} (hf : Monotone f) : IsPwo (f '' s) :=
  hs.image_of_monotone_on (hf.monotoneOn _)
#align set.is_pwo.image_of_monotone Set.IsPwo.image_of_monotone

protected nonrec theorem IsPwo.union (hs : IsPwo s) (ht : IsPwo t) : IsPwo (s ∪ t) :=
  hs.union ht
#align set.is_pwo.union Set.IsPwo.union

@[simp]
theorem isPwo_union : IsPwo (s ∪ t) ↔ IsPwo s ∧ IsPwo t :=
  partiallyWellOrderedOn_union
#align set.is_pwo_union Set.isPwo_union

protected theorem Finite.isPwo (hs : s.Finite) : IsPwo s := hs.partiallyWellOrderedOn
#align set.finite.is_pwo Set.Finite.isPwo

@[simp] theorem isPwo_of_finite [Finite α] : s.IsPwo := s.toFinite.isPwo
#align set.is_pwo_of_finite Set.isPwo_of_finite

@[simp] theorem isPwo_singleton (a : α) : IsPwo ({a} : Set α) := (finite_singleton a).isPwo
#align set.is_pwo_singleton Set.isPwo_singleton

@[simp] theorem isPwo_empty : IsPwo (∅ : Set α) := finite_empty.isPwo
#align set.is_pwo_empty Set.isPwo_empty

protected theorem Subsingleton.isPwo (hs : s.Subsingleton) : IsPwo s := hs.finite.isPwo
#align set.subsingleton.is_pwo Set.Subsingleton.isPwo

@[simp]
theorem isPwo_insert {a} : IsPwo (insert a s) ↔ IsPwo s := by
  simp only [← singleton_union, isPwo_union, isPwo_singleton, true_and_iff]
  -- 🎉 no goals
#align set.is_pwo_insert Set.isPwo_insert

protected theorem IsPwo.insert (h : IsPwo s) (a : α) : IsPwo (insert a s) :=
  isPwo_insert.2 h
#align set.is_pwo.insert Set.IsPwo.insert

protected theorem Finite.isWf (hs : s.Finite) : IsWf s := hs.isPwo.isWf
#align set.finite.is_wf Set.Finite.isWf

@[simp] theorem isWf_singleton {a : α} : IsWf ({a} : Set α) := (finite_singleton a).isWf
#align set.is_wf_singleton Set.isWf_singleton

protected theorem Subsingleton.isWf (hs : s.Subsingleton) : IsWf s := hs.isPwo.isWf
#align set.subsingleton.is_wf Set.Subsingleton.isWf

@[simp]
theorem isWf_insert {a} : IsWf (insert a s) ↔ IsWf s := by
  simp only [← singleton_union, isWf_union, isWf_singleton, true_and_iff]
  -- 🎉 no goals
#align set.is_wf_insert Set.isWf_insert

protected theorem IsWf.insert (h : IsWf s) (a : α) : IsWf (insert a s) :=
  isWf_insert.2 h
#align set.is_wf.insert Set.IsWf.insert

end IsPwo

section WellFoundedOn

variable {r : α → α → Prop} [IsStrictOrder α r] {s : Set α} {a : α}

protected theorem Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r :=
  letI := partialOrderOfSO r
  hs.isWf
#align set.finite.well_founded_on Set.Finite.wellFoundedOn

@[simp]
theorem wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).wellFoundedOn
#align set.well_founded_on_singleton Set.wellFoundedOn_singleton

protected theorem Subsingleton.wellFoundedOn (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.finite.wellFoundedOn
#align set.subsingleton.well_founded_on Set.Subsingleton.wellFoundedOn

@[simp]
theorem wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and_iff]
  -- 🎉 no goals
#align set.well_founded_on_insert Set.wellFoundedOn_insert

protected theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (insert a s) r :=
  wellFoundedOn_insert.2 h
#align set.well_founded_on.insert Set.WellFoundedOn.insert

end WellFoundedOn

section LinearOrder

variable [LinearOrder α] {s : Set α}

protected theorem IsWf.isPwo (hs : s.IsWf) : s.IsPwo := by
  intro f hf
  -- ⊢ ∃ m n, m < n ∧ (fun x x_1 => x ≤ x_1) (f m) (f n)
  lift f to ℕ → s using hf
  -- ⊢ ∃ m n, m < n ∧ (fun x x_1 => x ≤ x_1) ((fun i => ↑(f i)) m) ((fun i => ↑(f i …
  rcases hs.has_min (range f) (range_nonempty _) with ⟨_, ⟨m, rfl⟩, hm⟩
  -- ⊢ ∃ m n, m < n ∧ (fun x x_1 => x ≤ x_1) ((fun i => ↑(f i)) m) ((fun i => ↑(f i …
  simp only [forall_range_iff, not_lt] at hm
  -- ⊢ ∃ m n, m < n ∧ (fun x x_1 => x ≤ x_1) ((fun i => ↑(f i)) m) ((fun i => ↑(f i …
  exact ⟨m, m + 1, lt_add_one m, hm _⟩
  -- 🎉 no goals
#align set.is_wf.is_pwo Set.IsWf.isPwo

/-- In a linear order, the predicates `Set.IsWf` and `Set.IsPwo` are equivalent. -/
theorem isWf_iff_isPwo : s.IsWf ↔ s.IsPwo :=
  ⟨IsWf.isPwo, IsPwo.isWf⟩
#align set.is_wf_iff_is_pwo Set.isWf_iff_isPwo

end LinearOrder

end Set

namespace Finset

variable {r : α → α → Prop}

@[simp]
protected theorem partiallyWellOrderedOn [IsRefl α r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_toSet.partiallyWellOrderedOn
#align finset.partially_well_ordered_on Finset.partiallyWellOrderedOn

@[simp]
protected theorem isPwo [Preorder α] (s : Finset α) : Set.IsPwo (↑s : Set α) :=
  s.partiallyWellOrderedOn
#align finset.is_pwo Finset.isPwo

@[simp]
protected theorem isWf [Preorder α] (s : Finset α) : Set.IsWf (↑s : Set α) :=
  s.finite_toSet.isWf
#align finset.is_wf Finset.isWf

@[simp]
protected theorem wellFoundedOn [IsStrictOrder α r] (s : Finset α) :
    Set.WellFoundedOn (↑s : Set α) r :=
  letI := partialOrderOfSO r
  s.isWf
#align finset.well_founded_on Finset.wellFoundedOn

theorem wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]
                                 -- 🎉 no goals
                                                           -- 🎉 no goals
#align finset.well_founded_on_sup Finset.wellFoundedOn_sup

theorem partiallyWellOrderedOn_sup (s : Finset ι) {f : ι → Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]
                                 -- 🎉 no goals
                                                           -- 🎉 no goals
#align finset.partially_well_ordered_on_sup Finset.partiallyWellOrderedOn_sup

theorem isWf_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.wellFoundedOn_sup
#align finset.is_wf_sup Finset.isWf_sup

theorem isPwo_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partiallyWellOrderedOn_sup
#align finset.is_pwo_sup Finset.isPwo_sup

@[simp]
theorem wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_iSup] using s.wellFoundedOn_sup
  -- 🎉 no goals
#align finset.well_founded_on_bUnion Finset.wellFoundedOn_bUnion

@[simp]
theorem partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_iSup] using s.partiallyWellOrderedOn_sup
  -- 🎉 no goals
#align finset.partially_well_ordered_on_bUnion Finset.partiallyWellOrderedOn_bUnion

@[simp]
theorem isWf_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.wellFoundedOn_bUnion
#align finset.is_wf_bUnion Finset.isWf_bUnion

@[simp]
theorem isPwo_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partiallyWellOrderedOn_bUnion
#align finset.is_pwo_bUnion Finset.isPwo_bUnion

end Finset

namespace Set

section Preorder

variable [Preorder α] {s : Set α} {a : α}

/-- `Set.IsWf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable nonrec def IsWf.min (hs : IsWf s) (hn : s.Nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)
#align set.is_wf.min Set.IsWf.min

theorem IsWf.min_mem (hs : IsWf s) (hn : s.Nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2
#align set.is_wf.min_mem Set.IsWf.min_mem

nonrec theorem IsWf.not_lt_min (hs : IsWf s) (hn : s.Nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))
#align set.is_wf.not_lt_min Set.IsWf.not_lt_min

@[simp]
theorem isWf_min_singleton (a) {hs : IsWf ({a} : Set α)} {hn : ({a} : Set α).Nonempty} :
    hs.min hn = a :=
  eq_of_mem_singleton (IsWf.min_mem hs hn)
#align set.is_wf_min_singleton Set.isWf_min_singleton

end Preorder

section LinearOrder

variable [LinearOrder α] {s t : Set α} {a : α}

theorem IsWf.min_le (hs : s.IsWf) (hn : s.Nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_lt (hs.not_lt_min hn ha)
#align set.is_wf.min_le Set.IsWf.min_le

theorem IsWf.le_min_iff (hs : s.IsWf) (hn : s.Nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩
#align set.is_wf.le_min_iff Set.IsWf.le_min_iff

theorem IsWf.min_le_min_of_subset {hs : s.IsWf} {hsn : s.Nonempty} {ht : t.IsWf} {htn : t.Nonempty}
    (hst : s ⊆ t) : ht.min htn ≤ hs.min hsn :=
  (IsWf.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)
#align set.is_wf.min_le_min_of_subset Set.IsWf.min_le_min_of_subset

theorem IsWf.min_union (hs : s.IsWf) (hsn : s.Nonempty) (ht : t.IsWf) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) =
      Min.min (hs.min hsn) (ht.min htn) := by
  refine' le_antisymm (le_min (IsWf.min_le_min_of_subset (subset_union_left _ _))
    (IsWf.min_le_min_of_subset (subset_union_right _ _))) _
  rw [min_le_iff]
  -- ⊢ min hs hsn ≤ min (_ : IsWf (s ∪ t)) (_ : Set.Nonempty (s ∪ t)) ∨ min ht htn  …
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)
#align set.is_wf.min_union Set.IsWf.min_union

end LinearOrder

end Set

open Set

namespace Set.PartiallyWellOrderedOn

variable {r : α → α → Prop}

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def IsBadSeq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  (∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)
#align set.partially_well_ordered_on.is_bad_seq Set.PartiallyWellOrderedOn.IsBadSeq

theorem iff_forall_not_isBadSeq (r : α → α → Prop) (s : Set α) :
    s.PartiallyWellOrderedOn r ↔ ∀ f, ¬IsBadSeq r s f :=
  forall_congr' fun f => by simp [IsBadSeq]
                            -- 🎉 no goals
#align set.partially_well_ordered_on.iff_forall_not_is_bad_seq Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def IsMinBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬IsBadSeq r s g
#align set.partially_well_ordered_on.is_min_bad_seq Set.PartiallyWellOrderedOn.IsMinBadSeq

/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable def minBadSeqOfBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α)
    (hf : IsBadSeq r s f) :
    { g : ℕ → α // (∀ m : ℕ, m < n → f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g } := by
  classical
    have h : ∃ (k : ℕ) (g : ℕ → α), (∀ m, m < n → f m = g m) ∧ IsBadSeq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine' ⟨Classical.choose (Nat.find_spec h), h1, by convert h2, fun g hg1 hg2 con => _⟩
    refine' Nat.find_min h _ ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), con, rfl⟩
    rwa [← h3]
#align set.partially_well_ordered_on.min_bad_seq_of_bad_seq Set.PartiallyWellOrderedOn.minBadSeqOfBadSeq

theorem exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : Set α) :
    (∃ f, IsBadSeq r s f) → ∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  -- ⊢ ∃ f, IsBadSeq r s f ∧ ∀ (n : ℕ), IsMinBadSeq r rk s n f
  let fs : ∀ n : ℕ, { f : ℕ → α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine' Nat.rec _ fun n fn => _
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).1,
        (minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m := fun m n mn => by
    obtain ⟨k, rfl⟩ := exists_add_of_le mn; clear mn
    induction' k with k ih
    · rfl
    · rw [ih, (minBadSeqOfBadSeq r rk s (m + k + 1) (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iff.2 (Nat.add_le_add_left k.zero_le m))]
      rfl
  refine ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => ?_⟩, fun n g hg1 hg2 => ?_⟩
  -- ⊢ ¬r ((fun n => ↑(fs n) n) m) ((fun n => ↑(fs n) n) n)
  · dsimp
    -- ⊢ ¬r (↑(Nat.rec { val := ↑(minBadSeqOfBadSeq r rk s 0 f0 hf0), property := (_  …
    rw [h m n mn.le]
    -- ⊢ ¬r (↑(fs n) m) (↑(Nat.rec { val := ↑(minBadSeqOfBadSeq r rk s 0 f0 hf0), pro …
    exact (fs n).2.1.2 m n mn
    -- 🎉 no goals
  · refine (fs n).2.2 g (fun m mn => ?_) hg2
    -- ⊢ ↑(fs n) m = g m
    rw [← h m n mn.le, ← hg1 m mn]
    -- 🎉 no goals
#align set.partially_well_ordered_on.exists_min_bad_of_exists_bad Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad

theorem iff_not_exists_isMinBadSeq (rk : α → ℕ) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rw [iff_forall_not_isBadSeq, ← not_exists, not_congr]
  -- ⊢ (∃ x, IsBadSeq r s x) ↔ ∃ f, IsBadSeq r s f ∧ ∀ (n : ℕ), IsMinBadSeq r rk s  …
  constructor
  -- ⊢ (∃ x, IsBadSeq r s x) → ∃ f, IsBadSeq r s f ∧ ∀ (n : ℕ), IsMinBadSeq r rk s  …
  · apply exists_min_bad_of_exists_bad
    -- 🎉 no goals
  · rintro ⟨f, hf1, -⟩
    -- ⊢ ∃ x, IsBadSeq r s x
    exact ⟨f, hf1⟩
    -- 🎉 no goals
#align set.partially_well_ordered_on.iff_not_exists_is_min_bad_seq Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq

/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `List.SublistForall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `List.SublistForall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`.  -/
theorem partiallyWellOrderedOn_sublistForall₂ (r : α → α → Prop) [IsRefl α r] [IsTrans α r]
    {s : Set α} (h : s.PartiallyWellOrderedOn r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases isEmpty_or_nonempty α
  -- ⊢ PartiallyWellOrderedOn {l | ∀ (x : α), x ∈ l → x ∈ s} (List.SublistForall₂ r)
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
    -- 🎉 no goals
  inhabit α
  -- ⊢ PartiallyWellOrderedOn {l | ∀ (x : α), x ∈ l → x ∈ s} (List.SublistForall₂ r)
  rw [iff_not_exists_isMinBadSeq List.length]
  -- ⊢ ¬∃ f, IsBadSeq (List.SublistForall₂ r) {l | ∀ (x : α), x ∈ l → x ∈ s} f ∧ ∀  …
  rintro ⟨f, hf1, hf2⟩
  -- ⊢ False
  have hnil : ∀ n, f n ≠ List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  have : ∀ n, (f n).headI ∈ s
  -- ⊢ ∀ (n : ℕ), List.headI (f n) ∈ s
  · exact fun n => hf1.1 n _ (List.head!_mem_self (hnil n))
    -- 🎉 no goals
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (fun n => (f n).headI) this
  -- ⊢ False
  have hf' :=
    hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0))))
      (fun m hm => (if_pos hm).symm) ?_
  swap;
  -- ⊢ List.length ((fun n => if n < ↑g 0 then f n else List.tail (f (↑g (n - ↑g 0) …
  · simp only [if_neg (lt_irrefl (g 0)), tsub_self]
    -- ⊢ List.length (List.tail (f (↑g 0))) < List.length (f (↑g 0))
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    -- ⊢ Nat.pred (List.length (f (↑g 0))) < List.length (f (↑g 0))
    exact Nat.pred_lt fun con => hnil _ (List.length_eq_zero.1 con)
    -- 🎉 no goals
  rw [IsBadSeq] at hf'
  -- ⊢ False
  push_neg at hf'
  -- ⊢ False
  obtain ⟨m, n, mn, hmn⟩ := hf' <| fun n x hx => by
    split_ifs at hx with hn
    exacts [hf1.1 _ _ hx, hf1.1 _ _ (List.tail_subset _ hx)]
  by_cases hn : n < g 0
  -- ⊢ False
  · apply hf1.2 m n mn
    -- ⊢ List.SublistForall₂ r (f m) (f n)
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
    -- 🎉 no goals
  · obtain ⟨n', rfl⟩ := exists_add_of_le (not_lt.1 hn)
    -- ⊢ False
    rw [if_neg hn, add_comm (g 0) n', add_tsub_cancel_right] at hmn
    -- ⊢ False
    split_ifs at hmn with hm
    -- ⊢ False
    · apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))
      -- ⊢ List.SublistForall₂ r (f m) (f (↑g n'))
      exact _root_.trans hmn (List.tail_sublistForall₂_self _)
      -- 🎉 no goals
    · rw [← tsub_lt_iff_left (le_of_not_lt hm)] at mn
      -- ⊢ False
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      -- ⊢ List.SublistForall₂ r (f (↑g (m - ↑g 0))) (f (↑g n'))
      rw [← List.cons_head!_tail (hnil (g (m - g 0))), ← List.cons_head!_tail (hnil (g n'))]
      -- ⊢ List.SublistForall₂ r (List.head! (f (↑g (m - ↑g 0))) :: List.tail (f (↑g (m …
      exact List.SublistForall₂.cons (hg _ _ (le_of_lt mn)) hmn
      -- 🎉 no goals
#align set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂ Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂

end Set.PartiallyWellOrderedOn

theorem WellFounded.isWf [LT α] (h : WellFounded ((· < ·) : α → α → Prop)) (s : Set α) : s.IsWf :=
  (Set.isWf_univ_iff.2 h).mono s.subset_univ
#align well_founded.is_wf WellFounded.isWf

/-- A version of **Dickson's lemma** any subset of functions `Π s : σ, α s` is partially well
ordered, when `σ` is a `Fintype` and each `α s` is a linear well order.
This includes the classical case of Dickson's lemma that `ℕ ^ n` is a well partial order.
Some generalizations would be possible based on this proof, to include cases where the target is
partially well ordered, and also to consider the case of `Set.PartiallyWellOrderedOn` instead of
`Set.IsPwo`. -/
theorem Pi.isPwo {α : ι → Type*} [∀ i, LinearOrder (α i)] [∀ i, IsWellOrder (α i) (· < ·)]
    [Finite ι] (s : Set (∀ i, α i)) : s.IsPwo := by
  cases nonempty_fintype ι
  -- ⊢ IsPwo s
  suffices ∀ (s : Finset ι) (f : ℕ → ∀ s, α s),
    ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ x, x ∈ s → (f ∘ g) a x ≤ (f ∘ g) b x by
    refine isPwo_iff_exists_monotone_subseq.2 fun f _ => ?_
    simpa only [Finset.mem_univ, true_imp_iff] using this Finset.univ f
  refine' Finset.cons_induction _ _
  -- ⊢ ∀ (f : ℕ → (s : ι) → α s), ∃ g, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι), x ∈ ∅ → (f ∘ …
  · intro f
    -- ⊢ ∃ g, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι), x ∈ ∅ → (f ∘ ↑g) a x ≤ (f ∘ ↑g) b x
    exists RelEmbedding.refl (· ≤ ·)
    -- ⊢ ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι), x ∈ ∅ → (f ∘ ↑(RelEmbedding.refl fun x x_1 = …
    simp only [IsEmpty.forall_iff, imp_true_iff, forall_const, Finset.not_mem_empty]
    -- 🎉 no goals
  · intro x s hx ih f
    -- ⊢ ∃ g, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x_1 : ι), x_1 ∈ Finset.cons x s hx → (f ∘ ↑g) a …
    obtain ⟨g, hg⟩ :=
      (IsWellFounded.wf.isWf univ).isPwo.exists_monotone_subseq (fun n => f n x) mem_univ
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    -- ⊢ ∃ g, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x_1 : ι), x_1 ∈ Finset.cons x s hx → (f ∘ ↑g) a …
    refine' ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 _⟩
    -- ⊢ (f ∘ ↑(RelEmbedding.trans g' g)) a x ≤ (f ∘ ↑(RelEmbedding.trans g' g)) b x  …
    exact ⟨hg (OrderHomClass.mono g' hab), hg' hab⟩
    -- 🎉 no goals
#align pi.is_pwo Pi.isPwo

section ProdLex
variable {rα : α → α → Prop} {rβ : β → β → Prop} {f : γ → α} {g : γ → β} {s : Set γ}

/-- Stronger version of `prod.lex_wf`. Instead of requiring `rβ on g` to be well-founded, we only
require it to be well-founded on fibers of `f`.-/
theorem WellFounded.prod_lex_of_wellFoundedOn_fiber (hα : WellFounded (rα on f))
    (hβ : ∀ a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    WellFounded (Prod.Lex rα rβ on fun c => (f c, g c)) := by
  refine' (PSigma.lex_wf (wellFoundedOn_range.2 hα) fun a => hβ a).onFun.mono fun c c' h => _
  -- ⊢ γ → (a : ↑(range f)) ×' ↑(f ⁻¹' {↑a})
  exact fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩
  -- ⊢ ((PSigma.Lex (fun a b => rα ↑a ↑b) fun a a_1 b => (rβ on g) ↑a_1 ↑b) on fun  …
  obtain h' | h' := Prod.lex_iff.1 h
  -- ⊢ ((PSigma.Lex (fun a b => rα ↑a ↑b) fun a a_1 b => (rβ on g) ↑a_1 ↑b) on fun  …
  · exact PSigma.Lex.left _ _ h'
    -- 🎉 no goals
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    -- ⊢ PSigma.Lex (fun a b => rα ↑a ↑b) (fun a a_1 b => rβ (g ↑a_1) (g ↑b)) { fst : …
    convert PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    exacts [⟨c, h'.1⟩, PSigma.subtype_ext (Subtype.ext h'.1) rfl, h'.2]
    -- 🎉 no goals
#align well_founded.prod_lex_of_well_founded_on_fiber WellFounded.prod_lex_of_wellFoundedOn_fiber

theorem Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber (hα : s.WellFoundedOn (rα on f))
    (hβ : ∀ a, (s ∩ f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    s.WellFoundedOn (Prod.Lex rα rβ on fun c => (f c, g c)) := by
  refine' WellFounded.prod_lex_of_wellFoundedOn_fiber hα fun a ↦ (hβ a).onFun.mono (fun b c h ↦ _)
  -- ⊢ ((fun a_1 b => (rβ on g) ↑a_1 ↑b) on ?refine'_2 a) b c
  swap
  -- ⊢ (a : α) → ↑((fun a => f ↑a) ⁻¹' {a}) → ↑(s ∩ f ⁻¹' {a})
  exact fun _ x => ⟨x, x.1.2, x.2⟩
  -- ⊢ ((fun a_1 b => (rβ on g) ↑a_1 ↑b) on fun x => { val := ↑↑x, property := (_ : …
  assumption
  -- 🎉 no goals
#align set.well_founded_on.prod_lex_of_well_founded_on_fiber Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber

end ProdLex

section SigmaLex

variable {rι : ι → ι → Prop} {rπ : ∀ i, π i → π i → Prop} {f : γ → ι} {g : ∀ i, γ → π i} {s : Set γ}

/-- Stronger version of `psigma.lex_wf`. Instead of requiring `rπ on g` to be well-founded, we only
require it to be well-founded on fibers of `f`.-/
theorem WellFounded.sigma_lex_of_wellFoundedOn_fiber (hι : WellFounded (rι on f))
    (hπ : ∀ i, (f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    WellFounded (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  refine' (PSigma.lex_wf (wellFoundedOn_range.2 hι) fun a => hπ a).onFun.mono fun c c' h => _
  -- ⊢ γ → (a : ↑(range f)) ×' ↑(f ⁻¹' {↑a})
  exact fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩
  -- ⊢ ((PSigma.Lex (fun a b => rι ↑a ↑b) fun a a_1 b => (rπ ↑a on g ↑a) ↑a_1 ↑b) o …
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  -- ⊢ ((PSigma.Lex (fun a b => rι ↑a ↑b) fun a a_1 b => (rπ ↑a on g ↑a) ↑a_1 ↑b) o …
  · exact PSigma.Lex.left _ _ h'
    -- 🎉 no goals
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    -- ⊢ PSigma.Lex (fun a b => rι ↑a ↑b) (fun a a_1 b => rπ (↑a) (g ↑a ↑a_1) (g ↑a ↑ …
    convert PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    · exact ⟨c, h'⟩
      -- 🎉 no goals
    · exact PSigma.subtype_ext (Subtype.ext h') rfl
      -- 🎉 no goals
    · dsimp only [Subtype.coe_mk] at *
      -- ⊢ rπ (f c') (g (f c') c) (g (f c') c')
      revert h'
      -- ⊢ ∀ (h' : f c = f c'), rπ (f c') (h' ▸ g (f c) c) (g (f c') c') → rπ (f c') (g …
      generalize f c = d
      -- ⊢ ∀ (h' : d = f c'), rπ (f c') (h' ▸ g d c) (g (f c') c') → rπ (f c') (g (f c' …
      rintro rfl h''
      -- ⊢ rπ (f c') (g (f c') c) (g (f c') c')
      exact h''
      -- 🎉 no goals
#align well_founded.sigma_lex_of_well_founded_on_fiber WellFounded.sigma_lex_of_wellFoundedOn_fiber

theorem Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber (hι : s.WellFoundedOn (rι on f))
    (hπ : ∀ i, (s ∩ f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    s.WellFoundedOn (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  show WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  -- ⊢ WellFounded (Sigma.Lex rι rπ on fun c => { fst := f ↑c, snd := g (f ↑c) ↑c })
  refine'
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => (hπ i).onFun.mono (fun b c h => _)
  swap
  -- ⊢ (i : ι) → ↑((fun c => f ↑c) ⁻¹' {i}) → ↑(s ∩ f ⁻¹' {i})
  exact fun _ x => ⟨x, x.1.2, x.2⟩
  -- ⊢ ((fun a b => (rπ i on g i) ↑a ↑b) on fun x => { val := ↑↑x, property := (_ : …
  assumption
  -- 🎉 no goals
#align set.well_founded_on.sigma_lex_of_well_founded_on_fiber Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber

end SigmaLex
