/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.RelIso.Set
import Mathlib.Order.WellQuasiOrder
import Mathlib.Tactic.TFAE

/-!
# Well-founded sets

This file introduces versions of `WellFounded` and `WellQuasiOrdered` for sets.

## Main Definitions

* `Set.WellFoundedOn s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
* `Set.IsWF s` indicates that `<` is well-founded when restricted to `s`.
* `Set.PartiallyWellOrderedOn s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
* `Set.IsPWO s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results

* Higman's Lemma, `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`,
  shows that if `r` is partially well-ordered on `s`, then `List.SublistForall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
* `Set.wellFoundedOn_iff` relates `well_founded_on` to the well-foundedness of a relation on the
  original type, to avoid dealing with subtypes.
* `Set.IsWF.mono` shows that a subset of a well-founded subset is well-founded.
* `Set.IsWF.union` shows that the union of two well-founded subsets is well-founded.
* `Finset.isWF` shows that all `Finset`s are well-founded.

## TODO

* Prove that `s` is partially well-ordered iff it has no infinite descending chain or antichain.
* Rename `Set.PartiallyWellOrderedOn` to `Set.WellQuasiOrderedOn` and `Set.IsPWO` to `Set.IsWQO`.

## References
* [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
* [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/

assert_not_exists OrderedSemiring

open scoped Function -- required for scoped `on` notation

variable {ι α β γ : Type*} {π : ι → Type*}

namespace Set

/-! ### Relations well-founded on sets -/

/-- `s.WellFoundedOn r` indicates that the relation `r` is `WellFounded` when restricted to `s`. -/
def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded (Subrel r (· ∈ s))

@[simp]
theorem wellFoundedOn_empty (r : α → α → Prop) : WellFoundedOn ∅ r :=
  wellFounded_of_isEmpty _

section WellFoundedOn

variable {r r' : α → α → Prop}

section AnyRel

variable {f : β → α} {s t : Set α} {x y : α}

theorem wellFoundedOn_iff :
    s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s := by
  have f : RelEmbedding (Subrel r (· ∈ s)) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine ⟨fun h => ?_, f.wellFounded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s ∩ t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases h.has_min (Subtype.val ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, _⟩ => hm ⟨x, xs⟩ xt xm⟩
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x _ ⟨_, _, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩

@[simp]
theorem wellFoundedOn_univ : (univ : Set α).WellFoundedOn r ↔ WellFounded r := by
  simp [wellFoundedOn_iff]

theorem _root_.WellFounded.wellFoundedOn : WellFounded r → s.WellFoundedOn r :=
  InvImage.wf _

@[simp]
theorem wellFoundedOn_range : (range f).WellFoundedOn r ↔ WellFounded (r on f) := by
  let f' : β → range f := fun c => ⟨f c, c, rfl⟩
  refine ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨?_⟩⟩
  rintro ⟨_, c, rfl⟩
  refine Acc.of_downward_closed f' ?_ _ ?_
  · rintro _ ⟨_, c', rfl⟩ -
    exact ⟨c', rfl⟩
  · exact h.apply _

@[simp]
theorem wellFoundedOn_image {s : Set β} : (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f) := by
  rw [image_eq_range]; exact wellFoundedOn_range

namespace WellFoundedOn

protected theorem induction (hs : s.WellFoundedOn r) (hx : x ∈ s) {P : α → Prop}
    (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x := by
  let Q : s → Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine WellFounded.induction hs ⟨x, hx⟩ ?_
  simpa only [Subtype.forall]

protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) :
    s.WellFoundedOn r := by
  rw [wellFoundedOn_iff] at *
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h

theorem mono' (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), r' a b → r a b) :
    s.WellFoundedOn r → s.WellFoundedOn r' :=
  Subrelation.wf @fun a b => h _ a.2 _ b.2

theorem subset (h : t.WellFoundedOn r) (hst : s ⊆ t) : s.WellFoundedOn r :=
  h.mono le_rfl hst

open Relation

open List in
/-- `a` is accessible under the relation `r` iff `r` is well-founded on the downward transitive
closure of `a` under `r` (including `a` or not). -/
theorem acc_iff_wellFoundedOn {α} {r : α → α → Prop} {a : α} :
    TFAE [Acc r a,
      WellFoundedOn { b | ReflTransGen r b a } r,
      WellFoundedOn { b | TransGen r b a } r] := by
  tfae_have 1 → 2 := by
    refine fun h => ⟨fun b => InvImage.accessible Subtype.val ?_⟩
    rw [← acc_transGen_iff] at h ⊢
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 → 3 := fun h => h.subset fun _ => TransGen.to_reflTransGen
  tfae_have 3 → 1 := by
    refine fun h => Acc.intro _ (fun b hb => (h.apply ⟨b, .single hb⟩).of_fibration Subtype.val ?_)
    exact fun ⟨c, hc⟩ d h => ⟨⟨d, .head h hc⟩, h, rfl⟩
  tfae_finish

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s where
  toIsIrrefl := ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

theorem wellFoundedOn_iff_no_descending_seq :
    s.WellFoundedOn r ↔ ∀ f : ((· > ·) : ℕ → ℕ → Prop) ↪r r, ¬∀ n, f n ∈ s := by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_isEmpty, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : ∀ n, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
    refine ⟨⟨f, ?_⟩, H⟩
    simpa only [H, and_true] using @hf
  · rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩
    refine ⟨⟨f, ?_⟩⟩
    simpa only [hfs, and_true] using @hf

theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) :
    (s ∪ t).WellFoundedOn r := by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]

@[simp]
theorem wellFoundedOn_union : (s ∪ t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun h =>
    h.1.union h.2⟩

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/

section LT

variable [LT α] {s t : Set α}

/-- `s.IsWF` indicates that `<` is well-founded when restricted to `s`. -/
def IsWF (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)

@[simp]
theorem isWF_empty : IsWF (∅ : Set α) :=
  wellFounded_of_isEmpty _

theorem IsWF.mono (h : IsWF t) (st : s ⊆ t) : IsWF s := h.subset st

theorem isWF_univ_iff : IsWF (univ : Set α) ↔ WellFoundedLT α := by
  simp [IsWF, wellFoundedOn_iff, isWellFounded_iff]

theorem IsWF.of_wellFoundedLT [h : WellFoundedLT α] (s : Set α) : s.IsWF :=
  (Set.isWF_univ_iff.2 h).mono s.subset_univ

end LT

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

protected nonrec theorem IsWF.union (hs : IsWF s) (ht : IsWF t) : IsWF (s ∪ t) := hs.union ht

@[simp] theorem isWF_union : IsWF (s ∪ t) ↔ IsWF s ∧ IsWF t := wellFoundedOn_union

end Preorder

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

theorem isWF_iff_no_descending_seq :
    IsWF s ↔ ∀ f : ℕ → α, StrictAnti f → ¬∀ n, f n ∈ s :=
  wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_gt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

end Preorder

/-! ### Partially well-ordered sets -/

/-- `s.PartiallyWellOrderedOn r` indicates that the relation `r` is `WellQuasiOrdered` when
restricted to `s`.

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `IsAntichain`) is
finite, see `Set.partiallyWellOrderedOn_iff_finite_antichains`.

TODO: rename this to `WellQuasiOrderedOn` to match `WellQuasiOrdered`. -/
def PartiallyWellOrderedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellQuasiOrdered (Subrel r (· ∈ s))

section PartiallyWellOrderedOn

variable {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α} {t : Set α} {a : α}

theorem PartiallyWellOrderedOn.exists_lt (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ n, f n ∈ s) : ∃ m n, m < n ∧ r (f m) (f n) :=
  hs fun n ↦ ⟨_, hf n⟩

theorem partiallyWellOrderedOn_iff_exists_lt : s.PartiallyWellOrderedOn r ↔
    ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n, m < n ∧ r (f m) (f n) :=
  ⟨PartiallyWellOrderedOn.exists_lt, fun hf f ↦ hf _ fun n ↦ (f n).2⟩

theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) :
    s.PartiallyWellOrderedOn r :=
  fun f ↦ ht (Set.inclusion h ∘ f)

@[simp]
theorem partiallyWellOrderedOn_empty (r : α → α → Prop) : PartiallyWellOrderedOn ∅ r :=
  wellQuasiOrdered_of_isEmpty _

theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r)
    (ht : t.PartiallyWellOrderedOn r) : (s ∪ t).PartiallyWellOrderedOn r := by
  intro f
  obtain ⟨g, hgs | hgt⟩ := Nat.exists_subseq_of_forall_mem_union _ fun x ↦ (f x).2
  · rcases hs.exists_lt hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
  · rcases ht.exists_lt hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩

@[simp]
theorem partiallyWellOrderedOn_union :
    (s ∪ t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h ↦ h.1.union h.2⟩

theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : ∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' := by
  rw [partiallyWellOrderedOn_iff_exists_lt] at *
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g' := funext heq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

-- TODO: prove this in terms of `IsAntichain.finite_of_wellQuasiOrdered`
theorem _root_.IsAntichain.finite_of_partiallyWellOrderedOn (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite := by
  refine not_infinite.1 fun hi => ?_
  obtain ⟨m, n, hmn, h⟩ := hp (hi.natEmbedding _)
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

section IsRefl
variable [IsRefl α r]

protected theorem Finite.partiallyWellOrderedOn (hs : s.Finite) : s.PartiallyWellOrderedOn r :=
  hs.to_subtype.wellQuasiOrdered _

theorem _root_.IsAntichain.partiallyWellOrderedOn_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩

@[simp]
theorem partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).partiallyWellOrderedOn

@[nontriviality]
theorem Subsingleton.partiallyWellOrderedOn (hs : s.Subsingleton) : PartiallyWellOrderedOn s r :=
  hs.finite.partiallyWellOrderedOn

@[simp]
theorem partiallyWellOrderedOn_insert :
    PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and]

protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partiallyWellOrderedOn_insert.2 h

theorem partiallyWellOrderedOn_iff_finite_antichains [IsSymm α r] :
    s.PartiallyWellOrderedOn r ↔ ∀ t, t ⊆ s → IsAntichain r t → t.Finite := by
  refine ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), ?_⟩
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro hs f hf
  by_contra! H
  refine infinite_range_of_injective (fun m n hmn => ?_) (hs _ (range_subset_iff.2 hf) ?_)
  · obtain h | h | h := lt_trichotomy m n
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
    · exact h
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_gt
  · exact H _ _ h
  · exact mt symm (H _ _ h)

end IsRefl

section IsPreorder
variable [IsPreorder α r]

theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ n, f n ∈ s) : ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  WellQuasiOrdered.exists_monotone_subseq h fun n ↦ ⟨_, hf n⟩

theorem partiallyWellOrderedOn_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔
      ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  use PartiallyWellOrderedOn.exists_monotone_subseq
  rw [PartiallyWellOrderedOn, wellQuasiOrdered_iff_exists_monotone_subseq]
  exact fun H f ↦ H _ fun n ↦ (f n).2

protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') :
    PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht.exists_lt fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩

theorem PartiallyWellOrderedOn.wellFoundedOn (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬ r b a :=
  h.wellFounded

end IsPreorder

end PartiallyWellOrderedOn

section IsPWO

variable [Preorder α] [Preorder β] {s t : Set α}

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def IsPWO (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· ≤ ·)

nonrec theorem IsPWO.mono (ht : t.IsPWO) : s ⊆ t → s.IsPWO := ht.mono

nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) {f : ℕ → α} (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq hf

theorem isPWO_iff_exists_monotone_subseq :
    s.IsPWO ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partiallyWellOrderedOn_iff_exists_monotone_subseq

protected theorem IsPWO.isWF (h : s.IsPWO) : s.IsWF := by
  simpa only [← lt_iff_le_not_ge] using h.wellFoundedOn

nonrec theorem IsPWO.prod {t : Set β} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s ×ˢ t) :=
  hs.prod ht

theorem IsPWO.image_of_monotoneOn (hs : s.IsPWO) {f : α → β} (hf : MonotoneOn f s) :
    IsPWO (f '' s) :=
  hs.image_of_monotone_on hf

theorem IsPWO.image_of_monotone (hs : s.IsPWO) {f : α → β} (hf : Monotone f) : IsPWO (f '' s) :=
  hs.image_of_monotone_on (hf.monotoneOn _)

protected nonrec theorem IsPWO.union (hs : IsPWO s) (ht : IsPWO t) : IsPWO (s ∪ t) :=
  hs.union ht

@[simp]
theorem isPWO_union : IsPWO (s ∪ t) ↔ IsPWO s ∧ IsPWO t :=
  partiallyWellOrderedOn_union

protected theorem Finite.isPWO (hs : s.Finite) : IsPWO s := hs.partiallyWellOrderedOn

@[simp] theorem isPWO_of_finite [Finite α] : s.IsPWO := s.toFinite.isPWO

@[simp] theorem isPWO_singleton (a : α) : IsPWO ({a} : Set α) := (finite_singleton a).isPWO

@[simp] theorem isPWO_empty : IsPWO (∅ : Set α) := finite_empty.isPWO

protected theorem Subsingleton.isPWO (hs : s.Subsingleton) : IsPWO s := hs.finite.isPWO

@[simp]
theorem isPWO_insert {a} : IsPWO (insert a s) ↔ IsPWO s := by
  simp only [← singleton_union, isPWO_union, isPWO_singleton, true_and]

protected theorem IsPWO.insert (h : IsPWO s) (a : α) : IsPWO (insert a s) :=
  isPWO_insert.2 h

protected theorem Finite.isWF (hs : s.Finite) : IsWF s := hs.isPWO.isWF

@[simp] theorem isWF_singleton {a : α} : IsWF ({a} : Set α) := (finite_singleton a).isWF

protected theorem Subsingleton.isWF (hs : s.Subsingleton) : IsWF s := hs.isPWO.isWF

@[simp]
theorem isWF_insert {a} : IsWF (insert a s) ↔ IsWF s := by
  simp only [← singleton_union, isWF_union, isWF_singleton, true_and]

protected theorem IsWF.insert (h : IsWF s) (a : α) : IsWF (insert a s) :=
  isWF_insert.2 h

theorem IsPWO.exists_le_minimal {a} (hs : s.IsPWO) (ha : a ∈ s) :
    ∃ b ≤ a, Minimal (· ∈ s) b := by
  let t : Set s := {x | x ≤ a}
  let h : t.Nonempty := ⟨⟨a, ha⟩, le_rfl⟩
  refine ⟨hs.wellFounded.min t h, hs.wellFounded.min_mem t h,
    (hs.wellFounded.min t h).2, fun y hy hle => ?_⟩
  by_contra hnle
  exact hs.wellFounded.not_lt_min t h (x := ⟨y, hy⟩) (hle.trans (hs.wellFounded.min_mem t h))
    ⟨hle, hnle⟩

theorem IsPWO.exists_minimal (h : s.IsPWO) (hs : s.Nonempty) :
    ∃ a, Minimal (· ∈ s) a := by
  rcases hs with ⟨a, ha⟩
  obtain ⟨b, _, hb⟩ := h.exists_le_minimal ha
  exact ⟨b, hb⟩

theorem IsPWO.exists_minimalFor (f : ι → α) (s : Set ι) (h : (f '' s).IsPWO) (hs : s.Nonempty) :
    ∃ i, MinimalFor (· ∈ s) f i := by
  obtain ⟨_, h⟩ := h.exists_minimal (hs.image _)
  obtain ⟨a, ha, rfl⟩ := h.1
  exact ⟨a, ha, fun b hb => h.2 (mem_image_of_mem _ hb)⟩

end IsPWO

section WellFoundedOn

variable {r : α → α → Prop} [IsStrictOrder α r] {s : Set α} {a : α}

protected theorem Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r :=
  letI := partialOrderOfSO r
  hs.isWF

@[simp]
theorem wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).wellFoundedOn

protected theorem Subsingleton.wellFoundedOn (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.finite.wellFoundedOn

@[simp]
theorem wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and]

@[simp]
theorem wellFoundedOn_sdiff_singleton : WellFoundedOn (s \ {a}) r ↔ WellFoundedOn s r := by
  simp only [← wellFoundedOn_insert (a := a), insert_diff_singleton, mem_insert_iff, true_or,
    insert_eq_of_mem]

protected theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (insert a s) r :=
  wellFoundedOn_insert.2 h

protected theorem WellFoundedOn.sdiff_singleton (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (s \ {a}) r :=
  wellFoundedOn_sdiff_singleton.2 h

lemma WellFoundedOn.mapsTo {α β : Type*} {r : α → α → Prop} (f : β → α)
    {s : Set α} {t : Set β} (h : MapsTo f t s) (hw : s.WellFoundedOn r) :
    t.WellFoundedOn (r on f) := by
  exact InvImage.wf (fun x : t ↦ ⟨f x, h x.prop⟩) hw

end WellFoundedOn

section LinearOrder

variable [LinearOrder α] {s : Set α}

/-- In a linear order, the predicates `Set.IsPWO` and `Set.IsWF` are equivalent. -/
theorem isPWO_iff_isWF : s.IsPWO ↔ s.IsWF := by
  change WellQuasiOrdered (· ≤ ·) ↔ WellFounded (· < ·)
  rw [← wellQuasiOrderedLE_def, ← isWellFounded_iff, wellQuasiOrderedLE_iff_wellFoundedLT]

alias ⟨_, IsWF.isPWO⟩ := isPWO_iff_isWF

/--
If `α` is a linear order with well-founded `<`, then any set in it is a partially well-ordered set.
Note this does not hold without the linearity assumption.
-/
lemma IsPWO.of_linearOrder [WellFoundedLT α] (s : Set α) : s.IsPWO :=
  (IsWF.of_wellFoundedLT s).isPWO

end LinearOrder

end Set

namespace Finset

variable {r : α → α → Prop}

@[simp]
protected theorem partiallyWellOrderedOn [IsRefl α r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_toSet.partiallyWellOrderedOn

@[simp]
protected theorem isPWO [Preorder α] (s : Finset α) : Set.IsPWO (↑s : Set α) :=
  s.partiallyWellOrderedOn

@[simp]
protected theorem isWF [Preorder α] (s : Finset α) : Set.IsWF (↑s : Set α) :=
  s.finite_toSet.isWF

@[simp]
protected theorem wellFoundedOn [IsStrictOrder α r] (s : Finset α) :
    Set.WellFoundedOn (↑s : Set α) r :=
  letI := partialOrderOfSO r
  s.isWF

theorem wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

theorem partiallyWellOrderedOn_sup (s : Finset ι) {f : ι → Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

theorem isWF_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsWF ↔ ∀ i ∈ s, (f i).IsWF :=
  s.wellFoundedOn_sup

theorem isPWO_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsPWO ↔ ∀ i ∈ s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_sup

@[simp]
theorem wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_iSup] using s.wellFoundedOn_sup

@[simp]
theorem partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_iSup] using s.partiallyWellOrderedOn_sup

@[simp]
theorem isWF_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsWF ↔ ∀ i ∈ s, (f i).IsWF :=
  s.wellFoundedOn_bUnion

@[simp]
theorem isPWO_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsPWO ↔ ∀ i ∈ s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_bUnion

end Finset

namespace Set

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/-- `Set.IsWF.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable nonrec def IsWF.min (hs : IsWF s) (hn : s.Nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

theorem IsWF.min_mem (hs : IsWF s) (hn : s.Nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

nonrec theorem IsWF.not_lt_min (hs : IsWF s) (hn : s.Nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

theorem IsWF.min_of_subset_not_lt_min {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF}
    {htn : t.Nonempty} (hst : s ⊆ t) : ¬hs.min hsn < ht.min htn :=
  ht.not_lt_min htn (hst (min_mem hs hsn))

@[simp]
theorem isWF_min_singleton (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonempty} :
    hs.min hn = a :=
  eq_of_mem_singleton (IsWF.min_mem hs hn)

theorem IsWF.min_eq_of_lt (hs : s.IsWF) (ha : a ∈ s) (hlt : ∀ b ∈ s, b ≠ a → a < b) :
    hs.min (nonempty_of_mem ha) = a := by
  by_contra h
  exact (hs.not_lt_min (nonempty_of_mem ha) ha) (hlt (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha)) h)

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a : α}

theorem IsWF.min_eq_of_le (hs : s.IsWF) (ha : a ∈ s) (hle : ∀ b ∈ s, a ≤ b) :
    hs.min (nonempty_of_mem ha) = a :=
  (eq_of_le_of_not_lt (hle (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha))) (hs.not_lt_min (nonempty_of_mem ha) ha)).symm

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α} {a : α}

theorem IsWF.min_le (hs : s.IsWF) (hn : s.Nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_gt (hs.not_lt_min hn ha)

theorem IsWF.le_min_iff (hs : s.IsWF) (hn : s.Nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

theorem IsWF.min_le_min_of_subset {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}
    (hst : s ⊆ t) : ht.min htn ≤ hs.min hsn :=
  (IsWF.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)

theorem IsWF.min_union (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) =
      Min.min (hs.min hsn) (ht.min htn) := by
  refine le_antisymm (le_min (IsWF.min_le_min_of_subset subset_union_left)
    (IsWF.min_le_min_of_subset subset_union_right)) ?_
  rw [min_le_iff]
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)

end LinearOrder

end Set

open Set

section LocallyFiniteOrder

variable {s : Set α} [Preorder α] [LocallyFiniteOrder α]

theorem BddBelow.wellFoundedOn_lt : BddBelow s → s.WellFoundedOn (· < ·) := by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  refine infinite_range_of_injective f.injective ?_
  exact (finite_Icc a <| f 0).subset <| range_subset_iff.2 <| fun n =>
    ⟨ha <| hf _,
      antitone_iff_forall_lt.2 (fun a b hab => (f.map_rel_iff.2 hab).le) <| Nat.zero_le _⟩

theorem BddAbove.wellFoundedOn_gt : BddAbove s → s.WellFoundedOn (· > ·) :=
  fun h => h.dual.wellFoundedOn_lt

theorem BddBelow.isWF : BddBelow s → IsWF s :=
  BddBelow.wellFoundedOn_lt

end LocallyFiniteOrder

namespace Set.PartiallyWellOrderedOn

variable {r : α → α → Prop}

theorem bddAbove_preimage {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ m n : ℕ, m < n → ¬ r (f m) (f n)) :
    BddAbove (s.preimage f) := by
  contrapose! hf
  rw [not_bddAbove_iff] at hf
  obtain ⟨φ, hφm, hφs⟩ := Nat.exists_strictMono_subsequence
    fun n ↦ (hf n).casesOn fun m h ↦ h.casesOn fun hs hmn ↦ Exists.intro m ⟨hmn, hs⟩
  rw [partiallyWellOrderedOn_iff_exists_lt] at hs
  obtain ⟨m, n, hmn, hr⟩ := hs (fun n ↦ f (φ n)) hφs
  use (φ m), (φ n)
  exact ⟨hφm hmn, hr⟩

theorem exists_notMem_of_gt {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : ℕ → α}
    (hf : ∀ m n : ℕ, m < n → ¬ r (f m) (f n)) :
    ∃ k : ℕ, ∀ m, k < m → f m ∉ s := by
  have := hs.bddAbove_preimage hf
  contrapose! this
  simpa [not_bddAbove_iff, and_comm]

@[deprecated (since := "2025-05-23")] alias exists_not_mem_of_gt := exists_notMem_of_gt

-- TODO: move this material to the main file on WQOs.

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def IsBadSeq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  (∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)

theorem iff_forall_not_isBadSeq (r : α → α → Prop) (s : Set α) :
    s.PartiallyWellOrderedOn r ↔ ∀ f, ¬IsBadSeq r s f := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  exact forall_congr' fun f => by simp [IsBadSeq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def IsMinBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬IsBadSeq r s g

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
    refine ⟨Classical.choose (Nat.find_spec h), h1, by convert h2, fun g hg1 hg2 con => ?_⟩
    refine Nat.find_min h ?_ ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), con, rfl⟩
    rwa [← h3]

theorem exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : Set α) :
    (∃ f, IsBadSeq r s f) → ∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  let fs : ∀ n : ℕ, { f : ℕ → α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine Nat.rec ?_ fun n fn => ?_
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).1,
        (minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m := fun m n mn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le mn; clear mn
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih, (minBadSeqOfBadSeq r rk s (m + k + 1) (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iff.2 (Nat.add_le_add_left k.zero_le m))]
      rfl
  refine ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => ?_⟩, fun n g hg1 hg2 => ?_⟩
  · dsimp
    rw [h m n mn.le]
    exact (fs n).2.1.2 m n mn
  · refine (fs n).2.2 g (fun m mn => ?_) hg2
    rw [← h m n mn.le, ← hg1 m mn]

theorem iff_not_exists_isMinBadSeq (rk : α → ℕ) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rw [iff_forall_not_isBadSeq, ← not_exists, not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  · rintro ⟨f, hf1, -⟩
    exact ⟨f, hf1⟩

/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `List.SublistForall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `List.SublistForall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`. -/
theorem partiallyWellOrderedOn_sublistForall₂ (r : α → α → Prop) [IsPreorder α r]
    {s : Set α} (h : s.PartiallyWellOrderedOn r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases isEmpty_or_nonempty α
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
  inhabit α
  rw [iff_not_exists_isMinBadSeq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : ∀ n, f n ≠ List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq fun n => hf1.1 n _ (List.head!_mem_self (hnil n))
  have hf' :=
    hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0))))
      (fun m hm => (if_pos hm).symm) ?_
  swap
  · simp only [if_neg (lt_irrefl (g 0)), Nat.sub_self]
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    exact Nat.pred_lt fun con => hnil _ (List.length_eq_zero_iff.1 con)
  rw [IsBadSeq] at hf'
  push_neg at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' fun n x hx => by
    split_ifs at hx with hn
    exacts [hf1.1 _ _ hx, hf1.1 _ _ (List.tail_subset _ hx)]
  by_cases hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
    rw [if_neg hn, add_comm (g 0) n', Nat.add_sub_cancel_right] at hmn
    split_ifs at hmn with hm
    · apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))
      exact _root_.trans hmn (List.tail_sublistForall₂_self _)
    · rw [← Nat.sub_lt_iff_lt_add' (le_of_not_gt hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head!_tail (hnil (g (m - g 0))), ← List.cons_head!_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_lt mn)) hmn

theorem subsetProdLex [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hα : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO)
    (hβ : ∀ a, {y | toLex (a, y) ∈ s}.IsPWO) : s.IsPWO := by
  rw [IsPWO, partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  rw [isPWO_iff_exists_monotone_subseq] at hα
  obtain ⟨g, hg⟩ : ∃ (g : (ℕ ↪o ℕ)), Monotone fun n => (ofLex f (g n)).1 :=
    hα (fun n => (ofLex f n).1) (fun k => mem_image_of_mem (fun x => (ofLex x).1) (hf k))
  have hhg : ∀ n, (ofLex f (g 0)).1 ≤ (ofLex f (g n)).1 := fun n => hg n.zero_le
  by_cases hc : ∃ n, (ofLex f (g 0)).1 < (ofLex f (g n)).1
  · obtain ⟨n, hn⟩ := hc
    use (g 0), (g n)
    constructor
    · by_contra hx
      simp_all
    · exact Prod.Lex.toLex_le_toLex.mpr <| .inl hn
  · have hhc : ∀ n, (ofLex f (g 0)).1 = (ofLex f (g n)).1 := by
      intro n
      rw [not_exists] at hc
      exact (hhg n).eq_of_not_lt (hc n)
    obtain ⟨g', hg'⟩ : ∃ g' : ℕ ↪o ℕ, Monotone ((fun n ↦ (ofLex f (g (g' n))).2)) := by
      simp_rw [isPWO_iff_exists_monotone_subseq] at hβ
      apply hβ (ofLex f (g 0)).1 fun n ↦ (ofLex f (g n)).2
      intro n
      rw [hhc n]
      simpa using hf _
    use (g (g' 0)), (g (g' 1))
    suffices (f (g (g' 0))) ≤ (f (g (g' 1))) by simpa
    · refine Prod.Lex.toLex_le_toLex.mpr <| .inr ⟨?_, ?_⟩
      · exact (hhc (g' 0)).symm.trans (hhc (g' 1))
      · exact hg' (Nat.zero_le 1)

theorem imageProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) : ((fun (x : α ×ₗ β) => (ofLex x).1)'' s).IsPWO :=
  IsPWO.image_of_monotone hαβ Prod.Lex.monotone_fst

theorem fiberProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) (a : α) : {y | toLex (a, y) ∈ s}.IsPWO := by
  let f : α ×ₗ β → β := fun x => (ofLex x).2
  have h : {y | toLex (a, y) ∈ s} = f '' (s ∩ (fun x ↦ (ofLex x).1) ⁻¹' {a}) := by
    ext x
    simp [f]
  rw [h]
  apply IsPWO.image_of_monotoneOn (hαβ.mono inter_subset_left)
  rintro b ⟨-, hb⟩ c ⟨-, hc⟩ hbc
  simp only [mem_preimage, mem_singleton_iff] at hb hc
  have : (ofLex b).1 < (ofLex c).1 ∨ (ofLex b).1 = (ofLex c).1 ∧ f b ≤ f c :=
    Prod.Lex.toLex_le_toLex.mp hbc
  simp_all only [lt_self_iff_false, true_and, false_or]

theorem ProdLex_iff [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)} :
    s.IsPWO ↔
      ((fun (x : α ×ₗ β) ↦ (ofLex x).1) '' s).IsPWO ∧ ∀ a, {y | toLex (a, y) ∈ s}.IsPWO :=
  ⟨fun h ↦ ⟨imageProdLex h, fiberProdLex h⟩, fun h ↦ subsetProdLex h.1 h.2⟩

end Set.PartiallyWellOrderedOn

/-- A version of **Dickson's lemma** any subset of functions `Π s : σ, α s` is partially well
ordered, when `σ` is a `Fintype` and each `α s` is a linear well order.
This includes the classical case of Dickson's lemma that `ℕ ^ n` is a well partial order.
Some generalizations would be possible based on this proof, to include cases where the target is
partially well-ordered, and also to consider the case of `Set.PartiallyWellOrderedOn` instead of
`Set.IsPWO`. -/
theorem Pi.isPWO {α : ι → Type*} [∀ i, LinearOrder (α i)] [∀ i, IsWellOrder (α i) (· < ·)]
    [Finite ι] (s : Set (∀ i, α i)) : s.IsPWO := by
  cases nonempty_fintype ι
  suffices ∀ (s : Finset ι) (f : ℕ → ∀ s, α s),
    ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ x, x ∈ s → (f ∘ g) a x ≤ (f ∘ g) b x by
    refine isPWO_iff_exists_monotone_subseq.2 fun f _ => ?_
    simpa only [Finset.mem_univ, true_imp_iff] using this Finset.univ f
  refine Finset.cons_induction ?_ ?_
  · intro f
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro x s hx ih f
    obtain ⟨g, hg⟩ := (IsPWO.of_linearOrder univ).exists_monotone_subseq (f := (f · x)) mem_univ
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg (OrderHomClass.mono g' hab), hg' hab⟩

section ProdLex
variable {rα : α → α → Prop} {rβ : β → β → Prop} {f : γ → α} {g : γ → β} {s : Set γ}

/-- Stronger version of `WellFounded.prod_lex`. Instead of requiring `rβ on g` to be well-founded,
we only require it to be well-founded on fibers of `f`. -/
theorem WellFounded.prod_lex_of_wellFoundedOn_fiber (hα : WellFounded (rα on f))
    (hβ : ∀ a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    WellFounded (Prod.Lex rα rβ on fun c => (f c, g c)) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hα) fun a => hβ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | h' := Prod.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    exacts [⟨c, h'.1⟩, PSigma.subtype_ext (Subtype.ext h'.1) rfl, h'.2]

theorem Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber (hα : s.WellFoundedOn (rα on f))
    (hβ : ∀ a, (s ∩ f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    s.WellFoundedOn (Prod.Lex rα rβ on fun c => (f c, g c)) :=
  WellFounded.prod_lex_of_wellFoundedOn_fiber hα
    fun a ↦ ((hβ a).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun _ _ h ↦ ‹_›)

end ProdLex

section SigmaLex

variable {rι : ι → ι → Prop} {rπ : ∀ i, π i → π i → Prop} {f : γ → ι} {g : ∀ i, γ → π i} {s : Set γ}

/-- Stronger version of `PSigma.lex_wf`. Instead of requiring `rπ on g` to be well-founded, we only
require it to be well-founded on fibers of `f`. -/
theorem WellFounded.sigma_lex_of_wellFoundedOn_fiber (hι : WellFounded (rι on f))
    (hπ : ∀ i, (f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    WellFounded (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hι) fun a => hπ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    · exact ⟨c, h'⟩
    · exact PSigma.subtype_ext (Subtype.ext h') rfl
    · dsimp only [Subtype.coe_mk, Subrel, Order.Preimage] at *
      grind

theorem Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber (hι : s.WellFoundedOn (rι on f))
    (hπ : ∀ i, (s ∩ f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    s.WellFoundedOn (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  change WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  exact
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => ((hπ i).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun b c h => ‹_›)

end SigmaLex
