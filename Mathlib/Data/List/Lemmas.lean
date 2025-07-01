/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.List.InsertIdx

/-! # Some lemmas about lists involving sets

Split out from `Data.List.Basic` to reduce its dependencies.
-/

open List

variable {α β γ : Type*}

namespace List

@[simp]
theorem setOf_mem_eq_empty_iff {l : List α} : { x | x ∈ l } = ∅ ↔ l = [] :=
  Set.eq_empty_iff_forall_notMem.trans eq_nil_iff_forall_not_mem.symm

@[deprecated (since := "2024-12-10")] alias tail_reverse_eq_reverse_dropLast := tail_reverse

theorem injOn_insertIdx_index_of_notMem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => l.insertIdx k x) { n | n ≤ l.length } := by
  induction' l with hd tl IH
  · intro n hn m hm _
    simp_all [Set.mem_singleton_iff, Set.setOf_eq_eq_singleton, length]
  · intro n hn m hm h
    simp only [length, Set.mem_setOf_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [hx.left] at h
    · simp [Ne.symm hx.left] at h
    · simp only [true_and, eq_self_iff_true, insertIdx_succ_cons] at h
      rw [Nat.succ_inj]
      refine IH hx.right ?_ ?_ (by injection h)
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm

@[deprecated (since := "2025-05-23")]
alias injOn_insertIdx_index_of_not_mem := injOn_insertIdx_index_of_notMem

theorem foldr_range_subset_of_range_subset {f : β → α → α} {g : γ → α → α}
    (hfg : Set.range f ⊆ Set.range g) (a : α) : Set.range (foldr f a) ⊆ Set.range (foldr g a) := by
  rintro _ ⟨l, rfl⟩
  induction' l with b l H
  · exact ⟨[], rfl⟩
  · obtain ⟨c, hgf⟩ := hfg (Set.mem_range_self b)
    obtain ⟨m, hgf'⟩ := H
    rw [foldr_cons, ← hgf, ← hgf']
    exact ⟨c :: m, rfl⟩

theorem foldl_range_subset_of_range_subset {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) ⊆ Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) ⊆ Set.range (foldl g a) := by
  change (Set.range fun l => _) ⊆ Set.range fun l => _
  -- Porting note: have to write `(foldr_reverse)` instead of `foldr_reverse`.
  simp_rw [← (foldr_reverse), Set.range_comp' _ reverse,
    reverse_involutive.bijective.surjective.range_eq, Set.image_univ]
  exact foldr_range_subset_of_range_subset hfg a

theorem foldr_range_eq_of_range_eq {f : β → α → α} {g : γ → α → α} (hfg : Set.range f = Set.range g)
    (a : α) : Set.range (foldr f a) = Set.range (foldr g a) :=
  (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)

theorem foldl_range_eq_of_range_eq {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) = Set.range (foldl g a) :=
  (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)



/-!
  ### MapAccumr and Foldr
  Some lemmas relation `mapAccumr` and `foldr`
-/
section MapAccumr

theorem mapAccumr_eq_foldr {σ : Type*} (f : α → σ → σ × β) : ∀ (as : List α) (s : σ),
    mapAccumr f as s = List.foldr (fun a s =>
                                    let r := f a s.1
                                    (r.1, r.2 :: s.2)
                                  ) (s, []) as
  | [], _ => rfl
  | a :: as, s => by
    simp only [mapAccumr, foldr, mapAccumr_eq_foldr f as]

theorem mapAccumr₂_eq_foldr {σ φ : Type*} (f : α → β → σ → σ × φ) :
    ∀ (as : List α) (bs : List β) (s : σ),
    mapAccumr₂ f as bs s = foldr (fun ab s =>
                              let r := f ab.1 ab.2 s.1
                              (r.1, r.2 :: s.2)
                            ) (s, []) (as.zip bs)
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | a :: as, b :: bs, s => by
    simp only [mapAccumr₂, foldr, mapAccumr₂_eq_foldr f as]
    rfl

end MapAccumr

end List
