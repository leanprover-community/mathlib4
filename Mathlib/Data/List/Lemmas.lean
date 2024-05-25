/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.List.InsertNth
import Mathlib.Init.Data.List.Lemmas

#align_import data.list.lemmas from "leanprover-community/mathlib"@"2ec920d35348cb2d13ac0e1a2ad9df0fdf1a76b4"

/-! # Some lemmas about lists involving sets

Split out from `Data.List.Basic` to reduce its dependencies.
-/

open List

variable {α β γ : Type*}

namespace List

theorem injOn_insertNth_index_of_not_mem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => insertNth k x l) { n | n ≤ l.length } := by
  induction' l with hd tl IH
  · intro n hn m hm _
    simp only [Set.mem_singleton_iff, Set.setOf_eq_eq_singleton,
      length] at hn hm
    simp_all [hn, hm]
  · intro n hn m hm h
    simp only [length, Set.mem_setOf_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [hx.left] at h
    · simp [Ne.symm hx.left] at h
    · simp only [true_and_iff, eq_self_iff_true, insertNth_succ_cons] at h
      rw [Nat.succ_inj']
      refine IH hx.right ?_ ?_ (by injection h)
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm
#align list.inj_on_insert_nth_index_of_not_mem List.injOn_insertNth_index_of_not_mem

theorem foldr_range_subset_of_range_subset {f : β → α → α} {g : γ → α → α}
    (hfg : Set.range f ⊆ Set.range g) (a : α) : Set.range (foldr f a) ⊆ Set.range (foldr g a) := by
  rintro _ ⟨l, rfl⟩
  induction' l with b l H
  · exact ⟨[], rfl⟩
  · cases' hfg (Set.mem_range_self b) with c hgf
    cases' H with m hgf'
    rw [foldr_cons, ← hgf, ← hgf']
    exact ⟨c :: m, rfl⟩
#align list.foldr_range_subset_of_range_subset List.foldr_range_subset_of_range_subset

theorem foldl_range_subset_of_range_subset {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) ⊆ Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) ⊆ Set.range (foldl g a) := by
  change (Set.range fun l => _) ⊆ Set.range fun l => _
  -- Porting note: This was simply `simp_rw [← foldr_reverse]`
  simp_rw [← foldr_reverse _ (fun z w => g w z), ← foldr_reverse _ (fun z w => f w z)]
  -- Porting note: This `change` was not necessary in mathlib3
  change (Set.range (foldr (fun z w => f w z) a ∘ reverse)) ⊆
    Set.range (foldr (fun z w => g w z) a ∘ reverse)
  simp_rw [Set.range_comp _ reverse, reverse_involutive.bijective.surjective.range_eq,
    Set.image_univ]
  exact foldr_range_subset_of_range_subset hfg a
#align list.foldl_range_subset_of_range_subset List.foldl_range_subset_of_range_subset

theorem foldr_range_eq_of_range_eq {f : β → α → α} {g : γ → α → α} (hfg : Set.range f = Set.range g)
    (a : α) : Set.range (foldr f a) = Set.range (foldr g a) :=
  (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)
#align list.foldr_range_eq_of_range_eq List.foldr_range_eq_of_range_eq

theorem foldl_range_eq_of_range_eq {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) = Set.range (foldl g a) :=
  (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)
#align list.foldl_range_eq_of_range_eq List.foldl_range_eq_of_range_eq



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
  | [], s => rfl
  | a :: as, s => by
    simp only [mapAccumr, foldr, mapAccumr_eq_foldr f as]

theorem mapAccumr₂_eq_foldr {σ φ : Type*} (f : α → β → σ → σ × φ) :
    ∀ (as : List α) (bs : List β) (s : σ),
    mapAccumr₂ f as bs s = foldr (fun ab s =>
                              let r := f ab.1 ab.2 s.1
                              (r.1, r.2 :: s.2)
                            ) (s, []) (as.zip bs)
  | [], [], s => rfl
  | a :: as, [], s => rfl
  | [], b :: bs, s => rfl
  | a :: as, b :: bs, s => by
    simp only [mapAccumr₂, foldr, mapAccumr₂_eq_foldr f as]
    rfl

end MapAccumr

end List
