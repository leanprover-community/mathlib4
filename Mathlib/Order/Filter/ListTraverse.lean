/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Control.Traversable.Instances
import Mathlib.Order.Filter.Basic

#align_import order.filter.basic from "leanprover-community/mathlib"@"d4f691b9e5f94cfc64639973f3544c95f8d5d494"
/-!
# Properties of `Traversable.traverse` on `List`s and `Filter`s

In this file we prove basic properties (monotonicity, membership)
for `Traversable.traverse f l`, where `f : β → Filter α` and `l : List β`.
-/

open Set List

namespace Filter

universe u

variable {α β γ : Type u} {f : β → Filter α} {s : γ → Set α}

theorem sequence_mono : ∀ as bs : List (Filter α), Forall₂ (· ≤ ·) as bs → sequence as ≤ sequence bs
  | [], [], Forall₂.nil => le_rfl
  | _::as, _::bs, Forall₂.cons h hs => seq_mono (map_mono h) (sequence_mono as bs hs)
#align filter.sequence_mono Filter.sequence_mono

theorem mem_traverse :
    ∀ (fs : List β) (us : List γ),
      Forall₂ (fun b c => s c ∈ f b) fs us → traverse s us ∈ traverse f fs
  | [], [], Forall₂.nil => mem_pure.2 <| mem_singleton _
  | _::fs, _::us, Forall₂.cons h hs => seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)
#align filter.mem_traverse Filter.mem_traverse

-- TODO: add a `Filter.HasBasis` statement
theorem mem_traverse_iff (fs : List β) (t : Set (List α)) :
    t ∈ traverse f fs ↔
      ∃ us : List (Set α), Forall₂ (fun b (s : Set α) => s ∈ f b) fs us ∧ sequence us ⊆ t := by
  constructor
  · induction fs generalizing t with
    | nil =>
      simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff, exists_eq_left, Set.pure_def,
        singleton_subset_iff, traverse_nil]
    | cons b fs ih =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩
      rcases ih v hv with ⟨us, hus, hu⟩
      exact ⟨w::us, Forall₂.cons hw hus, (Set.seq_mono hwu hu).trans ht⟩
  · rintro ⟨us, hus, hs⟩
    exact mem_of_superset (mem_traverse _ _ hus) hs
#align filter.mem_traverse_iff Filter.mem_traverse_iff
