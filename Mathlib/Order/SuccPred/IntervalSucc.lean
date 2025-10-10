/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.SuccPred.Archimedean

/-!
# Intervals `Ixx (f x) (f (Order.succ x))`

In this file we prove

* `Monotone.biUnion_Ico_Ioc_map_succ`: if `α` is a linear archimedean succ order and `β` is a linear
  order, then for any monotone function `f` and `m n : α`, the union of intervals
  `Set.Ioc (f i) (f (Order.succ i))`, `m ≤ i < n`, is equal to `Set.Ioc (f m) (f n)`;

* `Monotone.pairwise_disjoint_on_Ioc_succ`: if `α` is a linear succ order, `β` is a preorder, and
  `f : α → β` is a monotone function, then the intervals `Set.Ioc (f n) (f (Order.succ n))` are
  pairwise disjoint.

For the latter lemma, we also prove various order dual versions.
-/


open Set Order

variable {α β : Type*} [LinearOrder α]

theorem biUnion_Ici_Ico_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    {a : α} (hf : ∀ i ∈ Ici a, f a ≤ f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i ∈ Ici a, Ico (f i) (f (succ i)) = Ici (f a) := by
  apply subset_antisymm <|
    iUnion₂_subset fun i hi ↦ Ico_subset_Ico_left (hf i hi) |>.trans Ico_subset_Ici_self
  intro b hb
  contrapose! h2f
  use b
  simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact Succ.rec (P := fun i _ ↦ f i ≤ b) hb (by aesop)

theorem biUnion_Ici_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    {a : α} (hf : ∀ i ∈ Ici a, f a ≤ f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i ∈ Ici a, Ioc (f i) (f (succ i)) = Ioi (f a) := by
  apply subset_antisymm <|
    iUnion₂_subset fun i hi ↦ Ioc_subset_Ioc_left (hf i hi) |>.trans Ioc_subset_Ioi_self
  intro b hb
  contrapose! h2f
  suffices ∀ i, a ≤ i → f i < b from ⟨b, by aesop (add simp [upperBounds, le_of_lt])⟩
  exact Succ.rec (P := fun i _ ↦ f i < b) hb (by aesop)

namespace Monotone

/-- If `α` is a linear archimedean succ order and `β` is a linear order, then for any monotone
function `f` and `m n : α`, the union of intervals `Set.Ioc (f i) (f (Order.succ i))`, `m ≤ i < n`,
is equal to `Set.Ioc (f m) (f n)` -/
theorem biUnion_Ico_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    (hf : Monotone f) (m n : α) : ⋃ i ∈ Ico m n, Ioc (f i) (f (succ i)) = Ioc (f m) (f n) := by
  rcases le_total n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), biUnion_empty]
  · refine Succ.rec ?_ ?_ hmn
    · simp only [Ioc_self, Ico_self, biUnion_empty]
    · intro k hmk ihk
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf <| le_succ _), union_comm, ← ihk]
      by_cases hk : IsMax k
      · rw [hk.succ_eq, Ioc_self, empty_union]
      · rw [Ico_succ_right_eq_insert_of_not_isMax hmk hk, biUnion_insert]

open scoped Function -- required for scoped `on` notation

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioc (f n) (f (Order.succ n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
      h₂.not_ge <| h₁.trans <| hf <| succ_le_of_lt hmn

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ico (f n) (f (Order.succ n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
      h₁.not_ge <| (hf <| succ_le_of_lt hmn).trans h₂

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioo (f n) (f (Order.succ n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (succ n))) :=
  hf.pairwise_disjoint_on_Ico_succ.mono fun _ _ h => h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioc (f Order.pred n) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f (pred n)) (f n)) := by
  simpa using hf.dual.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ico (f Order.pred n) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f (pred n)) (f n)) := by
  simpa using hf.dual.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioo (f Order.pred n) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f (pred n)) (f n)) := by
  simpa using hf.dual.pairwise_disjoint_on_Ioo_succ

end Monotone

namespace Antitone

open scoped Function -- required for scoped `on` notation

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioc (f (Order.succ n)) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ico (f (Order.succ n)) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ico_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioo (f (Order.succ n)) (f n)` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_pred

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioc (f n) (f (Order.pred n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ico (f n) (f (Order.pred n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioo (f n) (f (Order.pred n))` are pairwise disjoint. -/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_succ

end Antitone
