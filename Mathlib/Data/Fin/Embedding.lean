/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! # Constructions of embeddings of `Fin n` into a type

* `Fin.Embedding.merge` : merges two embeddings `Fin m ↪ α` and `Fin n ↪ α`
into an embedding `Fin p ↪ α` if they have disjoint range and `p = m + n`.

* `Fin.Embedding.merge_compl` : variant where one merges `Fin m ↪ s`
and `Fin n ↪ sᶜ`, where `s : Set α`.

* `Fin.Embedding.append` : from an embedding `x : Fin n ↪ α` and `a : α` such that
`a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α`.

* `Fin.Embedding.restrictSurjective_of_le_ENatCard` :
if `m ≤ n` and `n ≤ ENat.card α`,
then the restriction map `(n ↪ α) → (m ↪ α)` is surjective.

* `Fin.Embedding.restrictSurjective_of_le_NatCard` :
if `m ≤ n` and `n ≤ Nat.card α` (for `Finite α`),
then the restriction map `(n ↪ α) → (m ↪ α)` is surjective.

-/

open MulAction MulActionHom Function.Embedding Fin Set Nat

namespace Fin.Embedding

variable {α : Type*}

/-- Merge two disjoint embeddings from `Fin m` and `Fin n` into `α`
  to an embedding from `Fin m + n`. -/
def merge {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ α) (hxy : Disjoint (range x) (range y)) :
    Fin p ↪ α where
  toFun (i : Fin p) : α :=
    if hi : i < m
    then x ⟨i, hi⟩
    else y ⟨i - m, by
      rw [Nat.sub_lt_iff_lt_add (not_lt.mp hi), h]
      exact i.prop⟩
  inj' i j h := by
    by_cases hi : i < m
    · by_cases hj : j < m
      · apply Fin.eq_of_val_eq
        simpa [dif_pos hi, dif_pos hj] using h
      · simp only [dif_pos hi, dif_neg hj] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h
        apply hxy.not_mem_of_mem_right (by simp)
    · by_cases hj : j < m
      · simp only [dif_neg hi, dif_pos hj] at h
        exfalso
        apply ne_of_mem_of_not_mem (Set.mem_range_self _) _ h.symm
        apply hxy.not_mem_of_mem_right (by simp)
      · apply Fin.eq_of_val_eq
        rw [← tsub_left_inj (not_lt.mp hi) (not_lt.mp hj)]
        simpa [dif_neg hi, dif_neg hj, Subtype.coe_inj, y.injective.eq_iff] using h

@[simp]
theorem merge_apply {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ α) (hxy : Disjoint (range x) (range y)) (i : Fin p) :
    Fin.Embedding.merge h x y hxy i =
    if hi : i < m then x ⟨i, hi⟩ else y ⟨i - m, by
      rw [Nat.sub_lt_iff_lt_add (not_lt.mp hi), h]
      exact i.prop⟩ :=
  rfl

/-- Merge two disjoint embeddings from `Fin m` and `Fin n` into `α`
  to an embedding from `Fin m + n`. -/
def merge_compl {m n p : ℕ} (h : m + n = p)
    (x : Fin m ↪ α) (y : Fin n ↪ ↑(range ⇑x)ᶜ) : Fin p ↪ α :=
  Fin.Embedding.merge h x (y.trans (subtype _)) (by
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simp only [trans_apply, subtype_apply, ← mem_compl_iff]
    exact Subtype.coe_prop (y i))

/-- Extend a fin embedding by another element -/
def append {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range ⇑x) : Fin n.succ ↪ α :=
  Fin.Embedding.merge_compl (Nat.succ_eq_add_one n).symm x
    { toFun _ := ⟨a, ha⟩, inj' _ _ _ := Subsingleton.elim _ _ }

theorem append_apply {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} {i : Fin n.succ} :
    append x ha i = if hi : i.val < n then  x ⟨i, hi⟩ else a :=
  rfl

theorem append_apply_of_lt {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} {i : Fin n.succ} (hi : i.val < n) :
    Fin.Embedding.append x ha i = x ⟨i, hi⟩ := by
  simp_all [append_apply]

theorem append_apply_last {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range ⇑x) :
    Fin.Embedding.append x ha (Fin.last n) = a := by
  simp [append_apply]

theorem restrictSurjective_of_le_ENatCard
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ ENat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (Fin.castLEEmb hmn).trans x) := by
  intro x
  classical
  have : Nonempty (Fin (n - m) ↪ ((Set.range x)ᶜ : Set α)) := by
    rcases finite_or_infinite α with hα | hα
    · have : Fintype α := Fintype.ofFinite α
      classical
      apply Function.Embedding.nonempty_of_card_le
      rw [Fintype.card_fin, ← card_eq_fintype_card, Set.Nat.card_coe_set_eq,
        ← add_le_add_iff_left, ncard_add_ncard_compl, ← Set.Nat.card_coe_set_eq,
        Nat.card_range_of_injective x.injective, card_eq_fintype_card,
        Fintype.card_fin, Nat.add_sub_of_le hmn, ← ENat.coe_le_coe]
      exact le_trans hn (by simp)
    · exact ⟨valEmbedding.trans (finite_range x).infinite_compl.to_subtype.natEmbedding⟩
  obtain ⟨y⟩ := this
  use Fin.Embedding.merge_compl (add_sub_of_le hmn) x y
  ext i
  simp [Fin.Embedding.merge_compl, Fin.Embedding.merge, dif_pos i.prop]

theorem restrictSurjective_of_le_natCard
    {m n : ℕ} [Finite α] (hmn : m ≤ n) (hn : n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (Fin.castLEEmb hmn).trans x) :=
  Fin.Embedding.restrictSurjective_of_le_ENatCard
    hmn (by rwa [← ENat.coe_le_coe, ← ENat.card_eq_coe_natCard α] at hn)

end Fin.Embedding
