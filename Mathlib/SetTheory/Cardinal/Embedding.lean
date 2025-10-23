/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card

/-! # Existence of embeddings from finite types

Let `s : Set α` be a finite set.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card`
  If `s.ncard + n ≤ ENat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.exists_embedding_disjoint_range_of_add_le_Nat_card`
  If `α` is finite and `s.ncard + n ≤ Nat.card α`,
  then there exists an embedding `Fin n ↪ α`
  whose range is disjoint from `s`.

* `Fin.Embedding.restrictSurjective_of_add_le_ENatCard`
  If `m + n ≤ ENat.card α`, then the restriction map
  from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.

* `Fin.Embedding.restrictSurjective_of_add_le_natCard`
  If `α` is finite and `m + n ≤ Nat.card α`, then the restriction
  map from `Fin (m + n) ↪ α` to `Fin m ↪ α` is surjective.
-/

open Set Fin Function Function.Embedding

namespace Fin.Embedding

variable {α : Type*} {m n : ℕ} {s : Set α}

theorem exists_embedding_disjoint_range_of_add_le_ENat_card
    [Finite s] (hs : s.ncard + n ≤ ENat.card α) :
    ∃ y : Fin n ↪ α, Disjoint s (range y) := by
  rsuffices ⟨y⟩ : Nonempty (Fin n ↪ (sᶜ : Set α))
  · use y.trans (subtype _)
    rw [Set.disjoint_right]
    rintro _ ⟨i, rfl⟩
    simpa only [← mem_compl_iff] using Subtype.coe_prop (y i)
  rcases finite_or_infinite α with hα | hα
  · let _ : Fintype α := Fintype.ofFinite α
    classical
    apply nonempty_of_card_le
    rwa [Fintype.card_fin, ← add_le_add_iff_left s.ncard,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        ncard_add_ncard_compl, ← ENat.coe_le_coe,
        ← ENat.card_eq_coe_natCard, ENat.coe_add]
  · exact ⟨valEmbedding.trans s.toFinite.infinite_compl.to_subtype.natEmbedding⟩

theorem exists_embedding_disjoint_range_of_add_le_Nat_card
    [Finite α] (hs : s.ncard + n ≤ Nat.card α) :
    ∃ y : Fin n ↪ α, Disjoint s (range y) := by
  apply exists_embedding_disjoint_range_of_add_le_ENat_card
  rwa [← ENat.coe_add, ENat.card_eq_coe_natCard, ENat.coe_le_coe]

theorem restrictSurjective_of_add_le_ENatCard (hn : m + n ≤ ENat.card α) :
    Surjective (fun (x : Fin (m + n) ↪ α) ↦ (Fin.castAddEmb n).trans x) := by
  intro x
  obtain ⟨y, hxy⟩ :=
    exists_embedding_disjoint_range_of_add_le_ENat_card (s := range x)
      (by simpa [← Nat.card_coe_set_eq, Nat.card_range_of_injective x.injective])
  use append hxy
  ext i
  simp [trans_apply, coe_castAddEmb, append]

theorem restrictSurjective_of_le_ENatCard (hmn : m ≤ n) (hn : n ≤ ENat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_ENatCard hn

theorem restrictSurjective_of_add_le_natCard [Finite α] (hn : m + n ≤ Nat.card α) :
    Surjective (fun x : Fin (m + n) ↪ α ↦ (castAddEmb n).trans x) := by
  apply restrictSurjective_of_add_le_ENatCard
  rwa [← ENat.coe_add, ENat.card_eq_coe_natCard, ENat.coe_le_coe]

theorem restrictSurjective_of_le_natCard [Finite α] (hmn : m ≤ n) (hn : n ≤ Nat.card α) :
    Function.Surjective (fun x : Fin n ↪ α ↦ (castLEEmb hmn).trans x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Fin.Embedding.restrictSurjective_of_add_le_natCard hn

end Fin.Embedding
