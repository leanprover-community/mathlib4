/-
Copyright (c) 2025 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Data.Fintype.Card

/-!
# Pigeonhole-like results for Fin

This adapts Pigeonhole-like results from `Mathlib.Data.Fintype.Card` to the setting where the map
has the type `f : Fin m → Fin n`.

-/

namespace Fin

variable {m n : ℕ}

theorem le_of_injective (f : Fin m → Fin n) (hf : f.Injective) : m ≤ n :=
  Fintype.card_fin m ▸ Fintype.card_fin n ▸ Fintype.card_le_of_injective f hf

theorem le_of_embedding (f : Fin m ↪ Fin n) : m ≤ n :=
  Fintype.card_fin m ▸ Fintype.card_fin n ▸ Fintype.card_le_of_embedding f

theorem lt_of_injective_of_not_mem (f : Fin m → Fin n) (hf : f.Injective) {b : Fin n}
    (hb : b ∉ Set.range f) : m < n :=
  Fintype.card_fin m ▸ Fintype.card_fin n ▸ Fintype.card_lt_of_injective_of_not_mem f hf hb

theorem le_of_surjective (f : Fin m → Fin n) (hf : Function.Surjective f) : n ≤ m :=
  Fintype.card_fin m ▸ Fintype.card_fin n ▸ Fintype.card_le_of_surjective f hf

theorem card_range_le (f : Fin m → Fin n) : Fintype.card (Set.range f) ≤ m := by
  convert Fintype.card_range_le f
  exact (Fintype.card_fin m).symm

end Fin
