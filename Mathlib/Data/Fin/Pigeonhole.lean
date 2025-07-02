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

/--
If we have an injective map from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_injective` for the generalisation to arbitrary finite types.
-/
theorem le_of_injective (f : Fin m → Fin n) (hf : f.Injective) : m ≤ n := by
  simpa using Fintype.card_le_of_injective f hf

/--
If we have an embedding from `Fin m` to `Fin n`, then `m ≤ n`.
See also `Fintype.card_le_of_embedding` for the generalisation to arbitrary finite types.
-/
theorem le_of_embedding (f : Fin m ↪ Fin n) : m ≤ n := by
  simpa using Fintype.card_le_of_embedding f

/--
If we have an injective map from `Fin m` to `Fin n` whose image does not contain everything,
then `m < n`. See also `Fintype.card_lt_of_injective_of_notMem` for the generalisation to
arbitrary finite types.
-/
theorem lt_of_injective_of_notMem (f : Fin m → Fin n) (hf : f.Injective) {b : Fin n}
    (hb : b ∉ Set.range f) : m < n := by
  simpa using Fintype.card_lt_of_injective_of_notMem f hf hb

/--
If we have a surjective map from `Fin m` to `Fin n`, then `m ≥ n`.
See also `Fintype.card_le_of_surjective` for the generalisation to arbitrary finite types.
-/
theorem le_of_surjective (f : Fin m → Fin n) (hf : Function.Surjective f) : n ≤ m := by
  simpa using Fintype.card_le_of_surjective f hf

/--
Any map from `Fin m` reaches at most `m` different values.
See also `Fintype.card_range_le` for the generalisation to an arbitrary finite type.
-/
theorem card_range_le {α : Type*} [Fintype α] [DecidableEq α] (f : Fin m → α) :
    Fintype.card (Set.range f) ≤ m := by
  simpa using Fintype.card_range_le f

end Fin
