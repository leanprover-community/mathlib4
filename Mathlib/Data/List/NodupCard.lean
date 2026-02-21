/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Finite.Card

/-!
# Cardinality of lists with no duplicates
-/

@[expose] public section

namespace List.Nodup

variable {α : Type*} {l : List α} (h : l.Nodup)

include h in
theorem length_le_nat_card [Finite α] : l.length ≤ Nat.card α := by
  have := Fintype.ofFinite α
  grw [h.length_le_card, Fintype.card_eq_nat_card]

include h in
theorem length_le_enat_card : l.length ≤ ENat.card α := by
  cases finite_or_infinite α
  · grw [h.length_le_nat_card, ENat.card_eq_coe_natCard]
  · grw [ENat.card_eq_top_of_infinite]
    exact le_top

end List.Nodup
