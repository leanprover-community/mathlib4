/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Order.RelSeries
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lemmas about series of a relation
-/

public section

namespace RelSeries

variable {α : Type*} {r : SetRel α α} (p : RelSeries r)

theorem length_lt_natCard [r.IsIrrefl] [r.IsTrans] [Finite α] : p.length < Nat.card α := by
  simpa using Nat.card_le_card_of_injective p p.toFun_injective

theorem length_lt_enatCard [r.IsIrrefl] [r.IsTrans] : p.length < ENat.card α := by
  simpa [ENat.natCast_add_one_le_iff] using ENat.card_le_card_of_injective p.toFun_injective

end RelSeries
