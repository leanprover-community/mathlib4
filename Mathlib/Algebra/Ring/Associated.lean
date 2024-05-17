/-
Copyright (c) 2024 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Ring.Units

/-!
# Negation of associated elements.
-/

namespace Associated

variable {α : Type*} [Monoid α] [HasDistribNeg α] {a b : α} (h : Associated a b)

/-- Notation for two elements of a monoid are associated, i.e.
if one of them is another one multiplied by a unit on the right. -/
local infixl:50 " ~ᵤ " => Associated

theorem neg_left : (-a) ~ᵤ b :=
  let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩

theorem neg_right : a ~ᵤ (-b) :=
  h.symm.neg_left.symm

theorem neg_neg : (-a) ~ᵤ (-b) :=
  h.neg_left.neg_right

end Associated
