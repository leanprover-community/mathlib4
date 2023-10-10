/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Parity

#align_import data.fintype.parity from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# The cardinality of `Fin (bit0 n)` is even.
-/


variable {α : Type*}

namespace Fintype

instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α → Prop) := fun _ => Fintype.decidableExistsFintype
#align fintype.is_square.decidable_pred Fintype.IsSquare.decidablePred

end Fintype

set_option linter.deprecated false

/-- The cardinality of `Fin (bit0 n)` is even, `Fact` version.
This `Fact` is needed as an instance by `Matrix.SpecialLinearGroup.has_neg`. -/
theorem Fintype.card_fin_even {n : ℕ} : Fact (Even (Fintype.card (Fin (bit0 n)))) :=
  ⟨by rw [Fintype.card_fin]; exact even_bit0 _⟩
#align fintype.card_fin_even Fintype.card_fin_even
