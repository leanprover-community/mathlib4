/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card

#align_import data.fintype.parity from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# The cardinality of `Fin 2` is even.
-/


variable {α : Type*}

namespace Fintype

instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α → Prop) := fun _ => Fintype.decidableExistsFintype
#align fintype.is_square.decidable_pred Fintype.IsSquare.decidablePred

/-- The cardinality of `Fin 2` is even, `Fact` version.
This `Fact` is needed as an instance by `Matrix.SpecialLinearGroup.instNeg`. -/
instance card_fin_two : Fact (Even (Fintype.card (Fin 2))) :=
  ⟨⟨1, rfl⟩⟩
#noalign fintype.card_fin_even

end Fintype
