/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Card
import Mathlib.ModelTheory.Constants.Basic

/-!
# Cardinality results on adding constants to a language

-/

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable {α : Type w'}

theorem card_constantsOn : (constantsOn α).card = #α := by
  simp [card_eq_card_functions_add_card_relations, sum_nat_eq_add_sum_succ]

variable (L : Language.{u, v})

@[simp]
theorem card_withConstants :
    L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} #α := by
  rw [withConstants, card_sum, card_constantsOn]

end Language

end FirstOrder
