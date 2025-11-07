/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Order.Interval.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FastInstance
/-!
# The lexicographic order on intervals

This order is compatible with the inclusion ordering, but is total.

Under this ordering, `[(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)]` is sorted.
-/

namespace NonemptyInterval

variable {α}

section LELT
variable [LT α] [LE α]

instance : LE (Lex (NonemptyInterval α)) where
  le x y := toLex (ofLex x).toDualProd ≤ toLex (ofLex y).toDualProd

instance : LT (Lex (NonemptyInterval α)) where
  lt x y := toLex (ofLex x).toDualProd < toLex (ofLex y).toDualProd

theorem toLex_le_toLex {x y : NonemptyInterval α} :
    toLex x ≤ toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd ≤ y.snd :=
  Prod.lex_def

theorem toLex_lt_toLex {x y : NonemptyInterval α} :
    toLex x < toLex y ↔ y.fst < x.fst ∨ x.fst = y.fst ∧ x.snd < y.snd :=
  Prod.lex_def

instance [DecidableEq α] [DecidableLT α] [DecidableLE α] : DecidableLE (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_le_toLex

instance [DecidableEq α] [DecidableLT α] : DecidableLT (Lex (NonemptyInterval α)) :=
  fun _ _ => decidable_of_iff' _ toLex_lt_toLex

-- Sanity check on the ordering.
/-- info: [(3, 3), (2, 2), (2, 3), (1, 1), (1, 2), (1, 3)] -/
#guard_msgs in
#eval [
  NonemptyInterval.mk (1, 1) (by grind),
  NonemptyInterval.mk (1, 2) (by grind),
  NonemptyInterval.mk (1, 3) (by grind),
  NonemptyInterval.mk (2, 2) (by grind),
  NonemptyInterval.mk (2, 3) (by grind),
  NonemptyInterval.mk (3, 3) (by grind)].map toLex |>.mergeSort.map (·.toProd)

end LELT

instance [Preorder α] : Preorder (Lex (NonemptyInterval α)) := fast_instance%
  Preorder.lift fun x => toLex (ofLex x).toDualProd

theorem toLex_mono [PartialOrder α] : Monotone (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_mono.comp toDualProd_mono

theorem toLex_strictMono [PartialOrder α] : StrictMono (toLex : NonemptyInterval α → _) :=
  Prod.Lex.toLex_strictMono.comp toDualProd_strictMono

instance [PartialOrder α] : PartialOrder (Lex (NonemptyInterval α)) := fast_instance%
  PartialOrder.lift (fun x => toLex (ofLex x).toDualProd) <|
    toLex.injective.comp <| toDualProd_injective.comp ofLex.injective

instance [LinearOrder α] : LinearOrder (Lex (NonemptyInterval α)) := fast_instance%
  { LinearOrder.lift' (fun x : Lex (NonemptyInterval α) => toLex (ofLex x).toDualProd) <|
      toLex.injective.comp <| toDualProd_injective.comp ofLex.injective with
    toDecidableEq := inferInstance
    toDecidableLT := inferInstance
    toDecidableLE := inferInstance }

end NonemptyInterval
