/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.SetTheory.Surreal.Basic

/-!
# Surreals as games

We define the canonical map `Ordinal → Surreal` in terms of the map `Ordinal.toPGame`.

# Main declarations

- `Ordinal.toSurreal`: The canonical map between ordinals and surreal numbers.
-/

open Surreal SetTheory PGame

namespace Ordinal

/-- Ordinal games are numeric. -/
theorem numeric_toPGame (o : Ordinal) : o.toPGame.Numeric := by
  induction' o using Ordinal.induction with o IH
  apply numeric_of_isEmpty_rightMoves
  simpa using fun i => IH _ (Ordinal.toLeftMovesToPGame_symm_lt i)

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun o := .mk _ o.numeric_toPGame
  inj' _ _ h := toPGame_equiv_iff.1 (Quotient.exact h :)
  map_rel_iff' := @toPGame_le_iff

end Ordinal
