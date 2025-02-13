/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Patrick Massot, Simon Hudon, Alice Laroche, Frédéric Dupuis,
Jireh Loreaux
-/
import Mathlib.Tactic.Push.Basic

/-!
This file adds the `push` attribute to some basic theorems.
-/

namespace Mathlib.Tactic.Push

attribute [push] not_not not_or Classical.not_imp

@[push] theorem not_iff (p q : Prop) : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q) :=
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

end Mathlib.Tactic.Push
