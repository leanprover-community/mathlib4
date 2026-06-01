/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Sets are a complete atomic Boolean algebra.

This file contains only the definition of the complete atomic Boolean algebra structure on `Set`.
Indexed union/intersection are defined in `Mathlib.Order.SetNotation`; lemmas are available in
`Mathlib/Data/Set/Lattice.lean`.

## Main declarations

* `Set.completeAtomicBooleanAlgebra`: `Set α` is a `CompleteAtomicBooleanAlgebra` with `≤ = ⊆`,
  `< = ⊂`, `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference.
  See `Set.instBooleanAlgebra`.
-/

public section

variable {α : Type*}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/

instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Set α) where
  isLUB_sSup _ := ⟨fun s hs _ hx ↦ ⟨s, hs, hx⟩, fun _ h _ ⟨_, ⟨hs, hx⟩⟩ => h hs hx⟩
  isGLB_sInf _ := ⟨fun _ hs _ hx ↦ hx _ hs, fun _ h _ hx _ hs => h hs hx⟩
  iInf_iSup_eq := by intros; ext; simp [Classical.skolem]

instance : OrderTop (Set α) where
  top := univ
  le_top := by simp

end Set
