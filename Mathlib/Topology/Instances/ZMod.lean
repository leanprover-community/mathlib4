/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Constructions

/-!
This file adds a discrete topological structure to `ZMod n` for all `n`.
-/

namespace ZMod
/-- Making `ZMod` a discrete topological space. -/
instance {d : ℕ} : TopologicalSpace (ZMod d) := ⊥

instance {d : ℕ} : DiscreteTopology (ZMod d) := { eq_bot := rfl }
end ZMod

lemma embedding_val (d : ℕ) [NeZero d] : Embedding (ZMod.val : ZMod d → ℕ) :=
  Embedding.of_discreteTopology ZMod.val (ZMod.val_injective d)
