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

lemma embedding_coeHom (d : ℕ) : Embedding (Units.coeHom (ZMod d)) :=
  Units.embedding_of_discreteTopology _ Units.ext

lemma embedding_coe_inv (d : ℕ) : Embedding (fun u ↦ ↑u⁻¹ : (ZMod d)ˣ → (ZMod d)) :=
  Units.embedding_coe_iff.mp (embedding_coeHom d)
