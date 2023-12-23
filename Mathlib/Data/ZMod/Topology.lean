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

@[continuity]
lemma induced_top_cont_inv {n : ℕ} : @Continuous _ _ (TopologicalSpace.induced
    (Units.coeHom (ZMod n)) inferInstance) _ (Units.inv : (ZMod n)ˣ → ZMod n) := by
  convert continuous_of_discreteTopology
  have : @Embedding _ _ (TopologicalSpace.induced
    (Units.coeHom (ZMod n)) inferInstance) _ (Units.coeHom (ZMod n))
  { refine' Function.Injective.embedding_induced (λ a b h => _)
    simp only [Units.coeHom_apply, ← Units.ext_iff] at h
    rw [h] }
  refine' @Embedding.discreteTopology _ _ (TopologicalSpace.induced
    (Units.coeHom (ZMod n)) inferInstance) _ _ _ this
