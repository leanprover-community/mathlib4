/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Felix Weilacher
-/
import Mathlib.Topology.Bases

open Set TopologicalSpace Filter

/-!
We prove that countable discrete spaces are second countable.
-/

variable {α : Type*} [TopologicalSpace α]

instance (priority := 100) DiscreteTopology.secondCountableTopology_of_encodable
    [hd : DiscreteTopology α] [Encodable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (iUnion_of_singleton α)
#align discrete_topology.second_countable_topology_of_encodable DiscreteTopology.secondCountableTopology_of_encodable

instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable {α : Type*}
    [TopologicalSpace α] [DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  @DiscreteTopology.secondCountableTopology_of_encodable _ _ _ (Encodable.ofCountable _)
#align discrete_topology.second_countable_topology_of_countable DiscreteTopology.secondCountableTopology_of_countable
