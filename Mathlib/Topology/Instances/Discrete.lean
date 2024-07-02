/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Order.SuccPred.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Metrizable.Uniformity

#align_import topology.instances.discrete from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# Instances related to the discrete topology

We prove that the discrete topology is
* first-countable,
* second-countable for an encodable type,
* equal to the order topology in linear orders which are also `PredOrder` and `SuccOrder`,
* metrizable.

When importing this file and `Data.Nat.SuccPred`, the instances `SecondCountableTopology ℕ`
and `OrderTopology ℕ` become available.

-/


open Order Set TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

instance (priority := 100) DiscreteTopology.firstCountableTopology [DiscreteTopology α] :
    FirstCountableTopology α where
  nhds_generated_countable := by rw [nhds_discrete]; exact isCountablyGenerated_pure
#align discrete_topology.first_countable_topology DiscreteTopology.firstCountableTopology

instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable
    [hd : DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  haveI : ∀ i : α, SecondCountableTopology (↥({i} : Set α)) := fun i =>
    { is_open_generated_countable :=
        ⟨{univ}, countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩ }
  secondCountableTopology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (iUnion_of_singleton α)
#align discrete_topology.second_countable_topology_of_encodable DiscreteTopology.secondCountableTopology_of_countable

@[deprecated DiscreteTopology.secondCountableTopology_of_countable (since := "2024-03-11")]
theorem DiscreteTopology.secondCountableTopology_of_encodable {α : Type*}
    [TopologicalSpace α] [DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  DiscreteTopology.secondCountableTopology_of_countable
#align discrete_topology.second_countable_topology_of_countable DiscreteTopology.secondCountableTopology_of_countable

theorem bot_topologicalSpace_eq_generateFrom_of_pred_succOrder [PartialOrder α] [PredOrder α]
    [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] :
    (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a } := by
  refine (eq_bot_of_singletons_open fun a => ?_).symm
  have h_singleton_eq_inter : {a} = Iio (succ a) ∩ Ioi (pred a) := by
    suffices h_singleton_eq_inter' : {a} = Iic a ∩ Ici a by
      rw [h_singleton_eq_inter', ← Ioi_pred, ← Iio_succ]
    rw [inter_comm, Ici_inter_Iic, Icc_self a]
  rw [h_singleton_eq_inter]
  letI := Preorder.topology α
  apply IsOpen.inter
  · exact isOpen_generateFrom_of_mem ⟨succ a, Or.inr rfl⟩
  · exact isOpen_generateFrom_of_mem ⟨pred a, Or.inl rfl⟩
#align bot_topological_space_eq_generate_from_of_pred_succ_order bot_topologicalSpace_eq_generateFrom_of_pred_succOrder

theorem discreteTopology_iff_orderTopology_of_pred_succ' [PartialOrder α] [PredOrder α]
    [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · rw [h.eq_bot]
    exact bot_topologicalSpace_eq_generateFrom_of_pred_succOrder
  · rw [h.topology_eq_generate_intervals]
    exact bot_topologicalSpace_eq_generateFrom_of_pred_succOrder.symm
#align discrete_topology_iff_order_topology_of_pred_succ' discreteTopology_iff_orderTopology_of_pred_succ'

instance (priority := 100) DiscreteTopology.orderTopology_of_pred_succ' [h : DiscreteTopology α]
    [PartialOrder α] [PredOrder α] [SuccOrder α] [NoMinOrder α] [NoMaxOrder α] : OrderTopology α :=
  discreteTopology_iff_orderTopology_of_pred_succ'.1 h
#align discrete_topology.order_topology_of_pred_succ' DiscreteTopology.orderTopology_of_pred_succ'

theorem LinearOrder.bot_topologicalSpace_eq_generateFrom [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a } := by
  refine (eq_bot_of_singletons_open fun a => ?_).symm
  have h_singleton_eq_inter : {a} = Iic a ∩ Ici a := by rw [inter_comm, Ici_inter_Iic, Icc_self a]
  by_cases ha_top : IsTop a
  · rw [ha_top.Iic_eq, inter_comm, inter_univ] at h_singleton_eq_inter
    by_cases ha_bot : IsBot a
    · rw [ha_bot.Ici_eq] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      -- Porting note: Specified instance for `isOpen_univ` explicitly to fix an error.
      apply @isOpen_univ _ (generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a })
    · rw [isBot_iff_isMin] at ha_bot
      rw [← Ioi_pred_of_not_isMin ha_bot] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      exact isOpen_generateFrom_of_mem ⟨pred a, Or.inl rfl⟩
  · rw [isTop_iff_isMax] at ha_top
    rw [← Iio_succ_of_not_isMax ha_top] at h_singleton_eq_inter
    by_cases ha_bot : IsBot a
    · rw [ha_bot.Ici_eq, inter_univ] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      exact isOpen_generateFrom_of_mem ⟨succ a, Or.inr rfl⟩
    · rw [isBot_iff_isMin] at ha_bot
      rw [← Ioi_pred_of_not_isMin ha_bot] at h_singleton_eq_inter
      rw [h_singleton_eq_inter]
      -- Porting note: Specified instance for `IsOpen.inter` explicitly to fix an error.
      letI := Preorder.topology α
      apply IsOpen.inter
      · exact isOpen_generateFrom_of_mem ⟨succ a, Or.inr rfl⟩
      · exact isOpen_generateFrom_of_mem ⟨pred a, Or.inl rfl⟩
#align linear_order.bot_topological_space_eq_generate_from LinearOrder.bot_topologicalSpace_eq_generateFrom

theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h => ⟨?_⟩, fun h => ⟨?_⟩⟩
  · rw [h.eq_bot]
    exact LinearOrder.bot_topologicalSpace_eq_generateFrom
  · rw [h.topology_eq_generate_intervals]
    exact LinearOrder.bot_topologicalSpace_eq_generateFrom.symm
#align discrete_topology_iff_order_topology_of_pred_succ discreteTopology_iff_orderTopology_of_pred_succ

instance (priority := 100) DiscreteTopology.orderTopology_of_pred_succ [h : DiscreteTopology α]
    [LinearOrder α] [PredOrder α] [SuccOrder α] : OrderTopology α :=
  discreteTopology_iff_orderTopology_of_pred_succ.mp h
#align discrete_topology.order_topology_of_pred_succ DiscreteTopology.orderTopology_of_pred_succ

instance (priority := 100) DiscreteTopology.metrizableSpace [DiscreteTopology α] :
    MetrizableSpace α := by
  obtain rfl := DiscreteTopology.eq_bot (α := α)
  exact @UniformSpace.metrizableSpace α ⊥ (isCountablyGenerated_principal _) _
#align discrete_topology.metrizable_space DiscreteTopology.metrizableSpace
