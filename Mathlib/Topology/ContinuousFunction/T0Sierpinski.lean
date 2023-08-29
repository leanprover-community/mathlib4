/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.continuous_function.t0_sierpinski from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `productOfMemOpens` from `X` to `Opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `productOfMemOpens` is always inducing. Whenever `X` is T0, `productOfMemOpens` is
also injective and therefore an embedding.
-/


noncomputable section

namespace TopologicalSpace

theorem eq_induced_by_maps_to_sierpinski (X : Type*) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· ∈ u) := by
  apply le_antisymm
  -- ⊢ t ≤ ⨅ (u : Opens X), induced (fun x => x ∈ u) sierpinskiSpace
  · rw [le_iInf_iff]
    -- ⊢ ∀ (i : Opens X), t ≤ induced (fun x => x ∈ i) sierpinskiSpace
    exact fun u => Continuous.le_induced (isOpen_iff_continuous_mem.mp u.2)
    -- 🎉 no goals
  · intro u h
    -- ⊢ IsOpen u
    rw [← generateFrom_iUnion_isOpen]
    -- ⊢ IsOpen u
    apply isOpen_generateFrom_of_mem
    -- ⊢ u ∈ ⋃ (i : Opens X), {s | IsOpen s}
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, isOpen_induced_iff]
    -- ⊢ ∃ i t_1, IsOpen t_1 ∧ (fun x => x ∈ i) ⁻¹' t_1 = u
    exact ⟨⟨u, h⟩, {True}, isOpen_singleton_true, by simp [Set.preimage]⟩
    -- 🎉 no goals
#align topological_space.eq_induced_by_maps_to_sierpinski TopologicalSpace.eq_induced_by_maps_to_sierpinski

variable (X : Type*) [TopologicalSpace X]

/-- The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
open subset `u` of `X`). The `u` coordinate of `productOfMemOpens x` is given by `x ∈ u`.
-/
def productOfMemOpens : C(X, Opens X → Prop) where
  toFun x u := x ∈ u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.isOpen
#align topological_space.product_of_mem_opens TopologicalSpace.productOfMemOpens

theorem productOfMemOpens_inducing : Inducing (productOfMemOpens X) := by
  convert inducing_iInf_to_pi fun (u : Opens X) (x : X) => x ∈ u
  -- ⊢ inst✝ = ⨅ (i : Opens X), induced (fun x => x ∈ i) inferInstance
  apply eq_induced_by_maps_to_sierpinski
  -- 🎉 no goals
#align topological_space.product_of_mem_opens_inducing TopologicalSpace.productOfMemOpens_inducing

theorem productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMemOpens X) := by
  intro x1 x2 h
  -- ⊢ x1 = x2
  apply Inseparable.eq
  -- ⊢ Inseparable x1 x2
  rw [← Inducing.inseparable_iff (productOfMemOpens_inducing X), h]
  -- 🎉 no goals
#align topological_space.product_of_mem_opens_injective TopologicalSpace.productOfMemOpens_injective

theorem productOfMemOpens_embedding [T0Space X] : Embedding (productOfMemOpens X) :=
  Embedding.mk (productOfMemOpens_inducing X) (productOfMemOpens_injective X)
#align topological_space.product_of_mem_opens_embedding TopologicalSpace.productOfMemOpens_embedding

end TopologicalSpace
