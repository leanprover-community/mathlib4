/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.algebra.constructions
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `TopologicalSpace` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `HasContinuousMul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/


variable {M X : Type _}

open Filter Topology

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive "Put the same topological space structure on the opposite monoid as on the original
space."]
instance [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

@[to_additive] -- porting note: todo: restore `continuity`
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom
#align mul_opposite.continuous_unop MulOpposite.continuous_unop
#align add_opposite.continuous_unop AddOpposite.continuous_unop

@[to_additive] -- porting note: todo: restore `continuity`
theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) :=
  continuous_induced_rng.2 continuous_id
#align mul_opposite.continuous_op MulOpposite.continuous_op
#align add_opposite.continuous_op AddOpposite.continuous_op

/-- `MulOpposite.op` as a homeomorphism. -/
@[to_additive (attr := simps!) "`AddOpposite.op` as a homeomorphism."]
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv
  continuous_toFun := continuous_op
  continuous_invFun := continuous_unop
#align mul_opposite.op_homeomorph MulOpposite.opHomeomorph
#align add_opposite.op_homeomorph AddOpposite.opHomeomorph

@[to_additive]
instance [T2Space M] : T2Space Mᵐᵒᵖ :=
  opHomeomorph.symm.embedding.t2Space

@[to_additive (attr := simp)]
theorem map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x
#align mul_opposite.map_op_nhds MulOpposite.map_op_nhds
#align add_opposite.map_op_nhds AddOpposite.map_op_nhds

@[to_additive (attr := simp)]
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x
#align mul_opposite.map_unop_nhds MulOpposite.map_unop_nhds
#align add_opposite.map_unop_nhds AddOpposite.map_unop_nhds

@[to_additive (attr := simp)]
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x
#align mul_opposite.comap_op_nhds MulOpposite.comap_op_nhds
#align add_opposite.comap_op_nhds AddOpposite.comap_op_nhds

@[to_additive (attr := simp)]
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x
#align mul_opposite.comap_unop_nhds MulOpposite.comap_unop_nhds
#align add_opposite.comap_unop_nhds AddOpposite.comap_unop_nhds

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoid M] [TopologicalSpace X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive "The additive units of a monoid are equipped with a topology, via the embedding into
`M × M`."]
instance : TopologicalSpace Mˣ :=
  TopologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]
theorem inducing_embedProduct : Inducing (embedProduct M) :=
  ⟨rfl⟩
#align units.inducing_embed_product Units.inducing_embedProduct
#align add_units.inducing_embed_product AddUnits.inducing_embedProduct

@[to_additive]
theorem embedding_embedProduct : Embedding (embedProduct M) :=
  ⟨inducing_embedProduct, embedProduct_injective M⟩
#align units.embedding_embed_product Units.embedding_embedProduct
#align add_units.embedding_embed_product AddUnits.embedding_embedProduct

@[to_additive]
theorem continuous_embedProduct : Continuous (embedProduct M) :=
  continuous_induced_dom
#align units.continuous_embed_product Units.continuous_embedProduct
#align add_units.continuous_embed_product AddUnits.continuous_embedProduct

@[to_additive]
theorem continuous_val : Continuous ((↑) : Mˣ → M) :=
  (@continuous_embedProduct M _ _).fst
#align units.continuous_coe Units.continuous_val
#align add_units.continuous_coe AddUnits.continuous_val

@[to_additive]
protected theorem continuous_iff {f : X → Mˣ} :
    Continuous f ↔ Continuous (val ∘ f) ∧ Continuous (fun x => ↑(f x)⁻¹ : X → M) := by
  simp only [inducing_embedProduct.continuous_iff, embedProduct_apply, (· ∘ ·),
    continuous_prod_mk, opHomeomorph.symm.inducing.continuous_iff, opHomeomorph_symm_apply,
    unop_op]
#align units.continuous_iff Units.continuous_iff
#align add_units.continuous_iff AddUnits.continuous_iff

@[to_additive]
theorem continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ → M) :=
  (Units.continuous_iff.1 continuous_id).2
#align units.continuous_coe_inv Units.continuous_coe_inv
#align add_units.continuous_coe_neg AddUnits.continuous_coe_neg

end Units
