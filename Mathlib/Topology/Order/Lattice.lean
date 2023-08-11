/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Constructions

#align_import topology.order.lattice from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Topological lattices

In this file we define mixin classes `ContinuousInf` and `ContinuousSup`. We define the
class `TopologicalLattice` as a topological space and lattice `L` extending `ContinuousInf` and
`ContinuousSup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/


open Filter

open Topology

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimum* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousInf (L : Type*) [TopologicalSpace L] [Inf L] : Prop where
  /-- The infimum is continuous -/
  continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2
#align has_continuous_inf ContinuousInf

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous supremum* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousSup (L : Type*) [TopologicalSpace L] [Sup L] : Prop where
  /-- The supremum is continuous -/
  continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2
#align has_continuous_sup ContinuousSup

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.continuousSup (L : Type*) [TopologicalSpace L] [Inf L]
    [ContinuousInf L] : ContinuousSup Lᵒᵈ
    where continuous_sup := @ContinuousInf.continuous_inf L _ _ _
#align order_dual.has_continuous_sup OrderDual.continuousSup

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.continuousInf (L : Type*) [TopologicalSpace L] [Sup L]
    [ContinuousSup L] : ContinuousInf Lᵒᵈ
    where continuous_inf := @ContinuousSup.continuous_sup L _ _ _
#align order_dual.has_continuous_inf OrderDual.continuousInf

/-- Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
class TopologicalLattice (L : Type*) [TopologicalSpace L] [Lattice L]
  extends ContinuousInf L, ContinuousSup L : Prop
#align topological_lattice TopologicalLattice

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.topologicalLattice (L : Type*) [TopologicalSpace L]
    [Lattice L] [TopologicalLattice L] : TopologicalLattice Lᵒᵈ where
#align order_dual.topological_lattice OrderDual.topologicalLattice

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.topologicalLattice {L : Type*} [TopologicalSpace L]
    [LinearOrder L] [OrderClosedTopology L] : TopologicalLattice L
    where
  continuous_inf := continuous_min
  continuous_sup := continuous_max
#align linear_order.topological_lattice LinearOrder.topologicalLattice

variable [TopologicalSpace L] [TopologicalSpace X]

@[continuity]
theorem continuous_inf [Inf L] [ContinuousInf L] : Continuous fun p : L × L => p.1 ⊓ p.2 :=
  ContinuousInf.continuous_inf
#align continuous_inf continuous_inf

@[continuity]
theorem Continuous.inf [Inf L] [ContinuousInf L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊓ g x :=
  continuous_inf.comp (hf.prod_mk hg : _)
#align continuous.inf Continuous.inf

@[continuity]
theorem continuous_sup [Sup L] [ContinuousSup L] : Continuous fun p : L × L => p.1 ⊔ p.2 :=
  ContinuousSup.continuous_sup
#align continuous_sup continuous_sup

@[continuity]
theorem Continuous.sup [Sup L] [ContinuousSup L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊔ g x :=
  continuous_sup.comp (hf.prod_mk hg : _)
#align continuous.sup Continuous.sup

theorem Filter.Tendsto.sup_right_nhds' {ι β} [TopologicalSpace β] [Sup β] [ContinuousSup β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
  (continuous_sup.tendsto _).comp (Tendsto.prod_mk_nhds hf hg)
#align filter.tendsto.sup_right_nhds' Filter.Tendsto.sup_right_nhds'

theorem Filter.Tendsto.sup_right_nhds {ι β} [TopologicalSpace β] [Sup β] [ContinuousSup β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y)) :=
  hf.sup_right_nhds' hg
#align filter.tendsto.sup_right_nhds Filter.Tendsto.sup_right_nhds

theorem Filter.Tendsto.inf_right_nhds' {ι β} [TopologicalSpace β] [Inf β] [ContinuousInf β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
  (continuous_inf.tendsto _).comp (Tendsto.prod_mk_nhds hf hg)
#align filter.tendsto.inf_right_nhds' Filter.Tendsto.inf_right_nhds'

theorem Filter.Tendsto.inf_right_nhds {ι β} [TopologicalSpace β] [Inf β] [ContinuousInf β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y)) :=
  hf.inf_right_nhds' hg
#align filter.tendsto.inf_right_nhds Filter.Tendsto.inf_right_nhds
