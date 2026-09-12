/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
# Ordered topological groups

Behavior of one-sided neighborhood filters under multiplication, inversion, and division in
ordered topological groups.
-/

public section

open Filter Topology Pointwise

variable {H : Type*}

section OrderedCommGroup

variable [TopologicalSpace H] [CommGroup H] [PartialOrder H] [IsOrderedMonoid H]

section mul

variable [ContinuousMul H]

@[to_additive (attr := simp)]
theorem Filter.map_mul_left_nhdsGT {c a : H} : map (c * ·) (𝓝[>] a) = 𝓝[>] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
theorem Filter.map_mul_left_nhdsLT {c a : H} : map (c * ·) (𝓝[<] a) = 𝓝[<] (c * a) := by
  convert! (Homeomorph.mulLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [mul_comm]

@[to_additive (attr := simp)]
theorem Filter.map_mul_right_nhdsGT {c a : H} : map (· * c) (𝓝[>] a) = 𝓝[>] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.map_mul_right_nhdsLT {c a : H} : map (· * c) (𝓝[<] a) = 𝓝[<] (a * c) := by
  convert! (Homeomorph.mulRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end mul

section inv

variable [ContinuousInv H]

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsGT {a : H} : (𝓝[>] a)⁻¹ = 𝓝[<] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.inv_nhdsLT {a : H} : (𝓝[<] a)⁻¹ = 𝓝[>] (a⁻¹) := by
  convert! (Homeomorph.inv H).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive]
theorem tendsto_inv_nhdsGT {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsLT {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsGT_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGT (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsLT_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLT (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsGE {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsLE {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.tendsto a).inf <| by simp

@[to_additive]
theorem tendsto_inv_nhdsGE_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsGE (a := a⁻¹)

@[to_additive]
theorem tendsto_inv_nhdsLE_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using tendsto_inv_nhdsLE (a := a⁻¹)

alias tendsto_inv_nhdsWithin_Iic_inv := tendsto_inv_nhdsLE_inv

end inv

end OrderedCommGroup

section OrderedDiv

variable [TopologicalSpace H] [CommGroup H] [IsTopologicalGroup H]
  [PartialOrder H] [IsOrderedMonoid H]

@[to_additive (attr := simp)]
theorem Filter.map_divRight_nhdsGT {c a : H} : map (· / c) (𝓝[>] a) = 𝓝[>] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.map_divRight_nhdsLT {c a : H} : map (· / c) (𝓝[<] a) = 𝓝[<] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.map_divLeft_nhdsGT {c a : H} : map (c / ·) (𝓝[>] a) = 𝓝[<] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

@[to_additive (attr := simp)]
theorem Filter.map_divLeft_nhdsLT {c a : H} : map (c / ·) (𝓝[<] a) = 𝓝[>] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp

end OrderedDiv
