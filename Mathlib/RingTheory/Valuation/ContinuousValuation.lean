/-
Copyright (c) 2026 sfingali. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: sfingali
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Continuous valuations

A valuation `v : A → Γ₀` on a topological ring `A` is *continuous* if the map
`v : A → Γ₀` is continuous, where `Γ₀` carries the order topology. Equivalently
(Wedhorn, Def. 7.7, p. 58), the sets `{a : A | v a < γ}` are open in `A` for all
`γ ∈ Γ₀` — i.e. the topology of `A` is finer than the topology defined by `v`.

## Main definitions
* `ContinuousValuationClass` — the class of continuous valuations: a
  `ValuationClass` whose functions are continuous.
* `ContinuousValuation` — a bundled continuous valuation on `A` with values in
  `Γ₀`.

## Main results
* `ContinuousValuation.isOpen_lt` — the primary form of Wedhorn, Def. 7.7,
  p. 58: `{a | v a < γ}` is open for every `γ`.

## References
* [wedhorn_adic] T. Wedhorn, *Adic Spaces*, arXiv:1910.05934, Def. 7.7, Rem. 7.8
  (p. 58). The subspace `Cont(A) ⊆ Spv(A)` of continuous valuations (Wedhorn,
  p. 58) will build on `ValuationSpectrum` when that PR lands; this file
  provides the element-level notion.
-/

@[expose] public section

variable {A Γ₀ : Type*} [Ring A] [TopologicalSpace A]
  [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace Γ₀] [OrderTopology Γ₀]

/-- A continuous valuation on a topological ring `A` with values in `Γ₀`: a
valuation whose underlying function is continuous for the order topology on
`Γ₀`. Equivalent to the primary definition of Wedhorn, Def. 7.7, p. 58 via
Wedhorn, Rem. 7.8(1) (see `isOpen_lt`). -/
class ContinuousValuationClass (F : Type*) (A Γ₀ : outParam Type*)
    [Ring A] [TopologicalSpace A] [LinearOrderedCommGroupWithZero Γ₀]
    [TopologicalSpace Γ₀] [OrderTopology Γ₀] [FunLike F A Γ₀] : Prop
    extends ValuationClass F A Γ₀, ContinuousMapClass F A Γ₀ where

universe u v

/-- A bundled continuous valuation on `A` with values in `Γ₀`. -/
structure ContinuousValuation (A : Type u) [Ring A] [TopologicalSpace A]
    (Γ₀ : Type v) [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace Γ₀]
    [OrderTopology Γ₀] : Type (max u v) extends Valuation A Γ₀ where
  /-- The valuation is continuous. -/
  continuous_toValuation : Continuous toValuation

namespace ContinuousValuation

variable {F : Type*}

instance : FunLike (ContinuousValuation A Γ₀) A Γ₀ where
  coe v := v.toFun
  coe_injective := by
    intro v w h
    cases v
    cases w
    congr
    exact DFunLike.coe_injective h

instance : ValuationClass (ContinuousValuation A Γ₀) A Γ₀ where
  map_mul v := v.map_mul'
  map_one v := v.map_one'
  map_zero v := v.map_zero'
  map_add_le_max v := v.map_add_le_max'

instance : ContinuousValuationClass (ContinuousValuation A Γ₀) A Γ₀ where
  map_continuous v := v.continuous_toValuation

@[simp]
lemma coe_toValuation {A Γ₀ : Type*} [Ring A] [TopologicalSpace A]
    [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace Γ₀] [OrderTopology Γ₀]
    (v : ContinuousValuation A Γ₀) : v.toValuation = v := rfl

/-- The primary definition of Wedhorn, Def. 7.7, p. 58: for a continuous
valuation `v` on `A`, the set `{a : A | v a < γ}` is open for every `γ`. -/
theorem isOpen_lt (v : ContinuousValuation A Γ₀) (γ : Γ₀) :
    IsOpen {a : A | v a < γ} := by
  -- {a | v a < γ} = v⁻¹ (Iio γ), and Iio γ is open in the order topology on Γ₀
  have hpre : IsOpen (v.toFun ⁻¹' (Set.Iio γ)) :=
    (map_continuous v).isOpen_preimage (Set.Iio γ) isOpen_Iio
  convert hpre using 1
  ext a
  simp

end ContinuousValuation
