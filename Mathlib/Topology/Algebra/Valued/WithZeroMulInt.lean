/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Quotient.Basic

open Multiplicative WithZero

namespace Valued.WithZeroMulInt

variable {K : Type*} [Field K] [Valued K ℤₘ₀]

theorem valuation_le_pow_of_maximalIdeal [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} (n : ℕ)
    (hx : x ∈ 𝓂[K] ^ n) :
    Valued.v x.val ≤ Multiplicative.ofAdd (-n : ℤ) := by
  sorry

theorem units_toAdd_le_of_le {α : Type*} [AddGroup α] [Preorder α]
    {γ : (WithZero (Multiplicative α))ˣ} {m : (WithZero (Multiplicative α))} (hm : m ≠ 0)
    (hγ : γ.val ≤ m) :
    toAdd (unitsWithZeroEquiv γ) ≤ toAdd (m.unzero hm) := by
  rw [← ofAdd_le, ofAdd_toAdd, ← coe_le_coe, unitsWithZeroEquiv, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_unzero]
  apply le_trans hγ
  rw [ofAdd_toAdd, coe_unzero]

open scoped Classical in
/-- There is a finite covering of the `v`-adic integers of open balls of radius less than one,
obtained by using the finite representatives in the quotient of the `v`-adic integers by an
appropriate power of the maximal ideal. -/
theorem finite_subcover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] {γ : ℤₘ₀ˣ}
    (h : Finite 𝓀[K]) (hγ : γ.val ≤ 1) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t,
        { x | (x, y) ∈ { p | Valued.v (p.2 - p.1) < γ.val } } := by
  let M := (Valued.maximalIdeal K) ^ (- toAdd (unitsWithZeroEquiv γ) + 1).toNat
  letI := integer.finite_quotient_maximalIdeal_pow_of_finite_residueField h
    (-toAdd (unitsWithZeroEquiv γ) + 1).toNat
  have h : Fintype (𝒪[K] ⧸ M) := Fintype.ofFinite _
  let T := h.elems.image Quotient.out
  refine ⟨Subtype.val '' T.toSet, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := Quotient.out <| Ideal.Quotient.mk M ⟨x, hx⟩
  have h_mem : (Ideal.Quotient.mk M ⟨x, hx⟩).out ∈ T := Finset.mem_image_of_mem _ (h.complete _)
  refine ⟨y, Set.mem_image_of_mem _ h_mem,
    lt_of_le_of_lt (valuation_le_pow_of_maximalIdeal _ (Ideal.Quotient.out_sub M _)) ?_⟩
  rw [← coe_unitsWithZeroEquiv_eq_units_val, coe_lt_coe, ← ofAdd_toAdd (unitsWithZeroEquiv γ),
    ofAdd_lt, ofAdd_toAdd, Int.toNat_of_nonneg]
  · linarith
  · simp
    apply le_trans (units_toAdd_le_of_le one_ne_zero hγ)
    simp
    convert zero_le_one
    infer_instance

end Valued.WithZeroMulInt
