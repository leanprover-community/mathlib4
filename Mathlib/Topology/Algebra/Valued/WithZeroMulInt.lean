/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued K ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal` and use topological results on `NNReal`.
-/

open Multiplicative WithZero

open scoped Multiplicative Topology

namespace Valued.WithZeroMulInt

open Filter in
/-- In a `ℤₘ₀`-valued ring, powers of `x` tend to zero if `v x ≤ -1`. -/
theorem tendsto_zero_pow_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤₘ₀]
    {x : K} (hx : Valued.v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff, Set.mem_setOf_eq, map_pow,
    eventually_atTop]
  have h_lt : ofAdd (-1 : ℤ) < (1 : ℤₘ₀) := by
    rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; linarith
  intro γ _
  by_cases hγ : γ.val ≤ 1
  · let m := - toAdd (unitsWithZeroEquiv γ) + 1 |>.toNat
    refine ⟨m, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    replace hγ : 0 ≤ -toAdd (unitsWithZeroEquiv γ) + 1 := by
      rw [← coe_unitsWithZeroEquiv_eq_units_val, ← coe_one, coe_le_coe, ← toAdd_le, toAdd_one] at hγ
      linarith
    apply lt_of_le_of_lt <| pow_le_pow_left₀ zero_le' hx m
    rw [← coe_unitsWithZeroEquiv_eq_units_val, ← coe_pow, coe_lt_coe, ← ofAdd_nsmul,
      nsmul_eq_mul, Int.toNat_of_nonneg hγ]
    simp
    rw [← ofAdd_zero, ofAdd_lt]
    exact zero_lt_one
  · refine ⟨1, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    apply lt_trans _ (lt_of_not_le hγ)
    apply lt_of_le_of_lt (pow_one (Valued.v x) ▸ hx)
    exact h_lt

variable (K : Type*) [Field K] [Valued K ℤₘ₀]

theorem hasBasis_uniformity_le_one [IsDiscreteValuationRing 𝒪[K]] :
    (uniformity K).HasBasis
      (fun (γ : ℤₘ₀ˣ) => γ ≤ 1) (fun (γ : ℤₘ₀ˣ) => { p | Valued.v (p.2 - p.1) < γ }) := by
  have hq (γ : ℤₘ₀ˣ) (_ : True) :
    ∃ (γ' : ℤₘ₀ˣ), True ∧ γ' ≤ 1 ∧
      { p : K × _ | Valued.v (p.2 - p.1) < γ' } ⊆
        { p | Valued.v (p.2 - p.1) < γ } := by
    choose ϖ _ using IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    by_cases hγ : 1 < γ
    · exact ⟨1, trivial, le_refl _, fun _ hx => lt_trans (Set.mem_setOf.1 hx) hγ⟩
    · exact ⟨γ, trivial, not_lt.1 hγ, subset_rfl⟩
  convert (Valued.hasBasis_uniformity _ _).restrict hq
  simp only [true_and]

variable {K}

theorem valuation_le_pow_of_maximalIdeal [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} (n : ℕ) (hx : x ∈ 𝓂[K] ^ n) :
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
  let m := (- toAdd (unitsWithZeroEquiv γ) + 1).toNat
  letI := integer.finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := h.elems.image Quotient.out
  refine ⟨Subtype.val '' T.toSet, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem _ (h.complete _),
    lt_of_le_of_lt (valuation_le_pow_of_maximalIdeal _ (Ideal.Quotient.out_sub _ _)) ?_⟩
  simp only [m, ← coe_unitsWithZeroEquiv_eq_units_val, coe_lt_coe]
  rw [← ofAdd_toAdd (unitsWithZeroEquiv γ), ofAdd_lt, ofAdd_toAdd, Int.toNat_of_nonneg]
  · linarith
  · simp only [le_neg_add_iff_add_le, add_zero]
    exact le_trans (units_toAdd_le_of_le one_ne_zero hγ) zero_le_one

variable (K)

open Set Valued in
theorem integers_isClosed : IsClosed (𝒪[K] : Set K) := by
  refine isClosed_iff_nhds.2 fun x hx => ?_
  simp only [isClosed_iff_nhds, SetLike.mem_coe, Valuation.mem_integer_iff, not_le] at hx ⊢
  contrapose! hx
  refine ⟨{y | Valued.v y = Valued.v x}, loc_const (ne_zero_of_lt hx),
    subset_empty_iff.1 fun y ⟨hy₁, hy₂⟩ => ?_⟩
  exact (not_lt_of_le <| hy₂) <| hy₁.symm ▸ hx

theorem integers_compactSpace {K : Type*} [Field K] [Valued K ℤₘ₀] [CompleteSpace K]
    [IsDiscreteValuationRing 𝒪[K]] (h : Finite 𝓀[K]) : CompactSpace 𝒪[K] := by
  refine CompactSpace.mk (isCompact_iff_isCompact_univ.1 <| ?_)
  exact isCompact_iff_totallyBounded_isComplete.2
    ⟨(hasBasis_uniformity_le_one K).totallyBounded_iff.2 <| fun _ hγ =>
      finite_subcover_of_uniformity_basis h hγ, (integers_isClosed K).isComplete⟩

end Valued.WithZeroMulInt
