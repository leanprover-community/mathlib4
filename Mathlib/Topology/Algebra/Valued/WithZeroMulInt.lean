/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Order.Group.TypeTags
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued K ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Multiplicative WithZero

open scoped Multiplicative Topology

namespace Valued.WithZeroMulInt

open Set Filter in
/-- In a `ℤₘ₀`-valued ring, powers of `x` tend to zero if `v x ≤ ofAdd (-1 : ℤ)`. -/
theorem tendsto_zero_pow_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤₘ₀]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop]
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
    apply lt_of_le_of_lt (pow_one (v x) ▸ hx)
    exact h_lt

open Filter in
theorem exists_pow_lt_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤₘ₀]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) (γ : ℤₘ₀ˣ) :
    ∃ n, v x ^ n < γ := by
  simp_rw [← map_pow]
  let ⟨n, hn⟩ := eventually_atTop.1 <|
     ((hasBasis_nhds_zero _ _).tendsto_right_iff ).1 (tendsto_zero_pow_of_le_neg_one hx) γ trivial
  use n
  convert Set.mem_setOf_eq ▸ hn n le_rfl

variable {K : Type*} [Field K] [Valued K ℤₘ₀]

theorem irreducible_valuation_lt_one [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (h : Irreducible ϖ) :
    v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_unit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

theorem irreducible_valuation_le_ofAdd_neg_one [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp [hy]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

theorem units_toAdd_le_of_le {α : Type*} [AddGroup α] [Preorder α]
    {γ : (WithZero (Multiplicative α))ˣ} {m : (WithZero (Multiplicative α))} (hm : m ≠ 0)
    (hγ : γ.val ≤ m) :
    toAdd (unitsWithZeroEquiv γ) ≤ toAdd (m.unzero hm) := by
  rw [← ofAdd_le, ofAdd_toAdd, ← coe_le_coe, unitsWithZeroEquiv, MulEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_unzero]
  apply le_trans hγ
  rw [ofAdd_toAdd, coe_unzero]

/-- The ring of integers `𝒪[K]` of a `ℤₘ₀`-valued field `K` with finite residue
field has a finite covering by elements of the basis of uniformity of `K`, whenever
`𝒪[K]` is a discrete valuation ring. -/
theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] {γ : ℤₘ₀ˣ}
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := integer.finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out).toSet
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem _ (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

/-- The ring of integers `𝒪[K]` of a complete `ℤₘ₀`-valued field `K` with finite residue
field is compact, whenever `𝒪[K]` is a discrete valuation ring. -/
theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]] (h : Finite 𝓀[K]) :
    CompactSpace 𝒪[K] := by
  refine CompactSpace.mk (isCompact_iff_isCompact_univ.1 <| ?_)
  exact isCompact_iff_totallyBounded_isComplete.2
    ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 <| fun _ hγ =>
      finite_cover_of_uniformity_basis h, (integer_isClosed K).isComplete⟩

end Valued.WithZeroMulInt
