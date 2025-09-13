/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued R ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Filter WithZero Set
open scoped Topology

namespace Valued
variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

-- TODO: use ValuativeRel after https://github.com/leanprover-community/mathlib4/issues/26833
lemma tendsto_zero_pow_of_v_lt_one [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx y
  refine ⟨n, fun m hm ↦ ?_⟩
  refine hn.trans_le' ?_
  exact pow_le_pow_right_of_le_one' hx.le hm

/-- In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ exp (-1)`. -/
lemma tendsto_zero_pow_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero, exp_lt_exp]
  norm_num

lemma exists_pow_lt_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) (γ : ℤᵐ⁰ˣ) :
    ∃ n, v x ^ n < γ := by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero, exp_lt_exp]
  norm_num

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 :=
  lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) <|
    mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit

theorem irreducible_valuation_le_exp_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ exp (-1 : ℤ) := by
  have hϖ : v ϖ.1 ≠ 0 := by simp [h.ne_zero]
  have := log_one (M := ℤ) ▸  (log_lt_log hϖ one_ne_zero).2 (irreducible_valuation_lt_one h)
  rw [← log_le_iff_le_exp hϖ]
  linarith

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  rcases eq_or_ne x 0 with (rfl | hx₀) <;> try simp
  simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  simpa using le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

/-- The ring of integers `𝒪[K]` of a `ℤₘ₀`-valued field `K` with finite residue
field has a finite covering by elements of the basis of uniformity of `K`, whenever
`𝒪[K]` is a discrete valuation ring. -/
theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] {γ : ℤᵐ⁰ˣ}
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_exp_neg_one (irreducible_valuation_le_exp_neg_one hϖ) γ
  have := integer.finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out).toSet
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx ↦ ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  exact ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem _ (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

/-- The ring of integers `𝒪[K]` of a complete `ℤₘ₀`-valued field `K` with finite residue
field is compact, whenever `𝒪[K]` is a discrete valuation ring. -/
theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]] (h : Finite 𝓀[K]) :
    CompactSpace 𝒪[K] where
   isCompact_univ := isCompact_iff_isCompact_univ.1 <| isCompact_iff_totallyBounded_isComplete.2
      ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 fun _ _ ↦ finite_cover_of_uniformity_basis h,
        (isClosed_integer K).isComplete⟩

end Valued
