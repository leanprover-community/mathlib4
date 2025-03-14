/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact nonarchimedean normed field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

open NNReal

open scoped NormedField

@[simp]
lemma NormedField.v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x := rfl

namespace Valued.integer

-- should we do this all in the Valuation namespace instead?

/-- An element is in the valuation ring if the norm is bounded by 1. This is a variant of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation. -/
lemma mem_iff {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, ← NNReal.coe_le_coe]

lemma norm_le_one (x : 𝒪[K]) : ‖x‖ ≤ 1 := mem_iff.mp x.prop

@[simp]
lemma norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).valuation_unit u

lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  simp

lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).isUnit_iff_valuation_eq_one

lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  lt_of_le_of_ne (norm_le_one ϖ) (mt isUnit_iff_norm_eq_one.mpr h.not_isUnit)

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  lt_of_le_of_ne (_root_.norm_nonneg ϖ) (by simp [eq_comm, h.ne_zero])

lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  rcases eq_or_ne x 0 with rfl|hx
  · simp [Set.singleton_zero, Ideal.span_zero]
  ext y
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton', AddSubgroupClass.coe_norm,
    Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨z, rfl⟩
    simpa using mul_le_mul_of_nonneg_right (norm_le_one z) (_root_.norm_nonneg x)
  · intro h
    refine ⟨⟨y / x, ?_⟩, ?_⟩
    · simpa [mem_iff] using div_le_one_of_le₀ h (_root_.norm_nonneg _)
    · simpa only [Subtype.ext_iff] using div_mul_cancel₀ (y : K) (by simpa using hx)

lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  rw [← coe_span_singleton_eq_closedBall, ← h.maximalIdeal_eq]

lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  have : ‖ϖ‖ ^ n = ‖ϖ ^ n‖ := by simp
  rw [this, ← coe_span_singleton_eq_closedBall, ← Ideal.span_singleton_pow, ← h.maximalIdeal_eq]

section FiniteResidueField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

open Valued

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_finite_quot_finite_ideal
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

lemma totallyBounded_iff_finite_residueField [IsDiscreteValuationRing 𝒪[K]] :
    TotallyBounded (Set.univ (α := 𝒪[K])) ↔ Finite 𝓀[K] := by
  constructor
  · intro H
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have := Metric.finite_approx_of_totallyBounded H ‖p‖ (norm_pos_iff.mpr hp.ne_zero)
    simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at this
    obtain ⟨t, ht, ht'⟩ := this
    rw [← Set.finite_univ_iff]
    refine (ht.image (IsLocalRing.residue _)).subset ?_
    rintro ⟨x⟩
    replace ht' := ht'.ge (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ht'
    obtain ⟨y, hy, hy'⟩ := ht'
    simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Set.mem_univ,
      IsLocalRing.residue, Set.mem_image, true_implies]
    refine ⟨y, hy, ?_⟩
    convert (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := 𝓂[K]) y x).mpr _
    -- TODO: make Valued.maximalIdeal abbreviations instead of def
    rw [Valued.maximalIdeal, hp.maximalIdeal_eq, ← SetLike.mem_coe,
      coe_span_singleton_eq_closedBall]
    rw [dist_comm] at hy'
    simpa [dist_eq_norm] using hy'.le
  · intro H
    rw [Metric.totallyBounded_iff]
    intro ε εpos
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := norm_irreducible_lt_one hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖p‖ ^ n < ε := exists_pow_lt_of_lt_one εpos hp'
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H n
    refine ⟨Quotient.out '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ n))), Set.toFinite _, ?_⟩
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ n), hp.maximalIdeal_pow_eq_closedBall_pow,
      AddSubgroupClass.coe_norm, Set.image_add_left, preimage_add_closedBall, sub_neg_eq_add,
      zero_add, Set.image_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.iUnion_subset_iff, Metric.vadd_closedBall, vadd_eq_add, add_zero]
    intro
    exact (Metric.closedBall_subset_ball hn).trans (Set.subset_iUnion_of_subset _ le_rfl)

end FiniteResidueField

end Valued.integer
