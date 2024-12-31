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
  lt_of_le_of_ne (norm_le_one ϖ) (mt isUnit_iff_norm_eq_one.mpr h.not_unit)

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

section CompactDVR

open Valued

variable (K) in
lemma exists_norm_coe_lt : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
lemma exists_norm_lt : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 := by
  exact exists_norm_coe_lt K

variable (K) in
lemma exists_nnnorm_lt : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 := by
  exact exists_norm_coe_lt K

lemma discreteValuationRing_of_compactSpace [h : CompactSpace 𝒪[K]] :
    DiscreteValuationRing 𝒪[K] := by
  have hl : LocalRing 𝒪[K] := inferInstance
  obtain ⟨x, hx, hx'⟩ := exists_nnnorm_lt K
  rw [← nnnorm_one (K := K)] at hx'
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have key : IsPrincipalIdealRing 𝒪[K]:= by
    rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
    intro H
    replace H : DenselyOrdered (Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) := by
      constructor
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      replace h : (⟨_, a, rfl⟩ : Set.range (v : K → ℝ≥0)) < ⟨_, b, rfl⟩ := h
      obtain ⟨⟨_, c, rfl⟩, hc⟩ := exists_between h
      refine ⟨⟨_, ⟨c, ?_⟩, rfl⟩, hc⟩
      · rw [mem_integer_iff']
        simp only [v_eq_valuation, NormedField.valuation_apply, Subtype.mk_lt_mk, ← coe_lt_coe,
          coe_nnnorm] at hc
        simpa using hc.right.le.trans (mem_integer_iff'.mp b.prop)
    let U : 𝒪[K] → Set 𝒪[K] := fun y ↦ if ‖y‖₊ < ‖x‖₊
      then Metric.closedBall 0 ‖x‖
      else Metric.sphere 0 ‖y‖
    obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U <| by
      intro y
      simp only [AddSubgroupClass.coe_norm, U]
      split_ifs with hy
      · refine (IsUltrametricDist.isOpen_closedBall _ ?_).mem_nhds (by simpa using hy.le)
        simpa using hx
      · refine (IsUltrametricDist.isOpen_sphere _ ?_).mem_nhds (by simp)
        simpa using (hx.trans_le (le_of_not_lt hy)).ne'
    have htm : ∀ y : 𝒪[K], ‖x‖₊ < ‖y‖₊ → ∃ z ∈ t, ‖z‖₊ = ‖y‖₊ := by
      intro y hy
      have := ht.ge (Set.mem_univ y)
      simp only [AddSubgroupClass.coe_norm, Set.mem_iUnion, exists_prop', nonempty_prop, U] at this
      obtain ⟨z, hz, hz'⟩ := this
      split_ifs at hz' with h
      · simp only [← coe_lt_coe, coe_nnnorm, AddSubgroupClass.coe_norm] at hy
        simp [hy.not_le] at hz'
      · simp only [mem_sphere_iff_norm, sub_zero, AddSubgroupClass.coe_norm] at hz'
        refine ⟨z, hz, ?_⟩
        simp [← coe_inj, hz']
    obtain ⟨y, _, hy'⟩ : ∃ y : 𝒪[K], y ∈ t ∧ ‖y‖₊ = 1 := by simpa using htm 1 hx'
    obtain ⟨w, hwt, hw1, hxw⟩ : ∃ w : 𝒪[K], w ∈ t ∧ ‖w‖₊ < 1 ∧ ‖x‖₊ < ‖w‖₊ := by
      replace hx' : (⟨_, x, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < ⟨_, 1, rfl⟩ := hx'
      obtain ⟨⟨_, w, rfl⟩, hw, hw'⟩ := exists_between hx'
      obtain ⟨u, hu, hu'⟩ := htm w hw
      exact ⟨u, hu, hu' ▸ by simpa using hw', hu' ▸ by simpa using hw⟩
    let u := t.filter (fun a ↦ ‖a‖₊ < 1)
    have hwu : w ∈ u := by simp [u, hwt, hw1]
    obtain ⟨l, hl, hl'⟩ := u.sup'_mem (((‖·‖₊) : 𝒪[K] → ℝ≥0) '' u)
      (fun x hx y hy ↦ (max_cases x y).elim
        (fun h ↦ (sup_eq_max (a := x) (b := y) ▸ h).left.symm ▸ hx)
        (fun h ↦ (sup_eq_max (a := x) (b := y) ▸ h).left.symm ▸ hy))
      ⟨w, hwu⟩ (‖·‖₊) (fun _ ↦ Set.mem_image_of_mem _)
    simp only at hl'
    have hm : (⟨‖l‖₊, l, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < (⟨1, y, hy'⟩) := by
      simp only [Finset.coe_filter, Set.mem_setOf_eq, u] at hl
      simp [hl.right]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := exists_between hm
    simp only [Subtype.mk_lt_mk] at hm
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ t, ‖n‖₊ = ‖m‖₊ := by
      refine htm m (hxw.trans (hm.left.trans_le' ?_))
      rw [hl', Finset.le_sup'_iff]
      exact ⟨w, hwu, le_rfl⟩
    rw [← hn'] at hm
    refine hm.left.not_le ?_
    rw [hl', Finset.le_sup'_iff]
    refine ⟨n, ?_, le_rfl⟩
    simp [u, hn, hm.right]
  exact {
    __ := hl
    __ := key
    not_a_field' := by
      simp only [ne_eq, Ideal.ext_iff, LocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_bot,
        not_forall, isUnit_iff_norm_eq_one]
      refine ⟨x, ?_⟩
      simp only [← coe_lt_coe, coe_zero, coe_nnnorm, norm_pos_iff, ne_eq,
        ZeroMemClass.coe_eq_zero, nnnorm_one, coe_one] at hx hx'
      simpa [hx] using hx'.ne
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_discreteValuationRing_and_finite_residueField :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ DiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : DiscreteValuationRing 𝒪[K] := discreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
        totallyBounded_iff_finite_residueField] at h
    exact h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩

lemma properSpace_iff_compactSpace_integer :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             mem_integer_iff', ← mem_closedBall_zero_iff, Set.setOf_mem_eq]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_discreteValuationRing_integer_and_finite_residueField :
    ProperSpace K ↔ CompleteSpace K ∧ DiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_discreteValuationRing_and_finite_residueField,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype, mem_integer_iff', ← mem_closedBall_zero_iff, Set.setOf_mem_eq]

end Valued.integer
