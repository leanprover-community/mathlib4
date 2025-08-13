/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact valued field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

open NNReal

section NormedField

open scoped NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

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
  Valuation.integer.v_irreducible_lt_one h

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  Valuation.integer.v_irreducible_pos h

lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  simp [Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  simp [h.maximalIdeal_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  simp [h.maximalIdeal_pow_eq_setOf_le_v_coe_pow, Set.ext_iff, ← NNReal.coe_le_coe]

variable (K) in
lemma exists_norm_coe_lt_one : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
lemma exists_norm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_coe_lt_one K

variable (K) in
lemma exists_nnnorm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 :=
  exists_norm_coe_lt_one K

end Valued.integer

end NormedField

namespace Valued.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section FiniteResidueField

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

open scoped Valued
lemma totallyBounded_iff_finite_residueField [(Valued.v : Valuation K Γ₀).RankOne]
    [IsDiscreteValuationRing 𝒪[K]] :
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
      (Valuation.integer.integers _).coe_span_singleton_eq_setOf_le_v_algebraMap]
    rw [dist_comm] at hy'
    simpa [dist_eq_norm] using hy'.le
  · intro H
    rw [Metric.totallyBounded_iff]
    intro ε εpos
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := Valuation.integer.v_irreducible_lt_one hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : K)‖ ^ n < ε := exists_pow_lt_of_lt_one εpos
      (toNormedField.norm_lt_one_iff.mpr hp')
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H n
    refine ⟨Quotient.out '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ n))), Set.toFinite _, ?_⟩
    have : {y : 𝒪[K] | v (y : K) ≤ v (p : K) ^ n} = Metric.closedBall 0 (‖p‖ ^ n)  := by
      ext
      simp [← norm_pow]
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ n), hp.maximalIdeal_pow_eq_setOf_le_v_coe_pow,
      this, AddSubgroupClass.coe_norm, Set.image_univ, Set.mem_range, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', Set.iUnion_subset_iff, Metric.vadd_closedBall, vadd_eq_add, add_zero]
    intro
    exact (Metric.closedBall_subset_ball hn).trans (Set.subset_iUnion_of_subset _ le_rfl)

end FiniteResidueField

section CompactDVR

open Valued

open WithZeroTopology in
lemma locallyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    Nonempty (LocallyFiniteOrder (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ):= by
  -- TODO: generalize to `Valuation.Integer`, which will require showing that `IsCompact`
  -- pulls back across `TopologicalSpace.induced` from a `LocallyCompactSpace`.
  -- specify the topology again to increase priority to override subtype topology
  let : TopologicalSpace (MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := topologicalSpace
  let v' : Valuation K (MonoidHom.mrange (Valued.v : Valuation K Γ₀)) :=
   -- can't use mrangeRestrict directly, no CommGroupWithZero on MonoidHom mranges
  { __ := v.toMonoidWithZeroHom.mrangeRestrict
    map_zero' := by simp [Subtype.ext_iff]
    map_add_le_max' := by simp [← Subtype.coe_le_coe] }
  have : @Continuous _ _ _ topologicalSpace v' := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
    · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
      rintro ⟨-, y, rfl⟩ hy
      rw [Filter.Eventually, Valued.mem_nhds_zero]
      use Units.mk0 (v y) (by simpa [Subtype.ext_iff] using hy)
      simp [v', ← Subtype.coe_lt_coe]
    · have v_ne : v' x ≠ 0 := by simp [v', Subtype.ext_iff]
      rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
      simp [v', Subtype.ext_iff]
      apply Valued.loc_const
      simp
  rw [← locallyCompactSpace_iff_locallyFiniteOrder_units]
  refine locallyCompactSpace_of_compact_Iic one_ne_zero ?_
  convert hc.image_of_continuousOn this.continuousOn
  ext ⟨-, x, rfl⟩
  simp only [Set.mem_Iic, ← Subtype.coe_le_coe, OneMemClass.coe_one, Lean.Elab.WF.paramLet,
    OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Valuation.coe_mk, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, Set.mem_image, SetLike.mem_coe, Valuation.mem_integer_iff, Subtype.ext_iff,
    MonoidHom.coe_mrangeRestrict, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe,
    MonoidWithZeroHom.toZeroHom_coe, Valuation.toMonoidWithZeroHom_coe_eq_coe, OneHom.coe_mk, v']
  -- ideally, grind should solve this directly, but using it gives deterministic heartbeat timeout
  constructor <;>
  grind

lemma mulArchimedean_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    MulArchimedean (MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := by
  rw [← Units.mulArchimedean_iff]
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  exact MulArchimedean.of_locallyFiniteOrder

lemma isPrincipalIdealRing_of_compactSpace [hc : CompactSpace 𝒪[K]] :
    IsPrincipalIdealRing 𝒪[K] := by
  -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the valuation is densely ordered.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have hc : IsCompact (X := K) 𝒪[K] := by
    simpa [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype] using hc
  -- We can also construct that it has a locally finite order, by compactness
  -- which leads to a contradiction.
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  have hm := mulArchimedean_mrange_of_isCompact_integer hc
  -- The key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
  intro H
  -- since we are densely ordered, we necessarily are nontrivial
  replace H : DenselyOrdered (MonoidHom.mrange (v : Valuation K Γ₀)) := H
  obtain ⟨x, hx, hx'⟩ := exists_between (α := (MonoidHom.mrange (v : Valuation K Γ₀))) zero_lt_one
  lift x to (MonoidHom.mrange (v : Valuation K Γ₀))ˣ using IsUnit.mk0 _ hx.ne'
  rw [← Units.val_one, Units.val_lt_val] at hx'
  have : Nontrivial (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ := ⟨_, _, hx'.ne'⟩
  rw [← denselyOrdered_units_iff] at H
  exact not_lt_of_denselyOrdered_of_locallyFinite _ _ hx'

lemma isDiscreteValuationRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).IsNontrivial]
    [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] := by
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  obtain ⟨x, hx, hx'⟩ := hn.exists_lt_one
  have key : IsPrincipalIdealRing 𝒪[K] := isPrincipalIdealRing_of_compactSpace
  exact {
    not_a_field' := by
      -- here is the other place where the nontriviality of the valuation comes in,
      -- since if we had `v x = 0 ∨ v x = 1`, then the maximal ideal would be `⊥`.
      simp only [ne_eq, Ideal.ext_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Ideal.mem_bot, not_forall, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      refine ⟨⟨x, hx'.le⟩, ?_⟩
      simpa [Subtype.ext_iff, hx'] using hx
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : IsDiscreteValuationRing 𝒪[K] := isDiscreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
        totallyBounded_iff_finite_residueField] at h
    exact h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩

lemma properSpace_iff_compactSpace_integer [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             toNormedField.setOf_mem_integer_eq_closedBall]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField,
      toNormedField.setOf_mem_integer_eq_closedBall,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype]

end Valued.integer
