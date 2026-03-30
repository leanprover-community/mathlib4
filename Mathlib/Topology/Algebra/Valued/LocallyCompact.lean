/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact valued field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

public section

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

set_option backward.isDefEq.respectTransparency false in
lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  simp

lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).isUnit_iff_valuation_eq_one

lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  Valuation.integer.v_irreducible_lt_one h

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  Valuation.integer.v_irreducible_pos h

set_option backward.isDefEq.respectTransparency false in
lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  simp [Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

set_option backward.isDefEq.respectTransparency false in
lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  simp [h.maximalIdeal_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

set_option backward.isDefEq.respectTransparency false in
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
      .of_ideal_quotient (.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

open scoped Valued

set_option backward.isDefEq.respectTransparency false in
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
    have : {y : 𝒪[K] | v (y : K) ≤ v (p : K) ^ n} = Metric.closedBall 0 (‖p‖ ^ n) := by
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

set_option backward.isDefEq.respectTransparency false in
lemma locallyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    Nonempty (LocallyFiniteOrder (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ) := by
  -- TODO: generalize to `Valuation.Integer`, which will require showing that `IsCompact`
  -- pulls back across `TopologicalSpace.induced` from a `LocallyCompactSpace`.
  constructor
  refine LocallyFiniteOrder.ofFiniteIcc ?_
  -- We only need to show that we can construct a finite set for some set between
  -- a non-zero `z : Γ₀` and 1, because we can scale/invert this set to cover the whole group.
  suffices ∀ z : (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ, (Set.Icc z 1).Finite by
    rintro x y
    rcases lt_trichotomy y x with hxy | rfl | hxy
    · rw [Set.Icc_eq_empty_of_lt]
      · exact Set.finite_empty
      · simp [hxy]
    · simp
    wlog! h : x ≤ 1 generalizing x y
    · specialize this y⁻¹ x⁻¹ (inv_lt_inv' hxy) (inv_le_one_of_one_le (h.trans hxy).le)
      refine (this.inv).subset ?_
      rw [Set.inv_Icc]
      intro
      simp +contextual
    generalize_proofs _ _ _ _ hxu hyu
    rcases le_total y 1 with hy | hy
    · exact (this x).subset (Set.Icc_subset_Icc_right hy)
    · have H : (Set.Icc y⁻¹ 1).Finite := this _
      refine ((this x).union H.inv).subset (le_of_eq ?_)
      rw [Set.inv_Icc, inv_one, Set.Icc_union_Icc_eq_Icc] <;>
      simp [h, hy]
  -- We can construct a family of spheres at every single element of the valuation ring
  -- outside of a closed ball, which will cover.
  -- Since we are in a compact space, this cover has a finite subcover.
  -- First, we need to pick a threshold element with a nontrivial valuation less than 1,
  -- which will form -- the inner closed ball of the cover, which we need to cover 0.
  intro z
  obtain ⟨a, ha⟩ := z.val.prop
  rcases lt_or_ge 1 z with hz1 | hz1
  · rw [Set.Icc_eq_empty_of_lt]
    · exact Set.finite_empty
    · simp [hz1]
  have z0' : 0 < (z : MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := by simp
  have z0 : 0 < ((z : MonoidHom.mrange (Valued.v : Valuation K Γ₀)) : Γ₀) :=
    Subtype.coe_lt_coe.mpr z0'
  have a0 : 0 < v a := by simp [ha, z0]
  -- Construct our cover, which has an inner closed ball, and spheres for each element
  -- outside of the closed ball. These are all open sets by the nonarchimedean property.
  let U : K → Set K := fun y ↦ if v (y : K) ≤ z
    then {w | v (w : K) ≤ z}
    else {w | v (w : K) = v (y : K)}
  have := hc.elim_finite_subcover U
  specialize this ?_ ?_
  · intro w
    simp only [U]
    split_ifs with hw
    · obtain ⟨b, hb⟩ := MonoidHom.mem_mrange.mp z.1.2
      rw [← hb] at z0 ⊢
      simp_rw [← v.restrict_le_iff]
      refine Valued.isOpen_closedBall _ ?_
      rw [ne_eq, ← map_zero v.restrict, v.restrict_inj, map_zero]
      exact z0.ne'
    · simp_rw [← v.restrict_inj]
      refine Valued.isOpen_sphere _ ?_
      push Not at hw
      rw [← map_zero v.restrict, ne_eq, v.restrict_inj]
      refine (hw.trans' ?_).ne'
      simp [z0]
  · intro w
    simp only [integer, SetLike.mem_coe, Valuation.mem_integer_iff, Set.mem_iUnion, U]
    intro hw
    use if v w ≤ z then a else w
    split_ifs <;>
    simp_all
  -- For each element of the valuation ring that is bigger than our threshold element above,
  -- there must be something in the cover that has the precise valuation of the element,
  -- because it must be outside the inner closed ball, and thus is covered by some sphere.
  obtain ⟨t, ht⟩ := this
  classical
  refine (t.finite_toSet.dependent_image ?_).subset ?_
  · refine fun i hi ↦ if hi' : v i ≤ z then z else Units.mk0 ⟨(v i), by simp⟩ ?_
    push Not at hi'
    exact Subtype.coe_injective.ne_iff.mp (hi'.trans' z0).ne'
  · intro i
    simp only [Set.mem_Icc, Finset.mem_coe, exists_prop, Set.mem_setOf_eq, and_imp]
    -- we get the `c` from the cover that covers our arbitrary `i` with its set
    obtain ⟨c, hc⟩ := i.val.prop
    intro hzi hi1
    have hj := ht (hc.trans_le hi1)
    simp only [Set.mem_iUnion, exists_prop, U] at hj
    obtain ⟨j, hj, hj'⟩ := hj
    use j, hj
    -- and this `c` is either less than or greater than (or equal to) the threshold element
    split_ifs at hj' with hcj
    · simp only [Set.mem_setOf_eq, hc, Subtype.coe_le_coe, Units.val_le_val] at hj'
      simp [hcj, le_antisymm hj' hzi]
    · simp only [Set.mem_setOf_eq] at hj'
      rw [dif_neg hcj]
      simp [← hj', hc]

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
  have hc : IsCompact (X := K) 𝒪[K] := isCompact_iff_compactSpace.mpr hc
  -- We can also construct that it has a locally finite order, by compactness
  -- which leads to a contradiction.
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  have hm := mulArchimedean_mrange_of_isCompact_integer hc
  -- The key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  refine hi.isPrincipalIdealRing_iff_not_denselyOrdered_mrange.mpr fun _ ↦ ?_
  -- since we are densely ordered, we necessarily are nontrivial
  exact not_subsingleton (MonoidHom.mrange (v : Valuation K Γ₀))ˣ
    (LocallyFiniteOrder.denselyOrdered_iff_subsingleton.mp inferInstance)

theorem _root_.Valuation.isNontrivial_iff_not_a_field {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    v.IsNontrivial ↔ IsLocalRing.maximalIdeal v.integer ≠ ⊥ := by
  simp_rw [ne_eq, eq_bot_iff, v.isNontrivial_iff_exists_lt_one, SetLike.le_def, Ideal.mem_bot,
    not_forall, exists_prop, IsLocalRing.notMem_maximalIdeal.not_right,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact ⟨fun ⟨x, hx0, hx1⟩ ↦ ⟨⟨x, hx1.le⟩, by simp [Subtype.ext_iff, *]⟩,
  fun ⟨x, hx1, hx0⟩ ↦ ⟨x, by simp [*]⟩⟩

lemma isDiscreteValuationRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).IsNontrivial]
    [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] where
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  __ := isPrincipalIdealRing_of_compactSpace
  not_a_field' := v.isNontrivial_iff_not_a_field.mp hn

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
