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
lemma exists_norm_lt : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_coe_lt K

variable (K) in
lemma exists_nnnorm_lt : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 :=
  exists_norm_coe_lt K

lemma isDiscreteValuationRing_of_compactSpace [h : CompactSpace 𝒪[K]] :
    IsDiscreteValuationRing 𝒪[K] := by
  -- To prove we have a DVR, we need to show it is a local ring and a PIR and not a field.
  -- First, note that it is a local ring, which the TC knows about.
  -- We prove that it is not a field inline later.
  have hl : IsLocalRing 𝒪[K] := inferInstance
  -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the norms is densely ordered.
  -- We can construct a family of spheres at every single element of the valuation ring
  -- outside of a closed ball, which will cover.
  -- Since we are in a compact space, this cover has a finite subcover.
  -- This subcover, when excluding the sphere at 1, then has a max element since it is finite.
  -- However, since we are densely ordered, we can find an element with a norm between
  -- the max element and 1, which is a contradiction, since it is outside the cover.
  -- This proof works easier over a normed field as opposed to a `Valued R Γ₀` since
  -- it is easier to phrase that closed balls and spheres are open sets to provide the cover.
  -- There is additional juggling because working over `𝒪[K]` requires constantly proving
  -- that we remain in the subtype.

  -- First, we need to pick a threshold element with a nontrivial norm less than 1, which will form
  -- the inner closed ball of the cover, which we need to cover 0. We have such an element because
  -- we are in a nontrivially normed field.
  obtain ⟨x, hx, hx'⟩ := exists_nnnorm_lt K
  rw [← nnnorm_one (α := K)] at hx'
  -- the key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- must be a PIR iff the value group is not densely ordered.
  -- A nonarchimedean normed field has a natural valuation mapping into `ℝ≥0` which works.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have key : IsPrincipalIdealRing 𝒪[K] := by
    rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
    intro H
    -- we switch to discuss the range of the `nnnorm` instead of the valuation for ease of
    -- interop with the metric space structure. Additionally, the valuation has all of `K`
    -- as the domain, while we really are working only in the valuation ring `𝒪[K]`.
    replace H : DenselyOrdered (Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) := by
      -- this whole proof is juggling out subtypes to get a `c : K` that is between `v x` and `v y`
      constructor
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      replace h : (⟨_, a, rfl⟩ : Set.range (v : K → ℝ≥0)) < ⟨_, b, rfl⟩ := h
      obtain ⟨⟨_, c, rfl⟩, hc⟩ := exists_between h
      -- then plugging in that `c`, leaving a goal to show that it must be in our valuation ring
      refine ⟨⟨_, ⟨c, ?_⟩, rfl⟩, hc⟩
      · rw [mem_iff]
        simp only [Subtype.mk_lt_mk, ← coe_lt_coe, coe_nnnorm] at hc
        -- which is the case because we know it is less than our `y : 𝒪[K]`
        simpa using hc.right.le.trans (mem_iff.mp b.prop)
    -- Construct our cover, which has an inner closed ball, and spheres for each element
    -- outside of the closed ball. These are all open sets by the nonarchimedean property.
    -- TODO: generalize to `Valued R Γ₀` by creating lemmas that `{x | v x ≤ r}` is open etc
    let U : 𝒪[K] → Set 𝒪[K] := fun y ↦ if ‖y‖₊ < ‖x‖₊
      then Metric.closedBall 0 ‖x‖
      else Metric.sphere 0 ‖y‖
    -- Extract out the finite subcover from our cover, which is a finite set of elements of
    -- the valuation ring, whose spheres cover the whole ring.
    obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U <| by
      intro y
      simp only [U]
      split_ifs with hy
      · refine (IsUltrametricDist.isOpen_closedBall _ ?_).mem_nhds (by simpa using hy.le)
        simpa using hx
      · refine (IsUltrametricDist.isOpen_sphere _ ?_).mem_nhds (by simp)
        simpa using (hx.trans_le (le_of_not_lt hy)).ne'
    -- For each element of the valuation ring that is bigger than our threshold element above,
    -- then there must be something in the cover that has the precise norm of the element,
    -- because it must be outside the inner closed ball, and thus is covered by some sphere.
    have htm : ∀ y : 𝒪[K], ‖x‖₊ < ‖y‖₊ → ∃ z ∈ t, ‖z‖₊ = ‖y‖₊ := by
      intro y hy
      have := ht.ge (Set.mem_univ y)
      simp only [Set.mem_iUnion, exists_prop', nonempty_prop, U] at this
      -- we get the `z` from the cover that covers our arbitrary `y` with its set
      obtain ⟨z, hz, hz'⟩ := this
      -- and this `z` is either less than or greater than (or equal to) the threshold element
      split_ifs at hz' with h
      -- the `z` is inside closed ball case, which is a contradiction since we know `y` is outside
      · simp only [← coe_lt_coe, coe_nnnorm] at hy
        simp [hy.not_le, -AddSubgroupClass.coe_norm] at hz'
      -- the `z` is gives a sphere, so we plug it in (juggling between ℝ≥0 and ℝ)
      · simp only [mem_sphere_iff_norm, sub_zero] at hz'
        refine ⟨z, hz, ?_⟩
        simp [← coe_inj, hz']
    -- Pick an element of the valuation ring to use as the excluded element of the subcover
    -- (since we know that all elements of the valuation ring have norm less than or equal to 1).
    obtain ⟨y, _, hy'⟩ : ∃ y : 𝒪[K], y ∈ t ∧ ‖y‖₊ = 1 := by simpa using htm 1 hx'
    -- And pick an element in the subcover that is greater than the threshold element, but less
    -- than norm 1. We will need this to show that the subcover excluding the element with norm 1
    -- is nonempty, which will allow us to take a max element.
    obtain ⟨w, hwt, hw1, hxw⟩ : ∃ w : 𝒪[K], w ∈ t ∧ ‖w‖₊ < 1 ∧ ‖x‖₊ < ‖w‖₊ := by
      replace hx' : (⟨_, x, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < ⟨_, 1, rfl⟩ := hx'
      obtain ⟨⟨_, w, rfl⟩, hw, hw'⟩ := exists_between hx'
      obtain ⟨u, hu, hu'⟩ := htm w hw
      exact ⟨u, hu, hu' ▸ by simpa using hw', hu' ▸ by simpa using hw⟩
    -- We're ready to work with the cover that excludes elements with norm 1.
    let u := t.filter (fun a ↦ ‖a‖₊ < 1)
    have hwu : w ∈ u := by simp [u, hwt, hw1] -- and it is nonempty.
    -- So the element that takes on the largest norm in this partial cover is in the cover itself.
    obtain ⟨l, hl, hl'⟩ := u.sup'_mem (((‖·‖₊) : 𝒪[K] → ℝ≥0) '' u)
      -- which is the case because this partial cover is closed under the max (`⊔`) operation:
      -- if `‖x‖ ∈ u` and `‖y‖ ∈ u`, then `max ‖x‖ ‖y‖ ∈ u`, requiring a juggle since we're working
      -- on the finset sup of an image.
      -- TODO: should there be a helper lemma for images into linear orders?
      (fun x hx y hy ↦ (max_cases x y).elim (fun h ↦ h.left.symm ▸ hx) (fun h ↦ h.left.symm ▸ hy))
      ⟨w, hwu⟩ (‖·‖₊) (fun _ ↦ Set.mem_image_of_mem _)
    simp only at hl'
    -- we know that this largest element must have norm less than 1,
    -- since it is in the partial cover, and this is the property of the partial cover
    have hm : (⟨‖l‖₊, l, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < (⟨1, y, hy'⟩) := by
      simp only [Finset.coe_filter, Set.mem_setOf_eq, u] at hl
      simp [hl.right]
    -- Prepare the contradiction, pick an element that has a norm between the max element and 1.
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := exists_between hm
    simp only [Subtype.mk_lt_mk] at hm
    -- well, it is in the ring, so there is something in the cover that covers it,
    -- and it must be a sphere since it is larger than the threshold element by virtue of
    -- `‖x‖ < ‖l‖ < ‖m‖`.
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ t, ‖n‖₊ = ‖m‖₊ := by
      refine htm m (hxw.trans (hm.left.trans_le' ?_))
      rw [hl', Finset.le_sup'_iff]
      exact ⟨w, hwu, le_rfl⟩
    rw [← hn'] at hm -- clean up what norms we refer to
    -- to supply the contradiction, we have `‖l‖ < ‖n‖`, now prove that also `‖n‖ ≤ ‖l‖`
    refine hm.left.not_le ?_
    -- which is the case since `‖l‖ = u.sup' ..` and the property of `Finset.sup'`
    rw [hl', Finset.le_sup'_iff]
    refine ⟨n, ?_, le_rfl⟩
    simp [u, hn, hm.right]
  exact {
    __ := hl
    __ := key
    not_a_field' := by
      -- here is the other place where the nontriviality of the norm comes in,
      -- since if we had `‖x‖ = 0 ∨ ‖x‖ = 1`, then the maximal ideal would be `⊥`.
      simp only [ne_eq, Ideal.ext_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Ideal.mem_bot, not_forall, isUnit_iff_norm_eq_one]
      refine ⟨x, ?_⟩
      simp only [← coe_lt_coe, coe_zero, coe_nnnorm, norm_pos_iff, ne_eq,
        ZeroMemClass.coe_eq_zero, nnnorm_one, coe_one] at hx hx'
      simpa [hx] using hx'.ne
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField :
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

lemma properSpace_iff_compactSpace_integer :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             mem_iff, ← mem_closedBall_zero_iff, Set.setOf_mem_eq]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField :
    ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype, mem_iff, ← mem_closedBall_zero_iff, Set.setOf_mem_eq]

end Valued.integer
