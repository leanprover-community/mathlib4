/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `???`: Minkowski's second theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

public section

section
variable {ι X : Type*} [TopologicalSpace X] {s : ι → Set X}

lemma IsClosed.iUnion_of_finite_nonempty (hs : ∀ i, IsClosed (s i))
    (hs_nonempty : {i | (s i).Nonempty}.Finite) : IsClosed (⋃ i, s i) := by
  simpa using hs_nonempty.isClosed_biUnion (f := s) fun _ _ ↦ hs _

end

namespace Real

lemma atTop_le_cobounded : .atTop ≤ Bornology.cobounded ℝ := by
  rw [cobounded_eq]; exact le_sup_right

end Real

namespace NNReal

@[simp] lemma cobounded_eq_atTop : Bornology.cobounded ℝ≥0 = .atTop := by
  rw [← Metric.comap_dist_right_atTop 0]; simp [NNReal.dist_eq]

instance neBot_cobounded : (Bornology.cobounded ℝ≥0).NeBot := by simp; infer_instance

end NNReal


namespace MeasureTheory

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Submodule Filter
open scoped Pointwise NNReal Topology

variable {E S : Type*}

/-- **Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolume of the
countable subgroup `L` of `E`, then there exist two distinct points `x, y ∈ L` such that `(x + s)`
and `(y + s)` are not disjoint. -/
theorem exists_pair_mem_lattice_not_disjoint_vadd {L : Type*} {F s : Set E} [MeasurableSpace E]
    {μ : Measure E} [AddGroup L] [Countable L] [AddAction L E] [MeasurableSpace L]
    [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right)

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {F s : Set E} {i j : ℕ}

variable (L s i) in
/-- The `i`-th successive minimum of a compact convex set `s` around the origin with respect to a
lattice `L` is the smallest `r` such that `r • s ∩ L` spans a subspace of dimension strictly
greater than `i`.

Note that the usual textbook definition is that `r • s ∩ L` spans a subspace of dimension *at least*
`i`, but this makes the `0`-th successive minimum be `0`, which is inconvenient.
Values past the dimension of the ambient space `E` are junk. -/
noncomputable def successiveMin (s : Set E) (i : ℕ) : ℝ≥0 :=
  sInf {r | i < finrank ℝ (span ℝ <| r • s ∩ L)}

variable [FiniteDimensional ℝ E]

@[simp] lemma successiveMin_of_finrank_le (hi : finrank ℝ E ≤ i) : successiveMin L s i = 0 := by
  simp [successiveMin, ((finrank_le _).trans hi).not_gt]

variable [DiscreteTopology L] [IsZLattice ℝ L]

lemma exists_lt_finrank_span_smul_inter_zLattice (hs : Absorbent ℝ s) (hi : i < finrank ℝ E) :
    ∃ r : ℝ≥0, i < finrank ℝ (span ℝ <| r • s ∩ L) := by
  obtain ⟨ι, b⟩ := Free.exists_basis ℤ L
  have : DiscreteTopology (Submodule.ofClass L) := ‹_›
  have : Finite ι := Module.Finite.finite_basis b
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, .range (Subtype.val ∘ b) ⊆ r • s := by
    suffices ∀ᶠ r : ℝ in atTop, 0 ≤ r ∧ .range (Subtype.val ∘ b) ⊆ r • s by
     simpa [NNReal.exists, NNReal.smul_def] using this.exists
    filter_upwards [eventually_ge_atTop 0, Real.atTop_le_cobounded <|
      hs.absorbs_finite (Set.finite_range (Subtype.val ∘ b))] with r hr hbr
    exact ⟨hr, hbr⟩
  use r
  suffices span ℝ (r • s ∩ L) = ⊤ by rwa [this, finrank_top]
  refine eq_top_mono (span_mono <| subset_inter hr <| by simp [Set.range_subset_iff]) ?_
  convert (Basis.ofZLatticeBasis ℝ L b).span_eq
  ext
  simp

lemma isClosed_lt_finrank_span_smul_inter_zLattice (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0)
    (hi : i < finrank ℝ E) : IsClosed {r : ℝ≥0 | i < finrank ℝ (span ℝ (r • s ∩ L))} := by
  rw [isClosed_iff_nhds]
  rintro r hr
  -- convert_to IsClosed <|
  --   ⋃ (t : Set E) (ht : t.Finite) (hit : i < finrank ℝ (span ℝ t)),
  --     ⋂ (x ∈ t ∩ L), (· • x) ⁻¹' (s : Set E)
  -- swap; · infer_instance
  -- · ext
  --   simp
  --   sorry
  -- refine .iUnion_of_finite_nonempty
  --   (fun t ↦ isClosed_iUnion_of_finite fun ht ↦ isClosed_iUnion_of_finite fun hit ↦
  --     isClosed_iInter fun x ↦ isClosed_iInter fun hx ↦ hs.isClosed.preimage <|
  --       continuous_smul.comp <| continuous_id.prodMk continuous_const) ?_
  -- simp
  -- have : DiscreteTopology (s ∩ L) :=
  -- have := hs.finite_of
  sorry

@[gcongr] lemma successiveMin_mono (hs : Absorbent ℝ s) (hij : i ≤ j) (hj : j < finrank ℝ E) :
    successiveMin L s i ≤ successiveMin L s j :=
  csInf_le_csInf' (exists_lt_finrank_span_smul_inter_zLattice hs hj) fun _r ↦ hij.trans_lt

lemma lt_finrank_span_successiveMin (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℝ E) :
    i < finrank ℝ (span ℝ <| successiveMin L s i • s ∩ L) :=
  (isClosed_lt_finrank_span_smul_inter_zLattice hs hs₀ hi).csInf_mem
    (exists_lt_finrank_span_smul_inter_zLattice (absorbent_nhds_zero hs₀) hi) (OrderBot.bddBelow _)

/-- A compact set `s` around the origin admits a directional basis with respect to any lattice `L`,
i.e. a basis of the ambient space `E` lying in `L` such that the `i`-th basis element belongs to
the dilate of `s` by its `i`-th successive minimum.

Note that a directional basis does not necessarily span the lattice `L` with integer coefficients.
-/
lemma exists_directional_basis (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ b : Basis (Fin <| finrank ℝ E) ℝ E, ∀ i, b i ∈ successiveMin L s i.val • s ∩ L := by
  suffices ∀ d ≤ finrank ℝ E,
      ∃ v : Fin d → E, LinearIndependent ℝ v ∧ ∀ i, v i ∈ successiveMin L s i.val • s ∩ L by
    obtain ⟨v, hv, hvs⟩ := this _ le_rfl
    exact ⟨.ofLinearIndependentOfCardEqFinrank' v hv <| by simp, by simpa⟩
  rintro d hd
  induction d with
  | zero => exact ⟨isEmptyElim, by simp⟩
  | succ d ih =>
  obtain ⟨v, hv, hvs⟩ := ih <| by cutsat
  obtain ⟨w, hwv, hw⟩ : ∃ w ∉ span ℝ (.range v), w ∈ successiveMin L s d • s ∩ L := by
    by_contra!
    simp only [not_imp_not] at this
    refine lt_irrefl d ?_
    calc
      d < finrank ℝ (span ℝ <| successiveMin L s d • s ∩ L) :=
        lt_finrank_span_successiveMin hs hs₀ hd
      _ ≤ finrank ℝ (span ℝ <| range v) := finrank_mono <| span_le.2 this
      _ ≤ d := by simpa using finrank_range_le_card v
  exact ⟨Fin.snoc v w, .fin_snoc hv hwv, Fin.forall_fin_succ'.2 ⟨by simpa, by simpa using hw⟩⟩

variable [MeasurableSpace E] [BorelSpace E] [Countable L] {μ : Measure E} [IsAddHaarMeasure μ]

set_option linter.unusedSectionVars false in
/-- The second **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E`
whose volume is large enough compared to its successive minima and the covolume
of a lattice `L` of `E`, then it contains a non-zero lattice point of `L`. -/
proof_wanted exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure_mul_prod_successiveMin
    (hF : IsAddFundamentalDomain L F μ) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ finrank ℝ E < μ s * ∏ i < Module.finrank ℝ E, successiveMin L s i) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s

/-- The **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contains a non-zero
lattice point of `L`. -/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {L : AddSubgroup E} [DiscreteTopology L] [Countable L]
    (fund : IsAddFundamentalDomain L F μ) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ finrank ℝ E < μ s) : ∃ x ≠ 0, ((x : L) : E) ∈ s := by
  have h_vol : μ F < μ ((2⁻¹ : ℝ) • s) := by
    rw [addHaar_smul_of_nonneg μ (by simp : 0 ≤ (2 : ℝ)⁻¹) s,
      ← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank ℝ E) (two_ne_zero' _)) (by finiteness),
      mul_right_comm, ofReal_pow (by simp : 0 ≤ (2 : ℝ)⁻¹), ofReal_inv_of_pos zero_lt_two]
    norm_num
    rwa [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top, one_pow, one_mul]
  obtain ⟨x, y, hxy, h⟩ :=
    exists_pair_mem_lattice_not_disjoint_vadd fund ((h_conv.smul _).nullMeasurableSet _) h_vol
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := Set.not_disjoint_iff.mp h
  refine ⟨x - y, sub_ne_zero.2 hxy, ?_⟩
  rw [Set.mem_inv_smul_set_iff₀ (two_ne_zero' ℝ)] at hv hw
  simp_rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm _ w, ← sub_eq_sub_iff_add_eq_add, ←
    AddSubgroup.coe_sub] at hvw
  rw [← hvw, ← inv_smul_smul₀ (two_ne_zero' ℝ) (_ - _), smul_sub, sub_eq_add_neg, smul_add]
  refine h_conv hw (h_symm _ hv) ?_ ?_ ?_ <;> norm_num

set_option backward.isDefEq.respectTransparency false in
/-- The **Minkowski Convex Body Theorem for compact domain**. If `s` is a convex compact symmetric
domain of `E` whose volume is large enough compared to the covolume of a lattice `L` of `E`, then it
contains a non-zero lattice point of `L`. Compared to
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, this version requires in addition
that `s` is compact and `L` is discrete but assumes a weak inequality rather than a strict
inequality. -/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure [Nontrivial E]
    {L : AddSubgroup E} [Countable L] [DiscreteTopology L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : μ F * 2 ^ finrank ℝ E ≤ μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by
  have h_mes : μ s ≠ 0 := fun hμ ↦ fund.measure_ne_zero (NeZero.ne μ) <| by simpa [hμ] using h
  have h_nemp : s.Nonempty := nonempty_of_measure_ne_zero h_mes
  let u : ℕ → ℝ≥0 := (exists_seq_strictAnti_tendsto 0).choose
  let K : ConvexBody E := ⟨s, h_conv, h_cpt, h_nemp⟩
  let S : ℕ → ConvexBody E := fun n => (1 + u n) • K
  let Z : ℕ → Set E := fun n => (S n) ∩ (L \ {0})
  -- The convex bodies `S n` have volume strictly larger than `μ s` and thus we can apply
  -- `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to them and obtain that
  -- `S n` contains a nonzero point of `L`. Since the intersection of the `S n` is equal to `s`,
  -- it follows that `s` contains a nonzero point of `L`.
  have h_zero : 0 ∈ K := K.zero_mem_of_symmetric h_symm
  suffices Set.Nonempty (⋂ n, Z n) by
    erw [← Set.iInter_inter, K.iInter_smul_eq_self h_zero] at this
    · obtain ⟨x, hx⟩ := this
      exact ⟨⟨x, by simp_all⟩, by aesop⟩
    · exact (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.2.2
  have h_clos : IsClosed ((L : Set E) \ {0}) := by
    rsuffices ⟨U, hU⟩ : ∃ U : Set E, IsOpen U ∧ U ∩ L = {0}
    · rw [sdiff_eq_sdiff_iff_inf_eq_inf (z := U).mpr (by simp [Set.inter_comm .. ▸ hU.2, zero_mem])]
      exact AddSubgroup.isClosed_of_discrete.sdiff hU.1
    exact isOpen_inter_eq_singleton_of_mem_discrete ⟨inferInstance⟩ (zero_mem L)
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z (fun n => ?_)
    (fun n => ?_) ((S 0).isCompact.inter_right h_clos) (fun n => (S n).isClosed.inter h_clos)
  · refine Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr ?_)
    refine ConvexBody.smul_le_of_le K h_zero ?_
    rw [add_le_add_iff_left]
    exact le_of_lt <| (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.1 (Nat.lt_add_one n)
  · suffices μ F * 2 ^ finrank ℝ E < μ (S n : Set E) by
      have h_symm' : ∀ x ∈ S n, -x ∈ S n := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨-y, h_symm _ hy, by simp⟩
      obtain ⟨x, hx_nz, hx_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        fund h_symm' (S n).convex this
      exact ⟨x, hx_mem, by simp_all⟩
    refine lt_of_le_of_lt h ?_
    rw [ConvexBody.coe_smul', NNReal.smul_def, addHaar_smul_of_nonneg _ (NNReal.coe_nonneg _)]
    rw [show μ s < _ ↔ 1 * μ s < _ by rw [one_mul]]
    dsimp [K]
    gcongr
    · exact h_cpt.measure_ne_top
    rw [ofReal_pow (by positivity)]
    refine one_lt_pow₀ ?_ (ne_of_gt finrank_pos)
    simp [u, (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.2.1 n]

end MeasureTheory
