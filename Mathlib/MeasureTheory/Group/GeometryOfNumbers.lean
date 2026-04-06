/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies, Kevin H. Wilson
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Gauge
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

namespace Real

lemma atTop_le_cobounded : .atTop ≤ Bornology.cobounded ℝ := by
  rw [cobounded_eq]; exact le_sup_right

end Real

namespace NNReal

@[simp] lemma cobounded_eq_atTop : Bornology.cobounded ℝ≥0 = .atTop := by
  rw [← Metric.comap_dist_right_atTop 0]; simp [NNReal.dist_eq]

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
      (measure_mono <| iUnion_subset fun _ => inter_subset_right)

public section successiveMin

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {s : Set E} {i j : ℕ}

variable (L s i) in
/-- The `i`-th successive minimum of a set `s` around the origin with respect to another subset `L`
is the smallest `r` such that `r • s ∩ L` spans a subspace of dimension strictly greater than `i`.

While we provide a very general definition, the most common usage is when `L` is a discrete
submodule (i.e., a copy of `ℤ^r` in `E` for some `r ≤ finrank ℝ E`) and `s` is convex, balanced,
absorbent, and bounded.

Note that the usual definition of successive minimum is that `r • s ∩ L` spans a subspace of
dimension *at least* `i`. However, this makes the `0`-th successive minimum be `0`, which is
inconvenient. Values past the dimension of the ambient space `E` are junk. -/
noncomputable def successiveMin : ℝ≥0 := sInf {r | i < finrank ℝ (span ℝ <| r • s ∩ L)}

variable [FiniteDimensional ℝ E]

@[simp] lemma successiveMin_of_finrank_le (hi : finrank ℝ E ≤ i) : successiveMin L s i = 0 := by
  simp [successiveMin, ((finrank_le _).trans hi).not_gt]

@[simp] lemma successiveMin_of_finrank_span_le
    (hi : finrank ℝ (span ℝ (L : Set E)) ≤ i) : successiveMin L s i = 0 := by
  simp [successiveMin, fun r : ℝ≥0 =>
    ((Submodule.finrank_mono (span_mono (inter_subset_right (s := r • s)))).trans hi).not_gt]

variable [hL : DiscreteTopology L]

theorem finrank_real_span_range_eq_finrank_int {ι : Type*} {v : ι → L} :
    finrank ℝ (span ℝ <| .range (Subtype.val ∘ v)) =
      finrank ℤ (span ℤ <| .range (Subtype.val ∘ v)) := by
  have hd : DiscreteTopology (span ℤ (.range (Subtype.val ∘ v))) :=
    hL.of_subset (span_le.mpr <| range_subset_iff.mpr fun j => (v j).prop)
  simpa only [Set.finrank] using Real.finrank_eq_int_finrank_of_discrete hd

theorem successiveMin_of_finrank_int_le (hi : finrank ℤ L ≤ i) : successiveMin L s i = 0 := by
  have hd : DiscreteTopology (span ℤ (L : Set E)) := by rw [L.span_eq]; exact hL
  have h := Real.finrank_eq_int_finrank_of_discrete hd
  simp only [Set.finrank] at h
  rw [L.span_eq] at h
  simp [h, hi]

lemma exists_lt_finrank_span_smul_inter (hs : Absorbent ℝ s) (hi : i < finrank ℤ L) :
    ∃ r : ℝ≥0, i < finrank ℝ (span ℝ <| r • s ∩ L) := by
  obtain ⟨ι, b⟩ := Free.exists_basis ℤ L
  have : (Set.range (Subtype.val ∘ b)).Finite := by
    refine (finite_range_iff ?_).mpr (Module.Finite.finite_basis b)
    simp [b.injective]
  obtain ⟨r, hr, hr0⟩ :=
    ((hs.absorbs_finite this).filter_mono Real.atTop_le_cobounded |>.and
      (eventually_ge_atTop (0 : ℝ))).exists
  use ⟨r, hr0⟩
  have hspan_eq : span ℤ (.range (Subtype.val ∘ b)) = L := by
    have h : (span ℤ (.range b)).map L.subtype = L := by
      rw [b.span_eq, map_subtype_top]
    rwa [map_span, ← range_comp] at h
  calc
    i < finrank ℤ L := hi
    _ = finrank ℤ (span ℤ (.range (Subtype.val ∘ b))) := by rw [hspan_eq]
    _ = finrank ℝ (span ℝ (.range (Subtype.val ∘ b))) := finrank_real_span_range_eq_finrank_int.symm
    _ ≤ finrank ℝ (span ℝ <| r • s ∩ L) := by
      refine finrank_mono <| span_mono ?_
      rintro x ⟨j, rfl⟩
      refine mem_inter ?_ (by simp)
      simp_rw [subset_def, mem_range] at hr
      simp [hr]

lemma exists_lt_finrank_span_smul_inter_zLattice [IsZLattice ℝ L] (hs : Absorbent ℝ s)
    (hi : i < finrank ℝ E) : ∃ r : ℝ≥0, i < finrank ℝ (span ℝ <| r • s ∩ L) :=
  exists_lt_finrank_span_smul_inter hs (hi.trans_eq (ZLattice.rank ..).symm)

@[gcongr] lemma successiveMin_mono (hs : Absorbent ℝ s) (hij : i ≤ j) (hj : j < finrank ℤ L) :
    successiveMin L s i ≤ successiveMin L s j :=
  csInf_le_csInf' (exists_lt_finrank_span_smul_inter hs hj) fun _r ↦ hij.trans_lt

lemma exists_linearIndependent_of_successiveMin_lt {r : ℝ≥0} (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (hi : i < finrank ℤ L) (hr : successiveMin L s i < r) :
    ∃ v : Fin (i + 1) → L, (∀ j, (v j : E) ∈ r • s ∩ L) ∧ (LinearIndependent ℤ v) := by
  have h0s : (0 : E) ∈ s := mem_of_mem_nhds hs₀
  obtain ⟨r', hr'mem, hr'r⟩ := exists_lt_of_csInf_lt
    (exists_lt_finrank_span_smul_inter (absorbent_nhds_zero hs₀) hi) hr
  have hri : i < finrank ℝ (span ℝ (r • s ∩ L)) :=
    lt_of_lt_of_le hr'mem (finrank_mono (span_mono (inter_subset_inter_left _
      (hsc.smul_mono_of_zero_mem h0s r'.coe_nonneg (by exact_mod_cast hr'r.le)))))
  obtain ⟨f, hf_mem, -, hf_li⟩ := exists_fun_fin_finrank_span_eq ℝ (r • s ∩ L)
  use fun j ↦ ⟨f (Fin.castLE hri j), (hf_mem _).2⟩
  constructor
  · intro j; exact hf_mem _
  · refine ((hf_li.comp _ (Fin.castLE_injective hri)).restrict_scalars ?_).of_comp L.subtype
    exact fun a b h ↦ by simpa using h

lemma isClosed_lt_finrank_span_smul_inter (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0)
    (hi : i < finrank ℤ L) :
    IsClosed {r : ℝ≥0 | i < finrank ℝ (span ℝ (r • s ∩ L))} := by
  have hs₀' : (0 : E) ∈ s := mem_of_mem_nhds hs₀
  apply IsSeqClosed.isClosed
  intro r r₀ hr hlim
  simp only [mem_setOf_eq] at hr ⊢
  have hr₀ : successiveMin L s i ≤ r₀ := ge_of_tendsto' hlim fun n => csInf_le' (hr n)
  have hbdd := hlim.eventually_le_const (lt_add_of_pos_right r₀ one_pos)
  have hL_closed : IsClosed (L : Set E) := by
    haveI : DiscreteTopology L.toAddSubgroup := hL
    have : IsClosed (L.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
    simpa using this
  have hfin : ((r₀ + 1) • s ∩ (L : Set E)).Finite :=
    ((hs.smul (↑(r₀ + 1) : ℝ)).inter_right hL_closed).finite
      (DiscreteTopology.isDiscrete.mono inter_subset_right)
  let S := {v : Fin (i + 1) → L | ∀ j, (v j : E) ∈ ((r₀ + 1) • s ∩ (L : Set E))}
  have hS : S.Finite := by
    have h1 : Set.Finite {x : L | (x : E) ∈ (r₀ + 1) • s ∩ (L : Set E)} :=
      hfin.preimage (fun _ _ _ _ h => Subtype.coe_injective h)
    have h2 : Set.Finite {v : Fin (i + 1) → L | ∀ j, (v j : E) ∈ (r₀ + 1) • s ∩ (L : Set E)} :=
      Finite.pi' (fun _ => h1)
    simp only [S, h2]
  by_cases! hn : ∃ n, r n ≤ r₀
  · obtain ⟨n, hn'⟩ := hn
    calc
      i < finrank ℝ (span ℝ <| r n • s ∩ L) := hr n
      _ ≤ finrank ℝ (span ℝ <| r₀ • s ∩ L) := by
        refine finrank_mono <| span_mono (inter_subset_inter_left _ ?_)
        exact (hsc.smul_mono_of_zero_mem hs₀' (by simp) hn')
  have : ∀ n, ∃ vₙ : Fin (i + 1) → L,
    (∀ j, (vₙ j : E) ∈ (r n • s ∩ (L : Set E))) ∧ LinearIndependent ℤ vₙ :=
    fun n ↦ exists_linearIndependent_of_successiveMin_lt hsc hs₀ hi (hr₀.trans_lt (hn n))
  choose v hv using this
  have : ∀ᶠ n in atTop, v n ∈ S := by
    filter_upwards [hbdd] with n hn
    intro j
    refine mem_of_subset_of_mem ?_ ((hv n).1 j)
    gcongr
    exact hsc.smul_mono_of_zero_mem hs₀' (by simp) hn
  obtain ⟨v₀, hv₀, hfreq⟩ : ∃ v₀ ∈ S, ∃ᶠ n in atTop, v n = v₀ :=
    hS.frequently_exists.mp (this.frequently.mono fun _ hn ↦ ⟨_, hn, rfl⟩)
  calc
    i < i + 1 := by linarith
    _ = finrank ℤ (span ℤ (.range v₀)) := by
      obtain ⟨n, rfl⟩ := hfreq.exists
      exact (Fintype.card_fin _).symm.trans (finrank_span_eq_card ((hv n).2)).symm
    _ = finrank ℝ (span ℝ (.range (Subtype.val ∘ v₀))) := by
        trans finrank ℤ (span ℤ (.range (Subtype.val ∘ v₀)))
        · have : .range (Subtype.val ∘ v₀) = L.subtype '' .range v₀ := by
            rw [range_comp]; rfl
          rw [this, ← Submodule.map_span, Submodule.finrank_map_subtype_eq]
        · exact finrank_real_span_range_eq_finrank_int.symm
    _ ≤ finrank ℝ (span ℝ <| r₀ • s ∩ L) := by
      refine finrank_mono <| span_mono ?_
      rintro x ⟨j, rfl⟩
      simp only [Function.comp_apply, mem_inter_iff, Subtype.coe_prop, and_true]
      have : r₀ • s = ⋂ (r : ℝ) (_ : r₀ < r), r • s := by
        have h1 := (gauge_le_eq hsc hs₀' (absorbent_nhds_zero hs₀) r₀.2)
        have h2 := gauge_le_eq_closure_smul (a := r₀) hsc
          (NormedSpace.isVonNBounded_of_isBounded ℝ hs.isBounded) hs₀ (by simp)
        have h3 := (hs.isClosed.smul₀ (r₀ : ℝ)).closure_eq
        have : r₀ • s = (r₀ : ℝ) • s := rfl
        exact (this.trans <| (h3.symm.trans h2.symm).trans h1)
      simp_rw [this, mem_iInter]
      intro r' hr'
      let r'' : ℝ≥0 := ⟨r', show 0 ≤ r' by exact r₀.coe_nonneg.trans hr'.le⟩
      obtain ⟨n, ⟨rfl, hn⟩⟩ :=
        hfreq.and_eventually
          (hlim.eventually (eventually_lt_nhds (a := r₀) (b := r'') hr')) |>.exists
      apply mem_of_subset_of_mem (hsc.smul_mono_of_zero_mem hs₀' (by simp) hn.le)
      exact mem_of_mem_inter_left ((hv n).1 j)

lemma lt_finrank_span_successiveMin (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) (hi : i < finrank ℤ L) :
    i < finrank ℝ (span ℝ <| successiveMin L s i • s ∩ L) :=
  (isClosed_lt_finrank_span_smul_inter hsc hs hs₀ hi).csInf_mem
    (exists_lt_finrank_span_smul_inter (absorbent_nhds_zero hs₀) hi) (OrderBot.bddBelow _)

variable (L) in
/-- A bounded set `s` around the origin admits a directional set with respect to any discrete
additive subgroup `L`, i.e., a linearly independent subset of the ambient space `E` lying in `L`
that spans over `ℝ` the subspace `span ℝ L ≤ E` and such that the `i`-th basis element belongs to
the dilate of `s` by its `i`-th successive minimum.

Note that a directional basis does not necessarily span the subgroup `L` with integer coefficients.
See `exists_directional_set` for a version that concludes the set is `LinearIndependent`.
-/
lemma exists_directional_set' (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → E,
      (∀ j, (v j : E) ∈ successiveMin L s j.val • s ∩ L) ∧ LinearIndependent ℝ v := by
  suffices ∀ d, d ≤ finrank ℤ L →
      ∃ v : Fin d → E,
        (∀ j, (v j : E) ∈ successiveMin L s j.val • s ∩ L) ∧ LinearIndependent ℝ v by
    exact this _ le_rfl
  intro d hd
  induction d with
  | zero => exact ⟨isEmptyElim, isEmptyElim, linearIndependent_empty_type⟩
  | succ d ih =>
  obtain ⟨v, hv, hvli⟩ := ih (by omega)
  have hd' : d < finrank ℤ L := by omega
  obtain ⟨w, hwv, hw⟩ : ∃ w ∉ span ℝ (.range v),
      w ∈ successiveMin L s d • s ∩ ↑L := by
    by_contra! h
    apply lt_irrefl d
    calc
      d < finrank ℝ (span ℝ (successiveMin L s d • s ∩ L)) :=
        lt_finrank_span_successiveMin hsc hs hs₀ hd'
      _ ≤ finrank ℝ (span ℝ (.range v)) := by
        refine Submodule.finrank_mono <| span_le.mpr ?_
        intro w hw
        by_contra hx
        exact h w hx hw
      _ ≤ d := by simpa using finrank_range_le_card v
  refine ⟨Fin.snoc v w, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [Fin.snoc_last] using hw
    · intro i; simp [Fin.snoc_castSucc, hv i]
  · exact hvli.finSnoc hwv

variable (L) in
/-- A bounded set `s` around the origin admits a directional set with respect to any discrete
additive subgroup `L`, i.e., a linearly independent subset of the ambient space `E` lying in `L`
that spans over `ℝ` the subspace `span ℝ L ≤ E` and such that the `i`-th basis element belongs to
the dilate of `s` by its `i`-th successive minimum. Here we provide the weaker conclusion that
the set is `LinearIndependent` over `ℤ`.

See `exists_directional_set'` for a version that concludes the `ℝ`-span is all of `span ℝ L`.
-/
lemma exists_directional_set (hsc : Convex ℝ s) (hs : IsCompact s) (hs₀ : s ∈ 𝓝 0) :
    ∃ v : Fin (finrank ℤ L) → L,
      (∀ j, (v j : E) ∈ successiveMin L s j.val • s) ∧ LinearIndependent ℤ v := by
  obtain ⟨v, hv, hvli⟩ := exists_directional_set' L hsc hs hs₀
  refine ⟨fun j => ⟨v j, (hv j).2⟩, fun j => (hv j).1, ?_⟩
  rw [← L.subtype.linearIndependent_iff (Submodule.ker_subtype _)]
  exact hvli.restrict_scalars' ℤ

variable (L) in
/-- A bounded set `s` around the origin admits a directional basis with respect to any lattice `L`,
i.e. a basis of the ambient space `E` lying in `L` such that the `i`-th basis element belongs to
the dilate of `s` by its `i`-th successive minimum.

Note that a directional basis does not necessarily span the lattice `L` with integer coefficients.
-/
lemma exists_directional_basis [IsZLattice ℝ L] (hsc : Convex ℝ s) (hs : IsCompact s)
    (hs₀ : s ∈ 𝓝 0) :
    ∃ b : Basis (Fin <| finrank ℝ E) ℝ E, ∀ i, b i ∈ successiveMin L s i.val • s ∩ L := by
  obtain ⟨v, hva, hvli⟩ := exists_directional_set' L hsc hs hs₀
  rw [← ZLattice.rank ℝ L]
  by_cases! h : finrank ℤ L = 0
  · haveI : IsEmpty (Fin (finrank ℤ L)) := h ▸ Fin.isEmpty
    exact ⟨basisOfFinrankZero ((ZLattice.rank ℝ L).symm.trans h), isEmptyElim⟩
  haveI : Nonempty (Fin (finrank ℤ L)) := ⟨0, by omega⟩
  use basisOfLinearIndependentOfCardEqFinrank hvli (by simp [ZLattice.rank ℝ L])
  simp [hva]

end successiveMin

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

set_option linter.unusedSectionVars false in
/-- The second **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E`
whose volume is large enough compared to its successive minima and the covolume
of a lattice `L` of `E`, then it contains a non-zero lattice point of `L`. -/
proof_wanted exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure_mul_prod_successiveMin
    {L : Submodule ℤ E}
    (hF : IsAddFundamentalDomain L F μ) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ finrank ℝ E < μ s * ∏ i < Module.finrank ℝ E, successiveMin L s i) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s

/-- The **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contains a non-zero
lattice point of `L`. -/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    {L : AddSubgroup E} [Countable L]
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
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := not_disjoint_iff.mp h
  refine ⟨x - y, sub_ne_zero.2 hxy, ?_⟩
  rw [mem_inv_smul_set_iff₀ (two_ne_zero' ℝ)] at hv hw
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
    erw [← iInter_inter, K.iInter_smul_eq_self h_zero] at this
    · obtain ⟨x, hx⟩ := this
      exact ⟨⟨x, by simp_all⟩, by aesop⟩
    · exact (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.2.2
  have h_clos : IsClosed ((L : Set E) \ {0}) := by
    rsuffices ⟨U, hU⟩ : ∃ U : Set E, IsOpen U ∧ U ∩ L = {0}
    · rw [sdiff_eq_sdiff_iff_inf_eq_inf (z := U).mpr (by simp [inter_comm .. ▸ hU.2, zero_mem])]
      exact AddSubgroup.isClosed_of_discrete.sdiff hU.1
    exact isOpen_inter_eq_singleton_of_mem_discrete ⟨inferInstance⟩ (zero_mem L)
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z (fun n => ?_)
    (fun n => ?_) ((S 0).isCompact.inter_right h_clos) (fun n => (S n).isClosed.inter h_clos)
  · refine inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr ?_)
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
