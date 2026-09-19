/-
Copyright (c) 2026 Samuel Oettl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Oettl
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.Order.BourbakiWitt

/-!
# Characterization of ergodicity

In this file we prove that ergodicity wrt a probability measure is eqivalent to convergence of the
Birkhoff Averages of `μ (A ∩ (preimage f^[n] B))` to `μ A * μ B` for all measurable Sets A and B.
We also prove that the convergence for all measurable sets is equivalent to the convergence on a
π-system that generates the `σ`-algebra. (In particular for product measures it is enough to know
the convergence for measurable rectangles.)
-/

public section

open Function Set Filter MeasureTheory Topology

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α} {f : α → α}

namespace Ergodic

def OnAverageIndependent (s t : Set α) (f : α → α) (μ : Measure α) :=
  Tendsto (birkhoffAverage ℝ (preimage f) (fun S ↦ (μ.real (s ∩ S))) · t)
  atTop (𝓝 (μ.real s * μ.real t))



---------------------- seperate pull request for these 4
theorem Function.const.birkhoffAverage_eq₀ (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) {n : ℕ} (hn : (n : R) ≠ 0)
    (x : α) : birkhoffAverage R f (fun _ ↦ a) n x = a := by
  rw [birkhoffAverage, birkhoffSum, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul R,
    inv_smul_smul₀ hn]

theorem Function.const.birkhoffAverage_eq₀' (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) {n : ℕ} (hn : (n : R) ≠ 0) :
    birkhoffAverage R f (fun _ ↦ a) n = fun _ ↦ a := by
  ext x; exact Function.const.birkhoffAverage_eq₀ R a hn x

open Classical in
theorem Function.const.birkhoffAverage_eq (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) (n : ℕ)
    (x : α) : birkhoffAverage R f (fun _ ↦ a) n x = if (n : R) = 0 then 0 else a := by
  by_cases h : (n : R) = 0
  · simp [h, birkhoffAverage]
  simpa [h] using Function.const.birkhoffAverage_eq₀ R a h x

open Classical in
@[simp]
theorem Function.const.birkhoffAverage_eq' (R : Type*) {α : Type*} {M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] {f : α → α} (a : M) (n : ℕ) :
    birkhoffAverage R f (fun _ ↦ a) n = fun _ ↦ if (n : R) = 0 then 0 else a := by
  ext x; exact Function.const.birkhoffAverage_eq R a n x
-----------------------



lemma locallyConvex_tendstoUniformly_imp_tendstoUniformly_average (R : Type*) {β : Type*} [Field R]
    [AddCommGroup β] [UniformSpace β] [IsRightUniformAddGroup β] [Module R β] [LinearOrder R]
    [IsStrictOrderedRing R] [LocallyConvexSpace R β] {ι : Type*} {F : ι → ℕ → β} {f : ℕ → β}
    {p : Filter ι} (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i (n:ℕ) ↦ (n:R)⁻¹ • ∑ k ∈ Finset.range n, F i k)
      (fun n ↦ (n:R)⁻¹ • ∑ k ∈ Finset.range n, f k) p := by
  simp only [TendstoUniformly, uniformity_eq_comap_nhds_zero, mem_comap, forall_exists_index,
    and_imp] at ⊢ h
  intro u b hb hu
  have basis := LocallyConvexSpace.convex_basis_zero R β
  specialize h _ _ (HasBasis.set_index_mem basis hb) (subset_refl _)
  simp only [mem_preimage] at h
  filter_upwards [h] with i hn n
  refine mem_of_mem_of_subset ?_
    (subset_trans (preimage_mono (HasBasis.set_index_subset basis hb)) hu)
  rw [id_eq, mem_preimage, ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  by_cases h0 : (n:R) = 0
  · simpa [h0] using mem_of_mem_nhds <|HasBasis.set_index_mem basis hb
  exact Convex.sum_mem
    (HasBasis.property_index basis hb).right
    (fun _ _ ↦ inv_nonneg_of_nonneg <|Nat.cast_nonneg' n)
    (by simp [mul_inv_cancel₀ h0])
    (fun x _ ↦ hn x)

lemma birkhoffAverage_tendsto_of_tendstoUniformly {R : Type*} {α : Type*} {M : Type*} [Field R]
    [AddCommGroup M] [UniformSpace M] [IsRightUniformAddGroup M] [LinearOrder R]
    [IsStrictOrderedRing R] [Module R M] [LocallyConvexSpace R M] {f : α → α} {g : α → M}
    {ι : Type*} {xi : ι → α} {yi : ι → M} {y : M} {x : α} {p : Filter ι} [NeBot p] {p' : Filter ℕ}
    (h1 : TendstoUniformly (fun i k ↦ g (f^[k] (xi i))) (fun k ↦ g (f^[k] x)) p)
    (h2 : ∀ᶠ i in p, Tendsto (birkhoffAverage R f g · (xi i)) p' (𝓝 (yi i)))
    (h3 : Tendsto yi p (𝓝 y)) : Tendsto (birkhoffAverage R f g · x) p' (𝓝 y) :=
  TendstoUniformly.tendsto_of_eventually_tendsto
    (locallyConvex_tendstoUniformly_imp_tendstoUniformly_average R h1) h2 h3

theorem onAverageIndependent_forall_measurableSet_of_piSystem (C : Set (Set α))
    (h_eq : mα = MeasurableSpace.generateFrom C) (h_inter : IsPiSystem C) [IsProbabilityMeasure μ]
    (hMP : MeasurePreserving f μ μ) (h : ∀ s ∈ C, ∀ t ∈ C, OnAverageIndependent s t f μ) (s : Set α)
    (hs : MeasurableSet s) (t : Set α) (ht : MeasurableSet t) : OnAverageIndependent s t f μ := by
  apply MeasurableSpace.induction_on_inter (C:=fun S _ ↦ Tendsto (birkhoffAverage ℝ
    (preimage f) (fun T ↦ μ.real (s ∩ T)) · S) atTop (𝓝 (μ.real s * μ.real S))) (ht:=ht)
    h_eq h_inter
  · rw [show (μ.real s * μ.real ∅) = μ.real (s ∩ ∅) by simp]
    apply IsFixedPt.tendsto_birkhoffAverage _ (by rfl)
  · intro t ht
    have hBmeas : MeasurableSet t := by
      rw [h_eq]
      exact MeasurableSpace.measurableSet_generateFrom ht
    refine MeasurableSpace.induction_on_inter (C:=fun S _ ↦ Tendsto (birkhoffAverage ℝ
      (preimage f) (fun T ↦ μ.real (S ∩ T)) · t) atTop (𝓝 (μ.real S * μ.real t))) h_eq h_inter
      (by simp) (fun s hs ↦ h s hs t ht) (fun s hs hTendsto ↦ ?_)
      (fun sn dis hsnmeas hsnTendsto ↦ ?_) _ hs
    · simp only
      rw [probReal_compl_eq_one_sub hs]
      have (n: ℕ) : μ.real t - μ.real (s ∩ (preimage f)^[n] t) =
        μ.real (sᶜ∩(preimage f)^[n] t) := by
        change _ - (μ _).toReal = (μ _).toReal
        rw [sub_eq_iff_eq_add',
          ← MeasurePreserving.measureReal_preimage (hMP.iterate n) hBmeas.nullMeasurableSet,
          preimage_iterate_eq, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        apply congrArg ENNReal.toReal
        rw [← diff_eq_compl_inter, inter_comm, measure_inter_add_diff₀ _ hs.nullMeasurableSet]
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, ← this, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub, sub_mul, one_mul]
      apply Tendsto.sub (EventuallyEq.tendsto <|mem_atTop_sets.mpr ⟨1, fun n hn ↦ ?_⟩) hTendsto
      simp [← mul_assoc,
        inv_mul_cancel₀ <|Nat.cast_ne_zero (R:=ℝ).mpr <|Nat.ne_zero_iff_zero_lt.mpr hn]
    · have (A : Set α) : Tendsto (birkhoffAverage ℝ (preimage f)
        (fun S ↦ μ.real (A ∩ S)) · t) atTop (𝓝 (μ.real A * μ.real t)) = Tendsto
        (birkhoffAverage ℝ (Prod.map id (preimage f)) (fun s ↦ μ.real (s.fst ∩ s.snd)) ·
        (A, t)) atTop (𝓝 (μ.real A * μ.real t)) := by
        simp [birkhoffAverage, birkhoffSum]
      have hAnTendsto' (m : ℕ) : Tendsto (birkhoffAverage ℝ (Prod.map id (preimage f))
        (fun s ↦ μ.real (s.1 ∩ s.2)) · (⋃ i ∈ Finset.range m, sn i, t)) atTop
        (𝓝 (μ.real (⋃ i ∈ Finset.range m, sn i) * μ.real t)) := by
        have pairwise_disjoint (x : ℕ) :
          (Finset.range m:Set ℕ).PairwiseDisjoint (sn · ∩ (preimage f)^[x] t) :=
          fun _ _ _ _ hij _ h1 h2 ↦ (dis hij (subset_inter_iff.mp h1|>.1) (subset_inter_iff.mp h2|>.1))
        have measurable (x : ℕ) : ∀ i ∈ Finset.range m , MeasurableSet (sn i ∩ (preimage f)^[x] t) :=
          fun i _ ↦ MeasurableSet.inter (hsnmeas i)
            (MeasurableSet.congr (hMP.iterate x|>.measurable hBmeas) (congrFun preimage_iterate_eq t))
        have := fun x ↦ measureReal_biUnion_finset (μ:=μ) (pairwise_disjoint x)
          (measurable x) (fun _ _ ↦ measure_ne_top _ _)
        simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Prod.map_iterate, iterate_id,
          Prod.map_apply, id_eq, iUnion_inter, this, measureReal_biUnion_finset (s:= Finset.range m)
          (fun _ _ _ _ hij ↦ (dis hij)) (fun b _ ↦ (hsnmeas b)) (fun _ _ ↦ measure_ne_top _ _)]
        simp only [Finset.sum_comm (t := Finset.range m), Finset.sum_mul, Finset.mul_sum]
        apply tendsto_finset_sum
        simpa only [← Finset.mul_sum] using (fun _ ↦ hsnTendsto ·)
      simp only [this]
      have h2 := Eventually.of_forall (f:=atTop) hAnTendsto'
      have h3 : Tendsto (fun k ↦ μ.real (⋃ i ∈ Finset.range k, sn i)) atTop
        (𝓝 (μ.real (⋃ i, sn i))) := by
        change Tendsto (fun n ↦ (μ (⋃ i ∈ Finset.range n, sn i)).toReal)
          atTop (𝓝 ((μ (⋃ i, sn i)).toReal))
        rw [← tendsto_add_atTop_iff_nat 1]
        simpa [ENNReal.tendsto_toReal_iff] using tendsto_measure_iUnion_accumulate
      refine birkhoffAverage_tendsto_of_tendstoUniformly ?_ h2 (Tendsto.mul_const (μ.real t) h3)
      refine Metric.tendstoUniformly_of_dist_le_tendsto_zero
        (u:=fun n ↦ μ.real (symmDiff (⋃ i, sn i) (⋃ i ∈ Finset.range n, sn i))) (fun n x ↦ ?_) ?_
      · simp only [Prod.map_iterate, iterate_id, Prod.map_apply, id_eq, ← preimage_iterate_eq]
        apply le_trans
        · apply abs_measureReal_sub_le_measureReal_symmDiff
          · apply MeasurableSet.nullMeasurableSet
            apply MeasurableSet.inter (MeasurableSet.iUnion hsnmeas)
            exact hMP.iterate x|>.measurable hBmeas
          · apply MeasurableSet.nullMeasurableSet
            apply MeasurableSet.inter <|Finset.measurableSet_biUnion (Finset.range n)
              (fun _ ↦ hsnmeas ·)
            exact hMP.iterate x|>.measurable hBmeas
        rw [← inter_symmDiff_distrib_right]
        apply le_trans <|measureReal_mono inter_subset_left
        rfl
      · simpa only [fun n ↦ symmDiff_of_ge
          <|iUnion₂_subset_iUnion (Membership.mem (Finset.range n)) sn,
          fun n ↦ measureReal_diff (μ:=μ)
          (iUnion₂_subset_iUnion (Membership.mem (Finset.range n)) sn)
          (Finset.measurableSet_biUnion (Finset.range n) (fun _ ↦ hsnmeas ·)),
          ← sub_self (μ.real (⋃ i, sn i))] using Filter.Tendsto.const_sub _ h3
  · intro t htm
    simp only
    intro ht
    rw [probReal_compl_eq_one_sub htm]
    have : (birkhoffAverage ℝ (preimage f) (fun S ↦ μ.real (s ∩ S)) · tᶜ) =
      (birkhoffAverage ℝ (preimage f) (fun S ↦ μ.real s - μ.real (s ∩ S)) · t) := by
      funext n
      unfold birkhoffAverage birkhoffSum
      simp only [smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]
      refine Or.inl <| Finset.sum_congr rfl <|fun k _ ↦ ?_
      rw [← preimage_iterate_eq, preimage_compl, ← diff_eq, ← diff_self_inter, measureReal_diff'
          (MeasurableSet.inter hs (Measurable.iterate hMP.measurable k htm)),
        sub_left_inj, union_eq_self_of_subset_right inter_subset_left]
    rw [this, mul_sub, mul_one, ← Pi.sub_def]
    simpa [birkhoffAverage_sub] using Tendsto.sub (tendsto_atTop_of_eventually_const (i₀ := 1)
      (fun _ hi ↦ if_neg (Nat.ne_zero_of_lt hi))) ht
  · simp only
    intro Bn dis hBnmeas hBnTendsto
    have hBnTendsto' (m : ℕ) : Tendsto (birkhoffAverage ℝ (preimage f)
        (fun S ↦ μ.real (s ∩ S)) · (⋃ i ∈ Finset.range m, Bn i)) atTop
        (𝓝 (μ.real s * μ.real (⋃ i ∈ Finset.range m, Bn i))) := by
      rw [measureReal_biUnion_finset (Pairwise.pairwiseDisjoint dis (Finset.range m))
        (fun b _ ↦ hBnmeas b), Finset.mul_sum]
      refine Tendsto.congr ?_ <|tendsto_finset_sum (Finset.range m) (fun i _ ↦ hBnTendsto i)
      intro n
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, ← preimage_iterate_eq,
        preimage_iUnion, inter_iUnion]
      have disj (x : ℕ) : (Finset.range m:Set ℕ).PairwiseDisjoint
        (fun i ↦ s ∩ (f^[x] ⁻¹' Bn i)) := by
        have : Pairwise (Disjoint on (f^[x] ⁻¹' Bn ·)) :=
          fun _ _ hij ↦ Disjoint.preimage f^[x] (dis hij)
        exact fun _ _ _ _ hij _ h1 h2 ↦ this hij (subset_inter_iff.mp h1|>.2)
          (subset_inter_iff.mp h2|>.2)
      have meas (x : ℕ) : (∀ b ∈ Finset.range m, MeasurableSet (s ∩ f^[x] ⁻¹' Bn b)) :=
        fun b _ ↦  MeasurableSet.inter hs <|(hMP.iterate x).measurable <|hBnmeas b
      simp only [← Finset.mul_sum, fun x ↦ measureReal_biUnion_finset (μ := μ) (disj x) (meas x),
        Finset.sum_comm (s := Finset.range n)]
    have h3 : Tendsto (fun k ↦ μ.real (⋃ i ∈ Finset.range k, Bn i)) atTop
      (𝓝 (μ.real (⋃ i, Bn i))) := by
      change Tendsto (fun n ↦ (μ (⋃ i ∈ Finset.range (n), Bn i)).toReal)
        atTop (𝓝 ((μ (⋃ i, Bn i)).toReal))
      rw [← tendsto_add_atTop_iff_nat 1]
      simpa [ENNReal.tendsto_toReal_iff] using tendsto_measure_iUnion_accumulate
    refine birkhoffAverage_tendsto_of_tendstoUniformly (p:=atTop) ?_
      (Eventually.of_forall hBnTendsto') (Tendsto.const_mul (μ.real s) h3)
    refine Metric.tendstoUniformly_of_dist_le_tendsto_zero
      (u:=fun n ↦ μ.real (symmDiff (⋃ i, Bn i) (⋃ i ∈ Finset.range n, Bn i))) (fun n x ↦ ?_) ?_
    · rw [← preimage_iterate_eq]
      apply le_trans
      · apply abs_measureReal_sub_le_measureReal_symmDiff
        · apply MeasurableSet.nullMeasurableSet
          apply MeasurableSet.inter hs
          exact hMP.iterate x|>.measurable <|MeasurableSet.iUnion hBnmeas
        · apply MeasurableSet.nullMeasurableSet
          apply MeasurableSet.inter hs
          exact hMP.iterate x|>.measurable <|Finset.measurableSet_biUnion (Finset.range n)
            (fun _ ↦ hBnmeas ·)
      rw [← inter_symmDiff_distrib_left]
      apply le_trans <|measureReal_mono inter_subset_right
      rw [← preimage_symmDiff]
      rw [← map_measureReal_apply (hMP.iterate x|>.measurable)
        <|MeasurableSet.symmDiff (MeasurableSet.iUnion hBnmeas)
        <|Finset.measurableSet_biUnion (Finset.range n) (fun _ ↦ hBnmeas ·)]
      rw [hMP.iterate x|>.map_eq]
    · simpa only [fun n ↦ symmDiff_of_ge
        <|iUnion₂_subset_iUnion (Membership.mem (Finset.range n)) Bn,
        fun n ↦ measureReal_diff (μ:=μ)
        (iUnion₂_subset_iUnion (Membership.mem (Finset.range n)) Bn)
        (Finset.measurableSet_biUnion (Finset.range n) (fun _ ↦ hBnmeas ·)),
        ← sub_self (μ.real (⋃ i, Bn i))] using Filter.Tendsto.const_sub _ h3

theorem onAverageIndependent_imp_ergodic [IsProbabilityMeasure μ] (hM : Measurable f)
    (h : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B → OnAverageIndependent A B f μ) :
    Ergodic f μ := by
  unfold OnAverageIndependent at h
  simp_all only [measureReal_def]
  simp only [← ENNReal.toReal_mul] at h
  refine ⟨⟨hM, ?_⟩, ⟨fun B hB hBi ↦ ?_⟩⟩
  · -- seperate lemma?
    specialize h Set.univ MeasurableSet.univ
    ext S hS
    rw [Measure.map_apply hM hS]
    have h' := h (f ⁻¹' S) (hM hS)
    specialize h S hS
    simp_all only [Set.univ_inter, measure_univ, one_mul]
    have : Bornology.IsBounded (Set.range μ.real) := by
      apply Metric.isBounded_range_iff.mpr
      use 1+1
      intro A B
      have h1 : dist (μ.real A) 0 ≤ 1 := by
        rw [Real.dist_0_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
      have h5 : dist 0 (μ.real B) ≤ 1 := by
        rw [dist_comm, Real.dist_0_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
      apply le_trans <|dist_triangle (μ.real A) 0 (μ.real B)
      · apply add_le_add
        <;> simpa [dist_comm 0, abs_of_nonneg measureReal_nonneg] using measureReal_le_one
    have hgf1 := tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ this (Set.preimage f) S
    have hgf2 := Filter.Tendsto.sub h' h
    have := Eq.symm (tendsto_nhds_unique hgf1 hgf2)
    apply eq_of_sub_eq_zero at this
    exact measureReal_eq_measureReal_iff (measure_ne_top μ (f ⁻¹' S)) (measure_ne_top μ S)|>.mp this
  specialize h Bᶜ (MeasurableSet.compl hB) B hB
  have h := tendsto_nhds_unique
    (Function.IsFixedPt.tendsto_birkhoffAverage ℝ hBi (fun S ↦ (μ (Bᶜ ∩ S)).toReal)) h
  simp only [Set.compl_inter_self, measure_empty, ENNReal.toReal_zero, ENNReal.toReal_mul,
    zero_eq_mul] at h
  apply Filter.eventuallyConst_iff_exists_eventuallyEq.mpr
  cases h with
  | inl h =>
    use True
    apply MeasureTheory.mem_ae_iff.mp
    simp only [eq_iff_iff, iff_true]
    exact (measureReal_eq_zero_iff (measure_ne_top μ Bᶜ)).mp h
  | inr h =>
    use False
    apply MeasureTheory.mem_ae_iff.mp
    simp only [eq_iff_iff, iff_false]
    change μ Bᶜᶜ = 0
    simp only [compl_compl]
    exact (measureReal_eq_zero_iff (measure_ne_top μ B)).mp h

theorem ergodic_imp_onAverageIndependent [IsProbabilityMeasure μ]
    (h : Ergodic f μ) (A : Set α) (hA : MeasurableSet A) (B : Set α)
    (hB : MeasurableSet B) : OnAverageIndependent A B f μ := by
  unfold OnAverageIndependent
  simp_all only [Measure.real_def, ← ENNReal.toReal_mul]
  have := Filter.Tendsto.inner (𝕜:=ℝ)
    (tendsto_const_nhds (x:=indicatorConstLp 2 hA (measure_ne_top μ _) (1:ℂ)) (f:=atTop (α:=ℕ)))
    (tendsto_birkhoffAverage_const ℝ (indicatorConstLp 2 hB (measure_ne_top μ _) 1) h)
  simp only [integral_indicatorConstLp, Complex.real_smul, mul_one, ← indicatorConstLp_univ] at this

  rw [L2.inner_indicatorConstLp_indicatorConstLp] at this
  simp only [Set.inter_univ, Complex.inner, map_one, mul_one, Complex.ofReal_re,
    smul_eq_mul] at this
  simp only [ENNReal.toReal_mul]
  have average_lin := fun t ↦ map_birkhoffAverage ℝ ℝ
    (innerₛₗ ℝ ((indicatorConstLp 2 hA (measure_ne_top μ _) 1):Lp ℂ 2 μ))
    (Lp.compMeasurePreserving f h.toMeasurePreserving) id t
    (indicatorConstLp 2 hB (measure_ne_top μ _) 1)
  simp only [innerₛₗ_apply_apply, coe_innerₛₗ_apply, CompTriple.comp_eq] at average_lin
  rw [funext average_lin] at this
  unfold birkhoffAverage birkhoffSum at this
  simp at this

  sorry
  --simp only [compMeasurePreserving_iterate, Lp.indicatorConstLp_compMeasurePreserving,
  --  Set.preimage_iterate_eq, L2.inner_indicatorConstLp_indicatorConstLp, Complex.inner, map_one,
  --  mul_one, Complex.one_re, smul_eq_mul] at this
  --exact this

end Ergodic
