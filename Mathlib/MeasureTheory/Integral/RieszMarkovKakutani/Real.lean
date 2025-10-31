/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.Order.Interval.Set.Union

/-!
# Riesz–Markov–Kakutani representation theorem for real-linear functionals

The Riesz–Markov–Kakutani representation theorem relates linear functionals on spaces of continuous
functions on a locally compact space to measures.

There are many closely related variations of the theorem. This file contains that proof of the
version where the space is a locally compact T2 space, the linear functionals are real and the
continuous functions have compact support.

## Main definitions & statements

* `RealRMK.rieszMeasure`: the measure induced by a real linear positive functional.
* `RealRMK.integral_rieszMeasure`: the Riesz–Markov–Kakutani representation theorem for a real
  linear positive functional.
* `RealRMK.rieszMeasure_integralPositiveLinearMap`: the uniqueness of the representing measure in
  the Riesz–Markov–Kakutani representation theorem.

## Implementation notes

The measure is defined through `rieszContent` which is for `NNReal` using the `toNNRealLinear`
version of `Λ`.

The Riesz–Markov–Kakutani representation theorem is first proved for `Real`-linear `Λ` because
equality is proven using two inequalities by considering `Λ f` and `Λ (-f)` for all functions
`f`, yet on `C_c(X, ℝ≥0)` there is no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

open scoped ENNReal
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

/-- The measure induced for `Real`-linear positive functional `Λ`, defined through `toNNRealLinear`
and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK`, while
`rieszMeasure` without namespace is for `NNReal`-linear `Λ`. -/
noncomputable def rieszMeasure := (rieszContent (toNNRealLinear Λ)).measure

/-- If `f` assumes values between `0` and `1` and the support is contained in `V`, then
`Λ f ≤ rieszMeasure V`. -/
lemma le_rieszMeasure_tsupport_subset {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1)
    {V : Set X} (hV : tsupport f ⊆ V) : ENNReal.ofReal (Λ f) ≤ rieszMeasure Λ V := by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ))
    (contentRegular_rieszContent (toNNRealLinear Λ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport, rieszMeasure, this, rieszContent,
    ENNReal.ofReal_eq_coe_nnreal (Λ.map_nonneg fun x ↦ (hf x).1), Content.mk_apply,
    ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine (Λ.mono ?_).trans hg.2.le
  intro x
  by_cases hx : x ∈ tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`. -/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) {K : Set X}
    (hK : IsCompact K) (hfK : ∀ x ∈ K, f x = 1) : rieszMeasure Λ K ≤ ENNReal.ofReal (Λ f) := by
  rw [← Compacts.coe_mk K hK, rieszMeasure,
    Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_eq_ofReal_iff (Λ.map_nonneg hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_setOf_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx ↦ Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply, show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in
/-- Given `f : C_c(X, ℝ)` such that `range f ⊆ [a, b]` we obtain a partition of the support of `f`
determined by partitioning `[a, b]` into `N` pieces. -/
lemma range_cut_partition (f : C_c(X, ℝ)) (a : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hf : range f ⊆ Ioo a (a + N * ε)) : ∃ (E : Fin N → Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (∀ n : Fin N, ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1)) ∧
    ∀ n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N → ℝ := fun n ↦ a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε ≤ y m := calc
    _ ≤ a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) ∩ (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f ⊆ ⋃ n, Ioc (y n - ε) (y n) := calc
      _ ⊆ Ioc (a + (0 : ℕ) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ ⊆ ⋃ i ∈ Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n ↦ a + n * ε)
      _ ⊆ _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ ↦ ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ ↦ partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_setOf_eq, and_assoc] at hx
    simp_rw [mem_setOf_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by cutsat : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ ↦ (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in
/-- Given a set `E`, a function `f : C_c(X, ℝ)`, `0 < ε` and `∀ x ∈ E, f x < c`, there exists an
open set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V, f x < c`. -/
lemma exists_open_approx (f : C_c(X, ℝ)) {ε : ℝ} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E ≠ ∞) (hμ' : MeasurableSet E) {c : ℝ} (hfE : ∀ x ∈ E, f x < c) :
    ∃ (V : Opens X), E ⊆ V ∧ (∀ x ∈ V, f x < c) ∧ μ.measure V ≤ μ.measure E + ENNReal.ofReal ε := by
  have hε' := ne_of_gt <| Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices ∀ x ∈ V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a ↦ a
  · calc
      _ ≤ μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ ≤ μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ', ENNReal.ofNNReal_toNNReal]

/-- Choose `N` sufficiently large such that a particular quantity is small. -/
private lemma exists_nat_large (a' b' : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 0 < N ∧
    a' / N * (b' + a' / N) ≤ ε := by
  have A : Tendsto (fun (N : ℝ) ↦ a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

/-- The main estimate in the proof of the Riesz-Markov-Kakutani: `Λ f` is bounded above by the
integral of `f` with respect to the `rieszMeasure` associated to `Λ`. -/
private lemma integral_riesz_aux (f : C_c(X, ℝ)) : Λ f ≤ ∫ x, f x ∂(rieszMeasure Λ) := by
  let μ := rieszMeasure Λ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, a < b ∧ range f ⊆ Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * μ.real K + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧  ε' * (2 * μ.real K + |a| + b + ε') ≤ ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
  obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N <| by
    dsimp [ε']
    field_simp
    simp [hab.2]
  -- Introduce notation for the partition of the range.
  let y : Fin N → ℝ := fun n ↦ a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) ≠ ∞ := by
    have h : E n ⊆ tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
    apply lt_of_le_of_lt <| measure_mono h
    dsimp [μ]
    rw [rieszMeasure, ← coe_toContinuousMap, ← ContinuousMap.toFun_eq_coe,
      Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : ∃ V : Fin N → Opens X, ∀ n, E n ⊆ (V n) ∧ (∀ x ∈ V n, f x < y n + ε') ∧
      μ (V n) ≤ μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x ∈ E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n ↦ exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : ∃ g : Fin N → C_c(X, ℝ), (∀ n, tsupport (g n) ⊆ (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (∀ n x, (g n) x ∈ Icc 0 1) ∧
      ∀ n, HasCompactSupport (g n) := by
    have : tsupport f ⊆ ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ ⊆ _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n ↦ (V n).2) f.2 this
    exact ⟨fun n ↦ ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ ≤ ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artificially include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) :=
      by simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ ≤ ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * μ.real K := ?_
    _ = ∑ n, (y n - ε') * μ.real (E n) +
      2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + 2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + ε' * (2 * μ.real K + |a| + b + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, smul_eq_mul, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    intro x
    by_cases hx : x ∈ tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
      exact le_of_lt <| (hV n).2.1 x <| mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
        _ ≤ |a| + a := neg_le_iff_add_nonneg'.mp <| neg_abs_le a
        _ ≤ |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr <| Left.mul_nonneg
          (le_of_lt hε'.1) <| Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)
        _ ≤ _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ ≤ μ.real (V n) := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset Λ (fun x ↦ hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ ≤ _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2 (hE' n)
          · finiteness
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [← map_sum Λ g _]
    have h x : 0 ≤ (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n ↦ (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact Λ.map_nonneg (fun x ↦ h x)
    · have h' x (hx : x ∈ K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one Λ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * μ.real (E n) =
        (|a| + 2 * ε') * μ.real (E n) + (y n - ε') * μ.real (E n) := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, μ.real (E i) = μ.real K := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        simp only [measureReal_def, h]
        exact Eq.symm <| ENNReal.toReal_sum <| fun n _ ↦ hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn ↦ hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b ↦ μ (E b)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, this, ← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : ∀ n, (y n - ε') * μ.real (E n) ≤ ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ ≤ ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a ↦ h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
        refine Eq.symm <| integral_iUnion_fintype hE.2.2.2 (fun _ _ ↦ hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ ↦
          Integrable.integrableOn <| Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n ≤ N * b := by
      have (n : Fin N) := calc y n
        _ ≤ a + ε' * N := by simp_all [y, show (n : ℝ) + 1 ≤ N by norm_cast; cutsat]
        _ = b := by simp [field, ε']
      have : ∑ n, y n ≤ ∑ n, b := Finset.sum_le_sum (fun n ↦ fun _ ↦ this n)
      simp_all
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : ℝ) ≠ 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
      using (mul_le_mul_iff_of_pos_left hε'.1).mpr <| (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal to `Λ f`. -/
@[simp]
theorem integral_rieszMeasure (f : C_c(X, ℝ)) : ∫ x, f x ∂(rieszMeasure Λ) = Λ f := by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure Λ) := by simpa using integral_neg' (-f)
      _ ≤ - Λ (-f) := neg_le_neg (integral_riesz_aux Λ (-f))
      _ = _ := by simp
  -- prove the inequality for `f`
  · exact integral_riesz_aux Λ f

/-- The Riesz measure induced by a positive linear functional on `C_c(X, ℝ)` is regular. -/
instance regular_rieszMeasure : (rieszMeasure Λ).Regular :=
  (rieszContent _).regular

section integralPositiveLinearMap

variable {μ ν : Measure X}

/-! We show that `RealRMK.rieszMeasure` is a bijection between positive linear functionals on
`C_c(X, ℝ)` and regular measures with inverse `RealRMK.integralPositiveLinearMap`. -/

/-- Note: the assumption `IsFiniteMeasureOnCompacts μ` cannot be removed. For example, if
`μ` is infinite on any nonempty set and `ν = 0`, then the hypotheses are satisfied. -/
lemma measure_le_of_isCompact_of_integral [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ]
    (hμν : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    ⦃K : Set X⦄ (hK : IsCompact K) : μ K ≤ ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
  have hνK : ν K ≠ ⊤ := hν.ne
  have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : ∃ V ⊇ K, IsOpen V ∧ ν V ≤ ν K + ε :=
    exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices μ.real K ≤ ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  have VltTop : ν V < ⊤ := pV3.trans_lt <| by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      ∃ f : C_c(X, ℝ), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧ ∀ (x : X), f x ∈ Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuous_one_of_compact_subset_open hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
    μ.real K = ∫ x, K.indicator 1 x ∂μ := integral_indicator_one hK.measurableSet |>.symm
    _ ≤ ∫ x, f x ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ ≤ ∫ x, f x ∂ν := hμν f
    _ ≤ ∫ x, V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact integrableOn_const.integrable_indicator pV2.measurableSet
    _ ≤ (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

/-- If two regular measures give the same integral for every function in `C_c(X, ℝ)`,
then they are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    [μ.Regular] [ν.Regular] (hμν : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply Measure.OuterRegular.eq_of_eq_on_isOpen
  apply Measure.InnerRegularWRT.eq_on_outer_of_eq_on_inner Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact measure_le_of_isCompact_of_integral (fun f ↦ (hμν f).le) hK
  · exact measure_le_of_isCompact_of_integral (fun f ↦ (hμν f).ge) hK

/-- Two regular measures are equal iff they induce the same positive linear functional
on `C_c(X, ℝ)`. -/
theorem integralPositiveLinearMap_inj [μ.Regular] [ν.Regular] :
    integralPositiveLinearMap μ = integralPositiveLinearMap ν ↔ μ = ν where
  mp hμν := Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ congr($hμν f)
  mpr _ := by congr

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ)`.
That is, `RealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
theorem rieszMeasure_integralPositiveLinearMap [μ.Regular] :
    rieszMeasure (integralPositiveLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported (by simp)

@[simp]
theorem integralPositiveLinearMap_rieszMeasure :
    integralPositiveLinearMap (rieszMeasure Λ) = Λ := by ext; simp

end integralPositiveLinearMap

end RealRMK
