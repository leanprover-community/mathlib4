/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Riesz–Markov–Kakutani representation theorem for real-linear functionals

The Riesz–Markov–Kakutani representation theorem relates linear functionals on spaces of continuous
functions on a locally compact space to measures.

There are many closely related variations of the theorem. This file contains that proof of the
version where the space is a locally compact T2 space, the linear functionals are real and the
continuous functions have compact support.

## Main definitions

* `RealRMK.rieszMeasure`: the measure induced by a real linear positive functional.

## Main statements

* `RealRMK.integral_rieszMeasure`: the Riesz–Markov–Kakutani representation theorem for a real
linear positive functional.

## Implementation notes

The measure is defined through `rieszContent` which is for `NNReal` using the `toNNRealLinear`
version of `Λ`.

The Riesz–Markov–Kakutani representation theorem is first proved for `Real`-linear `Λ` because
equality is proven using two inequalities by considering `Λ f` and `Λ (-f)` for all functions
`f`, yet on `C_c(X, ℝ≥0)` there is no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

open scoped BoundedContinuousFunction ENNReal NNReal
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)

/-- The measure induced for `Real`-linear positive functional `Λ`, defined through `toNNRealLinear`
and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK`, while
`rieszMeasure` without namespace is for `NNReal`-linear `Λ`. -/
noncomputable def rieszMeasure := (rieszContent (toNNRealLinear Λ hΛ)).measure

/-- If `f` assumes values between `0` and `1` and the support is contained in `K`, then
`Λ f ≤ rieszMeasure K`. -/
lemma le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, ℝ)}
    (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {K : Set X} (hK : IsCompact K) (h : tsupport f ⊆ K) :
    ENNReal.ofReal (Λ f) ≤ rieszMeasure hΛ K := by
  rw [rieszMeasure, ← Compacts.coe_mk K hK, Content.measure_eq_content_of_regular
    (rieszContent (toNNRealLinear Λ hΛ)) (contentRegular_rieszContent (toNNRealLinear Λ hΛ))
    ⟨K, hK⟩, rieszContent, ENNReal.ofReal_eq_coe_nnreal (hΛ f fun x ↦ (hf x).1), ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ hΛ) ⟨K, hK⟩
    (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply monotone_of_nonneg hΛ
  intro x
  by_cases hx : x ∈ tsupport f
  · rw [coe_toRealLinearMap, toReal_apply]
    exact le_trans (hf x).2 (hg.1 x (mem_of_subset_of_mem h hx))
  · simp [image_eq_zero_of_nmem_tsupport hx]

/-- If `f` assumes values between `0` and `1` and the support is contained in `V`, then
`Λ f ≤ rieszMeasure V`. -/
lemma le_rieszMeasure_tsupport_subset {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1)
    {V : Set X} (h : tsupport f ⊆ V) : ENNReal.ofReal (Λ f) ≤ rieszMeasure hΛ V := by
  apply le_trans _ (measure_mono h)
  rw [← Compacts.coe_mk (tsupport f) f.2]
  exact le_rieszMeasure_of_isCompact_tsupport_subset hΛ hf f.hasCompactSupport subset_rfl

/-- If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`.-/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) {K : Set X}
    (hK : IsCompact K) (hfK : ∀ x ∈ K, f x = 1) : rieszMeasure hΛ K ≤ ENNReal.ofReal (Λ f) := by
  rw [show K = Compacts.mk K hK by exact rfl, rieszMeasure,
    Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ hΛ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_eq_ofReal_iff (hΛ f hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_setOf_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx => Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply, show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

/-- An `Ioc` partitions into a finite union of `Ioc`s. -/
private lemma RMK_iUnion_Ioc {N : ℕ} (hN : 0 < N) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ⋃ n : Fin N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc (c) (c + N * δ) := by
  ext x
  constructor
  · simp_rw [mem_iUnion, mem_Ioc, forall_exists_index, and_imp]
    intro n ha hb
    constructor
    · exact lt_of_le_of_lt
        ((le_add_iff_nonneg_right c).mpr <| Left.mul_nonneg (Nat.cast_nonneg' n) (le_of_lt hδ)) (ha)
    · calc
        _ ≤ c + (n + 1) * δ := by linarith
        _ ≤ _ := by field_simp [show (n : ℝ) + 1 ≤ N by norm_cast; omega]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one.mpr hN
    rw [hk]; clear hk
    induction' k with k hk
    · simp
    · rw [Nat.cast_add, Nat.cast_one]; rw [Nat.cast_add, Nat.cast_one] at hk
      rcases (le_or_lt x (c + (k + 1) * δ)) with hc | hc
      · rw [Nat.cast_add, Nat.cast_one, mem_Ioc, mem_iUnion, and_imp]
        intro hx hx'
        rw [mem_Ioc, mem_iUnion, and_imp] at hk
        obtain ⟨i, hi⟩ := hk hx hc
        use i; norm_cast
      · rw [Nat.cast_add, Nat.cast_one, mem_Ioc, mem_iUnion, and_imp]
        intro hx hx'
        use ⟨k + 1, by omega⟩
        push_cast
        exact ⟨hc, by linarith [hx']⟩

omit [T2Space X] [LocallyCompactSpace X] in
/-- Given `f : C_c(X, ℝ)` such that `range f ⊆ [a, b]` we obtain a partition of the support of `f`
determined by partitioning `[a, b]` into `N` pieces. -/
private lemma RMK_range_cut (f : C_c(X, ℝ)) (a : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : 0 < N) (hf : range f ⊆ Ioo a (a + N * ε)) : ∃ (E : Fin N → Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (∀ n : Fin N, ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1)) ∧
    ∀ n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N → ℝ := fun n => a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε ≤ y m := calc
    _ ≤ a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E : Fin N → Set X := fun n => (f ⁻¹' Ioc (y n - ε) (y n)) ∩ (tsupport f)
  use E
  -- Upper and lower bound on `f x` follow from the definition of `E n` .
  have bdd (n : Fin N) : ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1) := by
    intro x hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  -- The sets `E n` are pairwise disjoint.
  have disjoint : PairwiseDisjoint univ E := by
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_setOf_eq, and_assoc] at hx
    simp_rw [mem_setOf_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by omega : m < n ∨ n < m) with hc | hc
    · left;
      exact le_trans  hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left;
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  -- The sets `E n` are a partition of the support of `f`.
  have partition_aux: range f ⊆ ⋃ n, Ioc (y n - ε) (y n) := by
    intro z hz
    simp_rw [show ∀ n, y n - ε = (a + n * ε) by simp [y, mul_add, ← add_assoc, mul_comm],
      show ∀ n, y n = a + n * ε + ε by simp [y, mul_add, ← add_assoc, mul_comm]]
    rw [RMK_iUnion_Ioc hN a hε, mem_Ioc]
    exact ⟨(hf hz).1, le_of_lt (hf hz).2⟩
  have partition : tsupport f = ⋃ j, E j := by
    apply subset_antisymm
    · intro x hx
      simp_rw [E, mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right]
      obtain ⟨j, hj⟩ := mem_iUnion.mp <| mem_of_subset_of_mem partition_aux (mem_range_self x)
      constructor
      · use j
      · exact hx
    · exact iUnion_subset (show ∀ n, E n ⊆ tsupport f by simp [inter_subset_right, E])
  exact ⟨partition, disjoint, fun n x a ↦ bdd n x a,
    fun _ ↦ (f.1.measurable measurableSet_Ioc).inter measurableSet_closure⟩

omit [LocallyCompactSpace X] in
/-- Given a set `E`, a function `f : C_c(X, ℝ)` and `0 < ε` and `∀ x ∈ E, f x < c`, there exists an
open set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V, f x < c`. -/
private lemma RMK_open (f : C_c(X, ℝ)) {ε : ℝ} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E ≠ ⊤) (hμ' : MeasurableSet E) {c : ℝ} (hfE : ∀ x ∈ E, f x < c):
    ∃ (V : Opens X), E ⊆ V ∧ (∀ x ∈ V, f x < c) ∧ μ.measure V ≤ μ.measure E + ENNReal.ofReal ε := by
  have hε' := ne_of_gt <| Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  have h x (hx : x ∈ V₁ ⊓ V₂) : f x < c := by
    suffices ∀ x ∈ V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun  _ hx ↦ hx
  have h' : μ.measure ↑(V₁ ⊓ V₂) ≤ μ.measure E + ENNReal.ofReal ε := calc
      _ ≤ μ.measure V₁ := by apply measure_mono; simp
      _ = μ.outerMeasure V₁ := by rw [Content.measure_apply μ ?_]; exact V₁.2.measurableSet
      _ ≤ μ.outerMeasure E + ε.toNNReal := by exact hV₁.2
      _ = _ := by rw [Content.measure_apply μ ?_]; congr; exact hμ'
  exact ⟨subset_inter hV₁.1 hfE, h, h'⟩

omit [LocallyCompactSpace X] in
/- Define simultaneously sets which are each open approximations and obtain particular estimates. -/
private lemma RMK_open' {N : ℕ} (hN : 0 < N) (E : Fin N → Set X) (f : C_c(X, ℝ)) {y : Fin N → ℝ}
    (hy : ∀ n, ∀ x ∈ E n, f x ≤ y n) {ε : ℝ} (hε : 0 < ε) {ν : Content X}
    (hν : ∀ n, ν.measure (E n) ≠ ⊤) (hν' : ∀ n, MeasurableSet (E n)) :
    ∃ V : Fin N → Opens X, ∀ n, E n ⊆ (V n) ∧ (∀ x ∈ V n, f x < y n + ε)
    ∧ ν.measure (V n) ≤ ν.measure (E n) + ENNReal.ofReal (ε / N) := by
  have h (n : Fin N) (x : X) (hx : x ∈ E n) := lt_add_of_le_of_pos (hy n x hx) hε
  have h' (n : Fin N) : ν.outerMeasure (E n) ≠ ⊤ := by
    rw [← Content.measure_apply ν (hν' n)]
    exact hν n
  let V (n : Fin N) := Classical.choose <|
    RMK_open f (div_pos hε (Nat.cast_pos'.mpr hN)) (E n) (h' n) (hν' n) (h n)
  use V
  intro n
  let hV := Classical.choose_spec <|
    RMK_open f (div_pos hε (Nat.cast_pos'.mpr hN)) (E n) (h' n) (hν' n) (h n)
  exact ⟨hV.1, hV.2.1, hV.2.2⟩

/-- Choose `N` sufficiently large such that a particular quantity is small. -/
private lemma RMK_exists_nat (a' b' : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 0 < N ∧
    a' / N * (b' + a' / N) ≤ ε := by
  have A : Tendsto (fun (N : ℝ) ↦ a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε ).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

/-- The main estimate in the proof of the Riesz-Markov-Kakutani: `Λ f` is bounded above by the
integral of `f` with respect to the `rieszMeasure` associated to `L`. -/
private lemma RMK_le (f : C_c(X, ℝ)) : Λ f ≤ ∫ (x : X), f x ∂(rieszMeasure hΛ) := by
  by_cases hX : IsEmpty X
  -- The case `IsEmpty X` is elementry.
  · have : Λ f = 0 := by rw [show f = 0 by ext x; refine isEmptyElim x, LinearMap.map_zero Λ]
    rw [integral_of_isEmpty, this]
  -- Now assuming `Nonempty X`
  · rw [not_isEmpty_iff] at hX
    let μ := rieszMeasure hΛ
    let K := tsupport f
    -- Suffices to show that `Λ f ≤ ∫ (x : X), f x ∂μ + ε` for arbitrary `ε`.
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    -- Choose an interval `(a, b)` which contains the range of `f`.
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, a < b ∧ range f ⊆ Ioo a b := by
      obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
        (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
      exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
    -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
    obtain ⟨N, hN, hε'⟩ := RMK_exists_nat (b - a) (2 * (μ K).toReal + |a| + b) hε
    let ε' := (b - a) / N
    replace hε' : 0 < ε' ∧  ε' * (2 * (μ K).toReal + |a| + b + ε') ≤ ε :=
      ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
    -- Take a partition of the support of `f` into sets `E` by partitioning the range.
    obtain ⟨E, hE⟩ := RMK_range_cut f a hε'.1 hN (by field_simp [ε', ← mul_div_assoc,
      mul_div_cancel_left₀, hab.2])
    -- Introduce notation for the partition of the range.
    let y : Fin N → ℝ := fun n ↦ a + ε' * (n + 1)
    -- The measure of each `E n` is finite.
    have hE' (n : Fin N) : μ (E n) ≠ ⊤ := by
      have h : E n ⊆ tsupport f := by rw [hE.1]; exact subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a
      refine lt_top_iff_ne_top.mp ?_
      apply lt_of_le_of_lt <| measure_mono h
      dsimp [μ]
      rw [rieszMeasure, show f = f.toFun by rfl, Content.measure_apply _ f.2.measurableSet]
      exact Content.outerMeasure_lt_top_of_isCompact _ f.2
    -- Define sets `V` which are open approximations to the sets `E`
    obtain ⟨V, hV⟩ := RMK_open' hN E f (fun n x hx ↦ (hE.2.2.1 n x hx).right) hε'.1 hE' hE.2.2.2
    -- Define a partition of unity subordinated to the sets `V`
    obtain ⟨g, hg⟩ : ∃ (g : Fin N → C_c(X, ℝ)), (∀ n, tsupport (g n) ⊆ (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (∀ n x, (g n) x ∈ Icc 0 1) ∧
      ∀ n, HasCompactSupport (g n) := by
      have : tsupport f ⊆ ⋃ n, (V n).carrier := calc
        _ = ⋃ j, E j := hE.1
        _ ⊆ _ := by gcongr with n; exact (hV n).1
      obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n => (V n).2) f.2 this
      exact ⟨fun n ↦ ⟨g' n, hg.2.2.2 n⟩, hg⟩
    -- The proof is completed by a chain of inequalities.
    calc Λ f
      _ = Λ (∑ n, g n • f) := ?_
      _ = ∑ n, Λ (g n • f) := by simp
      _ ≤ ∑ n, Λ ((y n + ε') • g n) := ?_
      _ ≤ ∑ n, (y n + ε') * Λ (g n) := by simp
      -- That `y n + ε'` can be negative is bad the inequalities, so we artifically include `|a|`.
      _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) :=
        by simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ n, (|a| + y n + ε') * ((μ (E n)).toReal + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
      _ ≤ ∑ n, (|a| + y n + ε') * ((μ (E n)).toReal + ε' / N) - |a| * (μ K).toReal := ?_
      _ = ∑ n, (y n - ε') * (μ (E n)).toReal +
        2 * ε' * (μ K).toReal + ε' / N * ∑ n, (|a| + y n + ε') := ?_
      _ ≤ ∫ (x : X), f x ∂μ + 2 * ε' * (μ K).toReal + ε' / N * ∑ n, (|a| + y n + ε') := ?_
      _ ≤ ∫ (x : X), f x ∂μ + ε' * (2 * (μ K).toReal + |a| + b + ε') := ?_
      _ ≤ ∫ (x : X), f x ∂μ + ε := by simp [hε'.2]
    · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
      congr; ext x
      simp only [coe_sum, coe_smulc, smul_eq_mul, Finset.sum_apply, coe_mul, Pi.mul_apply,
        ← Finset.sum_mul, ← Finset.sum_apply]
      by_cases hx : x ∈ tsupport f
      · simp [hg.2.1 hx]
      · simp [image_eq_zero_of_nmem_tsupport hx]
    · -- use that `f ≤ y n + ε'` on `V n`
      gcongr with n hn
      apply monotone_of_nonneg hΛ
      intro x
      simp only [smul_eq_mul, coe_mul, Pi.mul_apply, coe_smul, Pi.smul_apply]
      by_cases hx : x ∈ tsupport (g n)
      · rw [mul_comm]
        apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
        exact le_of_lt <| (hV n).2.1 x <| mem_of_subset_of_mem (hg.1 n) hx
      · simp [image_eq_zero_of_nmem_tsupport hx]
    · -- use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
      gcongr with n hn
      · calc
          _ ≤ |a| + a := neg_le_iff_add_nonneg'.mp <| neg_abs_le a
          _ ≤ |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr <| Left.mul_nonneg
           (le_of_lt hε'.1) <| Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)
          _ ≤ _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
      · calc
          _ ≤ (μ (V n)).toReal := by
            apply (ENNReal.ofReal_le_iff_le_toReal _).mp
            · refine le_rieszMeasure_tsupport_subset hΛ ?_ (hg.1 n)
              exact fun x ↦ hg.2.2.1 n x
            · rw [← lt_top_iff_ne_top]
              apply lt_of_le_of_lt (hV n).2.2
              rw [WithTop.add_lt_top]
              exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
          _ ≤ _ := by
            rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
            apply ENNReal.toReal_le_add (hV n).2.2
            · exact hE' n
            · exact ENNReal.ofReal_ne_top
    · -- use that `μ K ≤ Λ (∑ n, g n)`
      gcongr
      rw [Eq.symm (map_sum Λ g _)]
      have h x : 0 ≤ (∑ n, g n) x := by
        rw [coe_sum, Finset.sum_apply]
        exact Fintype.sum_nonneg fun n ↦ (hg.2.2.1 n x).1
      have h' x (hx : x ∈ K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      apply ENNReal.toReal_le_of_le_ofReal
      · exact hΛ (∑ n, g n) (fun x ↦ h x)
      · exact rieszMeasure_le_of_eq_one hΛ h f.2 h'
    · -- Rearrange the sums
      simp_rw [mul_add]
      have (n : Fin N) : (|a| + y n + ε') * (μ (E n)).toReal =
          (|a| + 2 * ε') * (μ (E n)).toReal + (y n - ε') * (μ (E n)).toReal := by linarith
      simp_rw [this]
      have : ∑ i, (μ (E i)).toReal = (μ K).toReal := by
        suffices h : μ K = ∑ i, (μ (E i)) by
          rw [h]; exact Eq.symm <| ENNReal.toReal_sum <| fun n _ ↦ hE' n
        dsimp [K]; rw [hE.1]
        rw [measure_iUnion (fun m n hmn ↦ hE.2.1 trivial trivial hmn) hE.2.2.2]
        exact tsum_fintype fun b ↦ μ (E b)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, this, ← Finset.sum_mul]
      linarith
    · -- use that `y n - ε' ≤ f x` on `E n`
      gcongr
      suffices h : ∀ n, (y n - ε') * (μ (E n)).toReal ≤ ∫ x in (E n), f x ∂μ by
        calc
          _ ≤ ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a ↦ h i
          _ = ∫ x in (⋃ n, E n), f x ∂μ := by
            apply Eq.symm
            apply integral_fintype_iUnion hE.2.2.2 (fun ⦃i j⦄ ↦ hE.2.1 trivial trivial)
            refine fun _ ↦ Integrable.integrableOn ?_
            dsimp [μ, rieszMeasure]
            exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
          _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
          _ = _ := setIntegral_tsupport
      intro n
      apply setIntegral_ge_of_const_le (hE.2.2.2 n)
      · dsimp [μ]; push_neg
        rw [rieszMeasure, Content.measure_apply _ (hE.2.2.2 n), ← lt_top_iff_ne_top]
        have := le_of_le_of_eq (subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a) (Eq.symm hE.1)
        apply lt_of_le_of_lt (OuterMeasure.mono _ this)
        exact Content.outerMeasure_lt_top_of_isCompact _ f.2
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    · -- Rough bound of the sum
      rw [mul_comm 2 ε', show ε' / N = ε' * 1 / N by rw [mul_one], mul_assoc, mul_div_assoc,
        mul_assoc, add_assoc, ← mul_add]
      simp_rw [add_assoc |a|, add_comm (y _) ε', ← add_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add,
        nsmul_eq_mul, nsmul_eq_mul, ← mul_add, mul_add (1 / _), mul_comm (1 / _), mul_one_div,
        mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr <| Nat.not_eq_zero_of_lt hN), add_assoc _ ε',
        show 2 * (μ K).toReal + |a| + b + ε' = 2 * (μ K).toReal + |a| + ε' + b by linarith,
        ← add_assoc, ← add_assoc]
      gcongr
      · exact le_of_lt hε'.1
      · have h : ∑ n : Fin N, y n ≤ N * b := by
          have (n : Fin N) := calc y n
            _ ≤ a + ε' * N := by simp_all [y, show (n : ℝ) + 1 ≤ N by norm_cast; omega]
            _ = b := by field_simp [ε', ← mul_div_assoc, mul_div_cancel_left₀]
          have : ∑ n, y n ≤ ∑ n, b := Finset.sum_le_sum (fun n ↦ fun _ ↦ this n)
          simp_all
        calc
          _ ≤ 1 / N * (N * b) := by simp [h, hN]
          _ ≤ _ := by simp [div_mul_cancel₀, Nat.cast_ne_zero.mpr <| Nat.not_eq_zero_of_lt hN]

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal to `Λ f`. -/
theorem integral_rieszMeasure (f : C_c(X, ℝ)) : ∫ (x : X), f x ∂(rieszMeasure hΛ) = Λ f := by
  -- `RMK_le` tells that `Λ f ≤ ∫ (x : X), f x ∂(rieszMeasure hΛ)`, we apply this to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = ∫ (x : X), -(-f) x ∂(rieszMeasure hΛ) := by
        simp only [coe_neg, Pi.neg_apply, neg_neg]
      _ = - ∫ (x : X), (-f) x ∂(rieszMeasure hΛ) := integral_neg' (-f)
      _ ≤ - Λ (-f) := neg_le_neg (RMK_le hΛ (-f))
      _ = Λ (- -f) := Eq.symm (LinearMap.map_neg Λ (- f))
      _ = _ := by rw [neg_neg]
  -- prove the inequality for `f`
  · exact RMK_le hΛ f

end RealRMK
