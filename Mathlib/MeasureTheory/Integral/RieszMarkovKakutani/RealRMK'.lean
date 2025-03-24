/-
Copyright (c) 2024 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley
-/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
#  Riesz–Markov–Kakutani representation theorem for real-linear functionals

This file will prove the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `Real`-linear functionals `Λ`.

The measure is first defined through `rieszContent` for `toNNRealLinear`-version of `Λ`.
The result is first proved for `Real`-linear `Λ` because in a standard proof one has to prove the
inequalities by considering `Λ f` and `Λ (-f)` for all functions `f`, yet on `C_c(X, ℝ≥0)` there is
no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)

namespace RealRMK

section PositiveLinear

/-- The positivity of `Λ` implies that `Λ` is monotone. -/
lemma monotone_of_nonneg (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) : Monotone Λ := by
  intro f₁ f₂ h
  have : 0 ≤ Λ (f₂ - f₁) := by
    apply hΛ
    intro x
    simp only [coe_zero, Pi.zero_apply, coe_sub, Pi.sub_apply, sub_nonneg]
    exact h x
  calc
    _ ≤ Λ f₁ + Λ (f₂ - f₁) := (le_add_iff_nonneg_right (Λ f₁)).mpr this
    _ = Λ (f₁ + (f₂ - f₁)) := Eq.symm (LinearMap.map_add Λ f₁ (f₂ - f₁))
    _ = _ := by congr; exact add_sub_cancel f₁ f₂

end PositiveLinear

section RealRMK

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The measure induced for `Real`-linear positive functional `Λ`, defined through `toNNRealLinear`
  and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK`, while
  `rieszMeasure` without namespace is for `NNReal`-linear `Λ`. -/
def rieszMeasure := (rieszContent (toNNRealLinear Λ hΛ)).measure

/-- If `f` assumes values between `0` and `1` and the support is contained in `K`, then
  `Λ f ≤ rieszMeasure K`. -/
lemma le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, ℝ)}
    (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {K : Set X} (hK : IsCompact K) (h : tsupport f ⊆ K) :
    ENNReal.ofReal (Λ f) ≤ rieszMeasure hΛ K := by
  have Lfnonneg : 0 ≤ Λ f := by
    apply hΛ
    intro x
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply, coe_toContinuousMap]
    exact (hf x).1
  rw [rieszMeasure, ← Compacts.coe_mk K hK, MeasureTheory.Content.measure_eq_content_of_regular
    (rieszContent (toNNRealLinear Λ hΛ)) (contentRegular_rieszContent (toNNRealLinear Λ hΛ))
    ⟨K, hK⟩, rieszContent]
  simp only [ENNReal.ofReal_eq_coe_nnreal Lfnonneg, ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ hΛ) ⟨K, hK⟩
    (Real.toNNReal_pos.mpr hε)
  simp only [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply monotone_of_nonneg hΛ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · simp only [coe_toRealLinearMap, toReal_apply]
    exact le_trans (hf x).2 (hg.1 x (mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    simp

/-- If `f` assumes values between `0` and `1` and the support is contained in `V`, then
`Λ f ≤ rieszMeasure V`. -/
lemma le_rieszMeasure_of_isOpen_tsupport_subset {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1)
    {V : Set X} (h : tsupport f ⊆ V) : ENNReal.ofReal (Λ f) ≤ rieszMeasure hΛ V := by
  apply le_trans _ (measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply le_rieszMeasure_of_isCompact_tsupport_subset hΛ hf
  · simp only [Compacts.coe_mk]
    exact f.hasCompactSupport
  · exact subset_rfl

/-- If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`.-/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) {K : Set X}
    (hK : IsCompact K) (hfK : ∀ x ∈ K, f x = 1) : rieszMeasure hΛ K ≤ ENNReal.ofReal (Λ f) := by
  -- The definition of `rieszMeasure` is based on `rieszContentAux`:
  -- `def rieszContentAux : Compacts X → ℝ≥0 := fun K =>`
  -- `  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })`
  -- Consequently this result should follow from `rieszContentAux_le`.
  sorry

/-- An `Ioc` partitions into a finite union of `Ioc`s. -/
lemma iUnion_Fin_Ioc {N : ℕ} (hN : 0 < N) (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ⋃ n : Fin N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc (c) (c + N * δ) := by
  ext x
  constructor
  · simp only [mem_iUnion, mem_Ioc, forall_exists_index, and_imp]
    intro n ha hb
    constructor
    · calc
        _ ≤ c + n * δ := (le_add_iff_nonneg_right c).mpr <|
          Left.mul_nonneg (Nat.cast_nonneg' n) (le_of_lt hδ)
        _ < _ := ha
    · calc
        _ ≤ c + n * δ + δ := hb
        _ ≤ c + (n + 1) * δ := by ring_nf; rfl
        _ ≤ _ := by field_simp [show (n : ℝ) + 1 ≤ N by norm_cast; omega]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one.mpr hN
    rw [hk]; clear hk
    induction' k with k hk
    · simp
    · rw [Nat.cast_add, Nat.cast_one]; rw [Nat.cast_add, Nat.cast_one] at hk
      rcases (le_or_lt x (c + (↑k + 1) * δ)) with hc | hc
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
lemma range_cut_partition (f : C_c(X, ℝ)) (a : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : 0 < N) (hf : range f ⊆ Ioo a (a + N * ε)): ∃ (E : Fin N → Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (∀ n : Fin N, ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1)) ∧
    ∀ n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N → ℝ := fun n => a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε ≤ y m := calc
    _ ≤ a + ε * (m) + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; linarith
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
    simp only [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_setOf_eq, and_assoc] at hx
    simp only [mem_setOf_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by omega : m < n ∨ n < m) with hc | hc
    · left; calc
        _ ≤ y m := hx.2.1
        _ ≤ _ := le_tsub_of_add_le_right (hy hc)
    · right; left; calc
        _ ≤ y m - ε := le_tsub_of_add_le_right (hy hc)
        _ < _ := hx.1
  -- The sets `E n` are a partition of the support of `f`.
  have partition_aux: range f ⊆ ⋃ n : Fin N, Ioc (y n - ε) (y n) := by
    intro z hz
    simp_rw [show ∀ n, y n - ε = (a + n * ε) by simp [y, mul_add, ← add_assoc, mul_comm],
      show ∀ n, y n = a + n * ε + ε by simp [y, mul_add, ← add_assoc, mul_comm]]
    rw [iUnion_Fin_Ioc hN a hε, mem_Ioc]
    exact ⟨(hf hz).1, le_of_lt (hf hz).2⟩
  have partition : tsupport f = ⋃ j, E j := by
    apply subset_antisymm
    · intro x hx
      simp only [E, mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right]
      obtain ⟨j, hj⟩ := mem_iUnion.mp <| mem_of_subset_of_mem partition_aux (mem_range_self x)
      constructor
      · use j
      · exact hx
    · have (n : Fin N) : E n ⊆ tsupport f := by simp [inter_subset_right, E]
      exact iUnion_subset this
  exact ⟨partition, disjoint, fun n x a ↦ bdd n x a, fun _ ↦ MeasurableSet.inter
    ((ContinuousMap.measurable f.1) measurableSet_Ioc) measurableSet_closure⟩

omit [LocallyCompactSpace X] in
/-- Given a set `E`, a function `f : C_c(X, ℝ)` and `0 < ε` and `∀ x ∈ E, f x < c`, there exists a
  set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V, f x < c`. -/
lemma open_approx (f : C_c(X, ℝ)) {ε : ℝ} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E ≠ ⊤) (hμ' : MeasurableSet E) {c : ℝ} (hfE : ∀ x ∈ E, f x < c):
    ∃ (V : Opens X), E ⊆ V ∧ (∀ x ∈ V, f x < c) ∧ μ.measure V ≤ μ.measure E + ENNReal.ofReal ε := by
  have hε' := ne_of_gt <| Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := MeasureTheory.Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  have h : (∀ x ∈ V₁ ⊓ V₂, f x < c) := by
    suffices (∀ x ∈ V₂.carrier, f x < c) by
      exact fun x h ↦ (this x h.2)
    intro _ hx
    rw [mem_preimage, mem_Iio] at hx
    exact hx
  have h' : μ.measure ↑(V₁ ⊓ V₂) ≤ μ.measure E + ENNReal.ofReal ε := calc
      _ ≤ μ.measure V₁ := by apply measure_mono; simp
      _ = μ.outerMeasure V₁ := by
        rw [MeasureTheory.Content.measure_apply μ ?_]
        exact V₁.2.measurableSet
      _ ≤ μ.outerMeasure E + ↑ε.toNNReal := by
        exact hV₁.2
      _ = _ := by
        rw [MeasureTheory.Content.measure_apply μ ?_]
        congr; exact hμ'
  exact ⟨subset_inter hV₁.1 hfE, h, h'⟩

/-- Choose `N` sufficiently large such that particular quantity is small. -/
lemma RMK_le_aux {a b c ε : ℝ} (hab : a < b) (h' : 0 ≤ c) (hε : 0 < ε) : ∃ (N : ℕ), 0 < N ∧
    (b - a) / N * (2 * c + |a| + b + (b - a) / N) ≤ ε := by
  let ε''' := ε / (2 * c + |a| + b + 1)
  let ε'' := min ε''' 1
  let N' := (b - a) / ε''
  let N := ⌈N'⌉₊
  use N
  let ε' := (b - a) / N
  have h : 0 ≤ |a| + b := by
    by_cases hc : 0 ≤ b
    · positivity
    · linarith [abs_of_neg (show a < 0 by linarith)]
  have hN : 0 < N := by
    apply Nat.ceil_pos.mpr
    refine div_pos (sub_pos.mpr hab) ?_
    simp only [lt_inf_iff, zero_lt_one, and_true, ε'', N']
    apply div_pos hε ?_
    linarith
  have hε' : 0 < ε' := by exact div_pos (sub_pos.mpr hab) (Nat.cast_pos'.mpr hN)
  have h'' : ε' ≤ ε'' := calc
    _ = (b - a) / N := by rfl
    _ ≤ (b - a) / N' := by
      gcongr
      · exact sub_nonneg_of_le <| le_of_lt <| gt_iff_lt.mpr hab
      · exact Nat.one_le_ceil_iff.mp hN
      · exact Nat.le_ceil N'
    _ = _ := by
      rw [div_div_cancel₀]
      linarith
  have h''' : ε'' ≤ ε''' := by simp [ε'']
  constructor
  · exact hN
  · calc
      _ ≤ ε'' * (2 * c + |a| + b + ε') := by
        refine mul_le_mul_of_nonneg_right h'' ?_
        linarith
      _ ≤ ε'' * (2 * c + |a| + b + 1) := by
        gcongr
        · linarith
        · calc
            _ ≤ ε'' := h''
            _ ≤ 1 := by simp [ε'']
      _ ≤ ε''' * (2 * c + |a| + b + 1) := by
        refine mul_le_mul_of_nonneg_right h''' ?_
        linarith
      _ = _ := by
        dsimp [ε''']
        refine div_mul_cancel₀ ε ?_
        linarith

/-- `Λ f ≤ ∫ (x : X), f x ∂(rieszMeasure hΛ)` -/
theorem RMK_le [Nonempty X] (f : C_c(X, ℝ)) : Λ f ≤ ∫ (x : X), f x ∂(rieszMeasure hΛ) := by
  let μ := rieszMeasure hΛ
  let K := (tsupport f)
  -- Suffices to show that `Λ f ≤ ∫ (x : X), f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose interval `(a, b)` which contains the range of `f`.
  have exists_ab : ∃ a b : ℝ, a < b ∧ range f ⊆ Ioo a b := by
    obtain ⟨⟨a', ha⟩, ⟨b', hb⟩⟩ := isBounded_iff_bddBelow_bddAbove.mp
      (Metric.isCompact_iff_isClosed_bounded.mp (HasCompactSupport.isCompact_range f.2 f.1.2)).2
    let a := a' - 1
    let b := b' + 1
    have hf : range f ⊆ Ioo a b := fun x hx ↦
      ⟨lt_of_lt_of_le (sub_one_lt a') (ha hx), lt_of_le_of_lt (hb hx) (lt_add_one b')⟩
    have hab : a' ≤ b' := by
      obtain ⟨c, hc⟩ := instNonemptyRange f
      exact le_trans (mem_lowerBounds.mp ha c hc) (mem_upperBounds.mp hb c hc)
    have hab' : a < b := by
      exact lt_trans (lt_of_lt_of_le (sub_one_lt a') hab) (lt_add_one b')
    use a, b
  obtain ⟨a, b, hab⟩ := exists_ab
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := RMK_le_aux hab.1 (show 0 ≤ (μ K).toReal by exact ENNReal.toReal_nonneg) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧  ε' * (2 * (μ K).toReal + |a| + b + ε') ≤ ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
  obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 hN (by field_simp [ε', ← mul_div_assoc,
    mul_div_cancel_left₀, hab.2])
  -- Introduce notation for the partition of the range.
  let y : Fin N → ℝ := fun n ↦ a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) < ⊤ := by
    have h (n : Fin N) : E n ⊆ K := by
      dsimp [K]
      rw [hE.1]
      exact subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a
    apply lt_of_le_of_lt <| MeasureTheory.measure_mono (h n)
    dsimp [μ, K]
    rw [rieszMeasure, show f = f.toFun by rfl,
      MeasureTheory.Content.measure_apply _ f.2.measurableSet]
    exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  have exists_open_approx : ∃ V : Fin N → Opens X, ∀ n, E n ⊆ (V n) ∧ (∀ x ∈ V n, f x < y n + ε') ∧
      μ (V n) ≤ μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h (n : Fin N) : ∀ x ∈ E n, f x < y n + ε' := by
      intro x hx
      dsimp [y]
      linarith [(hE.2.2.1 n x hx).2]
    have h' (n : Fin N) : (rieszContent (toNNRealLinear Λ hΛ)).outerMeasure (E n) ≠ ⊤ := by
      rw [← MeasureTheory.Content.measure_apply (rieszContent (toNNRealLinear Λ hΛ)) (hE.2.2.2 n)]
      exact LT.lt.ne_top (hE' n)
    let V (n : Fin N) := Classical.choose (open_approx (f : C_c(X, ℝ))
      (div_pos hε'.1 (Nat.cast_pos'.mpr hN)) (E n) (h' n) (hE.2.2.2 n) (h n))
    use V
    intro n
    let hV := Classical.choose_spec (open_approx (f : C_c(X, ℝ))
      (div_pos hε'.1 (Nat.cast_pos'.mpr hN)) (E n) (h' n) (hE.2.2.2 n) (h n))
    exact ⟨hV.1, hV.2.1, hV.2.2⟩
  obtain ⟨V, hV⟩ := exists_open_approx
  -- Define a partition of unity subordinated to the sets `V`
  have : tsupport f ⊆ ⋃ n, (V n).carrier := calc
    _ = ⋃ j, E j := hE.1
    _ ⊆ _ := by gcongr with n; exact (hV n).1
  obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n => (V n).2) f.2 this
  let g (n : Fin N) := (⟨g' n, hg.2.2.2 n⟩ : C_c(X, ℝ))
  -- The proof is completed by a chain of inequalities.
  calc
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ ≤ ∑ n, Λ ((y n + ε') • g n) := ?_
    _ ≤ ∑ n, (y n + ε') * Λ (g n) := by simp
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
    simp only [CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_smulc,
      smul_eq_mul, Finset.sum_apply, coe_mul, Pi.mul_apply, ← Finset.sum_mul, ← Finset.sum_apply]
    by_cases hx : x ∈ tsupport f
    · simp [g, hg.2.1 hx]
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
  · -- use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / ↑N`
    gcongr with n hn
    · calc
        _ ≤ |a| + a := neg_le_iff_add_nonneg'.mp <| neg_abs_le a
        _ ≤ |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr <|
          Left.mul_nonneg (le_of_lt hε'.1) <| Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)
        _ ≤ _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ ≤ (μ (V n)).toReal := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · apply le_rieszMeasure_of_isOpen_tsupport_subset
            · intro x
              exact hg.2.2.1 n x
            · exact hg.1 n
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨hE' n, ENNReal.ofReal_lt_top⟩
        _ ≤ _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2
          · exact lt_top_iff_ne_top.mp (hE' n)
          · exact ENNReal.ofReal_ne_top
  · -- use that `μ K ≤ Λ (∑ n, g n)`
    have h :(μ K).toReal ≤ Λ (∑ n, g n) := by
      have h : ∀ x, 0 ≤ (∑ n, g n) x := by
        intro x
        rw [coe_sum, Finset.sum_apply]
        exact Fintype.sum_nonneg fun n ↦ (hg.2.2.1 n x).1
      have h' : ∀ x ∈ K, (∑ n, g n) x = 1 := by intro _ hx; simp [g, hg.2.1 hx]
      apply ENNReal.toReal_le_of_le_ofReal
      · refine hΛ (∑ n, g n) (fun x ↦ h x)
      · exact rieszMeasure_le_of_eq_one hΛ h f.2 h'
    gcongr
    rw [Eq.symm (map_sum Λ g _)]
    exact h
  · -- Rearrange the sums
    simp_rw [mul_add]
    have (n : Fin N) : (|a| + y n + ε') * (μ (E n)).toReal =
        (|a| + 2 * ε') * (μ (E n)).toReal + (y n - ε') * (μ (E n)).toReal := by linarith
    simp_rw [this]
    have : ∑ i : Fin N, (μ (E i)).toReal = (μ K).toReal := by
      suffices h : μ K = ∑ i : Fin N, (μ (E i)) by
        rw [h]
        exact Eq.symm <| ENNReal.toReal_sum <| fun n _ ↦ LT.lt.ne_top (hE' n)
      dsimp [K]; rw [hE.1]
      rw [MeasureTheory.measure_iUnion (fun m n hmn ↦ hE.2.1 trivial trivial hmn) hE.2.2.2]
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
          apply MeasureTheory.integral_fintype_iUnion hE.2.2.2 (fun ⦃i j⦄ ↦ hE.2.1 trivial trivial)
          have : Integrable (⇑f) μ := by
            dsimp [μ, rieszMeasure]
            exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
          exact fun _ ↦ MeasureTheory.Integrable.integrableOn this
        _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
        _ = _ := MeasureTheory.setIntegral_tsupport
    intro n
    apply MeasureTheory.setIntegral_ge_of_const_le (hE.2.2.2 n)
    · dsimp [μ]
      rw [rieszMeasure]
      rw [MeasureTheory.Content.measure_apply _ (hE.2.2.2 n)]
      push_neg
      rw [← lt_top_iff_ne_top]
      have (n : Fin N): E n ⊆ tsupport f := le_of_le_of_eq (subset_iUnion_of_subset n fun ⦃a⦄ a ↦ a)
        (Eq.symm hE.1)
      apply lt_of_le_of_lt (MeasureTheory.OuterMeasure.mono _ (this n))
      exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
    · intro x hx
      dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
    · apply MeasureTheory.Integrable.integrableOn
      dsimp [μ, rieszMeasure]
      exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
  · -- Rough bound of the sum
    rw [mul_comm 2 ε', show ε' / ↑N = ε' * 1 / ↑N by rw [mul_one], mul_assoc, mul_div_assoc,
      mul_assoc, add_assoc, ← mul_add]
    simp_rw [add_assoc |a|, add_comm (y _) ε', ← add_assoc]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add,
      nsmul_eq_mul, nsmul_eq_mul, ← mul_add, mul_add (1 / _), mul_comm (1 / _), mul_one_div,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr <| Nat.not_eq_zero_of_lt hN), add_assoc _ ε',
      show 2 * (μ K).toReal + |a| + b + ε' = 2 * (μ K).toReal + |a| + ε' + b by linarith,
      ← add_assoc, ← add_assoc]
    gcongr
    · exact le_of_lt hε'.1
    · have (n : Fin N) := calc
        y n = a + ε' * (↑↑n + 1) := by exact rfl
        _ ≤ a + ε' * N := by
          have : (n : ℝ) + 1 ≤ N := by norm_cast; omega
          simp_all
        _ = b := by field_simp [ε', ← mul_div_assoc, mul_div_cancel_left₀]
      have : ∑ x : Fin N, y x ≤ ∑ x : Fin N, b := Finset.sum_le_sum (fun n ↦ fun _ ↦ this n)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      calc
        _ ≤ 1 / N * (N * b) := by
          refine (mul_le_mul_iff_of_pos_left ?_).mpr this
          exact one_div_pos.mpr <| Nat.cast_pos'.mpr hN
        _ ≤ _ := by
          rw [mul_comm, mul_assoc, mul_comm, mul_assoc]
          rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr <| Nat.not_eq_zero_of_lt hN)]
          simp

/-- The **Riesz-Markov-Kakutani theorem** for a positive linear functional `Λ`. -/
theorem integral_rieszMeasure [Nonempty X] (f : C_c(X, ℝ)) :
    ∫ (x : X), f x ∂(rieszMeasure hΛ) = Λ f := by
  -- `RMK_le` tells that `Λ f ≤ ∫ (x : X), f x ∂(rieszMeasure hΛ)`, we apply this to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc ∫ (x : X), f x ∂(rieszMeasure hΛ) = ∫ (x : X), -(-f) x ∂(rieszMeasure hΛ) := by
          simp only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_neg]
    _ = - ∫ (x : X), (-f) x ∂(rieszMeasure hΛ) := by exact MeasureTheory.integral_neg' (-f)
    _ ≤ - Λ (-f) := by exact neg_le_neg (RMK_le hΛ (-f))
    _ = Λ (- -f) := by exact Eq.symm (LinearMap.map_neg Λ (- f))
    _ = Λ f := by simp only [neg_neg]
  -- prove the inequality for `f`
  · exact RMK_le hΛ f

end RealRMK

end RealRMK
