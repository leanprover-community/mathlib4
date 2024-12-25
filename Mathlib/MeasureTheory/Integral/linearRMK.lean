/-
Copyright (c) 2024 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.PartitionOfUnity

noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f.1 → 0 ≤ Λ f)

section Λ_mono

include hΛ

lemma Λ_mono' (f₁ f₂ : C_c(X, ℝ)) (h : f₁.1 ≤ f₂.1) : Λ f₁ ≤ Λ f₂ := by
  have : 0 ≤ Λ (f₂ - f₁) := by
    apply hΛ
    intro x
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply, coe_toContinuousMap, coe_sub,
      Pi.sub_apply, sub_nonneg]
    exact h x
  calc Λ f₁ ≤ Λ f₁ + Λ (f₂ - f₁) := by exact (le_add_iff_nonneg_right (Λ f₁)).mpr this
  _ =  Λ (f₁ + (f₂ - f₁)) := by exact Eq.symm (LinearMap.map_add Λ f₁ (f₂ - f₁))
  _ = Λ f₂ := by congr; exact add_sub_cancel f₁ f₂

end Λ_mono

section linearRMK

namespace linearRMK

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

def μ := (rieszContent (toNNRealLinear hΛ)).measure

theorem MeasureTheory.integral_tsupport {M : Type*} [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup M]
    [NormedSpace ℝ M] {F : X → M} {ν : MeasureTheory.Measure X} :
    ∫ (x : X), F x ∂ν = ∫ (x : X) in tsupport F, F x ∂ν := by
  rw [← MeasureTheory.setIntegral_univ]
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
    (subset_univ _)
  intro x hx
  apply image_eq_zero_of_nmem_tsupport
  exact not_mem_of_mem_diff hx

lemma leRieszMeasure_isCompact {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {K : Compacts X}
    (h : tsupport f ⊆ K) : ENNReal.ofReal (Λ f) ≤ (μ Λ hΛ) K := by
  have Lfnonneg : 0 ≤ Λ f := by
    apply hΛ
    intro x
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply, coe_toContinuousMap]
    exact (hf x).1
  rw [μ]
  rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear hΛ))
    (rieszContentRegular (toNNRealLinear hΛ))]
  simp only
  rw [rieszContent]
  simp only
  rw [ENNReal.ofReal_eq_coe_nnreal Lfnonneg]
  simp only [ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear hΛ) K
    (Real.toNNReal_pos.mpr hε)
  simp only [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  apply le_of_lt (lt_of_le_of_lt _ hg.2)
  apply Λ_mono' Λ hΛ f
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x).2 (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact NNReal.zero_le_coe


lemma leRieszMeasure_isOpen {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1) {V : Opens X}
    (h : tsupport f ⊆ V) :
    ENNReal.ofReal (Λ f) ≤ (μ Λ hΛ) V := by
  apply le_trans _ (MeasureTheory.measure_mono h)
  rw [← TopologicalSpace.Compacts.coe_mk (tsupport f) f.2]
  apply leRieszMeasure_isCompact Λ hΛ hf
  simp only [Compacts.coe_mk]
  exact subset_rfl

/-- The Riesz-Markov-Kakutani theorem. -/
theorem RMK [Nonempty X] : ∀ (f : C_c(X, ℝ)), ∫ (x : X), f x ∂(μ Λ hΛ) = Λ f := by
  have RMK_le : ∀ (f : C_c(X, ℝ)), Λ f ≤ ∫ (x : X), f x ∂(μ Λ hΛ) := by
    intro f
    set L := Set.range f with hLdef
    have hL : IsCompact L := by exact HasCompactSupport.isCompact_range f.2 f.1.2
    have hLNonempty : Nonempty L := instNonemptyRange f
    have BddBelow_bbdAbove_L := isBounded_iff_bddBelow_bddAbove.mp
      (Metric.isCompact_iff_isClosed_bounded.mp hL).2
    obtain ⟨a, ha⟩ := BddBelow_bbdAbove_L.1
    obtain ⟨b, hb⟩ := BddBelow_bbdAbove_L.2
    have hafx : ∀ (x : X), a ≤ f x := by
      intro x
      apply ha
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hfxb : ∀ (x : X), f x ≤ b:= by
      intro x
      apply hb
      rw [hLdef]
      simp only [mem_range, exists_apply_eq_apply]
    have hab : a ≤ b := by
      obtain ⟨c, hc⟩ := hLNonempty
      exact le_trans (mem_lowerBounds.mp ha c hc) (mem_upperBounds.mp hb c hc)
    have habnonneg : 0 ≤ |a| + b := by
      apply le_trans _ (add_le_add_right (neg_le_abs a) b)
      simp only [le_neg_add_iff_add_le, add_zero]
      exact hab
    apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    have hltε : ∃ (ε' : ℝ), 0 < ε' ∧
        ε' * (2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b + ε') < ε := by
      set A := 2 * ((μ Λ hΛ) (tsupport f)).toReal + |a| + b with hA
      use ε / (4 * A + 2 + 2 * ε)
      have hAnonneg : 0 ≤ A := by
        rw [hA, add_assoc]
        apply add_nonneg _ habnonneg
        simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, ENNReal.toReal_nonneg]
      constructor
      · apply div_pos hε
        linarith
      · rw [left_distrib]
        have h1 : ε / (4 * A + 2 + 2 * ε) * A < ε / 2 := by
          rw [← mul_div_right_comm, mul_div_assoc]
          nth_rw 3 [← mul_one ε]
          rw [mul_div_assoc]
          apply mul_lt_mul_of_pos_left _ hε
          apply (div_lt_div_iff₀ _ two_pos).mpr
          · linarith
          · linarith
        have h2 : ε / (4 * A + 2 + 2 * ε) < ε / 2 := by
          apply div_lt_div_of_pos_left hε two_pos
          linarith
        have h3 : 0 < 4 * A + 2 + 2 * ε := by
          linarith
        have h4 : ε / (4 * A + 2 + 2 * ε) * (ε / (4 * A + 2 + 2 * ε)) < ε / 2 := by
          rw [_root_.lt_div_iff₀ two_pos, mul_comm, ← mul_div_assoc, ← mul_div_assoc,
            div_lt_iff₀ h3, ← mul_assoc, mul_comm, ← mul_assoc, ← mul_div_assoc, div_lt_iff₀ h3,
            mul_assoc, mul_assoc]
          apply mul_lt_mul_of_pos_left _ hε
          have h41 : 2 < 4 * A + 2 + 2 * ε := by
            linarith
          have h42 : ε < 4 * A + 2 + 2 * ε := by
            linarith
          exact mul_lt_mul h41 (le_of_lt h42) hε (le_of_lt h3)
        nth_rw 7 [← add_halves ε]
        exact add_lt_add h1 h4
    obtain ⟨ε', hε'⟩ := hltε
    apply le_of_lt (lt_of_le_of_lt _ (add_lt_add_left hε'.2 _))
    set δ := ε' / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      exact div_pos hε'.1 two_pos
    set N := (b - a) / δ with hN
    have hNNonneg : 0 ≤ N :=
      by exact div_nonneg (sub_nonneg.mpr hab) (le_of_lt hδpos)
    set y : ℤ → ℝ := fun n => b + δ * (n - (⌈N⌉₊+1)) with hy
    have ymono : ∀ (j k : ℤ), y j < y k → j < k := by
      intro j k
      rw [hy]
      simp only [add_lt_add_iff_left]
      intro h
      apply (@Int.cast_lt ℝ).mp
      apply @lt_of_tsub_lt_tsub_right ℝ j k (⌈N⌉₊ + 1)
      exact lt_of_mul_lt_mul_left h (le_of_lt hδpos)
    have hy1leyn : ∀ (n : Fin (⌈N⌉₊ + 1)), y 1 ≤ y (n + 1) := by
      intro n
      rw [hy]
      simp only [Int.cast_one, sub_add_cancel_right, mul_neg, Int.cast_add, Int.cast_natCast,
        add_sub_add_right_eq_sub, add_lt_add_iff_left]
      rw [_root_.mul_sub]
      apply le_add_neg_iff_le.mp
      ring_nf
      simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right]
      exact mul_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _)
    have hymono' : ∀ (m n : Fin (⌈N⌉₊ + 1)), m ≤ n → y m ≤ y n := by
      intro m n hmn
      rw [hy]
      simp only [Int.cast_natCast, add_le_add_iff_left]
      rw [_root_.mul_sub, _root_.mul_sub]
      simp only [tsub_le_iff_right, sub_add_cancel]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδpos)
      rw [Nat.cast_le]
      simp only [Fin.val_fin_le]
      exact hmn
    have hy0 : y 0 < a := by
      rw [hy, hN]
      simp only [Int.cast_zero, Int.ceil_add_one, Int.cast_add, Int.cast_one, zero_sub, neg_add_rev]
      apply lt_tsub_iff_left.mp
      apply (lt_div_iff₀' hδpos).mp
      simp only [add_neg_lt_iff_lt_add]
      rw [neg_lt_iff_pos_add, add_assoc, ← neg_lt_iff_pos_add']
      apply lt_add_of_lt_add_right _ (Nat.le_ceil _)
      rw [neg_lt_iff_pos_add]
      apply pos_of_mul_pos_left _ (le_of_lt hδpos)
      rw [add_mul, add_mul, div_mul, div_mul, div_self (Ne.symm (ne_of_lt hδpos))]
      simp only [div_one, one_mul]
      linarith

    set E : ℤ → Set X := fun n => (f ⁻¹' Ioc (y n) (y (n+1))) ∩ (tsupport f) with hE
    set Erest : Fin (⌈N⌉₊ + 1) → Set X := fun n => E n with hErest
    have hErestdisjoint : PairwiseDisjoint univ Erest := by
      intro m _ n _ hmn
      apply Disjoint.preimage
      simp only [mem_preimage]
      by_cases hmltn : m < n
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        left
        left
        apply le_trans hx.1.2
        have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hmltn (Fin.le_last n)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hmltn
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        push_neg at hmltn
        set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
        left
        right
        apply lt_of_le_of_lt _ hx.1.1
        have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hnltm (Fin.le_last m)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hnltm
    have hErestdisjoint' : Pairwise (Disjoint on Erest) := by
      intro m n hmn
      apply Disjoint.preimage
      simp only [mem_preimage]
      by_cases hmltn : m < n
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        left
        left
        apply le_trans hx.1.2
        have : m.1 + (1 : ℤ) = (m+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hmltn (Fin.le_last n)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hmltn
      · rw [Set.disjoint_left]
        intro x hx
        simp only [mem_Ioc, mem_setOf_eq, not_and_or, not_lt, not_le]
        simp only [mem_Ioc, mem_setOf_eq] at hx
        push_neg at hmltn
        set hnltm := lt_of_le_of_ne hmltn (Ne.symm hmn)
        left
        right
        apply lt_of_le_of_lt _ hx.1.1
        have : n.1 + (1 : ℤ) = (n+1 : Fin (⌈N⌉₊ + 1)) := by
          rw [← Nat.cast_add_one, Nat.cast_inj]
          apply Eq.symm (Fin.val_add_one_of_lt _)
          exact lt_of_lt_of_le hnltm (Fin.le_last m)
        rw [this]
        apply hymono' _ _
        exact Fin.add_one_le_of_lt hnltm
    have hErestmeasurable : ∀ (n : Fin (⌈N⌉₊ + 1)), MeasurableSet (Erest n) := by
      intro n
      rw [hErest]
      simp only
      apply MeasurableSet.inter
      · exact (ContinuousMap.measurable f.1) measurableSet_Ioc
      · exact measurableSet_closure
    have hErestsubtsupport : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ tsupport f := by
      intro n
      rw [hErest]
      simp only
      rw [hE]
      simp only [inter_subset_right]
    have hrangefsubioc: range f ⊆ Ioc (y 0) (y (⌈N⌉₊ + 1)) := by
      intro z hz
      simp only [mem_Ioc]
      constructor
      · apply lt_of_lt_of_le hy0
        apply ha
        rw [hLdef]
        exact hz
      · rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
        apply hb
        rw [hLdef]
        exact hz
    have hrangefsubiunion: range f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), Ioc (y n) (y (n+1)) := by
      have : y = fun (n : ℤ) => b - δ * ⌈N⌉₊ - δ + n • δ := by
        ext n
        rw [hy]
        simp only [zsmul_eq_mul]
        ring
      have : ⋃ n, Ioc (y n) (y (n+1)) = univ := by
        rw [this]
        simp only [Int.cast_add, Int.cast_one]
        exact iUnion_Ioc_add_zsmul hδpos (b - δ * ⌈N⌉₊ - δ)
      intro z hz
      have : z ∈ ⋃ n, Ioc (y n) (y (n+1)) := by
        rw [this]
        exact trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp this
      have hjnonneg : 0 ≤ j := by
        apply (Int.add_le_add_iff_right 1).mp
        apply Int.le_of_sub_one_lt
        simp only [zero_add, sub_self]
        apply ymono
        apply lt_of_lt_of_le hy0
        simp only [mem_Ioc] at hj
        apply le_trans _ hj.2
        apply ha
        rw [hLdef]
        exact hz
      have hjltceil : j < ⌈N⌉₊ + 1 := by
        apply ymono
        simp only [mem_Ioc] at hj
        apply lt_of_lt_of_le hj.1 _
        rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, sub_self, mul_zero, add_zero]
        apply hb
        rw [hLdef]
        exact hz
      have hnltceil : j.toNat < ⌈N⌉₊ + 1 := by
        exact (Int.toNat_lt hjnonneg).mpr hjltceil
      rw [mem_iUnion]
      use ⟨j.toNat, hnltceil⟩
      simp only
      rw [Int.toNat_of_nonneg hjnonneg]
      exact hj
    have htsupportsubErest : tsupport f ⊆ ⋃ j, Erest j := by
      intro x hx
      rw [hErest, hE]
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, exists_and_right]
      obtain ⟨j, hj⟩ := mem_iUnion.mp (Set.mem_of_subset_of_mem hrangefsubiunion
        (Set.mem_range_self x))
      constructor
      · use j
      · exact hx
    have htsupporteqErest : tsupport f = ⋃ j, Erest j := by
      apply subset_antisymm
      · exact htsupportsubErest
      · exact Set.iUnion_subset hErestsubtsupport
    have hμsuppfeqμErest : (μ Λ hΛ) (tsupport f) = ∑ n, (μ Λ hΛ) (Erest n) := by
      rw [htsupporteqErest]
      rw [← MeasureTheory.measure_biUnion_finset]
      · simp only [Finset.mem_univ, iUnion_true]
      · simp only [Finset.coe_univ]
        exact hErestdisjoint
      · intro n _
        exact hErestmeasurable n
    set SpecV := fun (n : Fin (⌈N⌉₊ + 1)) =>
      MeasureTheory.Content.outerMeasure_exists_open (rieszContent (toNNRealLinear hΛ))
      (ne_of_lt (lt_of_le_of_lt ((rieszContent (toNNRealLinear hΛ)).outerMeasure.mono (hErestsubtsupport n))
      (MeasureTheory.Content.outerMeasure_lt_top_of_isCompact (rieszContent (toNNRealLinear hΛ)) f.2)))
      (ne_of_gt (Real.toNNReal_pos.mpr (div_pos hε'.1 (Nat.cast_pos.mpr (Nat.add_one_pos ⌈N⌉₊)))))
    set V : Fin (⌈N⌉₊ + 1) → Opens X := fun n => Classical.choose (SpecV n) ⊓
      ⟨(f ⁻¹' Iio (y (n + 1) + ε')), IsOpen.preimage f.1.2 isOpen_Iio⟩ with hV
    have hErestsubV : ∀ (n : Fin (⌈N⌉₊ + 1)), Erest n ⊆ V n := by
      intro n
      rw [hV]
      simp only [Nat.cast_succ, Opens.coe_inf, Opens.coe_mk, subset_inter_iff]
      constructor
      · simp only [Nat.cast_add, Nat.cast_one] at SpecV
        exact (Classical.choose_spec (SpecV n)).1
      · rw [hErest]
        simp only
        apply Set.Subset.trans (Set.inter_subset_left) _
        intro z hz
        rw [Set.mem_preimage]
        rw [Set.mem_preimage] at hz
        exact lt_of_le_of_lt hz.2 (lt_add_of_pos_right (y (n + 1)) hε'.1)
    have htsupportsubV : tsupport f ⊆ ⋃ n : Fin (⌈N⌉₊ + 1), V n := by
      apply Set.Subset.trans htsupportsubErest _
      apply Set.iUnion_mono
      exact hErestsubV
    obtain ⟨g, hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact
      (fun n => (V n).2) f.2 htsupportsubV
    have hf : f = ∑ n, g n • f := by
      ext x
      simp only [CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_smulc,
        smul_eq_mul, Finset.sum_apply]
      rw [← Finset.sum_mul, ← Finset.sum_apply]
      by_cases hx : x ∈ tsupport f
      · rw [hg.2.1 hx]
        simp only [Pi.one_apply, one_mul]
      · rw [image_eq_zero_of_nmem_tsupport hx]
        simp only [Finset.sum_apply, mul_zero]
    have μtsupportflesumΛgn :
        (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)) ≤
        ENNReal.ofReal (Λ (∑ n, ⟨g n, hg.2.2.2 n⟩)) := by
      rw [μ]
      rw [MeasureTheory.Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear hΛ))
        (rieszContentRegular (toNNRealLinear hΛ)) ⟨tsupport f, f.2⟩]
      rw [rieszContent]
      simp only [map_sum]
      apply ENNReal.coe_le_iff.mpr
      intro p hp
      rw [← ENNReal.ofReal_coe_nnreal] at hp
      rw [ENNReal.ofReal_eq_ofReal_iff] at hp
      apply csInf_le
      · use 0
        rw [mem_lowerBounds]
        simp only [mem_image, mem_setOf_eq, zero_le, implies_true]
      rw [Set.mem_image]
      -- need to define g n as C(X, ℝ≥0)
      set nng : Fin (⌈N⌉₊ + 1) → C_c(X, ℝ≥0) :=
        fun n => ⟨⟨Real.toNNReal ∘ (g n), Continuous.comp continuous_real_toNNReal (g n).2⟩,
        @HasCompactSupport.comp_left _ _ _ _ _ _ Real.toNNReal (g n) (hg.2.2.2 n) Real.toNNReal_zero⟩
        with hnng
      use ∑ n, nng n
      constructor
      · intro x hx
        rw [CompactlySupportedContinuousMap.sum_apply Finset.univ (fun n => nng n) x]
        rw [hnng]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, comp_apply]
        rw [← Real.toNNReal_sum_of_nonneg _]
        · simp only [Real.one_le_toNNReal]
          set hgx := hg.2.1 hx
          simp only [Finset.sum_apply, Pi.one_apply] at hgx
          rw [hgx]
        · intro n _
          exact (hg.2.2.1 n x).1
      · rw [toNNRealLinear]
        simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, map_sum, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [← NNReal.coe_inj, NNReal.coe_sum]
        simp_rw [← NNReal.val_eq_coe]
        rw [NNReal.val_eq_coe, ← hp]
        apply Finset.sum_congr (Eq.refl _)
        intro n _
        rw [hnng]
        simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
        apply congr (Eq.refl _)
        simp only [CompactlySupportedContinuousMap.mk.injEq]
        ext x
        simp only [ContinuousMap.coe_mk, comp_apply, Real.coe_toNNReal', max_eq_left_iff,
          NNReal.val_eq_coe, Real.coe_toNNReal', sup_eq_left]
        exact (hg.2.2.1 n x).1
      · rw [← map_sum Λ _ Finset.univ]
        apply hΛ
        intro x
        simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
          CompactlySupportedContinuousMap.coe_toContinuousMap,
          CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
          Finset.sum_apply]
        apply Finset.sum_nonneg
        intro n hn
        exact (hg.2.2.1 n x).1
      · exact p.2
    have μtsupportflesumΛgn' : (μ Λ hΛ (TopologicalSpace.Compacts.mk (tsupport f) f.2)).toReal ≤
        ∑ n, Λ ⟨g n, hg.2.2.2 n⟩ := by
      rw [← map_sum]
      apply ENNReal.toReal_le_of_le_ofReal _ μtsupportflesumΛgn
      apply hΛ
      intro x
      simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply,
        CompactlySupportedContinuousMap.coe_toContinuousMap,
        CompactlySupportedContinuousMap.coe_sum, CompactlySupportedContinuousMap.coe_mk,
        Finset.sum_apply]
      apply Finset.sum_nonneg
      intro n _
      exact (hg.2.2.1 n x).1
    have hErestx : ∀ (n : Fin (⌈N⌉₊ + 1)), ∀ (x : X), x ∈ Erest n → y n < f x := by
      intro n x hnx
      rw [hErest, hE] at hnx
      simp only [mem_inter_iff, mem_preimage, mem_Ioc] at hnx
      exact hnx.1.1
    have hgf : ∀ (n : Fin (⌈N⌉₊ + 1)),
        (g n • f).1 ≤ ((y (n + 1) + ε') • (⟨g n, hg.2.2.2 n⟩ : C_c(X, ℝ))).1 := by
      intro n x
      simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap,
        CompactlySupportedContinuousMap.smulc_apply, CompactlySupportedContinuousMap.coe_smul,
        CompactlySupportedContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ tsupport (g n)
      · rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (hg.2.2.1 n x).1
        have : x ∈ V n := Set.mem_of_subset_of_mem (hg.1 n) hx
        rw [hV] at this
        simp only [Nat.cast_add, Nat.cast_one] at this
        rw [TopologicalSpace.Opens.mem_mk] at this
        simp only [Opens.carrier_eq_coe, Opens.coe_inf, Opens.coe_mk, mem_inter_iff,
          SetLike.mem_coe, mem_preimage, mem_Iio] at this
        exact le_of_lt this.2
      · rw [image_eq_zero_of_nmem_tsupport hx]
        simp only [zero_mul, mul_zero, le_refl]
    have hΛgf : ∀ (n : Fin (⌈N⌉₊ + 1)), n ∈ Finset.univ →  Λ (g n • f)
        ≤ Λ ((y (n + 1) + ε') • (⟨g n, hg.2.2.2 n⟩ : C_c(X, ℝ))) := by
      intro n _
      exact Λ_mono' Λ hΛ _ _ (hgf n)
    nth_rw 1 [hf]
    simp only [map_sum, CompactlySupportedContinuousMap.coe_sum,
      Finset.sum_apply, Pi.mul_apply]
    apply le_trans (Finset.sum_le_sum hΛgf)
    simp only [map_smul, smul_eq_mul]
    rw [← add_zero ε']
    simp_rw [← add_assoc, ← sub_self |a|, ← add_sub_assoc, _root_.sub_mul]
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    have hy1a : 0 < y 1 + ε' + |a| := by
      rw [hy]
      simp only [Fin.val_zero, CharP.cast_eq_zero, zero_add, Int.cast_one, sub_add_cancel_right,
        mul_neg]
      rw [add_assoc, add_assoc, add_comm, add_assoc, lt_neg_add_iff_lt, ← lt_div_iff₀' hδpos]
      apply lt_trans (Nat.ceil_lt_add_one hNNonneg)
      rw [lt_div_iff₀' hδpos, hN, mul_add, mul_comm, div_mul, div_self (ne_of_gt hδpos)]
      simp only [div_one, mul_one]
      rw [hδ]
      apply lt_add_of_tsub_lt_right
      rw [add_sub_assoc, add_comm, ← add_sub_assoc]
      apply sub_right_lt_of_lt_add
      rw [sub_add]
      simp only [sub_self, sub_zero]
      apply lt_neg_add_iff_lt.mp
      rw [add_assoc, ← add_assoc]
      apply add_pos_of_pos_of_nonneg
      · simp only [lt_neg_add_iff_add_lt, add_zero, half_lt_self_iff]
        exact hε'.1
      · exact neg_le_iff_add_nonneg'.mp (neg_abs_le a)
    have hyna : ∀ (n : Fin (⌈N⌉₊ + 1)), 0 < y (n + 1) + ε' + |a| := by
      intro n
      by_cases hn : n = 0
      · rw [hn]
        exact hy1a
      · push_neg at hn
        have hnp : 0 < n := by
          exact Fin.pos_iff_ne_zero.mpr hn
        rw [← sub_add_cancel (y (n + 1)) (y 1), add_assoc, add_assoc]
        apply add_pos_of_nonneg_of_pos
        · exact sub_nonneg_of_le (hy1leyn n)
        · rw [← add_assoc]
          exact hy1a
    have hΛgnleμVn : ∀ (n : Fin (⌈N⌉₊ + 1)),
        ENNReal.ofReal (Λ (⟨g n, hg.2.2.2 n⟩)) ≤ (μ Λ hΛ) (V n) := by
      intro n
      apply leRieszMeasure_isOpen
      · simp only [CompactlySupportedContinuousMap.coe_mk]
        intro x
        exact hg.2.2.1 n x
      · simp only [CompactlySupportedContinuousMap.coe_mk]
        rw [← TopologicalSpace.Opens.carrier_eq_coe]
        exact hg.1 n
    have hμVnleμEnaddε : ∀ (n : Fin (⌈N⌉₊ + 1)),
        (μ Λ hΛ) (V n) ≤ (μ Λ hΛ) (Erest n) + ENNReal.ofReal (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
      intro n
      rw [μ]
      rw [← TopologicalSpace.Opens.carrier_eq_coe]
      rw [MeasureTheory.Content.measure_apply (rieszContent ((toNNRealLinear hΛ))) (V n).2.measurableSet]
      rw [TopologicalSpace.Opens.carrier_eq_coe]
      rw [MeasureTheory.Content.measure_apply (rieszContent ((toNNRealLinear hΛ))) (hErestmeasurable n)]
      set Un := Classical.choose (SpecV n) with hUn
      set SpecUn := Classical.choose_spec (SpecV n)
      have hVU : V n ≤ Un := by
        exact inf_le_left
      have hμVleμU :
          (rieszContent (toNNRealLinear hΛ)).outerMeasure (V n) ≤ (rieszContent (toNNRealLinear hΛ)).outerMeasure (Un) := by
        exact MeasureTheory.OuterMeasure.mono (rieszContent (toNNRealLinear hΛ)).outerMeasure hVU
      apply le_trans hμVleμU
      rw [hUn]
      have hENNNR : ∀ (p : ℝ), ENNReal.ofReal p = p.toNNReal := by
        intro p
        rfl
      rw [hENNNR]
      exact SpecUn.2
    have hμErestlttop : ∀ (n : Fin (⌈N⌉₊ + 1)), (μ Λ hΛ) (Erest n) < ⊤ := by
      intro n
      apply lt_of_le_of_lt (MeasureTheory.measure_mono (hErestsubtsupport n))
      have : f = f.toFun := by
        exact rfl
      rw [μ, this,
        MeasureTheory.Content.measure_apply _ f.2.measurableSet]
      exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
    have hμsuppfeqμErest' : ((μ Λ hΛ) (tsupport f)).toReal = ∑ n, ((μ Λ hΛ) (Erest n)).toReal := by
      rw [← ENNReal.toReal_sum]
      exact congr rfl hμsuppfeqμErest
      intro n _
      rw [← lt_top_iff_ne_top]
      exact hμErestlttop n
    have hΛgnleμVn' : ∀ (n : Fin (⌈N⌉₊ + 1)),
        Λ (⟨g n, hg.2.2.2 n⟩) ≤ ((μ Λ hΛ) (V n)).toReal := by
      intro n
      apply (ENNReal.ofReal_le_iff_le_toReal _).mp (hΛgnleμVn n)
      rw [← lt_top_iff_ne_top]
      apply lt_of_le_of_lt (hμVnleμEnaddε n)
      rw [WithTop.add_lt_top]
      constructor
      · exact hμErestlttop n
      · exact ENNReal.ofReal_lt_top
    have hμVnleμEnaddε' : ∀ (n : Fin (⌈N⌉₊ + 1)),
        ((μ Λ hΛ) (V n)).toReal ≤ ((μ Λ hΛ) (Erest n)).toReal + (ε' / ((⌈N⌉₊ + 1 : ℕ))) := by
      intro n
      rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
      apply ENNReal.toReal_le_add (hμVnleμEnaddε n)
      · exact lt_top_iff_ne_top.mp (hμErestlttop n)
      · exact ENNReal.ofReal_ne_top
    have ynsubεmulμEnleintEnf :
        ∀ (n : Fin (⌈N⌉₊ + 1)), (y (n + 1) - ε') * ((μ Λ hΛ) (Erest n)).toReal
        ≤ ∫ x in (Erest n), f x ∂(μ Λ hΛ) := by
      intro n
      apply MeasureTheory.setIntegral_ge_of_const_le (hErestmeasurable n)
      · rw [μ]
        rw [MeasureTheory.Content.measure_apply _ (hErestmeasurable n)]
        rw [← lt_top_iff_ne_top]
        apply lt_of_le_of_lt (MeasureTheory.OuterMeasure.mono _ (hErestsubtsupport n))
        exact MeasureTheory.Content.outerMeasure_lt_top_of_isCompact _ f.2
      · intro x hx
        apply le_of_lt (lt_trans _ (hErestx n x hx))
        rw [hy]
        simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub]
        rw [sub_add_eq_sub_sub]
        nth_rw 2 [_root_.mul_sub]
        rw [add_sub_assoc]
        simp only [mul_one, add_lt_add_iff_left, sub_lt_sub_iff_left]
        rw [hδ]
        linarith
      · apply MeasureTheory.Integrable.integrableOn
        rw [μ]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    apply le_trans (tsub_le_tsub_left (mul_le_mul_of_nonneg_left μtsupportflesumΛgn' (abs_nonneg a)) _)
    rw [add_mul]
    simp only [add_sub_cancel_right]
    apply le_trans (tsub_le_tsub_right (Finset.sum_le_sum (fun n => (fun _ =>
      mul_le_mul_of_nonneg_left
      (le_trans (hΛgnleμVn' n) (hμVnleμEnaddε' n)) (le_of_lt (hyna n))))) _)
    simp_rw [mul_add _ ((μ Λ hΛ) _).toReal _]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    nth_rw 1 [← sub_add_cancel ε' ε']
    simp_rw [add_assoc _ _ |a|, ← add_assoc _ _ (ε' + |a|), Eq.symm (add_comm_sub _ ε' ε'),
      add_assoc _ ε' _, ← add_assoc ε' ε' |a|, Eq.symm (two_mul ε')]
    simp_rw [add_mul _ (2 * ε' + |a|) ((μ Λ hΛ) _).toReal]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hμsuppfeqμErest', add_mul (2 * ε') |a| _]
    simp only [Compacts.coe_mk]
    have hynleb : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) ≤ b := by
      intro n
      rw [hy]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_add_right_eq_sub,
        add_le_iff_nonpos_right]
      apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδpos)
      simp only [tsub_le_iff_right, zero_add, Nat.cast_le]
      exact Fin.is_le n
    have hynleb' : ∀ (n : Fin (⌈N⌉₊ + 1)), y (n + 1) + (ε' + |a|) ≤ |a| + b + ε':= by
      intro n
      set h := hynleb n
      linarith
    rw [add_assoc, add_sub_assoc, add_sub_assoc, add_add_sub_cancel, ← add_assoc]
    apply le_trans ((add_le_add_iff_left _).mpr (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum (fun n => fun _ => hynleb' n))
      (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    rw [mul_comm _ (|a| + b + ε'), mul_assoc (|a| + b + ε') _ _, ← mul_div_assoc]
    nth_rw 2 [mul_comm _ ε']
    rw [mul_div_assoc, div_self (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) one_pos)),
      mul_one]
    rw [MeasureTheory.integral_tsupport, htsupporteqErest]
    nth_rw 3 [μ]
    have : f = f.toFun := by rfl
    rw [this]
    rw [MeasureTheory.integral_fintype_iUnion hErestmeasurable hErestdisjoint'
      fun n =>
      (MeasureTheory.Integrable.integrableOn (Continuous.integrable_of_hasCompactSupport f.1.2 f.2))]
    rw [add_assoc]
    apply add_le_add
    · apply Finset.sum_le_sum
      exact fun n => fun _ => ynsubεmulμEnleintEnf n
    · linarith
  intro f
  apply le_antisymm
  · calc ∫ (x : X), f x ∂(μ Λ hΛ) = ∫ (x : X), -(-f) x ∂(μ Λ hΛ) := by simp only
      [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_neg]
    _ = - ∫ (x : X), (-f) x ∂(μ Λ hΛ) := by exact MeasureTheory.integral_neg' (-f)
    _ ≤ - Λ (-f) := by exact neg_le_neg (RMK_le (-f))
    _ = Λ (- -f) := by exact Eq.symm (LinearMap.map_neg Λ (- f))
    _ = Λ f := by simp only [neg_neg]
  · exact RMK_le f

end linearRMK

end linearRMK

#min_imports
