/-
Copyright (c) 2026 Nicholas Cimino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Cimino
-/

module

public import Mathlib.Analysis.Fourier.AddCircle

import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fejér kernels and means on `AddCircle`

This file develops the Fourier-analytic infrastructure used in Fejér's theorem
for continuous complex-valued functions on `AddCircle T`.

It:

* defines symmetric Fourier partial sums and their Cesàro means;
* defines the Fejér kernel and proves its representation as a normalized squared
  Fourier prefix;
* proves that the kernel is real and nonnegative;
* proves that its normalized Haar integral is one;
* establishes uniform decay of the kernel on compact sets away from the origin;
* expresses Fejér means as convolution with the Fejér kernel.

Important results include `integral_fejerKernel`,
`fejerKernel_tendsto_zero_uniformly_on_compact`, and
`fejerMean_eq_integral_fejerKernel`.

The uniform-convergence theorem itself is proved in
`Mathlib.Analysis.Fourier.Fejer`.

Several algebraic and pointwise kernel lemmas are proved without the positivity
assumption on `T`; positivity is retained where the compact-circle, Fourier
coefficient, or Haar-measure infrastructure requires it.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]
/-!
## Fourier partial sums and Fejér means

We begin with the symmetric Fourier index sets, partial Fourier sums, and the
Cesàro averages that define the Fejér means.
-/

/-- The symmetric set of Fourier modes from `-n` through `n`. -/
noncomputable def fourierIndices (n : ℕ) : Finset ℤ :=
Finset.Icc (-(n : ℤ)) n

/-- An integer lies in `fourierIndices n` exactly when it lies between `-n` and `n`. -/
lemma mem_fourierIndices {n : ℕ} {k : ℤ} :
    k ∈ fourierIndices n ↔ -(n : ℤ) ≤ k ∧ k ≤ n := by
  simp [fourierIndices]

/-- An integer lies in `fourierIndices n` exactly when its natural absolute value is at most `n`. -/
lemma mem_fourierIndices_iff_natAbs_le
    (n : ℕ) (m : ℤ) :
    m ∈ fourierIndices n ↔ m.natAbs ≤ n := by
  rw [mem_fourierIndices]
  omega

/-- The `n`th symmetric partial Fourier sum of `f` on `AddCircle T`. -/
noncomputable def fourierPartialSum
    (f : AddCircle T → ℂ)
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ k ∈ fourierIndices n,
    fourierCoeff f k * fourier k x

private theorem fourierPartialSum_fourier_of_mem
    (n : ℕ) (m : ℤ)
    (hm : m ∈ fourierIndices n) :
    fourierPartialSum (T := T) ⇑(fourier m) n = ⇑(fourier m) := by
  funext x
  simp [fourierPartialSum, fourierCoeff_fourier, Pi.single_apply, hm]

private theorem fourierPartialSum_fourier_of_not_mem
    (n : ℕ) (m : ℤ)
    (hm : m ∉ fourierIndices n) :
    fourierPartialSum (T := T) ⇑(fourier m) n = 0 := by
  funext x
  simp [fourierPartialSum, fourierCoeff_fourier, Pi.single_apply, hm]

/-- The `n`th symmetric Fourier partial sum of a Fourier mode is that mode when its
frequency lies in `fourierIndices n`, and zero otherwise. -/
theorem fourierPartialSum_fourier
    (n : ℕ) (m : ℤ) :
    fourierPartialSum (T := T) ⇑(fourier m) n =
      if m ∈ fourierIndices n then ⇑(fourier m) else 0 := by
  by_cases hm : m ∈ fourierIndices n
  · simp [hm, fourierPartialSum_fourier_of_mem]
  · simp [hm, fourierPartialSum_fourier_of_not_mem]

/-- The `n`th Fejér mean, defined as the average of the first `n + 1`
    symmetric Fourier partial sums. -/
noncomputable def fejerMean
    (f : AddCircle T → ℂ)
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  (((n + 1 : ℕ) : ℂ)⁻¹) *
    ∑ j ∈ Finset.range (n + 1),
      fourierPartialSum (T := T) f j x

private theorem fejerMean_fourier
    (n : ℕ) (m : ℤ) :
    fejerMean (T := T) ⇑(fourier m) n =
      fun x =>
        (((n + 1 : ℕ) : ℂ)⁻¹) *
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then fourier m x else 0 := by
  funext x
  unfold fejerMean
  apply congrArg
    (fun z : ℂ => (((n + 1 : ℕ) : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourierPartialSum_fourier (T := T) j m]
  by_cases h : m ∈ fourierIndices j
  · simp [h]
  · simp [h]

private lemma card_filter_natAbs_le
    (n : ℕ) (m : ℤ) :
    ((Finset.range (n + 1)).filter (fun j => m.natAbs ≤ j)).card =
      n + 1 - m.natAbs := by
  have hfilter :
      (Finset.range (n + 1)).filter (fun j => m.natAbs ≤ j) =
        Finset.Icc m.natAbs n := by
    ext j
    simp
    omega
  rw [hfilter]
  simp

private lemma sum_indicator
    (n : ℕ) (m : ℤ) (c : ℂ) :
    (∑ j ∈ Finset.range (n + 1),
        if m ∈ fourierIndices j then c else 0) =
      ((n + 1 - m.natAbs : ℕ) : ℂ) * c := by
  simp only [mem_fourierIndices_iff_natAbs_le]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [card_filter_natAbs_le]

/-- The Fejér mean of a Fourier mode is the mode multiplied by the corresponding
triangular Fejér weight. -/
theorem fejerMean_fourier_eq_weighted
    (n : ℕ) (m : ℤ) :
    fejerMean (T := T) ⇑(fourier m) n =
      fun x =>
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m x) := by
  funext x
  rw [fejerMean_fourier (T := T) n m]
  change
    (((n + 1 : ℕ) : ℂ)⁻¹) *
        (∑ j ∈ Finset.range (n + 1),
          if m ∈ fourierIndices j then
            (fourier m : C(AddCircle T, ℂ)) x
          else 0) =
      (((n + 1 - m.natAbs : ℕ) : ℂ) /
        ((n + 1 : ℕ) : ℂ)) *
        (fourier m : C(AddCircle T, ℂ)) x
  rw [sum_indicator]
  rw [div_eq_mul_inv]
  ring

/-!
## Algebraic form of the Fejér kernel

This section introduces the Fejér kernel and rewrites it in terms of the square
of a finite Fourier prefix. The combinatorial lemmas below count pairs of
indices with a prescribed difference.
-/

/-- The Fejér kernel on `AddCircle T`, written as its finite weighted Fourier expansion. -/
noncomputable def fejerKernel
    {T : ℝ}
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ m ∈ fourierIndices n,
    ((((n + 1 - m.natAbs : ℕ) : ℂ) /
      ((n + 1 : ℕ) : ℂ)) *
      fourier m x)

/-- The finite sum of the nonnegative Fourier modes from `0` through `n`. -/
noncomputable def fourierPrefix
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    fourier (k : ℤ) x

omit [Fact (0 < T)] in
private lemma star_fourierPrefix
    (n : ℕ) (x : AddCircle T) :
    starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ k ∈ Finset.range (n + 1),
        fourier (-(k : ℤ)) x := by
  unfold fourierPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_neg]

omit [Fact (0 < T)] in
private lemma fourierPrefix_mul_star
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          fourier ((j : ℤ) - (k : ℤ)) x := by
  rw [star_fourierPrefix]
  unfold fourierPrefix
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [← fourier_add]
  ring_nf

/-- The pairs of indices in `0, ..., n` whose integer difference is `m`. -/
private noncomputable def differencePairs
    (n : ℕ) (m : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = m)

private lemma card_differencePairs_of_nonneg
    (n r : ℕ) :
    (differencePairs n (r : ℤ)).card =
      n + 1 - r := by
  classical
  by_cases hr : r ≤ n
  · calc
      (differencePairs n (r : ℤ)).card =
          (Finset.range (n + 1 - r)).card := by
        apply Finset.card_bij (fun p _ => p.2)
        · intro p hp
          have hp' := hp
          simp [differencePairs] at hp'
          simp only [Finset.mem_range]
          omega
        · intro p₁ hp₁ p₂ hp₂ h
          have hp₁' := hp₁
          have hp₂' := hp₂
          simp [differencePairs] at hp₁' hp₂'
          apply Prod.ext
          · omega
          · exact h
        · intro k hk
          simp only [Finset.mem_range] at hk
          refine ⟨(k + r, k), ?_, ?_⟩
          · simp [differencePairs]
            omega
          · rfl
      _ = n + 1 - r := by
        simp
  · have hr' : n < r := Nat.lt_of_not_ge hr
    have hempty : differencePairs n (r : ℤ) = ∅ := by
      ext p
      simp [differencePairs]
      omega
    rw [hempty]
    simp
    omega

private lemma card_differencePairs_of_neg
    (n r : ℕ) :
    (differencePairs n (-(r : ℤ))).card =
      n + 1 - r := by
  classical
  by_cases hr : r ≤ n
  · calc
      (differencePairs n (-(r : ℤ))).card =
          (Finset.range (n + 1 - r)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          have hp' := hp
          simp [differencePairs] at hp'
          simp only [Finset.mem_range]
          omega
        · intro p₁ hp₁ p₂ hp₂ h
          have hp₁' := hp₁
          have hp₂' := hp₂
          simp [differencePairs] at hp₁' hp₂'
          apply Prod.ext
          · exact h
          · omega
        · intro j hj
          simp only [Finset.mem_range] at hj
          refine ⟨(j, j + r), ?_, ?_⟩
          · simp [differencePairs]
            omega
          · rfl
      _ = n + 1 - r := by
        simp
  · have hr' : n < r := Nat.lt_of_not_ge hr
    have hempty : differencePairs n (-(r : ℤ)) = ∅ := by
      ext p
      simp [differencePairs]
      omega
    rw [hempty]
    simp
    omega

private lemma card_differencePairs
    (n : ℕ) (m : ℤ) :
    (differencePairs n m).card =
      n + 1 - m.natAbs := by
  rcases Int.natAbs_eq m with hm | hm
  · calc
      (differencePairs n m).card =
          (differencePairs n (m.natAbs : ℤ)).card := by
            exact congrArg
              (fun z : ℤ => (differencePairs n z).card)
              hm
      _ = n + 1 - m.natAbs :=
        card_differencePairs_of_nonneg n m.natAbs
  · calc
      (differencePairs n m).card =
          (differencePairs n (-(m.natAbs : ℤ))).card := by
            exact congrArg
              (fun z : ℤ => (differencePairs n z).card)
              hm
      _ = n + 1 - m.natAbs :=
        card_differencePairs_of_neg n m.natAbs

private lemma sub_mem_fourierIndices
    (n j k : ℕ)
    (hj : j < n + 1)
    (hk : k < n + 1) :
    (j : ℤ) - (k : ℤ) ∈ fourierIndices n := by
  rw [mem_fourierIndices]
  omega

omit [Fact (0 < T)] in
private lemma sum_by_difference
    (n : ℕ) (x : AddCircle T) :
    ∑ m ∈ fourierIndices n,
        ∑ _p ∈ differencePairs n m,
          fourier m x =
      ∑ p ∈
          (Finset.range (n + 1)).product (Finset.range (n + 1)),
        fourier ((p.1 : ℤ) - (p.2 : ℤ)) x := by
  classical
  refine Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.range (n + 1)).product (Finset.range (n + 1)))
    (t := fourierIndices n)
    (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
    ?_
    (fun m : ℤ => fourier m x)
  intro p hp
  simp at hp
  apply sub_mem_fourierIndices n p.1 p.2
  · omega
  · omega

omit [Fact (0 < T)] in
private lemma sum_differencePairs
    (n : ℕ) (m : ℤ) (x : AddCircle T) :
    ∑ _p ∈ differencePairs n m, fourier m x =
      ((n + 1 - m.natAbs : ℕ) : ℂ) * fourier m x := by
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [card_differencePairs]

omit [Fact (0 < T)] in
private lemma double_sum_eq_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    ∑ p ∈
        (Finset.range (n + 1)).product (Finset.range (n + 1)),
      fourier ((p.1 : ℤ) - (p.2 : ℤ)) x =
    ∑ m ∈ fourierIndices n,
      ((n + 1 - m.natAbs : ℕ) : ℂ) * fourier m x := by
  rw [← sum_by_difference]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_differencePairs]

omit [Fact (0 < T)] in
private lemma product_sum_eq_nested_sum
    (n : ℕ) (x : AddCircle T) :
    ∑ p ∈
        (Finset.range (n + 1)).product (Finset.range (n + 1)),
      fourier ((p.1 : ℤ) - (p.2 : ℤ)) x =
    ∑ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (n + 1),
        fourier ((j : ℤ) - (k : ℤ)) x := by
  exact
    Finset.sum_product
      (s := Finset.range (n + 1))
      (t := Finset.range (n + 1))
      (f := fun p : ℕ × ℕ =>
        (fourier ((p.1 : ℤ) - (p.2 : ℤ)) x : ℂ))

omit [Fact (0 < T)] in
private lemma fourierPrefix_mul_star_eq_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ m ∈ fourierIndices n,
        ((n + 1 - m.natAbs : ℕ) : ℂ) *
          fourier m x := by
  calc
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            fourier ((j : ℤ) - (k : ℤ)) x := by
      exact fourierPrefix_mul_star (T := T) n x
    _ =
        ∑ p ∈
            (Finset.range (n + 1)).product (Finset.range (n + 1)),
          fourier ((p.1 : ℤ) - (p.2 : ℤ)) x := by
      exact (product_sum_eq_nested_sum (T := T) n x).symm
    _ =
        ∑ m ∈ fourierIndices n,
          ((n + 1 - m.natAbs : ℕ) : ℂ) *
            fourier m x := by
      exact double_sum_eq_weighted_sum (T := T) n x

omit [Fact (0 < T)] in
private lemma fejerKernel_eq_inv_mul_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        ∑ m ∈ fourierIndices n,
          ((n + 1 - m.natAbs : ℕ) : ℂ) *
            fourier m x := by
  unfold fejerKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [div_eq_mul_inv]
  ring

omit [Fact (0 < T)] in
private lemma fejerKernel_eq_prefix_mul_star
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        (fourierPrefix (T := T) n x *
          starRingEnd ℂ (fourierPrefix (T := T) n x)) := by
  rw [fejerKernel_eq_inv_mul_weighted_sum]
  rw [fourierPrefix_mul_star_eq_weighted_sum]

omit [Fact (0 < T)] in
/-- The Fejér kernel is `1 / (n + 1)` times the squared norm of the one-sided Fourier prefix. -/
lemma fejerKernel_eq_normSq
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        (Complex.normSq (fourierPrefix (T := T) n x) : ℂ) := by
  rw [fejerKernel_eq_prefix_mul_star]
  rw [Complex.mul_conj]

omit [Fact (0 < T)] in
/-- The real part of the Fejér kernel is `1 / (n + 1)` times the squared norm of the
one-sided Fourier prefix. -/
lemma fejerKernel_re
    (n : ℕ) (x : AddCircle T) :
    (fejerKernel (T := T) n x).re =
      (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x) := by
  rw [fejerKernel_eq_normSq]
  have h :
      (((n + 1 : ℕ) : ℂ)⁻¹) =
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    norm_num
  rw [h]
  change
    (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Complex.normSq (fourierPrefix (T := T) n x) : ℝ) : ℂ)).re =
      (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x)
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fact (0 < T)] in
/-- The Fejér kernel is real-valued. -/
lemma fejerKernel_im
    (n : ℕ) (x : AddCircle T) :
    (fejerKernel (T := T) n x).im = 0 := by
  rw [fejerKernel_eq_normSq]
  have h :
      (((n + 1 : ℕ) : ℂ)⁻¹) =
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    norm_num
  rw [h]
  simp

omit [Fact (0 < T)] in
/-- The real part of the Fejér kernel is nonnegative. -/
lemma fejerKernel_nonneg
    (n : ℕ) (x : AddCircle T) :
    0 ≤ (fejerKernel (T := T) n x).re := by
  rw [fejerKernel_re]
  have h₁ : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have h₂ :
      0 ≤ Complex.normSq (fourierPrefix (T := T) n x) :=
    Complex.normSq_nonneg _
  exact mul_nonneg h₁ h₂

end AddCircle

namespace AddCircle

/-!
## Normalization of the Fejér kernel

We compute the Haar integral of the Fourier modes and deduce that every Fejér
kernel has total mass one.
-/

/-- The normalized Haar integral of a Fourier mode is one at frequency zero and zero at
every nonzero frequency. -/
lemma integral_fourier
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) :
    (∫ x : AddCircle T,
        fourier m x ∂AddCircle.haarAddCircle) =
      if m = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) m) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

private lemma integral_fourier_zero
    {T : ℝ} [Fact (0 < T)] :
    (∫ x : AddCircle T,
        fourier (0 : ℤ) x ∂AddCircle.haarAddCircle) = 1 := by
  rw [integral_fourier]
  simp

private lemma integral_fourier_ne_zero
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) (hm : m ≠ 0) :
    (∫ x : AddCircle T,
        fourier m x ∂AddCircle.haarAddCircle) = 0 := by
  rw [integral_fourier]
  simp [hm]

/-- Every Fourier mode on `AddCircle T` is integrable with respect to normalized Haar measure. -/
lemma integrable_fourier
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) :
    MeasureTheory.Integrable
      (fun x : AddCircle T => fourier m x)
      AddCircle.haarAddCircle := by
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun x : AddCircle T => fourier m x)
        AddCircle.haarAddCircle :=
    (fourier m).continuous.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

private lemma integrable_weighted_fourier
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) (m : ℤ) :
    MeasureTheory.Integrable
      (fun x : AddCircle T =>
        (((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m x)
      AddCircle.haarAddCircle := by
  exact
    (integrable_fourier m).const_mul
      ((((n + 1 - m.natAbs : ℕ) : ℂ) /
        ((n + 1 : ℕ) : ℂ)))

/-- The Fejér kernel has normalized Haar integral equal to one. -/
lemma integral_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ x : AddCircle T,
        fejerKernel (T := T) n x
          ∂AddCircle.haarAddCircle) = 1 := by
  unfold fejerKernel
  rw [MeasureTheory.integral_finsetSum (fourierIndices n)]
  · simp_rw [MeasureTheory.integral_const_mul]
    simp_rw [integral_fourier]
    have hn :
        (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    rw [Finset.sum_eq_single 0]
    · simp only [Int.natAbs_zero, Nat.sub_zero, ite_true, mul_one]
      exact div_self hn
    · intro m hm hne
      simp [hne]
    · intro hzero
      exfalso
      apply hzero
      simp [fourierIndices]
  · intro m hm
    exact integrable_weighted_fourier n m

/-!
## Concentration away from the origin

Using the geometric-sum formula, we bound the Fejér kernel uniformly on compact
sets that avoid the origin. This yields uniform decay to zero away from zero.
-/

private lemma fourier_nat_eq_pow
    {T : ℝ}
    (k : ℕ) (x : AddCircle T) :
    fourier (k : ℤ) x =
      (fourier (1 : ℤ) x) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.cast_succ]
      rw [fourier_add]
      rw [ih]
      rw [pow_succ]

private lemma fourierPrefix_eq_geom_sum
    {T : ℝ}
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x =
      ∑ k ∈ Finset.range (n + 1),
        (fourier (1 : ℤ) x) ^ k := by
  unfold fourierPrefix
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_nat_eq_pow]

private lemma fourierPrefix_mul_sub_one
    {T : ℝ}
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        (fourier (1 : ℤ) x - 1) =
      fourier ((n + 1 : ℕ) : ℤ) x - 1 := by
  rw [fourierPrefix_eq_geom_sum]
  rw [fourier_nat_eq_pow]
  exact geom_sum_mul (fourier (1 : ℤ) x) (n + 1)

/-- Every Fourier mode on `AddCircle T` has pointwise norm one. -/
lemma norm_fourier
    {T : ℝ}
    (m : ℤ) (x : AddCircle T) :
    ‖fourier m x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe ((m • x).toCircle)

private lemma norm_fourier_sub_one_le_two
    {T : ℝ}
    (m : ℤ) (x : AddCircle T) :
    ‖fourier m x - 1‖ ≤ 2 := by
  calc
    ‖fourier m x - 1‖
        ≤ ‖fourier m x‖ + ‖(1 : ℂ)‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le (fourier m x) (-1 : ℂ)
    _ = 2 := by
      rw [norm_fourier]
      norm_num

private lemma norm_fourierPrefix_mul_norm_sub_one_le_two
    {T : ℝ}
    (n : ℕ) (x : AddCircle T) :
    ‖fourierPrefix (T := T) n x‖ *
        ‖fourier (1 : ℤ) x - 1‖ ≤ 2 := by
  have h :=
    congrArg norm
      (fourierPrefix_mul_sub_one (T := T) n x)
  rw [norm_mul] at h
  rw [h]
  exact norm_fourier_sub_one_le_two
    ((n + 1 : ℕ) : ℤ) x

private lemma norm_fourierPrefix_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    ‖fourierPrefix (T := T) n x‖ ≤
      2 / ‖fourier (1 : ℤ) x - 1‖ := by
  have hpos :
      0 < ‖fourier (1 : ℤ) x - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hx
  have h :=
    norm_fourierPrefix_mul_norm_sub_one_le_two
      (T := T) n x
  exact (le_div_iff₀ hpos).2 h

private lemma normSq_fourierPrefix_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    Complex.normSq (fourierPrefix (T := T) n x) ≤
      4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
  have h :=
    norm_fourierPrefix_le (T := T) n x hx
  have hnonneg :
      0 ≤ ‖fourierPrefix (T := T) n x‖ := norm_nonneg _
  have hden :
      0 ≤ 2 / ‖fourier (1 : ℤ) x - 1‖ := by
    positivity
  have hsq :
      ‖fourierPrefix (T := T) n x‖ ^ 2 ≤
        (2 / ‖fourier (1 : ℤ) x - 1‖) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg h 2
  rw [Complex.sq_norm] at hsq
  calc
    Complex.normSq (fourierPrefix (T := T) n x)
        ≤ (2 / ‖fourier (1 : ℤ) x - 1‖) ^ 2 := hsq
    _ = 4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
      ring

/-- Away from the origin, the real part of the Fejér kernel is bounded by the standard
geometric-series estimate. -/
lemma fejerKernel_re_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    (fejerKernel (T := T) n x).re ≤
      4 /
        (((n + 1 : ℕ) : ℝ) *
          ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
  rw [fejerKernel_re]
  have hsq :=
    normSq_fourierPrefix_le (T := T) n x hx
  have hn :
      0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have hmul :
      (((n + 1 : ℕ) : ℝ)⁻¹) *
          Complex.normSq (fourierPrefix (T := T) n x)
        ≤
      (((n + 1 : ℕ) : ℝ)⁻¹) *
          (4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq hn
  calc
    (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x)
      ≤
        (((n + 1 : ℕ) : ℝ)⁻¹) *
          (4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2) := hmul
    _ =
        4 /
          (((n + 1 : ℕ) : ℝ) *
            ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
      field_simp

private lemma continuous_norm_fourier_one_sub_one
    {T : ℝ} :
    Continuous
      (fun x : AddCircle T =>
        ‖fourier (1 : ℤ) x - 1‖) := by
  fun_prop

private lemma exists_pos_lower_bound_norm_fourier_one_sub_one
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ K,
        c ≤ ‖fourier (1 : ℤ) x - 1‖ := by
  by_cases hKne : K.Nonempty
  · have hcont :
        ContinuousOn
          (fun x : AddCircle T =>
            ‖fourier (1 : ℤ) x - 1‖) K :=
      continuous_norm_fourier_one_sub_one.continuousOn
    obtain ⟨x₀, hx₀min⟩ :=
      hK.exists_isMinOn hKne hcont
    have hx₀K : x₀ ∈ K := by
      exact hx₀min.1
    refine ⟨‖fourier (1 : ℤ) x₀ - 1‖, ?_, ?_⟩
    · rw [norm_pos_iff]
      apply sub_ne_zero.mpr
      intro hfourier
      have hcircle :
          x₀.toCircle = (1 : Circle) := by
        apply Subtype.ext
        simpa [fourier_one] using hfourier
      have hT : T ≠ 0 := by
        exact ne_of_gt (Fact.out : 0 < T)
      have hx₀ : x₀ = 0 := by
        apply AddCircle.injective_toCircle hT
        simpa using hcircle
      exact h0 (hx₀ ▸ hx₀K)
    · intro x hxK
      exact hx₀min.2 hxK
  · refine ⟨1, by positivity, ?_⟩
    intro x hxK
    exfalso
    exact hKne ⟨x, hxK⟩

private lemma fejerKernel_re_le_on_compact
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, ∀ x ∈ K,
        (fejerKernel (T := T) n x).re ≤
          4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) := by
  obtain ⟨c, hcpos, hc⟩ :=
    exists_pos_lower_bound_norm_fourier_one_sub_one
      (T := T) K hK h0
  refine ⟨c, hcpos, ?_⟩
  intro n x hxK
  have hc_le :
      c ≤ ‖fourier (1 : ℤ) x - 1‖ :=
    hc x hxK
  have hc_nonneg : 0 ≤ c := le_of_lt hcpos
  have hnorm_pos :
      0 < ‖fourier (1 : ℤ) x - 1‖ := by
    exact lt_of_lt_of_le hcpos hc_le
  have hx :
      fourier (1 : ℤ) x ≠ 1 := by
    intro h
    have :
        ‖fourier (1 : ℤ) x - 1‖ = 0 := by
      rw [h]
      simp
    linarith
  have hkernel :=
    fejerKernel_re_le (T := T) n x hx
  have hsq :
      c ^ 2 ≤ ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
    nlinarith [hc_le, hc_nonneg, norm_nonneg (fourier (1 : ℤ) x - 1)]
  have hnpos :
      0 < (((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hden :
      (((n + 1 : ℕ) : ℝ) * c ^ 2) ≤
        (((n + 1 : ℕ) : ℝ) *
          ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq (le_of_lt hnpos)
  have hdenpos :
      0 < (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    positivity
  have hfrac :
      4 /
          (((n + 1 : ℕ) : ℝ) *
            ‖fourier (1 : ℤ) x - 1‖ ^ 2)
        ≤
      4 /
          (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    apply div_le_div_of_nonneg_left
    · norm_num
    · exact hdenpos
    · exact hden
  exact le_trans hkernel hfrac

/-- On every compact set avoiding the origin, the real parts of the Fejér
    kernels converge uniformly to zero. -/
lemma fejerKernel_tendsto_zero_uniformly_on_compact
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n →
          ∀ x ∈ K,
            (fejerKernel (T := T) n x).re < ε := by
  intro ε hε
  obtain ⟨c, hcpos, hbound⟩ :=
    fejerKernel_re_le_on_compact
      (T := T) K hK h0
  have hc2pos : 0 < c ^ 2 := by
    positivity
  have hεc2pos : 0 < ε * c ^ 2 := by
    positivity
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 / (ε * c ^ 2))
  refine ⟨N, ?_⟩
  intro n hn x hxK
  have hkernel :
      (fejerKernel (T := T) n x).re ≤
        4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) :=
    hbound n x hxK
  have hNcast :
      4 / (ε * c ^ 2) < (N : ℝ) := by
    exact hN
  have hncast :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge :
      4 / (ε * c ^ 2) < (n : ℝ) := by
    exact lt_of_lt_of_le hNcast hncast
  have hnlarge' :
      4 / (ε * c ^ 2) <
        ((n + 1 : ℕ) : ℝ) := by
    norm_num at *
    linarith
  have hfour :
      4 <
        ((n + 1 : ℕ) : ℝ) * (ε * c ^ 2) := by
    exact (div_lt_iff₀ hεc2pos).mp hnlarge'
  have hdenpos :
      0 < (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    positivity
  have hfrac :
      4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) < ε := by
    apply (div_lt_iff₀ hdenpos).2
    nlinarith
  exact lt_of_le_of_lt hkernel hfrac

/-!
## Convolution representation of the Fejér means

We relate translation of Fourier modes to Haar integration and derive the
representation of a Fejér mean as convolution with the Fejér kernel.
-/

/-- A Fourier mode sends addition on `AddCircle T` to multiplication in `ℂ`. -/
lemma fourier_apply_add
    {T : ℝ}
    (m : ℤ)
    (x y : AddCircle T) :
    fourier m (x + y) =
      fourier m x * fourier m y := by
  simp [fourier_apply, AddCircle.toCircle_add]

/-- A Fourier mode sends subtraction on `AddCircle T` to multiplication by the
opposite-frequency mode. -/
lemma fourier_apply_sub
    {T : ℝ}
    (m : ℤ)
    (x y : AddCircle T) :
    fourier m (x - y) =
      fourier m x * fourier (-m) y := by
  rw [sub_eq_add_neg]
  rw [fourier_apply_add]
  congr 1
  rw [fourier_apply]
  rw [fourier_apply]
  simp

private lemma integral_neg_haarAddCircle
    {T : ℝ} [Fact (0 < T)]
    (g : AddCircle T → ℂ) :
    (∫ y : AddCircle T,
        g (-y) ∂AddCircle.haarAddCircle) =
      ∫ y : AddCircle T,
        g y ∂AddCircle.haarAddCircle := by
  exact
    MeasureTheory.integral_neg_eq_self
      g
      AddCircle.haarAddCircle

/-- Convolution of a Fourier mode with a translate of `f` extracts the corresponding
Fourier coefficient of `f`. -/
lemma integral_fourier_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℂ)
    (m : ℤ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fourier m y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      fourier m x * fourierCoeff f m := by
  have hshift :=
    MeasureTheory.integral_add_right_eq_self
      (μ := AddCircle.haarAddCircle)
      (fun y : AddCircle T =>
        fourier m y * f (x - y))
      x
  calc
    (∫ y : AddCircle T,
        fourier m y * f (x - y)
          ∂AddCircle.haarAddCircle)
        =
      ∫ y : AddCircle T,
        fourier m (y + x) * f (x - (y + x))
          ∂AddCircle.haarAddCircle := hshift.symm
    _ =
      ∫ y : AddCircle T,
        fourier m x * (fourier m y * f (-y))
          ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [fourier_apply_add]
      have hsub :
          x - (y + x) = -y := by
        abel
      rw [hsub]
      ring
    _ =
      fourier m x *
        (∫ y : AddCircle T,
          fourier m y * f (-y)
            ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_const_mul]
    _ =
      fourier m x *
        (∫ y : AddCircle T,
          fourier (-m) y * f y
            ∂AddCircle.haarAddCircle) := by
      congr 1
      have hneg :=
        integral_neg_haarAddCircle
          (T := T)
          (fun y : AddCircle T =>
            fourier (-m) y * f y)
      simpa [fourier_neg, mul_comm, mul_left_comm, mul_assoc]
        using hneg
    _ =
      fourier m x * fourierCoeff f m := by
      simp [fourierCoeff, smul_eq_mul]

private lemma integrable_weighted_fourier_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (m : ℤ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m y) *
          f (x - y))
      AddCircle.haarAddCircle := by
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          ((((n + 1 - m.natAbs : ℕ) : ℂ) /
            ((n + 1 : ℕ) : ℂ)) *
            fourier m y) *
            f (x - y)) := by
    fun_prop
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          ((((n + 1 - m.natAbs : ℕ) : ℂ) /
            ((n + 1 : ℕ) : ℂ)) *
            fourier m y) *
            f (x - y))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

private lemma integral_fejerKernel_mul_translate_eq_sum
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          (fourier m x * fourierCoeff f m)) := by
  unfold fejerKernel
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum (fourierIndices n)]
  · apply Finset.sum_congr rfl
    intro m hm
    simp_rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_fourier_mul_translate]
  · intro m hm
    exact
      integrable_weighted_fourier_mul_translate
        (T := T) f n m x

private lemma integral_fejerKernel_mul_translate_eq_weighted_fourier
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
  rw [integral_fejerKernel_mul_translate_eq_sum
    (T := T) f n x]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private lemma fourierPartialSum_eq_sum_indicator
    {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℂ)
    (n j : ℕ)
    (hj : j ≤ n)
    (x : AddCircle T) :
    fourierPartialSum (T := T) f j x =
      ∑ m ∈ fourierIndices n,
        if m ∈ fourierIndices j then
          fourierCoeff f m * fourier m x
        else 0 := by
  unfold fourierPartialSum
  rw [← Finset.sum_filter]
  have hfilter :
      (fourierIndices n).filter
          (fun m => m ∈ fourierIndices j) =
        fourierIndices j := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · intro hm
      exact hm.2
    · intro hm
      constructor
      · rw [mem_fourierIndices] at hm ⊢
        omega
      · exact hm
  rw [hfilter]

/-- A Fejér mean is the finite Fourier sum with the usual triangular Fejér weights. -/
lemma fejerMean_eq_weighted_fourier_sum
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
  unfold fejerMean
  calc
    (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ j ∈ Finset.range (n + 1),
          fourierPartialSum (T := T) f j x)
        =
      (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ j ∈ Finset.range (n + 1),
          ∑ m ∈ fourierIndices n,
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply fourierPartialSum_eq_sum_indicator
        (T := T) f n j
      simp at hj
      omega
    _ =
      (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ m ∈ fourierIndices n,
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      congr 1
      rw [Finset.sum_comm]
    _ =
      ∑ m ∈ fourierIndices n,
        (((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      rw [Finset.mul_sum]
    _ =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [sum_indicator
        n m (fourierCoeff f m * fourier m x)]
      rw [div_eq_mul_inv]
      ring

/-- A Fejér mean is the convolution of `f` with the Fejér kernel with respect
    to normalized Haar measure. -/
lemma fejerMean_eq_integral_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle := by
  rw [fejerMean_eq_weighted_fourier_sum]
  rw [integral_fejerKernel_mul_translate_eq_weighted_fourier]

end AddCircle
