/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Linarith

/-!
# Radon's convexity theorem

Radon's theorem on convex sets states that any affine dependent set can be partitioned into two sets
whose convex hulls intersect.

## Main results

* `Radon_partition`: Radon convexity theorem

## Tags
convex hull, radon

-/


open Set Finset
open BigOperators

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Any family `f` of affine dependent vectors contains a set `I` with the property that
convex hulls of `I` and `Iᶜ` intersect. -/
theorem radon_partition {ι : Type*} {f : ι → E}
    (h : ¬AffineIndependent 𝕜 f) : ∃ (I : Set ι),
    (Set.Nonempty ((convexHull 𝕜 (f '' I)) ∩ (convexHull 𝕜 (f '' Iᶜ)))) := by
  unfold AffineIndependent at h; push_neg at h
  rcases h with ⟨s1, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩
  let I : Finset ι := s1.filter (fun i => w i ≥ 0)
  let J : Finset ι := s1.filter (fun i => w i < 0)
  use (I : Set ι)

  let weights_sum_I := ∑ i in I, w i
  let weights_sum_J := ∑ i in J, w i
  have h3 : weights_sum_I + weights_sum_J = 0 := by
    rw [←h_wsum]; simp
    have h3_aux := Finset.sum_filter_add_sum_filter_not s1 (fun i => 0 ≤ w i) w
    simp at h3_aux; exact h3_aux

  have h4 : (weights_sum_I > 0) ∧ (weights_sum_J < 0) := by
    rcases (lt_or_gt_of_ne h2) with h_neg | h_pos
    have h_J_neg : weights_sum_J < 0 := by
      rw [←neg_pos, ←Finset.sum_neg_distrib]
      let neg_w : ι → 𝕜 := fun i => -w i
      have h4_aux : neg_w nonzero_w_index ≤ (Finset.sum J neg_w) := by
        apply Finset.single_le_sum
        intros i hi
        simp; rw [Finset.mem_filter] at hi; linarith
        simp; constructor; exact h1; exact h_neg
      simp at h4_aux; simp; linarith
    constructor
    linarith
    exact h_J_neg

    have h_I_pos : weights_sum_I > 0 := by
      have h4_aux : weights_sum_I ≥ w nonzero_w_index := by
        apply Finset.single_le_sum
        intros i hi
        rw [Finset.mem_filter] at hi; exact hi.right
        simp; constructor; exact h1; exact LT.lt.le h_pos
      linarith
    constructor
    exact h_I_pos
    linarith
  rcases h4 with ⟨h_I_pos, h_J_neg⟩

  let w' : ι → 𝕜 := fun i => if w i ≥ 0
    then (w i) / weights_sum_I
    else -(w i) / weights_sum_I
  let p : E := ∑ i in I, (w' i) • (f i) -- point of intersection

  have h5_I : ∑ i in I, w' i = 1 := by
    let w'' : ι → 𝕜 := fun i => (w i) / weights_sum_I
    have h5_aux : ∑ i in I, w' i = ∑ i in I, w'' i := by
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨_, hh⟩
      simp
      contrapose; intros
      exact Iff.mpr not_lt hh
    rw [h5_aux]
    simp
    rw [←Finset.sum_div]
    apply div_self
    exact ne_of_gt h_I_pos

  have h5_J : ∑ i in J, w' i = 1 := by
    let w'' : ι → 𝕜 := fun i => (w i) / weights_sum_J
    have h5_aux1 : weights_sum_I = -weights_sum_J := by
      exact Iff.mp add_eq_zero_iff_eq_neg h3
    have h5_aux2 : ∑ i in J, w' i = ∑ i in J, w'' i := by
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨_, h_neg⟩
      simp
      split_ifs
      exfalso; linarith
      simp_rw [h5_aux1, div_neg]
      ring
    rw [h5_aux2]; simp
    rw [←Finset.sum_div]
    apply div_self
    exact ne_of_lt h_J_neg

  have h6 : ∀ v, w' v ≥ 0 := by
    intro; simp; split_ifs
    repeat {apply div_nonneg; linarith; linarith}

  let p' : E := (Finset.sum J fun i => (w' i) • (f i))
  have h7 : p = p' := by
    suffices h7_suf1 : p -ᵥ p' = 0 by
      exact eq_of_vsub_eq_zero h7_suf1

    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s1 w f h_wsum 0]
      at h_vsum
    simp at h_vsum; simp

    let g : ι → E := fun i =>  weights_sum_I⁻¹ • ((w i) • (f i))
    have h7_aux2 : ∑ i in I, (w' i) • (f i) = ∑ i in I, g i := by
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi
      simp
      ring_nf; split_ifs
      rw [mul_comm, mul_smul]
      exfalso; linarith

    have h7_aux3 : ∑ i in J, (w' i) • (f i) = -∑ i in J, g i := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi
      simp
      ring_nf; split_ifs
      exfalso; linarith
      rw [mul_comm, ←neg_smul, ←neg_mul, mul_smul]

    rw [h7_aux2, h7_aux3]
    simp
    have h7_aux4 := Finset.sum_filter_add_sum_filter_not s1 (fun i => 0 ≤ w i) g
    simp at h7_aux4; rw [h7_aux4]
    rw [←Finset.smul_sum, h_vsum, smul_zero]

  use p
  apply Set.mem_inter

  apply Convex.sum_mem
  exact convex_convexHull 𝕜 _
  intros i _; exact h6 i
  exact h5_I
  intros i hi
  have h8 : f i ∈ (f '' I) := by
    exact Set.mem_image_of_mem f hi
  apply Set.mem_of_mem_of_subset h8
  apply subset_convexHull

  rw [h7]
  apply Convex.sum_mem
  exact convex_convexHull 𝕜 _
  intros i _; exact h6 i
  exact h5_J
  intros i hi
  have h9 : f i ∈ (f '' Iᶜ) := by
    apply Set.mem_image_of_mem
    apply Set.mem_compl
    intro h9_neg
    have := (Iff.mp Finset.mem_filter hi).right
    have := (Iff.mp Finset.mem_filter h9_neg).right
    linarith
  apply Set.mem_of_mem_of_subset h9
  apply subset_convexHull

/-- If `s` is a set of affine dependent vectors, it has subset `I` with the property that
convex hulls of `I` and `s \ I` intersect. -/
theorem radon_set_partition (s : Set E)
    (h : ¬AffineIndependent 𝕜 ((↑) : s → E)) : ∃ (I : Set E), (I ⊆ s) ∧
    (Set.Nonempty ((convexHull 𝕜 I) ∩ (convexHull 𝕜 (s \ I)))) := by
  have h1 := radon_partition h
  rcases h1 with ⟨I, h1⟩
  use I; constructor
  exact Set.coe_subset

  have h2 : Subtype.val '' I = Lean.Internal.coeM I := by
    apply Set.ext
    intro x; constructor
    intro hx
    rw [Set.mem_image] at hx; rcases hx with ⟨x1, hx1, hx2⟩
    rw [←hx2]
    apply Set.mem_coe_of_mem; exact hx1
    intro hx
    have hx := Set.mem_of_mem_coe hx
    rw [Set.mem_image]
    constructor; constructor
    exact hx; rfl

  have h3 : Subtype.val '' Iᶜ = s \ Lean.Internal.coeM I := by
    apply Set.ext
    intro x; constructor
    intro hx
    rw [Set.mem_image] at hx; rcases hx with ⟨x1, hx1, hx2⟩
    rw [←hx2, Set.mem_diff]; constructor
    exact Subtype.mem x1
    intro hx3
    have hx3 := Set.mem_of_mem_coe hx3
    simp at hx3
    exact hx1 hx3
    intro hx
    rw [Set.mem_diff] at hx; rcases hx with ⟨hx1, hx2⟩
    rw [Set.mem_image]
    use {val := x, property := hx1}; constructor
    by_contra hx3; simp at hx3
    simp at hx2
    contrapose hx2; simp
    apply Set.mem_coe_of_mem
    exact hx3; rfl

  rw [←h3, ←h2]; exact h1
