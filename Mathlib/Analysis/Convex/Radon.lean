/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Linarith

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

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

namespace Radon

/-- If `s` is a set of affine dependent vectors, it has subset `I` with the property that
convex hulls of `I` and `s \ I` intersect. -/
theorem Radon_partition (s : Set E) 
(h : ¬AffineIndependent 𝕜 ((↑) : s → E)) : ∃ (I : Set E), (I ⊆ s) ∧ 
(Set.Nonempty ((convexHull 𝕜 I) ∩ (convexHull 𝕜 (s \ I)))) := by
  unfold AffineIndependent at h; push_neg at h
  rcases h with ⟨s1, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩
  let I : Finset { x // x ∈ s } := s1.filter (fun x => w x ≥ 0)
  let J : Finset { x // x ∈ s } := s1.filter (fun x => w x < 0)
  use (I : Set {x // x ∈ s})
  constructor
  exact Set.coe_subset

  let weights_sum_I := ∑ i in I, w i
  let weights_sum_J := ∑ i in J, w i
  have h3 : weights_sum_I + weights_sum_J = 0 := by
    rw [←h_wsum]; simp
    have h3_aux := Finset.sum_filter_add_sum_filter_not s1 (fun x => 0 ≤ w x) w
    simp at h3_aux; exact h3_aux
  
  have h4 : (weights_sum_I > 0) ∧ (weights_sum_J < 0) := by
    rcases (lt_or_gt_of_ne h2) with h_neg | h_pos
    have h_J_neg : weights_sum_J < 0 := by
      rw [←neg_pos, ←Finset.sum_neg_distrib]
      let neg_w : {x // x ∈ s} → 𝕜 := fun v => -w v
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

  let w' : { x // x ∈ s} → 𝕜 := fun i => if w i ≥ 0 
    then (w i) / weights_sum_I 
    else -(w i) / weights_sum_I
  let p : E := ∑ v in I, w' v • (v : E) -- point of intersection
  
  have h5_I : ∑ v in I, w' v = 1 := by
    let w'' : { x // x ∈ s} → 𝕜 := fun i => (w i) / weights_sum_I
    have h5_aux : ∑ v in I, w' v = ∑ v in I, w'' v := by
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
  
  have h5_J : ∑ v in J, w' v = 1 := by
    let w'' : { x // x ∈ s} → 𝕜 := fun i => (w i) / weights_sum_J
    have h5_aux1 : weights_sum_I = -weights_sum_J := by
      exact Iff.mp add_eq_zero_iff_eq_neg h3
    have h5_aux2 : ∑ v in J, w' v = ∑ v in J, w'' v := by
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
  
  let p' : E := (Finset.sum J fun v => w' v • (v : E))
  have h7 : p = p' := by
    suffices h7_suf1 : p -ᵥ p' = 0 by
      exact eq_of_vsub_eq_zero h7_suf1
    
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s1 w Subtype.val h_wsum 0] 
      at h_vsum
    simp at h_vsum; simp

    let g : { x // x ∈ s} → E := fun v =>  weights_sum_I⁻¹ • ((w v) • (v : E))
    have h7_aux2 : ∑ v in I, (w' v) • (v : E) = ∑ v in I, g v := by
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi
      simp
      ring; split_ifs
      rw [mul_comm, mul_smul]
      exfalso; linarith
    
    have h7_aux3 : ∑ v in J, (w' v) • (v : E) = -∑ v in J, g v := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr; rfl
      intros i hi
      rw [Finset.mem_filter] at hi
      rcases hi
      simp
      ring; split_ifs
      exfalso; linarith
      rw [mul_comm, ←neg_smul, ←neg_mul, mul_smul]
    
    rw [h7_aux2, h7_aux3]
    simp
    have h7_aux4 := Finset.sum_filter_add_sum_filter_not s1 (fun x => 0 ≤ w x) g
    simp at h7_aux4; rw [h7_aux4]
    rw [←Finset.smul_sum, h_vsum, smul_zero]
  
  use p
  apply Set.mem_inter
  
  apply Convex.sum_mem
  exact convex_convexHull 𝕜 _
  intros i _; exact h6 i
  exact h5_I
  intros i hi
  have h8 : (i : E) ∈ (Lean.Internal.coeM (I : Set {x // x ∈ s})) := by
    apply Set.mem_coe_of_mem (Subtype.mem i)
    exact hi
  apply Set.mem_of_mem_of_subset h8
  apply subset_convexHull

  rw [h7]
  apply Convex.sum_mem
  exact convex_convexHull 𝕜 _
  intros i _; exact h6 i
  exact h5_J
  intros i hi
  have h9 : (i : E) ∈ (s \ Lean.Internal.coeM (I : Set {x // x ∈ s})) := by
    apply Set.mem_diff_of_mem
    exact Subtype.mem i
    intro h9_neg
    have h9_aux1 : i ∈ I := Iff.mpr Finset.mem_coe (Set.mem_of_mem_coe h9_neg)
    have := (Iff.mp Finset.mem_filter hi).right
    have := (Iff.mp Finset.mem_filter h9_aux1).right
    linarith
  apply Set.mem_of_mem_of_subset h9
  apply subset_convexHull