/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Radon's theorem on convex sets

Radon's theorem states that any affine dependent set can be partitioned into two sets whose convex
hulls intersect.

## Tags

convex hull, Radon, Helly, affine independence
-/

open Finset Set
open BigOperators

variable {ι 𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Radon's theorem on convex sets**: Any family `f` of affine dependent vectors contains a set
`I` with the property that convex hulls of `I` and `Iᶜ` intersect. -/
theorem Convex.radon_partition {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by
  rw [affineIndependent_iff] at h
  push_neg at h
  obtain ⟨s, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩ := h
  let I : Finset ι := s.filter fun i ↦ 0 ≤ w i
  let J : Finset ι := s.filter fun i ↦ w i < 0
  let p : E := centerMass I w f -- point of intersection
  have hJI : ∑ j in J, w j + ∑ i in I, w i = 0 := by
    simpa only [h_wsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) w
  have hI : 0 < ∑ i in I, w i := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos' (λ _i hi ↦ (mem_filter.1 hi).2)
      ⟨pos_w_index, by simp only [mem_filter, h1', h2'.le, and_self, h2']⟩
  have hp : centerMass J w f = p := Finset.centerMass_of_sum_add_sum_eq_zero hJI $ by
    simpa only [←h_vsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) _
  refine ⟨I, p, ?_, ?_⟩
  · exact centerMass_mem_convexHull _ (fun _i hi ↦ (mem_filter.mp hi).2) hI
      (fun _i hi ↦ Set.mem_image_of_mem _ hi)
  rw [←hp]
  refine centerMass_mem_convexHull_of_nonpos _ (fun _ hi ↦ (mem_filter.mp hi).2.le) ?_
    (fun _i hi ↦ Set.mem_image_of_mem _ fun hi' ↦ ?_)
  · linarith only [hI, hJI]
  · exact (mem_filter.mp hi').2.not_lt (mem_filter.mp hi).2


open FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- **Helly's theorem on convex sets**: If `F` is a finite family of convex sets in a vector space
of finite dimension `d`, and any `d + 1` sets of `F` intersect, then all sets of `F` intersect. -/
theorem helly_theorem (F : Set (Set E)) {hF_fin : Set.Finite F}
    (h_card : (finrank 𝕜 E) + 1 ≤ ncard F) (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Set (Set E), (G ⊆ F) → (ncard G = (finrank 𝕜 E) + 1) →
    (⋂₀ G).Nonempty) : (⋂₀ F).Nonempty := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ncard F = n := ⟨ncard F, rfl⟩ -- for induction on ncard F
  rw [hn] at h_card
  induction' n, h_card using Nat.le_induction with k h_card hk generalizing F
  exact h_inter F (Eq.subset rfl) hn
  have h1 : ∀ X ∈ F, (⋂₀ (F \ {X})).Nonempty := by
    intro X hX
    apply @hk _ (Finite.diff hF_fin {X})
    · exact fun Y hY ↦ h_convex Y (mem_of_mem_diff hY)
    · exact fun G hG_1 hG_2 ↦ h_inter G (Subset.trans hG_1 (diff_subset F {X})) hG_2
    · rw [ncard_diff_singleton_of_mem hX hF_fin, Nat.sub_eq_of_eq_add hn]
  let a : F → E := fun X ↦ (h1 X (Subtype.mem X)).some
  have h2 : ¬AffineIndependent 𝕜 a := by
    have : Fintype ↑F := Finite.fintype hF_fin -- for instance inferring
    rw [←finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a (n := (k - 1))]
    · exact (Submodule.finrank_le (vectorSpan 𝕜 (Set.range a))).trans (Nat.le_pred_of_lt h_card)
    · rw [←Finite.card_toFinset hF_fin, ←ncard_eq_toFinset_card F hF_fin, hn,
      ←Nat.sub_add_comm (Nat.one_le_of_lt h_card)]
      rfl
  obtain ⟨I, p, h4_I, h4_Ic⟩ := Convex.radon_partition h2
  use p
  rw [mem_sInter]
  intro X hX
  have h3 (X Y : Set E) (hX : X ∈ F) (hY : Y ∈ F) (hneq : X ≠ Y) : a ⟨Y, hY⟩ ∈ X := by
    apply @mem_of_subset_of_mem _ (⋂₀ (F \ {Y})) _
    apply sInter_subset_of_mem
    · simp only [mem_diff, hX, mem_singleton_iff, hneq, not_false_eq_true, and_self]
    · exact (h1 Y hY).some_mem
  have h4 (I : Set F) (h : ⟨X, hX⟩ ∈ I) : (convexHull 𝕜) (a '' Iᶜ) ⊆ X := by
    rw [Convex.convexHull_subset_iff (h_convex X hX)]
    intro z hz; simp only [Set.mem_image] at hz; rcases hz with ⟨Y, hY1, hY2⟩
    rw [←hY2]
    apply h3
    · exact hX
    · by_contra heq
      simp only [heq, Subtype.coe_eta] at h
      contradiction
  by_cases (⟨X, hX⟩ ∈ I)
  · exact h4 I h h4_Ic
  · apply h4 Iᶜ h; rwa [compl_compl]
