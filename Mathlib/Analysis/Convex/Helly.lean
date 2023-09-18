/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Radon

/-!
# Helly's theorem on convex sets

Helly's theorem is a basic result in discrete geometry on the intersection of convex sets. Let
`X₁, ⋯, Xₙ` be a finite family of convex sets in `ℝᵈ` with `n ≥ d + 1`. The theorem states that if
any `d + 1` sets from this family intersect, then the whole family intersect.

## Tags

convexity, radon, helly
-/

open Set
open FiniteDimensional

variable {𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

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
    rw [←@finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 _ _ _ _ _ _ _ _ a (k - 1)]
    · exact (Submodule.finrank_le (vectorSpan 𝕜 (Set.range a))).trans (Nat.le_pred_of_lt h_card)
    · rw [←Finite.card_toFinset hF_fin, ←ncard_eq_toFinset_card F hF_fin, hn,
      ←Nat.sub_add_comm (Nat.one_le_of_lt h_card)]; rfl

  obtain ⟨I, p, h4_I, h4_Ic⟩ := Convex.radon_partition h2
  use p; simp; intro X hX

  have h3 (X Y : Set E) (hX : X ∈ F) (hY : Y ∈ F) (hneq : X ≠ Y) : a ⟨Y, hY⟩ ∈ X := by
    apply @mem_of_subset_of_mem _ (⋂₀ (F \ {Y})) _
    apply sInter_subset_of_mem
    · simp only [mem_diff, hX, mem_singleton_iff, hneq, not_false_eq_true, and_self]
    · exact (h1 Y hY).some_mem

  have h4 (I : Set F) (h : ⟨X, hX⟩ ∈ I) : (convexHull 𝕜) (a '' Iᶜ) ⊆ X := by
    rw [Convex.convexHull_subset_iff (h_convex X hX)]
    intro z hz; simp only [mem_image] at hz; rcases hz with ⟨Y, hY1, hY2⟩
    rw [←hY2]
    apply h3
    · exact hX
    · by_contra heq
      simp only [heq, Subtype.coe_eta] at h
      contradiction

  by_cases (⟨X, hX⟩ ∈ I)
  · exact h4 I h h4_Ic
  · apply h4 Iᶜ h; rwa [compl_compl]
