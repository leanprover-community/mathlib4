/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation

/-!
# Radon's theorem on convex sets

Radon's theorem states that any affine dependent set can be partitioned into two sets whose convex
hulls intersect.

As a corollary, we prove Helly's theorem, that is a basic result in discrete geometry on the
intersection of convex sets. Let `X₁, ⋯, Xₙ` be a finite family of convex sets in `ℝᵈ` with
`n ≥ d + 1`. The theorem states that if any `d + 1` sets from this family intersect, then the whole
family intersect. For the infinite family of sets it is not true, as example of `Set.Ioo 0 1/n` for
`n : ℕ` shows. But the statement is true, if we assume compactness of sets (see
`Convex.helly_theorem_infinite`)

## Tags

convex hull, radon, affine independence
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
    exact sum_pos' (fun _i hi ↦ (mem_filter.1 hi).2)
      ⟨pos_w_index, by simp only [I, mem_filter, h1', h2'.le, and_self, h2']⟩
  have hp : centerMass J w f = p := Finset.centerMass_of_sum_add_sum_eq_zero hJI <| by
    simpa only [← h_vsum, not_lt] using sum_filter_add_sum_filter_not s (fun i ↦ w i < 0) _
  refine ⟨I, p, ?_, ?_⟩
  · exact centerMass_mem_convexHull _ (fun _i hi ↦ (mem_filter.mp hi).2) hI
      (fun _i hi ↦ Set.mem_image_of_mem _ hi)
  rw [← hp]
  refine centerMass_mem_convexHull_of_nonpos _ (fun _ hi ↦ (mem_filter.mp hi).2.le) ?_
    (fun _i hi ↦ Set.mem_image_of_mem _ fun hi' ↦ ?_)
  · linarith only [hI, hJI]
  · exact (mem_filter.mp hi').2.not_lt (mem_filter.mp hi).2

open FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- **Helly's theorem on convex sets**: If `F` is a finite family of convex sets in a vector space
of finite dimension `d`, and any `d + 1` sets of `F` intersect, then all sets of `F` intersect. -/
theorem Convex.helly_theorem (F : ι → Set E) {hF_fin : Finite ι}
    (h_convex : ∀ i : ι, Convex 𝕜 (F i))
    (h_inter : ∀ I : Set ι, (ncard I ≤ (finrank 𝕜 E) + 1) →
    (⋂ i ∈ I, F i).Nonempty) : (⋂ i : ι, F i).Nonempty := by
  by_cases h_card : Nat.card ι < (finrank 𝕜 E) + 1
  · rw [show ⋂ i, F i = ⋂ i ∈ Set.univ, F i by simp]
    apply h_inter Set.univ
    rw [Set.ncard_univ]
    exact le_of_lt h_card
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ι = n := ⟨Nat.card ι, rfl⟩ -- for induction on ncard F
    simp only [not_lt] at h_card
    rw [hn] at h_card
    induction' n, h_card using Nat.le_induction with k h_card hk generalizing ι
    · rw [show ⋂ i, F i = ⋂ i ∈ Set.univ, F i by simp]
      apply h_inter Set.univ
      rw [Set.ncard_univ]
      exact hn.le
      /- Construct a family of vectors indexed by `ι` such that the vector corresponding to `i : ι`
      is an arbitrary element of the intersection `⋂ i : ι, F i` which *does not lie in `F i`*. -/
    · let a (i : ι) : E := Set.Nonempty.some (s := ⋂₀ (F '' (Set.univ \ {i}))) <| by
        let ι' := Set.univ \ {i}
        let F' : ι' → Set E := fun j ↦ F j
        rw [show ⋂₀ (F '' (Set.univ \ {i})) = ⋂ i, F' i by simp [ι']]
        apply hk (F := F')
        · exact fun i ↦ h_convex ↑i
        · intro J hJ_card
          rw [show (⋂ i ∈ J, F' i) = (⋂ i ∈ Subtype.val '' J, F i) by simp]
          apply h_inter
          exact le_trans Set.ncard_image_le hJ_card
        · rw [Nat.card_coe_set_eq ι', Set.ncard_diff_singleton_of_mem]
          · rw [Set.ncard_univ]
            omega
          · trivial
        · exact Subtype.finite
      /- This family of vectors is not affine independent because the number of them exceeds the
      dimension of the space. -/
      have h2 : ¬AffineIndependent 𝕜 a := by
        have : Fintype ι := by exact Fintype.ofFinite ι -- for instance inferring
        rw [← finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a (n := (k - 1))]
        · exact (Submodule.finrank_le (vectorSpan 𝕜 (Set.range a))).trans (Nat.le_pred_of_lt h_card)
        · rw [Fintype.card_eq_nat_card]; omega
      /- Use `Convex.radon_partition` to conclude there is a subset `I` of `ι` and a point `p : E`
      which lies in the convex hull of either `a '' I` or `a '' Iᶜ`. We claim that `p ∈ ⋂₀ F`. -/
      obtain ⟨I, p, h4_I, h4_Ic⟩ := Convex.radon_partition h2
      use p
      apply Set.mem_iInter_of_mem
      intro i
      /- It suffices to show that for any set `F i` in a subcollection `I` of `ι`, that the convex
      hull of `a '' Iᶜ` is contained in `F i`. -/
      suffices ∀ I : Set ι, i ∈ I → (convexHull 𝕜) (a '' Iᶜ) ⊆ F i by
        by_cases h : i ∈ I
        · exact this I h h4_Ic
        · apply this Iᶜ h; rwa [compl_compl]
      /- Given any subcollection `I` of `ι` containing `i`, because `F i` is convex, we need only
      show that `a j ∈ F i` for each `j ∈ Iᶜ`. -/
      intro I hi
      rw [Convex.convexHull_subset_iff (h_convex i)]
      rintro - ⟨j, hj, rfl⟩
      /- Since `j ∈ Iᶜ` and `i ∈ I`, we conclude that `i ≠ j`, and hence by the definition of `a`:
      `a j ∈ ⋂ F '' (Set.univ \ {j}) ⊆ F i`. -/
      apply Set.mem_of_subset_of_mem (s₁ := ⋂₀ (F '' (Set.univ \ {j})))
      · apply sInter_subset_of_mem
        use i
        simp only [mem_diff, Set.mem_univ, mem_singleton_iff, true_and, and_true]
        exact fun h' ↦ hj (h' ▸ hi)
      · apply Set.Nonempty.some_mem

/-- The version of `Convex.helly_theorem` for infinite families with additional compactness
assumption. -/
theorem Convex.helly_theorem_infinite [TopologicalSpace E] [T2Space E] (F : ι → Set E)
    (h_convex : ∀ i : ι, Convex 𝕜 (F i)) (h_compact : ∀ i : ι, IsCompact (F i)) (h_inf : Infinite ι)
    (h_inter : ∀ I : Set ι, I.Finite → (ncard I ≤ (finrank 𝕜 E) + 1) →
    (⋂ i ∈ I, F i).Nonempty) : (⋂ i : ι, F i).Nonempty := by
    /- By the finite version of theorem, every finite subfamily has an intersection. -/
    have h1 (I : Set ι) (hI_fin : I.Finite) : (⋂ i ∈ I, F i).Nonempty := by
      rw [show ⋂ i ∈ I, F i = ⋂ i : I, F ↑i by simp only [iInter_coe_set]]
      apply Convex.helly_theorem (ι := I) (fun i : I ↦ F i) (𝕜 := 𝕜)
      · simp only [Subtype.forall]; exact fun a _ ↦ h_convex a
      · intro J hJ_card
        rw [show ⋂ i ∈ J, F ↑i = ⋂ i ∈ Subtype.val '' J, F i by
          simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          iInter_exists, iInter_coe_set]]
        have hJ_fin : J.Finite := by
          have : Finite ↑I := hI_fin
          exact toFinite J
        apply h_inter J
        · exact Finite.image Subtype.val hJ_fin
        · exact le_trans (Set.ncard_image_le (hs := hJ_fin)) hJ_card
      · exact hI_fin
    /- The following is a clumsy proof that family of compact sets with the finite intersection
    property has a nonempty intersection -/
    have i0 : ι := Nonempty.some h_inf.nonempty
    rw [show ⋂ i, F i = (F i0) ∩ (⋂ i, F i) by aesop]
    apply IsCompact.inter_iInter_nonempty
    · exact h_compact i0
    · intro i
      exact (h_compact i).isClosed
    · intro I
      simpa using (h1 ({i0} ∪ I))
