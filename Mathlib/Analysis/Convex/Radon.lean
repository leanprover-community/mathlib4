/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov, Jireh Loreaux
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
theorem helly_theorem (F : Set (Set E)) {hF_fin : Set.Finite F}
    (h_card : (finrank 𝕜 E) + 1 ≤ ncard F) (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Set (Set E), (G ⊆ F) → (ncard G = (finrank 𝕜 E) + 1) →
    (⋂₀ G).Nonempty) : (⋂₀ F).Nonempty := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ncard F = n := ⟨ncard F, rfl⟩ -- for induction on ncard F
  rw [hn] at h_card
  induction' n, h_card using Nat.le_induction with k h_card hk generalizing F
  exact h_inter F (Eq.subset rfl) hn
  /- construct a family of vectors indexed by `F` such that the vector corresponding to `X : F` is
  an arbitrary element of the intersection `⋂₀ F` which *does not lie in `X`*. -/
  let a : F → E := fun X : F ↦ Set.Nonempty.some (s := ⋂₀ (F \ {(X : Set E)})) <| by
    apply @hk _ (Finite.diff hF_fin {(X : Set E)})
    · exact fun Y hY ↦ h_convex Y (mem_of_mem_diff hY)
    · exact fun G hG_1 hG_2 ↦ h_inter G (Subset.trans hG_1 (diff_subset F {(X : Set E)})) hG_2
    · rw [ncard_diff_singleton_of_mem X.property hF_fin, Nat.sub_eq_of_eq_add hn]
  /- This family of vectors is not affine independent because the number of them exceeds the
  dimension of the space. -/
  have h2 : ¬AffineIndependent 𝕜 a := by
    have : Fintype ↑F := Finite.fintype hF_fin -- for instance inferring
    rw [←finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a (n := (k - 1))]
    · exact (Submodule.finrank_le (vectorSpan 𝕜 (Set.range a))).trans (Nat.le_pred_of_lt h_card)
    · rw [←Finite.card_toFinset hF_fin, ←ncard_eq_toFinset_card F hF_fin, hn,
        ←Nat.sub_add_comm (Nat.one_le_of_lt h_card)]
      rfl
  /- Use `Convex.radon_partition` to conclude there is a subset `I` of `F` and a point `p : E`
  which lies in the convex hull of either `a '' I` or `a '' Iᶜ`. We claim that `p ∈ ⋂₀ F`.
  (here `Iᶜ` is the complement within `F`, i.e., it is effectively `F \ I`.) -/
  obtain ⟨I, p, h4_I, h4_Ic⟩ := Convex.radon_partition h2
  refine ⟨p, fun X hX ↦ ?_⟩
  lift X to F using hX
  /- It suffices to show that for any set `X` in a subcollection `I` of `F`, that the convex hull
  of `a '' Iᶜ` is contained in `X`. -/
  suffices ∀ I : Set F, X ∈ I → (convexHull 𝕜) (a '' Iᶜ) ⊆ X by
    by_cases (X ∈ I)
    · exact this I h h4_Ic
    · apply this Iᶜ h; rwa [compl_compl]
  /- Given any subcollection `I` of `F` containing `X`, because `X` is convex, we need only show
  that `a Y ∈ X` for each `Y ∈ Iᶜ` -/
  intro I h
  rw [Convex.convexHull_subset_iff (h_convex _ X.prop)]
  rintro - ⟨Y, hY, rfl⟩
  /- Since `Y ∈ Iᶜ` and `X ∈ I`, we conclude that `X ≠ Y`, and hence by the definition of `a`:
  `a Y ∈ ⋂₀ F \ {Y} ⊆ X`  -/
  have : X ≠ Y := fun h' ↦ hY (h' ▸ h)
  exact (sInter_subset_of_mem <| mem_diff_singleton.mpr ⟨X.prop, Subtype.coe_injective.ne this⟩)
    (Set.Nonempty.some_mem _)
