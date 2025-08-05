/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy
Consider two dynamical systems `(X, S)` and `(Y, T)` together with a semiconjugacy `φ`:


```
X ---S--> X
|         |
φ         φ
|         |
v         v
Y ---T--> Y
```

We relate the topological entropy of a subset `F ⊆ X` with the topological entropy
of its image `φ '' F ⊆ Y`.

The best-known theorem is that, if all maps are uniformly continuous, then
`coverEntropy T (φ '' F) ≤ coverEntropy S F`. This is theorem
`coverEntropy_image_le_of_uniformContinuous` herein. We actually prove the much more general
statement that `coverEntropy T (φ '' F) = coverEntropy S F` if `X` is endowed with the pullback
by `φ` of the uniform structure of `Y`.

This more general statement has another direct consequence: if `F` is `S`-invariant, then the
topological entropy of the restriction of `S` to `F` is exactly `coverEntropy S F`. This
corollary is essential: in most references, the entropy of an invariant subset (or subsystem) `F` is
defined as the entropy of the restriction to `F` of the system. We chose instead to give a direct
definition of the topological entropy of a subset, so as to avoid working with subtypes. Theorem
`coverEntropy_restrict` shows that this choice is coherent with the literature.

## Implementation notes
We use only the definition of the topological entropy using covers; the simplest version of
`IsDynCoverOf.image` for nets fails.

## Main results
- `coverEntropy_image_of_comap`/`coverEntropyInf_image_of_comap`: the entropy of `φ '' F` equals
the entropy of `F` if `X` is endowed with the pullback by `φ` of the uniform structure of `Y`.
- `coverEntropy_image_le_of_uniformContinuous`/`coverEntropyInf_image_le_of_uniformContinuous`:
the entropy of `φ '' F` is lower than the entropy of `F` if `φ` is uniformly continuous.
- `coverEntropy_restrict`: the entropy of the restriction of `S` to an invariant set `F` is
`coverEntropy S F`.

## Tags
entropy, semiconjugacy
-/

namespace Dynamics

open Function Prod Set Uniformity UniformSpace

variable {X Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}

lemma IsDynCoverOf.image (h : Semiconj φ S T) {F : Set X} {V : Set (Y × Y)} {n : ℕ} {s : Set X}
    (h' : IsDynCoverOf S F ((map φ φ) ⁻¹' V) n s) :
    IsDynCoverOf T (φ '' F) V n (φ '' s) := by
  simp only [IsDynCoverOf, image_subset_iff, preimage_iUnion₂, biUnion_image]
  refine h'.trans (iUnion₂_mono fun i _ ↦ subset_of_eq ?_)
  rw [← h.preimage_dynEntourage V n, ball_preimage]

lemma IsDynCoverOf.preimage (h : Semiconj φ S T) {F : Set X} {V : Set (Y × Y)}
    (V_symm : IsSymmetricRel V) {n : ℕ} {t : Finset Y} (h' : IsDynCoverOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynCoverOf S F ((map φ φ) ⁻¹' (V ○ V)) n s ∧ s.card ≤ t.card := by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · exact ⟨∅, eq_empty_of_isEmpty F ▸ ⟨isDynCoverOf_empty, Finset.card_empty ▸ zero_le t.card⟩⟩
  -- If `t` is a dynamical cover of `φ '' F`, then we want to choose one preimage by `φ` for each
  -- element of `t`. This is complicated by the fact that `t` may not be a subset of `φ '' F`,
  -- and may not even be in the range of `φ`. Hence, we first modify `t` to make it a subset
  -- of `φ '' F`. This requires taking larger entourages.
  obtain ⟨s, s_cover, s_card, s_inter⟩ := h'.nonempty_inter
  choose! g gs_cover using fun (x : Y) (h : x ∈ s) ↦ nonempty_def.1 (s_inter x h)
  choose! f f_section using fun (y : Y) (a : y ∈ φ '' F) ↦ a
  refine ⟨s.image (f ∘ g), ?_, Finset.card_image_le.trans s_card⟩
  simp only [IsDynCoverOf, Finset.mem_coe, image_subset_iff, preimage_iUnion₂] at s_cover ⊢
  apply s_cover.trans
  rw [← h.preimage_dynEntourage (V ○ V) n, Finset.set_biUnion_finset_image]
  refine iUnion₂_mono fun i i_s ↦ ?_
  rw [comp_apply, ball_preimage, (f_section (g i) (gs_cover i i_s).2).2]
  refine preimage_mono fun x x_i ↦ mem_ball_dynEntourage_comp T n V_symm x (g i) ⟨i, ?_⟩
  replace gs_cover := (gs_cover i i_s).1
  rw [mem_ball_symmetry (V_symm.dynEntourage T n)] at x_i gs_cover
  exact ⟨x_i, gs_cover⟩

lemma le_coverMincard_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : IsSymmetricRel V) (n : ℕ) :
    coverMincard S F ((map φ φ) ⁻¹' (V ○ V)) n ≤ coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨t, t_cover, t_card⟩ := (coverMincard_finite_iff T (φ '' F) V n).1 h'
  obtain ⟨s, s_cover, s_card⟩ := t_cover.preimage h V_symm
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s_card)

lemma coverMincard_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    coverMincard T (φ '' F) V n ≤ coverMincard S F ((map φ φ) ⁻¹' V) n := by
  classical
  rcases eq_top_or_lt_top (coverMincard S F ((map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_card⟩ := (coverMincard_finite_iff S F ((map φ φ) ⁻¹' V) n).1 h'
  rw [← s_card]
  have := s_cover.image h
  rw [← s.coe_image] at this
  exact this.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s.card_image_le)

open ENNReal EReal ExpGrowth Filter

lemma le_coverEntropyEntourage_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : IsSymmetricRel V) :
    coverEntropyEntourage S F ((map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropyEntourage T (φ '' F) V :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (le_coverMincard_image h F V_symm n)

lemma le_coverEntropyInfEntourage_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : IsSymmetricRel V) :
    coverEntropyInfEntourage S F ((map φ φ) ⁻¹' (V ○ V)) ≤ coverEntropyInfEntourage T (φ '' F) V :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (le_coverMincard_image h F V_symm n)

lemma coverEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    coverEntropyEntourage T (φ '' F) V ≤ coverEntropyEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_image_le h F V n)

lemma coverEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    coverEntropyInfEntourage T (φ '' F) V ≤ coverEntropyInfEntourage S F ((map φ φ) ⁻¹' V) :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_image_le h F V n)

/-- The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pullback by `φ`
  of the uniform structure of `Y`. -/
theorem coverEntropy_image_of_comap (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropy T (φ '' F) = @coverEntropy X (comap φ u) S F := by
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦ (coverEntropyEntourage_image_le h F V).trans ?_
    apply @coverEntropyEntourage_le_coverEntropy X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    exact ⟨V, V_uni, Subset.rfl⟩
  · refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyEntourage_image h F W_symm).trans
    exact coverEntropyEntourage_le_coverEntropy T (φ '' F) W_uni

/-- The entropy of `φ '' F` equals the entropy of `F` if `X` is endowed with the pullback by `φ`
  of the uniform structure of `Y`. This version uses a `liminf`. -/
theorem coverEntropyInf_image_of_comap (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropyInf T (φ '' F) = @coverEntropyInf X (comap φ u) S F := by
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦ (coverEntropyInfEntourage_image_le h F V).trans ?_
    apply @coverEntropyInfEntourage_le_coverEntropyInf X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    exact ⟨V, V_uni, Subset.rfl⟩
  · refine iSup₂_le fun U U_uni ↦ ?_
    simp only [uniformity_comap φ, mem_comap] at U_uni
    obtain ⟨V, V_uni, V_sub⟩ := U_uni
    obtain ⟨W, W_uni, W_symm, W_V⟩ := comp_symm_mem_uniformity_sets V_uni
    apply (coverEntropyInfEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyInfEntourage_image h F W_symm).trans
    exact coverEntropyInfEntourage_le_coverEntropyInf T (φ '' F) W_uni

open Subtype

lemma coverEntropy_restrict_subset [UniformSpace X] {T : X → X} {F G : Set X} (hF : F ⊆ G)
    (hG : MapsTo T G G) :
    coverEntropy (hG.restrict T G G) (val ⁻¹' F) = coverEntropy T F := by
  rw [← coverEntropy_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F), image_preimage_coe G F,
    inter_eq_right.2 hF]

lemma coverEntropyInf_restrict_subset [UniformSpace X] {T : X → X} {F G : Set X} (hF : F ⊆ G)
    (hG : MapsTo T G G) :
    coverEntropyInf (hG.restrict T G G) (val ⁻¹' F) = coverEntropyInf T F := by
  rw [← coverEntropyInf_image_of_comap _ hG.val_restrict_apply (val ⁻¹' F), image_preimage_coe G F,
    inter_eq_right.2 hF]

/-- The entropy of the restriction of `T` to an invariant set `F` is `coverEntropy S F`. This
theorem justifies our definition of `coverEntropy T F`. -/
theorem coverEntropy_restrict [UniformSpace X] {T : X → X} {F : Set X} (h : MapsTo T F F) :
    coverEntropy (h.restrict T F F) univ = coverEntropy T F := by
  rw [← coverEntropy_restrict_subset Subset.rfl h, coe_preimage_self F]

/-- The entropy of `φ '' F` is lower than entropy of `F` if  `φ` is uniformly continuous. -/
theorem coverEntropy_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropy T (φ '' F) ≤ coverEntropy S F := by
  rw [coverEntropy_image_of_comap _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff.1 h')

/-- The entropy of `φ '' F` is lower than entropy of `F` if  `φ` is uniformly continuous. This
  version uses a `liminf`. -/
theorem coverEntropyInf_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [coverEntropyInf_image_of_comap _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff.1 h')

lemma coverEntropy_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F ⊆ G) (hG : MapsTo S G G) :
    coverEntropy T (φ '' F) ≤ coverEntropy S F := by
  rw [← coverEntropy_restrict_subset hF hG]
  have hφ : Semiconj (G.restrict φ) (hG.restrict S G G) T := by
    intro x
    rw [G.restrict_apply, G.restrict_apply, hG.val_restrict_apply, h.eq x]
  apply (coverEntropy_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_restrict_image, image_preimage_coe G F, inter_eq_right.2 hF]

lemma coverEntropyInf_image_le_of_uniformContinuousOn_invariant [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) {F G : Set X}
    (h' : UniformContinuousOn φ G) (hF : F ⊆ G) (hG : MapsTo S G G) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [← coverEntropyInf_restrict_subset hF hG]
  have hφ : Semiconj (G.restrict φ) (hG.restrict S G G) T := by
    intro a
    rw [G.restrict_apply, G.restrict_apply, hG.val_restrict_apply, h.eq a]
  apply (coverEntropyInf_image_le_of_uniformContinuous hφ
    (uniformContinuousOn_iff_restrict.1 h') (val ⁻¹' F)).trans_eq'
  rw [← image_image_val_eq_restrict_image, image_preimage_coe G F, inter_eq_right.2 hF]

end Dynamics
