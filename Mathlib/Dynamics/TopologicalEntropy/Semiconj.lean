/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of the image of a set under a semiconjugacy
The main lemma is `image_entropy`/`image_entropy'`: the entropy of the image of a set by a
semiconjugacy is the entropy of the set for the inverse image filter. This lemma needs very little
hypotheses, and generalizes many important results.

First, a uniformly continuous semiconjugacy descreases the entropy of subsets:
`image_entropy_uniformContinuous_le`, `image_entropy'_uniformContinuous_le`.

Second, the entropy of `Set.univ` for a subsystem is equal to the entropy of the subset, which
justifies the implementation of the entropy of a subset: `subset_restriction_entropy`.

TODO: Investigate the consequences of `image_entropy` for embeddings.

TODO: There are some interesting related results about the entropy of fibered systems.

/- TODO : Is it possible to have an implicit instance of UniformSpace X instead of an explicit
  argument ?-/

/- TODO : Try to get a lower bound on the entropy of the image. What is a right hypothesis on φ ?
  Of course UX ≤ UniformSpace.comap φ UY works, but are there "natural" statements
  (proper map...) ? -/
-/

namespace Dynamics

open Function Set Uniformity UniformSpace

variable {X Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}

lemma IsDynCoverOf.preimage (h : Semiconj φ S T) {F : Set X} {V : Set (Y × Y)}
    (V_symm : SymmetricRel V) {n : ℕ} {t : Finset Y} (h' : IsDynCoverOf T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynCoverOf S F ((Prod.map φ φ) ⁻¹' (V ○ V)) n s ∧ s.card ≤ t.card := by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · use ∅
    simp [eq_empty_of_isEmpty F]
  rcases h'.nonempty_inter with ⟨s, s_cover, s_card, s_inter⟩
  replace s_inter := fun (x : Y) (h : x ∈ s) ↦ nonempty_def.1 (s_inter x h)
  choose! g gs_cover using s_inter
  have (y : Y) (a : y ∈ φ '' F) : ∃ x ∈ F, φ x = y := a
  choose! f f_section using this
  use Finset.image (f  ∘ g) s
  apply And.intro _ (Finset.card_image_le.trans s_card)
  simp only [IsDynCoverOf, Finset.mem_coe, image_subset_iff, preimage_iUnion₂] at s_cover ⊢
  apply s_cover.trans
  rw [← Semiconj.preimage_dynEntourage h (V ○ V) n, Finset.set_biUnion_finset_image]
  refine iUnion₂_mono fun i i_s ↦ ?_
  specialize s_cover (mem_image_of_mem φ x_F)
  simp only [Finset.mem_coe, mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨y, y_s, hy⟩
  use y, y_s
  specialize gs_cover y y_s
  rw [(f_section (g y) gs_cover.2).2]
  exact (dynEntourage_comp_subset T V V n)
    (mem_comp_of_mem_ball (V_symm.dynEntourage T n) gs_cover.1 hy)

-- Finir preuve
-- Utiliser une seule fois AOC ?

lemma IsDynCoverOf.image (h : Semiconj φ S T) {F : Set X} {V : Set (Y × Y)} {n : ℕ} {s : Finset X}
    (h' : IsDynCoverOf S F ((Prod.map φ φ) ⁻¹' V) n s) :
    ∃ t : Finset Y, IsDynCoverOf T (φ '' F) V n t ∧ t.card ≤ s.card := by
  classical
  use Finset.image φ s
  apply And.intro _ Finset.card_image_le
  simp only [IsDynCoverOf, image_subset_iff, preimage_iUnion₂]
  apply h'.trans
  simp only [Finset.mem_coe, Finset.set_biUnion_finset_image]
  refine iUnion₂_mono fun i _ ↦ subset_of_eq ?_
  rw [← Semiconj.preimage_dynEntourage h V n]
  ext x
  simp only [ball, mem_preimage, Prod.map_apply]

-- TODO : check DynEntourage file and tweak the lemma ?

lemma le_coverMincard_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : SymmetricRel V) (n : ℕ) :
    coverMincard S F ((Prod.map φ φ) ⁻¹' (V ○ V)) n ≤ coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  rcases (coverMincard_finite_iff T (φ '' F) V n).1 h' with ⟨t, t_cover, t_card⟩
  rcases t_cover.preimage h V_symm with ⟨s, s_cover, s_card⟩
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s_card)

lemma coverMincard_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    coverMincard T (φ '' F) V n ≤ coverMincard S F ((Prod.map φ φ) ⁻¹' V) n := by
  rcases eq_top_or_lt_top (coverMincard S F ((Prod.map φ φ) ⁻¹' V) n) with h' | h'
  · exact h' ▸ le_top
  rcases (coverMincard_finite_iff S F ((Prod.map φ φ) ⁻¹' V) n).1 h' with ⟨s, s_cover, s_card⟩
  rw [← s_card]
  rcases s_cover.image h with ⟨t, t_cover, t_card⟩
  exact t_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 t_card)

open ENNReal EReal Filter

lemma le_coverEntropyEntourage_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : SymmetricRel V) :
    coverEntropyEntourage S F ((Prod.map φ φ) ⁻¹' (V ○ V))
      ≤ coverEntropyEntourage T (φ '' F) V := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (le_coverMincard_image h F V_symm n))

lemma le_coverEntropyInfEntourage_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : SymmetricRel V) :
    coverEntropyInfEntourage S F ((Prod.map φ φ) ⁻¹' (V ○ V))
      ≤ coverEntropyInfEntourage T (φ '' F) V := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (le_coverMincard_image h F V_symm n))

lemma coverEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    coverEntropyEntourage T (φ '' F) V ≤ coverEntropyEntourage S F ((Prod.map φ φ) ⁻¹' V) := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (coverMincard_image_le h F V n))

lemma coverEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    coverEntropyInfEntourage T (φ '' F) V
      ≤ coverEntropyInfEntourage S F ((Prod.map φ φ) ⁻¹' V) := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (coverMincard_image_le h F V n))

theorem coverEntropy_image (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropy T (φ '' F) = @coverEntropy X (comap φ u) S F := by
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦ (coverEntropyEntourage_image_le h F V).trans ?_
    apply @coverEntropyEntourage_le_coverEntropy X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    exact ⟨V, V_uni, Set.Subset.refl _⟩
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    simp only [uniformity_comap φ, mem_comap] at U_uni
    rcases U_uni with ⟨V, V_uni, V_sub⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, W_uni, W_symm, W_V⟩
    apply (coverEntropyEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyEntourage_image h F W_symm).trans
    exact coverEntropyEntourage_le_coverEntropy T (φ '' F) W_uni

theorem coverEntropyInf_image (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropyInf T (φ '' F) = @coverEntropyInf X (comap φ u) S F := by
  apply le_antisymm
  · refine iSup₂_le fun V V_uni ↦ (coverEntropyInfEntourage_image_le h F V).trans ?_
    apply @coverEntropyInfEntourage_le_coverEntropyInf X (comap φ u) S F
    rw [uniformity_comap φ, mem_comap]
    exact ⟨V, V_uni, Set.Subset.refl _⟩
  · refine iSup₂_le (fun U U_uni ↦ ?_)
    simp only [uniformity_comap φ, mem_comap] at U_uni
    rcases U_uni with ⟨V, V_uni, V_sub⟩
    rcases comp_symm_mem_uniformity_sets V_uni with ⟨W, W_uni, W_symm, W_V⟩
    apply (coverEntropyInfEntourage_antitone S F ((preimage_mono W_V).trans V_sub)).trans
    apply (le_coverEntropyInfEntourage_image h F W_symm).trans
    exact coverEntropyInfEntourage_le_coverEntropyInf T (φ '' F) W_uni

theorem coverEntropy_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropy T (φ '' F) ≤ coverEntropy S F := by
  rw [coverEntropy_image _ h F]
  exact coverEntropy_antitone S F (uniformContinuous_iff.1 h')

theorem coverEntropyInf_image_le_of_uniformContinuous [UniformSpace X] [UniformSpace Y] {S : X → X}
    {T : Y → Y} {φ : X → Y} (h : Semiconj φ S T) (h' : UniformContinuous φ) (F : Set X) :
    coverEntropyInf T (φ '' F) ≤ coverEntropyInf S F := by
  rw [coverEntropyInf_image _ h F]
  exact coverEntropyInf_antitone S F (uniformContinuous_iff.1 h')

theorem coverEntropy_restrict [UniformSpace X] {T : X → X} {F : Set X} (h : MapsTo T F F) :
    coverEntropy (MapsTo.restrict T F F h) univ = coverEntropy T F := by
  rw [← coverEntropy_image _ (MapsTo.val_restrict_apply h) univ, image_univ,
    Subtype.range_coe_subtype, setOf_mem_eq]

end Dynamics
