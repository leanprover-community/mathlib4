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
  use Finset.image f (Finset.image g s)
  refine And.intro (fun x x_F ↦ ?_) (Finset.card_image_le.trans (Finset.card_image_le.trans s_card))
  rw [← Semiconj.preimage_dynEntourage h (V ○ V) n, mem_iUnion₂]
  simp only [Finset.coe_image, mem_image, Finset.mem_coe, exists_exists_and_eq_and, ball,
    mem_preimage, Prod.map_apply, exists_prop]
  specialize s_cover (mem_image_of_mem φ x_F)
  simp only [Finset.mem_coe, mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨y, y_s, hy⟩
  use y, y_s
  specialize gs_cover y y_s
  rw [(f_section (g y) gs_cover.2).2]
  exact (dynEntourage_comp_subset T V V n)
    (mem_comp_of_mem_ball (V_symm.dynEntourage T n) gs_cover.1 hy)

lemma IsDynNetIn.preimage (h : Semiconj φ S T) {F : Set X} {V : Set (Y × Y)} {n : ℕ} {t : Finset Y}
    (h' : IsDynNetIn T (φ '' F) V n t) :
    ∃ s : Finset X, IsDynNetIn S F ((Prod.map φ φ) ⁻¹' V) n s ∧ t.card ≤ s.card := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | t_nemp
  · use ∅
    simp [isDynNetIn_empty]
  have _ : Nonempty X := Nonempty.to_type (Nonempty.of_image (Nonempty.mono h'.1 t_nemp))
  have (y : Y) (y_t : y ∈ t) : ∃ x ∈ F, φ x = y := h'.1 y_t
  choose! f f_section using this
  use Finset.image f t
  split_ands
  · intro y y_ft
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at y_ft
    rcases y_ft with ⟨x, x_t, y_fx⟩
    rw [← y_fx]
    exact (f_section x x_t).1
  · rw [Finset.coe_image, ← Semiconj.preimage_dynEntourage h V n]
    apply (InjOn.pairwiseDisjoint_image _).2
    · intro x x_t y y_t x_y inter_balls inter_x inter_y z z_inter
      specialize inter_x z_inter
      specialize inter_y z_inter
      simp only [ball, comp_apply, mem_preimage, Prod.map_apply] at inter_x inter_y
      rw [(f_section x x_t).2] at inter_x
      rw [(f_section y y_t).2] at inter_y
      replace inter_x : {φ z} ⊆ ball x (dynEntourage T V n) := singleton_subset_iff.2 inter_x
      replace inter_y : {φ z} ⊆ ball y (dynEntourage T V n) := singleton_subset_iff.2 inter_y
      have := h'.2 x_t y_t x_y inter_x inter_y
      simp only [bot_eq_empty, le_eq_subset, subset_empty_iff, singleton_ne_empty] at this
    · intro x x_t y y_t fx_fy
      rw [← (f_section x x_t).2, ← (f_section y y_t).2, fx_fy]
  · apply le_trans (b := (Finset.image (φ ∘ f) t).card)
    · refine Finset.card_mono (fun x x_t ↦ ?_)
      rw [← (f_section x x_t).2]
      exact Finset.mem_image_of_mem (φ ∘ f) x_t
    · rw [← Finset.image_image]
      exact Finset.card_image_le

lemma le_coverMincard_image (h : Semiconj φ S T) (F : Set X) {V : Set (Y × Y)}
    (V_symm : SymmetricRel V) (n : ℕ) :
    coverMincard S F ((Prod.map φ φ) ⁻¹' (V ○ V)) n ≤ coverMincard T (φ '' F) V n := by
  rcases eq_top_or_lt_top (coverMincard T (φ '' F) V n) with h' | h'
  · exact h' ▸ le_top
  rcases (coverMincard_finite_iff T (φ '' F) V n).1 h' with ⟨t, t_cover, t_card⟩
  rcases t_cover.preimage h V_symm with ⟨s, s_cover, s_card⟩
  rw [← t_card]
  exact s_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 s_card)

lemma netMaxcard_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) (n : ℕ) :
    netMaxcard T (φ '' F) V n ≤ netMaxcard S F ((Prod.map φ φ) ⁻¹' V) n := by
  rcases lt_or_eq_of_le (le_top (a := netMaxcard T (φ '' F) V n)) with h' | h'
  · rcases (netMaxcard_finite_iff T (φ '' F) V n).1 h' with ⟨t, t_net, t_card⟩
    rcases t_net.preimage h with ⟨s, s_net, s_card⟩
    rw [← t_card]
    exact (WithTop.coe_le_coe.2 s_card).trans s_net.card_le_netMaxcard
  · apply le_top.trans_eq (Eq.symm _)
    refine (netMaxcard_infinite_iff S F ((Prod.map φ φ) ⁻¹' V) n).2 (fun k ↦ ?_)
    rcases (netMaxcard_infinite_iff T (φ '' F) V n).1 h' k with ⟨t, t_net, t_card⟩
    rcases t_net.preimage h with ⟨s, s_net, s_card⟩
    exact ⟨s, s_net, t_card.trans s_card⟩

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

lemma netEntropyEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    netEntropyEntourage T (φ '' F) V ≤ netEntropyEntourage S F ((Prod.map φ φ) ⁻¹' V) := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (netMaxcard_image_le h F V n))

lemma netEntropyInfEntourage_image_le (h : Semiconj φ S T) (F : Set X) (V : Set (Y × Y)) :
    netEntropyInfEntourage T (φ '' F) V ≤ netEntropyInfEntourage S F ((Prod.map φ φ) ⁻¹' V) := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
  exact log_monotone (ENat.toENNReal_mono (netMaxcard_image_le h F V n))

theorem coverEntropy_image (u : UniformSpace Y) {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Semiconj φ S T) (F : Set X) :
    coverEntropy T (φ '' F) = @coverEntropy X (comap φ u) S F := by
  apply le_antisymm
  · rw [coverEntropy_eq_iSup_netEntropyEntourage T (φ '' F)]
    refine iSup₂_le fun V V_uni ↦ (netEntropyEntourage_image_le h F V).trans ?_
    apply @netEntropyEntourage_le_coverEntropy X (comap φ u) S F
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
  · rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T (φ '' F)]
    refine iSup₂_le fun V V_uni ↦ (netEntropyInfEntourage_image_le h F V).trans ?_
    apply @netEntropyInfEntourage_le_coverEntropyInf X (comap φ u) S F
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
