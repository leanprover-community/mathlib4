/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure, union
This file contains general results about the topological entropy of various subsets of the same
dynamical system `(X, T)`. We prove that:
- the topological entropy `CoverEntropy T F` of `F` is monotone in `F`: the larger the subset,
the larger its entropy.
- the topological entropy of a subset equals the entropy of its closure.
- the entropy of the union of two sets is the maximum of their entropies. We generalize
the latter property to finite unions.

## Implementation notes
Most results are proved using only the definition of the topological entropy by covers. Some lemmas
of general interest are also proved for nets.

## Main results

## TODO
TODO: one may implement a notion of Hausdorff convergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of the lemmas on closures.

## Tags
closure, entropy, subset, union
-/

namespace Dynamics

variable {X : Type*}

/-! ### Monotonicity of entropy as a function of the subset -/

section Subset

lemma IsDynCoverOf.monotone_subset {T : X → X} {F G : Set X} (F_G : F ⊆ G) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s :=
  F_G.trans h

lemma IsDynNetIn.monotone_subset {T : X → X} {F G : Set X} (F_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynNetIn T F U n s) :
    IsDynNetIn T G U n s :=
  ⟨h.1.trans F_G, h.2⟩

lemma coverMincard_monotone_subset (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone fun F : Set X ↦ coverMincard T F U n :=
  fun _ _ F_G ↦ biInf_mono fun _ h ↦ h.monotone_subset F_G

lemma netMaxcard_monotone_subset (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone fun F : Set X ↦ netMaxcard T F U n :=
  fun _ _ F_G ↦ biSup_mono fun _ h ↦ h.monotone_subset F_G

lemma coverEntropyInfEntourage_monotone (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ coverEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

lemma coverEntropyEntourage_monotone (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ coverEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

lemma netEntropyInfEntourage_monotone (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ netEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

lemma netEntropyEntourage_monotone (T : X → X) (U : Set (X × X)) :
    Monotone fun F : Set X ↦ netEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

lemma coverEntropyInf_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropyInf T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyInfEntourage_monotone T U F_G

lemma coverEntropy_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropy T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyEntourage_monotone T U F_G

end Subset

/-! ### Topological entropy and closure -/

section Closure

open Set Uniformity UniformSpace

variable [UniformSpace X] {T : X → X}

lemma IsDynCoverOf.closure (h : Continuous T) {F : Set X} {U V : Set (X × X)}
    (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X} (s_cover : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (U ○ V) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (compRel_mono (refl U) W_V) fun x x_clos ↦ ?_
  obtain ⟨y, y_x, y_F⟩ := mem_closure_iff_nhds.1 x_clos _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, z_s, y_z⟩ := mem_iUnion₂.1 (s_cover y_F)
  refine mem_iUnion₂.2 ⟨z, z_s, ?_⟩
  rw [mem_ball_symmetry (W_symm.dynEntourage T n)] at y_x
  exact ball_mono (dynEntourage_comp_subset T U W n) z (mem_ball_comp y_z y_x)

lemma coverMincard_closure_le (h : Continuous T) (F : Set X) (U : Set (X × X)) {V : Set (X × X)}
    (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    coverMincard T (closure F) (U ○ V) n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card

open ENat ENNReal EReal Filter Nat

lemma coverEntropyInfEntourage_closure (h : Continuous T) (F : Set X) (U : Set (X × X))
    {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropyInfEntourage T (closure F) (U ○ V) ≤ coverEntropyInfEntourage T F U :=
  liminf_le_liminf <| Eventually.of_forall fun n ↦ monotone_div_right_of_nonneg
    (cast_nonneg' n) (log_monotone (toENNReal_le.2 (coverMincard_closure_le h F U V_uni n)))

lemma coverEntropyEntourage_closure (h : Continuous T) (F : Set X) (U : Set (X × X))
    {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropyEntourage T (closure F) (U ○ V) ≤ coverEntropyEntourage T F U :=
  limsup_le_limsup <| Eventually.of_forall fun n ↦ monotone_div_right_of_nonneg
    (cast_nonneg' n) (log_monotone (toENNReal_le.2 (coverMincard_closure_le h F U V_uni n)))

lemma coverEntropyInf_closure (h : Continuous T) (F : Set X) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))

theorem coverEntropy_closure (h : Continuous T) (F : Set X) :
    coverEntropy T (closure F) = coverEntropy T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

end Closure

/-! ### Topological entropy of finite unions -/

section Union

open Set

lemma IsDynCoverOf.union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F ∪ G) U n (s ∪ t) :=
  union_subset (hs.trans (biUnion_subset_biUnion_left subset_union_left))
    (ht.trans (biUnion_subset_biUnion_left subset_union_right))

lemma coverMincard_union_le (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    coverMincard T (F ∪ G) U n ≤ coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard, ← t_coverMincard, ← ENat.coe_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover

open ExpGrowth

lemma coverEntropyEntourage_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    coverEntropyEntourage T (F ∪ G) U
      = coverEntropyEntourage T F U ⊔ coverEntropyEntourage T G U := by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n ↦ ?_) expGrowthSup_add
    rw [Pi.add_apply, ← ENat.toENNReal_add]
    apply ENat.toENNReal_mono
    exact coverMincard_union_le T F G U n
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

lemma coverEntropy_union [UniformSpace X] (T : X → X) (F G : Set X) :
    coverEntropy T (F ∪ G) = coverEntropy T F ⊔ coverEntropy T G := by
  simp only [coverEntropy, ← iSup_sup_eq, ← iSup_subtype']
  exact biSup_congr fun U _ ↦ coverEntropyEntourage_union T F G U

open Function

lemma some_other_test {α β F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] [Finite ι] (f : F) (g : ι → α) :
    f (⨆ i : ι, g i) =  ⨆ i : ι, f (g i) := by
  apply Finite.induction_empty_option (P := fun ι ↦ ∀ (f : F) (g : ι → α),
    f (⨆ i : ι, g i) =  ⨆ i : ι, f (g i))
  · intro γ δ γ_δ h f g
    specialize h f (g ∘ γ_δ)
    simp only [comp_apply] at h
    rwa [γ_δ.iSup_comp, γ_δ.iSup_comp (g := fun i ↦ f (g i))] at h
  · intro f _
    rw [iSup_of_empty, iSup_of_empty, map_bot f]
  · intro _ _ h f g
    rw [iSup_option g, map_sup f, iSup_option fun i ↦ f (g i), h f fun i ↦ g i]

noncomputable def coverEntropy_supBotHom [UniformSpace X] (T : X → X) :
    SupBotHom (Set X) EReal where
  toFun := coverEntropy T
  map_sup' := coverEntropy_union T
  map_bot' := by
    simp only [bot_eq_empty, coverEntropy_empty]

variable {ι : Type*} [UniformSpace X]

lemma coverEntropyInf_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropyInf_monotone T (subset_iUnion F i)

lemma coverEntropy_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropy T (F i) ≤ coverEntropy T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropy_monotone T (subset_iUnion F i)

lemma coverEntropyInf_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)

lemma coverEntropy_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropy T (F i) ≤ coverEntropy T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropy_monotone T (subset_biUnion_of_mem i_s)

lemma coverEntropy_finite_iUnion [Finite ι] (T : X → X) (F : ι → Set X) :
    coverEntropy T (⋃ i : ι, F i) = ⨆ i : ι, coverEntropy T (F i) := by
  have := some_other_test (coverEntropy_supBotHom T) F
  rw [← SupBotHom.toFun_eq_coe] at this
  exact this

lemma coverEntropy_finite_biUnion (T : X → X) (F : ι → Set X) (s : Finset ι) :
    coverEntropy T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropy T (F i) := by
  have := map_finset_sup (coverEntropy_supBotHom T) s F
  rw [s.sup_set_eq_biUnion, s.sup_eq_iSup, coverEntropy_supBotHom, SupBotHom.coe_mk,
    SupHom.coe_mk] at this
  rw [this]
  congr

end Union

end Dynamics
