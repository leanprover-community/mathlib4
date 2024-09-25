/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure
Proof that the topological entropy depends monotonically on the subset. Main results
are `entropy_monotone_space₁`/`entropy'_monotone_space₁` (for the cover version)
and `entropy_monotone_space₂`/`entropy'_monotone_space₂` (for the net version). I have decided
to keep all the intermediate steps, since they may be useful in the study of other systems.

For uniformly continuous maps, proof that the entropy of a subset is the entropy of its closure.
Main results are `entropy_of_closure` and `entropy'_of_closure`.

TODO: I think one could implement a notion of Hausdorff onvergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of these lemmas on closures.
-/

namespace Dynamics

open EReal ENNReal Set

variable {X : Type*}

/-! ### Monotonicity of entropy as a function of the subset -/

theorem dynCover_monotone_space {T : X → X} {F G : Set X} (F_G : F ⊆ G) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s := Subset.trans F_G h

theorem dynNet_monotone_space {T : X → X} {F G : Set X} (F_G : F ⊆ G ) {U : Set (X × X)} {n : ℕ}
    {s : Set X} (h : IsDynNetOf T F U n s) :
    IsDynNetOf T G U n s := ⟨Subset.trans h.1 F_G, h.2⟩

theorem coverMincard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ coverMincard T F U n) := by
  intro F G F_G
  simp only [coverMincard_eq_sInf T F U n, coverMincard_eq_sInf T G U n]
  exact sInf_le_sInf (image_mono (image_mono fun _ ↦ dynCover_monotone_space F_G))

theorem netMaxcard_monotone_space (T : X → X) (U : Set (X × X)) (n : ℕ) :
    Monotone (fun F : Set X ↦ netMaxcard T F U n) := by
  intro F G F_G
  simp only [netMaxcard_eq_sSup T F U n, netMaxcard_eq_sSup T G U n]
  exact sSup_le_sSup (image_mono (image_mono (fun _ ↦ dynNet_monotone_space F_G)))

theorem coverEntropyInfUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ coverEntropyInfUni T F U) := by
  intro F G F_G
  refine liminf_le_liminf <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_monotone_space T U n F_G

theorem coverEntropySupUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ coverEntropySupUni T F U) := by
  intro F G F_G
  refine limsup_le_limsup <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_monotone_space T U n F_G

theorem netEntropyInfUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ netEntropyInfUni T F U) := by
  intro F G F_G
  refine liminf_le_liminf <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact netMaxcard_monotone_space T U n F_G

theorem netEntropySupUni_monotone_space (T : X → X) (U : Set (X × X)) :
    Monotone (fun F : Set X ↦ netEntropySupUni T F U) := by
  intro F G F_G
  refine limsup_le_limsup <| Filter.eventually_of_forall fun n ↦ ?_
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact netMaxcard_monotone_space T U n F_G

theorem coverEntropyInf_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ coverEntropyInf T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ coverEntropyInfUni_monotone_space T U F_G)

theorem coverEntropySup_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ coverEntropySup T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ coverEntropySupUni_monotone_space T U F_G)

theorem NetEntropyInf_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ netEntropyInf T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ netEntropyInfUni_monotone_space T U F_G)

theorem NetEntropySup_monotone_space [UniformSpace X] (T : X → X) :
    Monotone (fun F : Set X ↦ netEntropySup T F) :=
  fun _ _ F_G ↦ iSup₂_mono (fun U _ ↦ netEntropySupUni_monotone_space T U F_G)

/-! ### Topological entropy of closure -/

open Function Uniformity UniformSpace

theorem dynCover_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T) {F : Set X}
    {U V : Set (X × X)} (V_uni : V ∈ 𝓤 X) {n : ℕ} {s : Set X}
    (s_cover : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (U ○ V) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  rw [id_eq] at W_V
  refine dynCover_monotone (compRel_mono (Subset.refl U) W_V) (fun x x_clos ↦ ?_)
  rcases mem_closure_iff_ball.1 x_clos (dynamical_uni_of_uni h W_uni n) with ⟨y, y_x, y_F⟩
  specialize s_cover y_F
  simp only [iUnion_coe_set, mem_iUnion, exists_prop] at s_cover
  rcases s_cover with ⟨z, z_s, y_z⟩
  simp only [iUnion_coe_set, mem_iUnion, exists_prop]
  use z, z_s
  rw [mem_ball_symmetry (dynamical_uni_of_symm T W_symm n)] at y_x
  exact ball_mono (dynamical_uni_of_comp T U W n) z (mem_ball_comp y_z y_x)

theorem coverMincard_of_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T) (F : Set X)
    (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    coverMincard T (closure F) (U ○ V) n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with (h' | h')
  . exact h' ▸ le_top
  . rcases (coverMincard_finite_iff T F U n).1 h' with ⟨s, s_cover, s_coverMincard⟩
    exact s_coverMincard ▸ coverMincard_le_card (dynCover_closure h V_uni s_cover)

theorem coverEntropyInfUni_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
  (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropyInfUni T (closure F) (U ○ V) ≤ coverEntropyInfUni T F U := by
  refine liminf_le_liminf <| Filter.eventually_of_forall (fun n ↦ ?_)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_of_closure h F U V_uni n

theorem coverEntropySupUni_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) (U : Set (X × X)) {V : Set (X × X)} (V_uni : V ∈ 𝓤 X) :
    coverEntropySupUni T (closure F) (U ○ V) ≤ coverEntropySupUni T F U := by
  refine limsup_le_limsup <| Filter.eventually_of_forall (fun n ↦ ?_)
  apply EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  rw [ENat.toENNReal_le]
  exact coverMincard_of_closure h F U V_uni n

theorem coverEntropyInf_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine le_antisymm (iSup₂_le fun U U_uni ↦ ?_)
    (coverEntropyInf_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (coverEntropyInfUni_antitone T (closure F) V_U)
    (coverEntropyInfUni_closure h F V V_uni))

theorem coverEntropySup_closure [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    (F : Set X) :
    coverEntropySup T (closure F) = coverEntropySup T F := by
  refine le_antisymm (iSup₂_le fun U U_uni ↦ ?_)
    (coverEntropySup_monotone_space T (subset_closure (s := F)))
  rcases comp_mem_uniformity_sets U_uni with ⟨V, V_uni, V_U⟩
  exact le_iSup₂_of_le V V_uni (le_trans (coverEntropySupUni_antitone T (closure F) V_U)
    (coverEntropySupUni_closure h F V V_uni))

/-! ### Topological entropy of unions -/

theorem dynCover_union {T : X → X} {F G : Set X} {U : Set (X × X)} {n : ℕ} {s t : Set X}
    (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F ∪ G) U n (s ∪ t) := by
  intro x x_FG
  rcases x_FG with (x_F | x_G)
  . refine mem_of_subset_of_mem (iSup₂_mono' fun y y_s ↦ ?_) (hs x_F)
    use y, (mem_union_left t y_s)
  . refine mem_of_subset_of_mem (iSup₂_mono' fun y y_t ↦ ?_) (ht x_G)
    use y, (mem_union_right s y_t)

theorem coverMincard_union_le (T : X → X) (F G : Set X) (U : Set (X × X)) (n : ℕ) :
    coverMincard T (F ∪ G) U n ≤ coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with (hF | hF)
  . rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with (hG | hG)
  . rw [hG, add_top]; exact le_top
  rcases (coverMincard_finite_iff T F U n).1 hF with ⟨s, s_cover, s_coverMincard⟩
  rcases (coverMincard_finite_iff T G U n).1 hG with ⟨t, t_cover, t_coverMincard⟩
  rw [← s_coverMincard, ← t_coverMincard]
  have := dynCover_union s_cover t_cover
  rw [← Finset.coe_union s t] at this
  apply le_trans (coverMincard_le_card this) (le_trans (WithTop.coe_mono (Finset.card_union_le s t)) _)
  norm_cast

theorem coverEntropySupUni_union (T : X → X) (F G : Set X) (U : Set (X × X)) :
    coverEntropySupUni T (F ∪ G) U = max (coverEntropySupUni T F U) (coverEntropySupUni T G U) := by
  classical
  rcases F.eq_empty_or_nonempty with (rfl | hF)
  · simp only [empty_union, coverEntropySupUni_bot, bot_le, max_eq_right]
  apply le_antisymm _ (max_le (coverEntropySupUni_monotone_space T U subset_union_left)
    (coverEntropySupUni_monotone_space T U subset_union_right))
  simp only
  have key : ∀ n : ℕ, log (coverMincard T (F ∪ G) U n) / n
      ≤ log (max (coverMincard T F U n) (coverMincard T G U n)) / n + log (2 : ENNReal) / n := by
    intro n
    have h_logm : 0 ≤ log (max (coverMincard T F U n) (coverMincard T G U n)) := by
      rw [Monotone.map_max log_monotone]
      exact le_trans (log_coverMincard_nonneg T hF U n) (le_max_left _ _)
    rw [← div_right_distrib_of_nonneg (c := n) h_logm (zero_le_log_iff.2 one_le_two)]
    apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    rw [← log_mul_add]
    apply log_monotone
    norm_cast
    rw [mul_two]
    exact le_trans (coverMincard_union_le T F G U n) (add_le_add (le_max_left _ _) (le_max_right _ _))
  apply le_trans (limsup_le_limsup (Filter.eventually_of_forall fun n ↦ key n))
  have := Filter.Tendsto.limsup_eq <| EReal.tendsto_const_div_atTop_nhds_zero_nat
    (ne_of_gt (bot_lt_log_iff.2 Nat.ofNat_pos)) (ne_of_lt (log_lt_top_iff.2 two_lt_top))
  apply le_trans (limsup_add_le_add_limsup (Or.inr (this ▸ EReal.zero_ne_top))
    (Or.inr (this ▸ EReal.zero_ne_bot)))
  apply le_of_eq
  rw [coverEntropySupUni, coverEntropySupUni, this, add_zero, ← limsup_max]
  congr
  ext n
  rw [Monotone.map_max log_monotone,
    Monotone.map_max (EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' n))]

theorem coverEntropySup_union [UniformSpace X] (T : X → X) (F G : Set X) :
    coverEntropySup T (F ∪ G) = max (coverEntropySup T F) (coverEntropySup T G) := by
  rw [coverEntropySup, coverEntropySup, coverEntropySup, iSup_subtype', iSup_subtype',
    iSup_subtype', ← _root_.sup_eq_max, ← iSup_sup_eq]
  congr
  ext U_uni
  exact coverEntropySupUni_union T F G U_uni.1

theorem coverEntropyInf_union [UniformSpace X] (T : X → X) {F G : Set X}
    (hF : MapsTo T F F) (hG : MapsTo T G G) :
    coverEntropyInf T (F ∪ G) = max (coverEntropyInf T F) (coverEntropyInf T G) := by
  rw [coverEntropyInf_eq_coverEntropySup T hF,
    coverEntropyInf_eq_coverEntropySup T hG, ← coverEntropySup_union T F G]
  exact coverEntropyInf_eq_coverEntropySup T (MapsTo.union_union hF hG)

/-! ### Topological entropy of finite unions -/

theorem coverEntropySup_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropySup T (F i) ≤ coverEntropySup T (⋃ i, F i) :=
  iSup_le (fun i ↦ (coverEntropySup_monotone_space T (subset_iUnion F i)))

theorem coverEntropySup_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropySup T (F i) ≤ coverEntropySup T (⋃ i ∈ s, F i) :=
  iSup₂_le (fun _ i_s ↦ (coverEntropySup_monotone_space T (subset_biUnion_of_mem i_s)))

theorem coverEntropyInf_iUnion_le {ι : Type*} [UniformSpace X] (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i, F i) :=
  iSup_le (fun i ↦ (coverEntropyInf_monotone_space T (subset_iUnion F i)))

theorem coverEntropyInf_biUnion_le {ι : Type*} [UniformSpace X] (s : Set ι) (T : X → X)
   (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le (fun _ i_s ↦ (coverEntropyInf_monotone_space T (subset_biUnion_of_mem i_s)))

theorem coverEntropySup_finite_iUnion {ι : Type*} [UniformSpace X] [Fintype ι] (T : X → X)
    (F : ι → Set X) :
    coverEntropySup T (⋃ i, F i) = ⨆ i, coverEntropySup T (F i) := by
  apply Fintype.induction_empty_option (P := fun ι _ ↦ ∀ F : ι → Set X,
    coverEntropySup T (⋃ i, F i) = ⨆ i, coverEntropySup T (F i))
  · intro α β _ α_β h F
    specialize h (F ∘ α_β)
    simp only [comp_apply] at h
    rw [← iUnion_congr_of_surjective (g := F) α_β (Equiv.surjective α_β) (fun _ ↦ comp_apply), h]
    exact Equiv.iSup_comp (g := fun i : β ↦ coverEntropySup T (F i)) α_β
  · intro _
    simp only [iUnion_of_empty, coverEntropySup_bot, ciSup_of_empty]
  · intro α _ h F
    rw [iSup_option, iUnion_option, coverEntropySup_union T (F none) (⋃ i, F (some i)),
      _root_.sup_eq_max]
    congr
    exact h (fun i : α ↦ F (some i))

theorem CoverEntropySup_finite_biUnion {ι : Type*} [UniformSpace X] (s : Finset ι) (T : X → X)
    (F : ι → Set X) :
    coverEntropySup T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropySup T (F i) := by
  have fin_coe : Fintype { i // i ∈ s } := FinsetCoe.fintype s
  have := @coverEntropySup_finite_iUnion X {i // i ∈ s} _ fin_coe T (fun i ↦ F i)
  rw [iSup_subtype', ← this, iUnion_subtype]

theorem CoverEntropyInf_finite_iUnion {ι : Type*} [UniformSpace X] [Fintype ι] {T : X → X}
    {F : ι → Set X} (h : ∀ i, MapsTo T (F i) (F i)) :
    coverEntropyInf T (⋃ i, F i) = ⨆ i, coverEntropyInf T (F i) := by
  rw [coverEntropyInf_eq_coverEntropySup T (mapsTo_iUnion_iUnion h),
    coverEntropySup_finite_iUnion T F]
  exact iSup_congr (fun i ↦ Eq.symm (coverEntropyInf_eq_coverEntropySup T (h i)))

theorem CoverEntropyInf_finite_biUnion {ι : Type*} [UniformSpace X] (s : Finset ι)
    (T : X → X) {F : ι → Set X} (h : ∀ i ∈ s, MapsTo T (F i) (F i)) :
    coverEntropyInf T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropyInf T (F i) := by
  rw [coverEntropyInf_eq_coverEntropySup T (mapsTo_iUnion₂_iUnion₂ h),
    CoverEntropySup_finite_biUnion s T F]
  exact biSup_congr' (fun i i_s ↦ Eq.symm (coverEntropyInf_eq_coverEntropySup T (h i i_s)))

end Dynamics

#lint
