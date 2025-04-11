/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Topological entropy via nets
We implement Bowen-Dinaburg's definitions of the topological entropy, via nets.

The major design decisions are the same as in `Mathlib.Dynamics.TopologicalEntropy.CoverEntropy`,
and are explained in detail there: use of uniform spaces, definition of the topological entropy of
a subset, and values taken in `EReal`.

Given a map `T : X → X` and a subset `F ⊆ X`, the topological entropy is loosely defined using
nets as the exponential growth (in `n`) of the number of distinguishable orbits of length `n`
starting from `F`. More precisely, given an entourage `U`, two orbits of length `n` can be
distinguished if there exists some index `k < n` such that `T^[k] x` and `T^[k] y` are far enough
(i.e. `(T^[k] x, T^[k] y)` is not in `U`). The maximal number of distinguishable orbits of
length `n` is `netMaxcard T F U n`, and its exponential growth `netEntropyEntourage T F U`. This
quantity increases when `U` decreases, and a definition of the topological entropy is
`⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U`.

The definition of topological entropy using nets coincides with the definition using covers.
Instead of defining a new notion of topological entropy, we prove that
`coverEntropy` coincides with `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`.

## Main definitions
- `IsDynNetIn`: property that dynamical balls centered on a subset `s` of `F` are disjoint.
- `netMaxcard`: maximal cardinality of a dynamical net. Takes values in `ℕ∞`.
- `netEntropyInfEntourage`/`netEntropyEntourage`: exponential growth of `netMaxcard`. The former is
defined with a `liminf`, the latter with a `limsup`. Take values in `EReal`.

## Implementation notes
As when using covers, there are two competing definitions `netEntropyInfEntourage` and
`netEntropyEntourage` in this file: one uses a `liminf`, the other a `limsup`. When using covers,
we chose the `limsup` definition as the default.

## Main results
- `coverEntropy_eq_iSup_netEntropyEntourage`: equality between the notions of topological entropy
defined with covers and with nets. Has a variant for `coverEntropyInf`.

## Tags
net, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

namespace Dynamics

open Set Uniformity UniformSpace

variable {X : Type*}

/-! ### Dynamical nets -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` of `F` is a
`(U, n)`-dynamical net of `F` if no two orbits of length `n` of points in `s` shadow each other. -/
def IsDynNetIn (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  s ⊆ F ∧ s.PairwiseDisjoint (fun x : X ↦ ball x (dynEntourage T U n))

lemma IsDynNetIn.of_le {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n) {s : Set X}
    (h : IsDynNetIn T F U m s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_antitone T U m_n) x)⟩

lemma IsDynNetIn.of_entourage_subset {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynNetIn T F V n s) :
    IsDynNetIn T F U n s :=
  ⟨h.1, PairwiseDisjoint.mono h.2 (fun x ↦ ball_mono (dynEntourage_monotone T n U_V) x)⟩

lemma isDynNetIn_empty {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} :
    IsDynNetIn T F U n ∅ :=
  ⟨empty_subset F, pairwise_empty _⟩

lemma isDynNetIn_singleton (T : X → X) {F : Set X} (U : Set (X × X)) (n : ℕ) {x : X} (h : x ∈ F) :
    IsDynNetIn T F U n {x} :=
  ⟨singleton_subset_iff.2 h, pairwise_singleton x _⟩

/-- Given an entourage `U` and a time `n`, a dynamical net has a smaller cardinality than
  a dynamical cover. This lemma is the first of two key results to compare two versions of
  topological entropy: with cover and with nets, the second being `coverMincard_le_netMaxcard`. -/
lemma IsDynNetIn.card_le_card_of_isDynCoverOf {T : X → X} {F : Set X} {U : Set (X × X)}
    {n : ℕ} {s t : Finset X} (hs : IsDynNetIn T F U n s) (ht : IsDynCoverOf T F U n t) :
    s.card ≤ t.card := by
  have (x : X) (x_s : x ∈ s) : ∃ z ∈ t, z ∈ ball x (dynEntourage T U n) := by
    simpa using ht (hs.1 x_s)
  choose! F s_t using this
  apply Finset.card_le_card_of_injOn F (fun x x_s ↦ (s_t x x_s).1)
  exact fun x x_s y y_s Fx_Fy ↦
    PairwiseDisjoint.elim_set hs.2 x_s y_s (F x) (s_t x x_s).2 (Fx_Fy ▸ (s_t y y_s).2)

/-! ### Maximal cardinality of dynamical nets -/

/-- The largest cardinality of a `(U, n)`-dynamical net of `F`. Takes values in `ℕ∞`, and is
infinite if and only if `F` admits nets of arbitrarily large size. -/
noncomputable def netMaxcard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨆ (s : Finset X) (_ : IsDynNetIn T F U n s), (s.card : ℕ∞)

lemma IsDynNetIn.card_le_netMaxcard {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ} {s : Finset X}
    (h : IsDynNetIn T F U n s) :
    s.card ≤ netMaxcard T F U n :=
  le_iSup₂ (α := ℕ∞) s h

lemma netMaxcard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ netMaxcard T F U n) :=
  fun _ _ m_n ↦ biSup_mono (fun _ h ↦ h.of_le m_n)

lemma netMaxcard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ netMaxcard T F U n) :=
  fun _ _ U_V ↦ biSup_mono (fun _ h ↦ h.of_entourage_subset U_V)

lemma netMaxcard_finite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynNetIn T F U n s ∧ (s.card : ℕ∞) = netMaxcard T F U n := by
  apply Iff.intro <;> intro h
  · rcases WithTop.ne_top_iff_exists.1 h.ne with ⟨k, k_max⟩
    rw [← k_max]
    simp only [ENat.some_eq_coe, Nat.cast_inj]
    -- The criterion we want to use is `Nat.sSup_mem`. We rewrite `netMaxcard` with an `sSup`,
    -- then check its `BddAbove` and `Nonempty` hypotheses.
    have : netMaxcard T F U n
      = sSup (WithTop.some '' (Finset.card '' {s : Finset X | IsDynNetIn T F U n s})) := by
      rw [netMaxcard, ← image_comp, sSup_image]
      simp only [mem_setOf_eq, ENat.some_eq_coe, Function.comp_apply]
    rw [this] at k_max
    have h_bdda : BddAbove (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}) := by
      refine ⟨k, mem_upperBounds.2 ?_⟩
      simp only [mem_image, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s h
      rw [← WithTop.coe_le_coe, k_max]
      apply le_sSup
      simp only [ENat.some_eq_coe, mem_image, mem_setOf_eq, Nat.cast_inj, exists_eq_right]
      exact Filter.frequently_principal.mp fun a ↦ a h rfl
    have h_nemp : (Finset.card '' {s : Finset X | IsDynNetIn T F U n s}).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [mem_image, mem_setOf_eq, Finset.card_eq_zero, exists_eq_right, Finset.coe_empty]
      exact isDynNetIn_empty
    rw [← WithTop.coe_sSup' h_bdda, ENat.some_eq_coe, Nat.cast_inj] at k_max
    have key := Nat.sSup_mem h_nemp h_bdda
    rw [← k_max, mem_image] at key
    simp only [mem_setOf_eq] at key
    exact key
  · rcases h with ⟨s, _, s_netMaxcard⟩
    rw [← s_netMaxcard]
    exact WithTop.coe_lt_top s.card

@[simp]
lemma netMaxcard_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : netMaxcard T ∅ U n = 0 := by
  rw [netMaxcard, ← bot_eq_zero, iSup₂_eq_bot]
  intro s s_net
  replace s_net := subset_empty_iff.1 s_net.1
  norm_cast at s_net
  rw [s_net, Finset.card_empty, CharP.cast_eq_zero, bot_eq_zero']

lemma netMaxcard_eq_zero_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n = 0 ↔ F = ∅ := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ by rw [h, netMaxcard_empty])
  rw [eq_empty_iff_forall_not_mem]
  intro x x_F
  have key := isDynNetIn_singleton T U n x_F
  rw [← Finset.coe_singleton] at key
  replace key := key.card_le_netMaxcard
  rw [Finset.card_singleton, Nat.cast_one, h] at key
  exact key.not_lt zero_lt_one

lemma one_le_netMaxcard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    1 ≤ netMaxcard T F U n ↔ F.Nonempty := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty]
  exact not_iff_not.2 (netMaxcard_eq_zero_iff T F U n)

lemma netMaxcard_zero (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    netMaxcard T F U 0 = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F U 0).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_zero, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

lemma netMaxcard_univ (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    netMaxcard T F univ n = 1 := by
  apply (iSup₂_le _).antisymm ((one_le_netMaxcard_iff T F univ n).2 h)
  intro s ⟨_, s_net⟩
  simp only [ball, dynEntourage_univ, preimage_univ] at s_net
  norm_cast
  refine Finset.card_le_one.2 (fun x x_s y y_s ↦ ?_)
  exact PairwiseDisjoint.elim_set s_net x_s y_s x (mem_univ x) (mem_univ x)

lemma netMaxcard_infinite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    netMaxcard T F U n = ⊤ ↔ ∀ k : ℕ, ∃ s : Finset X, IsDynNetIn T F U n s ∧ k ≤ s.card := by
  apply Iff.intro <;> intro h
  · intro k
    rw [netMaxcard, iSup_subtype', iSup_eq_top] at h
    specialize h k (ENat.coe_lt_top k)
    simp only [Nat.cast_lt, Subtype.exists, exists_prop] at h
    rcases h with ⟨s, s_net, s_k⟩
    exact ⟨s, ⟨s_net, s_k.le⟩⟩
  · refine WithTop.eq_top_iff_forall_gt.2 fun k ↦ ?_
    specialize h (k + 1)
    rcases h with ⟨s, s_net, s_card⟩
    apply s_net.card_le_netMaxcard.trans_lt'
    rw [ENat.some_eq_coe, Nat.cast_lt]
    exact (lt_add_one k).trans_le s_card

lemma netMaxcard_le_coverMincard (T : X → X) (F : Set X) {U : Set (X × X)} (n : ℕ) :
    netMaxcard T F U n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h | h
  · exact h ▸ le_top
  · rcases ((coverMincard_finite_iff T F U n).1 h) with ⟨t, t_cover, t_mincard⟩
    rw [← t_mincard]
    exact iSup₂_le (fun s s_net ↦ Nat.cast_le.2 (s_net.card_le_card_of_isDynCoverOf t_cover))

/-- Given an entourage `U` and a time `n`, a minimal dynamical cover by `U ○ U` has a smaller
  cardinality than a maximal dynamical net by `U`. This lemma is the second of two key results to
  compare two versions topological entropy: with cover and with nets. -/
lemma coverMincard_le_netMaxcard (T : X → X) (F : Set X) {U : Set (X × X)} (U_rfl : idRel ⊆ U)
    (U_symm : IsSymmetricRel U) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ netMaxcard T F U n := by
  classical
  -- WLOG, there exists a maximal dynamical net `s`.
  rcases (eq_top_or_lt_top (netMaxcard T F U n)) with h | h
  · exact h ▸ le_top
  rcases ((netMaxcard_finite_iff T F U n).1 h) with ⟨s, s_net, s_netMaxcard⟩
  rw [← s_netMaxcard]
  apply IsDynCoverOf.coverMincard_le_card
  --  We have to check that `s` is a cover for `dynEntourage T F (U ○ U) n`.
  -- If `s` is not a cover, then we can add to `s` a point `x` which is not covered
  -- and get a new net. This contradicts the maximality of `s`.
  rw [IsDynCoverOf, isCover_iff_subset_iUnion_ball U_symm.comp_self.dynEntourage]
  by_contra h
  rcases not_subset.1 h with ⟨x, x_F, x_uncov⟩
  simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
  have larger_net : IsDynNetIn T F U n (insert x s) :=
    And.intro (insert_subset x_F s_net.1) (pairwiseDisjoint_insert.2 (And.intro s_net.2
      (fun y y_s _ ↦ (disjoint_left.2 (fun z z_x z_y ↦ x_uncov y y_s
        (mem_ball_dynEntourage_comp T n U_symm x y (nonempty_of_mem ⟨z_x, z_y⟩)))))))
  rw [← Finset.coe_insert x s] at larger_net
  apply larger_net.card_le_netMaxcard.not_lt
  rw [← s_netMaxcard, Nat.cast_lt]
  refine (lt_add_one s.card).trans_eq (Finset.card_insert_of_not_mem fun x_s ↦ ?_).symm
  apply x_uncov x x_s (ball_mono (dynEntourage_monotone T n (subset_comp_self U_rfl)) x
    (ball_mono (idRel_subset_dynEntourage T U_rfl n) x _))
  simp only [ball, mem_preimage, mem_idRel]

open ENNReal EReal

lemma log_netMaxcard_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (netMaxcard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (one_le_netMaxcard_iff T F U n).2 h

/-! ### Net entropy of entourages -/

open Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `limsup`, and is chosen as the default definition. -/
noncomputable def netEntropyEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.limsup fun n : ℕ ↦ log (netMaxcard T F U n) / n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size of the
largest `(U, n)`-dynamical net of `F`. Takes values in the space of extended real numbers
`[-∞,+∞]`. This version uses a `liminf`, and is an alternative definition. -/
noncomputable def netEntropyInfEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.liminf fun n : ℕ ↦ log (netMaxcard T F U n) / n

lemma netEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ netEntropyInfEntourage T F U) :=
  fun _ _ U_V ↦ (liminf_le_liminf) (Eventually.of_forall
    fun n ↦ monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
      (log_monotone (ENat.toENNReal_mono (netMaxcard_antitone T F n U_V))))

lemma netEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ netEntropyEntourage T F U) :=
  fun _ _ U_V ↦ (limsup_le_limsup) (Eventually.of_forall
    fun n ↦ (monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
      (log_monotone (ENat.toENNReal_mono (netMaxcard_antitone T F n U_V)))))

lemma netEntropyInfEntourage_le_netEntropyEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :
    netEntropyInfEntourage T F U ≤ netEntropyEntourage T F U := liminf_le_limsup

@[simp]
lemma netEntropyEntourage_empty {T : X → X} {U : Set (X × X)} : netEntropyEntourage T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in atTop, log (netMaxcard T ∅ U n) / n = ⊥ by
    rw [netEntropyEntourage, limsup_congr h]
    exact limsup_const ⊥
  simp only [netMaxcard_empty, ENat.toENNReal_zero, log_zero, eventually_atTop]
  exact ⟨1, fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

@[simp]
lemma netEntropyInfEntourage_empty {T : X → X} {U : Set (X × X)} :
    netEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (netEntropyInfEntourage_le_netEntropyEntourage T ∅ U) netEntropyEntourage_empty

lemma netEntropyInfEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ netEntropyInfEntourage T F U :=
  (le_iInf fun n ↦ div_nonneg (log_netMaxcard_nonneg T h U n) (Nat.cast_nonneg' n)).trans
    iInf_le_liminf

lemma netEntropyEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ netEntropyEntourage T F U :=
  (netEntropyInfEntourage_nonneg T h U).trans (netEntropyInfEntourage_le_netEntropyEntourage T F U)

lemma netEntropyInfEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropyInfEntourage T F univ = 0 := by simp [netEntropyInfEntourage, netMaxcard_univ T h]

lemma netEntropyEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    netEntropyEntourage T F univ = 0 := by simp [netEntropyEntourage, netMaxcard_univ T h]

lemma netEntropyInfEntourage_le_coverEntropyInfEntourage (T : X → X) (F : Set X) {U : Set (X × X)} :
    netEntropyInfEntourage T F U ≤ coverEntropyInfEntourage T F U :=
  (liminf_le_liminf) (Eventually.of_forall fun n ↦ (div_le_div_right_of_nonneg (Nat.cast_nonneg' n)
    (log_monotone (ENat.toENNReal_le.2 (netMaxcard_le_coverMincard T F n)))))

lemma coverEntropyInfEntourage_le_netEntropyInfEntourage (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : IsSymmetricRel U) :
    coverEntropyInfEntourage T F (U ○ U) ≤ netEntropyInfEntourage T F U := by
  refine (liminf_le_liminf) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_le_netMaxcard T F U_rfl U_symm n)

lemma netEntropyEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) {U : Set (X × X)} :
    netEntropyEntourage T F U ≤ coverEntropyEntourage T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (netMaxcard_le_coverMincard T F n)

lemma coverEntropyEntourage_le_netEntropyEntourage (T : X → X) (F : Set X) {U : Set (X × X)}
    (U_rfl : idRel ⊆ U) (U_symm : IsSymmetricRel U) :
    coverEntropyEntourage T F (U ○ U) ≤ netEntropyEntourage T F U := by
  refine (limsup_le_limsup) (Eventually.of_forall fun n ↦ ?_)
  apply div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact ENat.toENNReal_le.2 (coverMincard_le_netMaxcard T F U_rfl U_symm n)

/-! ### Relationship with entropy via covers -/

variable [UniformSpace X] (T : X → X) (F : Set X)

/-- Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topological entropy using
  covers, so there is no need to define a new notion of topological entropy. This version of the
  theorem relates the `liminf` versions of topological entropy. -/
theorem coverEntropyInf_eq_iSup_netEntropyInfEntourage :
    coverEntropyInf T F = ⨆ U ∈ 𝓤 X, netEntropyInfEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply (coverEntropyInfEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyInfEntourage_le_netEntropyInfEntourage T F (refl_le_uniformity V_uni) V_symm
  · apply (netEntropyInfEntourage_antitone T F (symmetrizeRel_subset_self U)).trans
    apply (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyInfEntourage_le_coverEntropyInfEntourage T F

/-- Bowen-Dinaburg's definition of topological entropy using nets is
  `⨆ U ∈ 𝓤 X, netEntropyEntourage T F U`. This quantity is the same as the topological entropy using
  covers, so there is no need to define a new notion of topological entropy. This version of the
  theorem relates the `limsup` versions of topological entropy. -/
theorem coverEntropy_eq_iSup_netEntropyEntourage :
    coverEntropy T F = ⨆ U ∈ 𝓤 X, netEntropyEntourage T F U := by
  apply le_antisymm <;> refine iSup₂_le fun U U_uni ↦ ?_
  · rcases (comp_symm_mem_uniformity_sets U_uni) with ⟨V, V_uni, V_symm, V_comp_U⟩
    apply (coverEntropyEntourage_antitone T F V_comp_U).trans (le_iSup₂_of_le V V_uni _)
    exact coverEntropyEntourage_le_netEntropyEntourage T F (refl_le_uniformity V_uni) V_symm
  · apply (netEntropyEntourage_antitone T F (symmetrizeRel_subset_self U)).trans
    apply (le_iSup₂ (symmetrizeRel U) (symmetrize_mem_uniformity U_uni)).trans'
    exact netEntropyEntourage_le_coverEntropyEntourage T F

lemma coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → Set (X × X)} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), netEntropyInfEntourage T F (s i) := by
  rw [coverEntropyInf_eq_iSup_netEntropyInfEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  rcases (HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
  apply (netEntropyInfEntourage_antitone T F si_U).trans
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ netEntropyInfEntourage T F (s i)) i h_i

lemma coverEntropy_eq_iSup_basis_netEntropyEntourage {ι : Sort*} {p : ι → Prop}
    {s : ι → Set (X × X)} (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), netEntropyEntourage T F (s i) := by
  rw [coverEntropy_eq_iSup_netEntropyEntourage T F]
  apply (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩).antisymm'
  refine iSup₂_le fun U U_uni ↦ ?_
  rcases (HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
  apply (netEntropyEntourage_antitone T F si_U).trans _
  exact le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ netEntropyEntourage T F (s i)) i h_i

lemma netEntropyInfEntourage_le_coverEntropyInf {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    netEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  coverEntropyInf_eq_iSup_netEntropyInfEntourage T F ▸
    le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ netEntropyInfEntourage T F U) U h

lemma netEntropyEntourage_le_coverEntropy {U : Set (X × X)} (h : U ∈ 𝓤 X) :
    netEntropyEntourage T F U ≤ coverEntropy T F :=
  coverEntropy_eq_iSup_netEntropyEntourage T F ▸
    le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ netEntropyEntourage T F U) U h

end Dynamics
