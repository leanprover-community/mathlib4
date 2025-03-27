/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.UniformSpace.Cover

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single theorem (`subset_restriction_entropy` in `TopologicalEntropy.Semiconj`) will give the
equivalence between both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal` numbers.

## Main definitions
- `IsDynCoverOf`: property that dynamical balls centered on a subset `s` cover a subset `F`.
- `coverMincard`: minimal cardinality of a dynamical cover. Takes values in `ℕ∞`.
- `coverEntropyInfEntourage`/`coverEntropyEntourage`: exponential growth of `coverMincard`.
The former is defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `coverEntropyInf`/`coverEntropy`: supremum of `coverEntropyInfEntourage`/`coverEntropyEntourage`
over all entourages (or limit as the entourages go to the diagonal). These are Bowen-Dinaburg's
versions of the topological entropy with covers. Take values in `EReal`.

## Implementation notes
There are two competing definitions of topological entropy in this file: one uses a `liminf`,
the other a `limsup`. These two topological entropies are equal as soon as they are applied to an
invariant subset by theorem `coverEntropyInf_eq_coverEntropy`. We choose the default definition
to be the definition using a `limsup`, and give it the simpler name `coverEntropy` (instead of
`coverEntropySup`). Theorems about the topological entropy of invariant subsets will be stated
using only `coverEntropy`.

## Main results
- `IsDynCoverOf.iterate_le_pow`: given a dynamical cover at time `n`, creates dynamical covers
at all iterates `n * m` with controlled cardinality.
- `IsDynCoverOf.coverEntropyEntourage_le_log_card_div`: upper bound on `coverEntropyEntourage`
given any dynamical cover.
- `coverEntropyInf_eq_coverEntropy`: equality between the notions of topological entropy defined
with a `liminf` and a `limsup`.

## Tags
cover, entropy

## TODO
The most painful part of many manipulations involving topological entropy is going from
`coverMincard` to `coverEntropyInfEntourage`/`coverEntropyEntourage`. It involves a logarithm,
a division, a `liminf`/`limsup`, and multiple coercions. The best thing to do would be to write
a file on "exponential growth" to make a clean pathway from estimates on `coverMincard`
to estimates on `coverEntropyInf`/`coverEntropy`. It would also be useful
in other similar contexts, including the definition of entropy using nets.

Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

open scoped Finset

namespace Dynamics

open Set Uniformity UniformSpace

variable {X : Type*} {T : X → X} {U : Set (X × X)} {n : ℕ} {F s : Set X} {n : ℕ}

/-! ### Dynamical covers -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` is a `(U, n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an orbit of length `n`
of a point in `s`. -/
def IsDynCoverOf (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) : Prop :=
  IsCover (dynEntourage T U n) F s

lemma IsDynCoverOf.of_le {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ} (m_n : m ≤ n)
    {s : Set X} (h : IsDynCoverOf T F U n s) :
    IsDynCoverOf T F U m s := h.mono_entourage <| by gcongr

lemma IsDynCoverOf.of_entourage_subset {T : X → X} {F : Set X} {U V : Set (X × X)} (U_V : U ⊆ V)
    {n : ℕ} {s : Set X} (h : IsDynCoverOf T F U n s) :
    IsDynCoverOf T F V n s := h.mono_entourage <| by gcongr

@[simp] lemma isDynCoverOf_empty : IsDynCoverOf T ∅ U n s := .empty

@[simp] lemma isDynCoverOf_empty_right : IsDynCoverOf T F U n ∅ ↔ F = ∅ := by
  simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h

lemma isDynCoverOf_zero (T : X → X) (F : Set X) (U : Set (X × X)) (h : s.Nonempty) :
    IsDynCoverOf T F U 0 s := by simp [IsDynCoverOf, h]

lemma isDynCoverOf_univ (T : X → X) (F : Set X) (n : ℕ) {s : Set X} (h : s.Nonempty) :
    IsDynCoverOf T F univ n s := by simp [IsDynCoverOf, h]

lemma IsDynCoverOf.nonempty_inter (hU : IsSymmetricRel U) {s : Finset X}
    (h : IsDynCoverOf T F U n s) :
    ∃ t : Finset X, IsDynCoverOf T F U n t ∧ #t ≤ #s ∧
      ∀ x ∈ t, (ball x (dynEntourage T U n) ∩ F).Nonempty := by
  classical
  use {x ∈ s | (ball x (dynEntourage T U n) ∩ F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F ↦ ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, hU.dynEntourage.mk_mem_comm.1 y_Bz, y_F⟩, y_Bz⟩

/-- From a dynamical cover `s` with entourage `U` and time `m`, we construct covers with entourage
`U ○ U` and any multiple `m * n` of `m` with controlled cardinality. This lemma is the first step
in a submultiplicative-like property of `coverMincard`, with consequences such as explicit bounds
for the topological entropy (`coverEntropyInfEntourage_le_card_div`) and an equality between
two notions of topological entropy (`coverEntropyInf_eq_coverEntropySup_of_inv`). -/
lemma IsDynCoverOf.iterate_le_pow {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) {m : ℕ} (n : ℕ) {s : Finset X} (h : IsDynCoverOf T F U m s) :
    ∃ t : Finset X, IsDynCoverOf T F (U ○ U) (m * n) t ∧ t.card ≤ s.card ^ n := by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := nonempty_of_exists F_nemp
  have s_nemp := h.nonempty F_nemp
  rcases F_nemp with ⟨x, x_F⟩
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact And.intro (isDynCoverOf_zero T F (U ○ U) (singleton_nonempty x))
      <| one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n
  -- The proof goes as follows. Given an orbit of length `(m * n)` starting from `y`, each of its
  -- iterates `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to a point of `s`.
  -- Conversely, given a sequence `t 0`, `t 1`, `t 2` of points in `s`, we choose a point
  -- `z = dyncover t` such that  `z`, `T^[m] z`, `T^[m]^[2] z` ... are `(dynEntourage T U m)`-close
  --  to `t 0`, `t 1`, `t 2`... Then  `y`, `T^[m] y`, `T^[m]^[2] y` ... are
  -- `(dynEntourage T (U ○ U) m)`-close to `z`, `T^[m] z`, `T^[m]^[2] z`, so that the union of such
  -- `z` provides the desired cover. Since there are at most `s.card ^ n` sequences of
  -- length `n` with values in `s`, we get the upper bound we want on the cardinality.
  -- First step: construct `dyncover`. Given `t 0`, `t 1`, `t 2`, if we cannot find such a point
  -- `dyncover t`, we use the dummy `x`.
  have (t : Fin n → s) : ∃ y : X, (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)) ⊆
      ball y (dynEntourage T (U ○ U) (m * n)) := by
    rcases (⋂ k : Fin n, T^[m * k] ⁻¹' ball (t k) (dynEntourage T U m)).eq_empty_or_nonempty
      with inter_empt | inter_nemp
    · exact inter_empt ▸ ⟨x, empty_subset _⟩
    · rcases inter_nemp with ⟨y, y_int⟩
      refine ⟨y, fun z z_int ↦ ?_⟩
      simp only [ball, dynEntourage, Prod.map_iterate, mem_preimage, mem_iInter,
        Prod.map_apply] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball U_symm y_int z_int
  choose! dyncover h_dyncover using this
  -- The cover we want is the set of all `dyncover t`, that is, `range dyncover`. We need to check
  -- that it is indeed a `(U ○ U, m * n)` cover, and that its cardinality is at most `card s ^ n`.
  -- Only the first point requires significant work.
  let sn := range dyncover
  have := fintypeRange dyncover
  refine ⟨sn.toFinset, ?_, ?_⟩
  · -- We implement the argument at the beginning: given `y ∈ F`, we extract `t 0`, `t 1`, `t 2`
    -- such that `y`, `T^[m] y`, `T^[m]^[2] y` ... is `(dynEntourage T U m)`-close to `t 0`, `t 1`,
    -- `t 2`... Then `dyncover t` is a point of `range dyncover` which satisfies the conclusion
    -- of the lemma.
    rw [Finset.coe_nonempty] at s_nemp
    have _ : Nonempty s := Finset.Nonempty.coe_sort s_nemp
    intro y y_F
    have key : ∀ k : Fin n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (dynEntourage T U m) := by
      intro k
      have := h (MapsTo.iterate F_inv (m * k) y_F)
      simp only [Finset.coe_sort_coe, mem_iUnion, Subtype.exists, exists_prop] at this
      rcases this with ⟨z, z_s, hz⟩
      exact ⟨⟨z, z_s⟩, U_symm.dynEntourage.mk_mem_comm.1 hz⟩
    choose! t ht using key
    simp only [toFinset_range, Finset.coe_image, Finset.coe_univ, image_univ, mem_range,
      exists_exists_eq_and, sn]
    refine ⟨t, U_symm.comp_self.dynEntourage.mk_mem_comm.1 <| h_dyncover t ?_⟩
    simp only [mem_iInter, mem_preimage] at ht ⊢
    exact ht
  · rw [toFinset_card]
    apply (Fintype.card_range_le dyncover).trans
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

lemma exists_isDynCoverOf_of_isCompact_uniformContinuous [UniformSpace X] {T : X → X} {F : Set X}
    (F_comp : IsCompact F) (h : UniformContinuous T) {U : Set (X × X)}  (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨V, hV, (hVsymm : IsSymmetricRel _), hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ ↦ ball_mem_nhds x uni_ite
  exact ⟨s, .of_entourage_subset hVU <| .of_subset_iUnion_ball hVsymm.dynEntourage s_cover⟩

lemma exists_isDynCoverOf_of_isCompact_invariant [UniformSpace X] {T : X → X} {F : Set X}
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, (V_symm : IsSymmetricRel _), V_U⟩
  obtain ⟨s, _, s_cover⟩ := IsCompact.elim_nhds_subcover F_comp (fun x : X ↦ ball x V)
    (fun (x : X) _ ↦ ball_mem_nhds x V_uni)
  have : IsDynCoverOf T F V 1 s :=
    .of_subset_iUnion_ball V_symm.dynEntourage <| by simpa using s_cover
  rcases this.iterate_le_pow F_inv V_symm n with ⟨t, t_dyncover, t_card⟩
  rw [one_mul n] at t_dyncover
  exact ⟨t, t_dyncover.of_entourage_subset V_U⟩

/-! ### Minimal cardinality of dynamical covers -/

/-- The smallest cardinality of a `(U, n)`-dynamical cover of `F`. Takes values in `ℕ∞`, and is
  infinite if and only if `F` admits no finite dynamical cover. -/
noncomputable def coverMincard (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : ℕ∞)

lemma IsDynCoverOf.coverMincard_le_card {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ}
    {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverMincard T F U n ≤ s.card := iInf₂_le s h

lemma coverMincard_monotone_time (T : X → X) (F : Set X) (U : Set (X × X)) :
    Monotone (fun n : ℕ ↦ coverMincard T F U n) :=
  fun _ _ m_n ↦ biInf_mono fun _ h ↦ h.of_le m_n

lemma coverMincard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone (fun U : Set (X × X) ↦ coverMincard T F U n) :=
  fun _ _ U_V ↦ biInf_mono fun _ h ↦ h.of_entourage_subset U_V

lemma coverMincard_finite_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    coverMincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynCoverOf T F U n s ∧ s.card = coverMincard T F U n := by
  refine ⟨fun h_fin ↦ ?_, (fun ⟨s, _, s_coverMincard⟩ ↦ s_coverMincard ▸ WithTop.coe_lt_top s.card)⟩
  rcases WithTop.ne_top_iff_exists.1 (ne_of_lt h_fin) with ⟨k, k_min⟩
  rw [← k_min]
  simp only [ENat.some_eq_coe, Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.coe_ne_top k
    rw [← ENat.some_eq_coe, k_min, coverMincard, iInf₂_eq_top]
    simp only [ENat.coe_ne_top, imp_false]
    rw [nonempty_subtype, not_exists] at h
    exact h
  have key := ciInf_mem (fun s : {s : Finset X // IsDynCoverOf T F U n s} ↦ (s.val.card : ℕ∞))
  rw [coverMincard, iInf_subtype'] at k_min
  rw [← k_min, mem_range, Subtype.exists] at key
  simp only [ENat.some_eq_coe, Nat.cast_inj, exists_prop] at key
  exact key

@[simp]
lemma coverMincard_empty {T : X → X} {U : Set (X × X)} {n : ℕ} : coverMincard T ∅ U n = 0 :=
  (sInf_le (by simp [IsDynCoverOf])).antisymm (zero_le (coverMincard T ∅ U n))

lemma coverMincard_eq_zero_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    coverMincard T F U n = 0 ↔ F = ∅ := by
  simp [coverMincard, ENat.iInf_eq_zero]

lemma one_le_coverMincard_iff (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    1 ≤ coverMincard T F U n ↔ F.Nonempty := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty, not_iff_not]
  exact coverMincard_eq_zero_iff T F U n

lemma coverMincard_zero (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    coverMincard T F U 0 = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  rcases h with ⟨x, _⟩
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]

lemma coverMincard_univ (T : X → X) {F : Set X} (h : F.Nonempty) (n : ℕ) :
    coverMincard T F univ n = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  rcases h with ⟨x, _⟩
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]

lemma coverMincard_mul_le_pow {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) (m n : ℕ) :
    coverMincard T F (U ○ U) (m * n) ≤ coverMincard T F U m ^ n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · rw [coverMincard_empty]; exact zero_le _
  rcases n.eq_zero_or_pos with rfl | n_pos
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · exact h ▸ (le_top (α := ℕ∞)).trans_eq (ENat.top_pow n_pos).symm
  · rcases (coverMincard_finite_iff T F U m).1 h with ⟨s, s_cover, s_coverMincard⟩
    rcases s_cover.iterate_le_pow F_inv U_symm n with ⟨t, t_cover, t_le_sn⟩
    rw [← s_coverMincard]
    exact t_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 t_le_sn)

lemma coverMincard_le_pow {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ coverMincard T F U m ^ (n / m + 1) :=
  (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv U_symm m (n / m + 1))

lemma coverMincard_finite_of_isCompact_uniformContinuous [UniformSpace X] {T : X → X}
    {F : Set X} (F_comp : IsCompact F) (h : UniformContinuous T) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X)
    (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  rcases exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n with ⟨s, s_cover⟩
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

lemma coverMincard_finite_of_isCompact_invariant [UniformSpace X] {T : X → X} {F : Set X}
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  rcases exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n with ⟨s, s_cover⟩
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

/-- All dynamical balls of a minimal dynamical cover of `F` intersect `F`. This lemma is the key
  to relate Bowen-Dinaburg's definition of topological entropy with covers and their definition
  of topological entropy with nets. -/
lemma nonempty_inter_of_coverMincard {T : X → X} {F : Set X} {U : Set (X × X)}
    (hU : IsSymmetricRel U) {n : ℕ} {s : Finset X} (h : IsDynCoverOf T F U n s)
    (h' : #s = coverMincard T F U n) :
    ∀ x ∈ s, (F ∩ ball x (dynEntourage T U n)).Nonempty := by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! hypo
  rcases hypo with ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (Finset.erase s x) := by
    intro y y_F
    specialize h y_F
    simp only [Finset.mem_coe, mem_iUnion, exists_prop] at h
    rcases h with ⟨z, z_s, hz⟩
    simp only [Finset.coe_erase, mem_diff, Finset.mem_coe, mem_singleton_iff, mem_iUnion,
      exists_prop]
    refine ⟨z, And.intro (And.intro z_s fun z_x ↦ not_mem_empty y ?_) hz⟩
    rw [← ball_empt]
    rw [z_x] at hz
    exact mem_inter y_F <| hU.dynEntourage hz
  apply smaller_cover.coverMincard_le_card.not_lt
  rw [← h']
  exact_mod_cast Finset.card_erase_lt_of_mem x_s

open ENNReal EReal

lemma log_coverMincard_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) (n : ℕ) :
    0 ≤ log (coverMincard T F U n) := by
  apply zero_le_log_iff.2
  rw [← ENat.toENNReal_one, ENat.toENNReal_le]
  exact (one_le_coverMincard_iff T F U n).2 h

lemma log_coverMincard_iterate_le {T : X → X} {F : Set X} (F_inv : MapsTo T F F) {U : Set (X × X)}
    (U_symm : IsSymmetricRel U) (m : ℕ) {n : ℕ} (n_pos : 0 < n) :
    log (coverMincard T F (U ○ U) (m * n)) / n ≤ log (coverMincard T F U m) := by
  apply (EReal.div_le_iff_le_mul (b := n) (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)).2
  rw [← log_pow, StrictMono.le_iff_le log_strictMono]
  nth_rw 2 [← ENat.toENNRealRingHom_apply]
  rw [← RingHom.map_pow ENat.toENNRealRingHom _ n, ENat.toENNRealRingHom_apply, ENat.toENNReal_le]
  exact coverMincard_mul_le_pow F_inv U_symm m n

lemma log_coverMincard_le_add {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : IsSymmetricRel U) {m n : ℕ} (m_pos : 0 < m) (n_pos : 0 < n) :
    log (coverMincard T F (U ○ U) n) / n
    ≤ log (coverMincard T F U m) / m + log (coverMincard T F U m) / n := by
  -- If `n` is a multiple of `m`, this follows directly from `log_coverMincard_iterate_le`.
  -- Otherwise, we bound the LHS by the smallest multiple of `m` larger than `n`, which gives the
  -- error term `log (coverMincard T F U m) / n`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · rw [coverMincard_empty, ENat.toENNReal_zero, log_zero,
      bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)]
    exact bot_le
  have h_nm : (0 : EReal) ≤ (n / m : ℕ) := Nat.cast_nonneg' (n / m)
  have h_log := log_coverMincard_nonneg T F_nemp U m
  have n_div_n := EReal.div_self (natCast_ne_bot n) (natCast_ne_top n)
    (Nat.cast_pos'.2 n_pos).ne.symm
  apply le_trans <| div_le_div_right_of_nonneg (Nat.cast_pos'.2 n_pos).le
    (log_monotone (ENat.toENNReal_le.2 (coverMincard_le_pow F_inv U_symm m_pos n)))
  rw [ENat.toENNReal_pow, log_pow, Nat.cast_add, Nat.cast_one, right_distrib_of_nonneg h_nm
    zero_le_one, one_mul, div_right_distrib_of_nonneg (Left.mul_nonneg h_nm h_log) h_log, mul_comm,
    ← EReal.mul_div, div_eq_mul_inv _ (m : EReal)]
  apply add_le_add_right (mul_le_mul_of_nonneg_left _ h_log)
  apply (div_le_div_right_of_nonneg (Nat.cast_pos'.2 n_pos).le (natCast_div_le n m)).trans_eq
  rw [EReal.div_div, mul_comm, ← EReal.div_div, n_div_n, one_div (m : EReal)]

/-! ### Cover entropy of entourages -/

open Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This first version uses a `limsup`, and is chosen as the default definition. -/
noncomputable def coverEntropyEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.limsup fun n : ℕ ↦ log (coverMincard T F U n) / n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This second version uses a `liminf`, and is chosen as an alternative definition. -/
noncomputable def coverEntropyInfEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :=
  atTop.liminf fun n : ℕ ↦ log (coverMincard T F U n) / n

lemma coverEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ coverEntropyInfEntourage T F U) :=
  fun _ _ U_V ↦ (liminf_le_liminf) <| Eventually.of_forall
    fun n ↦ monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (coverMincard_antitone T F n U_V))

lemma coverEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone (fun U : Set (X × X) ↦ coverEntropyEntourage T F U) :=
  fun _ _ U_V ↦ (limsup_le_limsup) <| Eventually.of_forall
    fun n ↦ monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    <| log_monotone (ENat.toENNReal_mono (coverMincard_antitone T F n U_V))

lemma coverEntropyInfEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) (U : Set (X × X)) :
    coverEntropyInfEntourage T F U ≤ coverEntropyEntourage T F U := liminf_le_limsup

@[simp]
lemma coverEntropyEntourage_empty {T : X → X} {U : Set (X × X)} :
    coverEntropyEntourage T ∅ U = ⊥ := by
  suffices h : ∀ᶠ n : ℕ in atTop, log (coverMincard T ∅ U n) / n = ⊥ by
    rw [coverEntropyEntourage]
    exact limsup_congr h ▸ limsup_const ⊥
  · simp only [coverMincard_empty, ENat.toENNReal_zero, log_zero, eventually_atTop]
    exact ⟨1, fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

@[simp]
lemma coverEntropyInfEntourage_empty {T : X → X} {U : Set (X × X)} :
    coverEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty

lemma coverEntropyInfEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ coverEntropyInfEntourage T F U :=
  (le_iInf fun n ↦ div_nonneg (log_coverMincard_nonneg T h U n) (Nat.cast_nonneg' n)).trans
    iInf_le_liminf

lemma coverEntropyEntourage_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) (U : Set (X × X)) :
    0 ≤ coverEntropyEntourage T F U :=
  (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)

lemma coverEntropyEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    coverEntropyEntourage T F univ = 0 := by
  simp [coverEntropyEntourage, coverMincard_univ T h]

lemma coverEntropyInfEntourage_univ (T : X → X) {F : Set X} (h : F.Nonempty) :
    coverEntropyInfEntourage T F univ = 0 := by
  simp [coverEntropyInfEntourage, coverMincard_univ T h]

lemma coverEntropyEntourage_le_log_coverMincard_div {T : X → X} {F : Set X} (F_inv : MapsTo T F F)
    {U : Set (X × X)} (U_symm : IsSymmetricRel U) {n : ℕ} (n_pos : 0 < n) :
    coverEntropyEntourage T F (U ○ U) ≤ log (coverMincard T F U n) / n := by
  -- Deal with the edge cases: `F = ∅` or `F` has no finite cover.
  rcases eq_or_ne (log (coverMincard T F U n)) ⊥ with logm_bot | logm_nneg
  · rw [log_eq_bot_iff, ← ENat.toENNReal_zero, ENat.toENNReal_inj,
      coverMincard_eq_zero_iff T F U n] at logm_bot
    simp [logm_bot]
  rcases eq_or_ne (log (coverMincard T F U n)) ⊤ with logm_top | logm_fin
  · rw [logm_top, top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)]
    exact le_top
  -- The general case follows from `log_coverMincard_le_add`, with careful manipulation of limits.
  let u := fun _ : ℕ ↦ log (coverMincard T F U n) / n
  let v := fun m : ℕ ↦ log (coverMincard T F U n) / m
  let w := fun m : ℕ ↦ log (coverMincard T F (U ○ U) m) / m
  have key : w ≤ᶠ[atTop] u + v :=
    eventually_atTop.2 ⟨1, fun m m_pos ↦ log_coverMincard_le_add F_inv U_symm n_pos m_pos⟩
  apply ((limsup_le_limsup) key).trans
  suffices h : atTop.limsup v = 0 by
    have := @limsup_add_le ℕ atTop u v
    rw [h, add_zero] at this
    specialize this (Or.inr EReal.zero_ne_top) (Or.inr EReal.zero_ne_bot)
    exact this.trans_eq (limsup_const (log (coverMincard T F U n) / n))
  exact Tendsto.limsup_eq (EReal.tendsto_const_div_atTop_nhds_zero_nat logm_nneg logm_fin)

lemma IsDynCoverOf.coverEntropyEntourage_le_log_card_div {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) {U : Set (X × X)} (U_symm : IsSymmetricRel U) {n : ℕ} (n_pos : 0 < n)
    {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) ≤ log s.card / n := by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv U_symm n_pos).trans
  apply monotone_div_right_of_nonneg (Nat.cast_nonneg' n) (log_monotone _)
  exact_mod_cast coverMincard_le_card h

lemma coverEntropyEntourage_le_coverEntropyInfEntourage {T : X → X} {F : Set X}
    (F_inv : MapsTo T F F) {U : Set (X × X)} (U_symm : IsSymmetricRel U) :
    coverEntropyEntourage T F (U ○ U) ≤ coverEntropyInfEntourage T F U :=
  (le_liminf_of_le) (eventually_atTop.2
    ⟨1, fun m m_pos ↦ coverEntropyEntourage_le_log_coverMincard_div F_inv U_symm m_pos⟩)

lemma coverEntropyEntourage_finite_of_isCompact_invariant [UniformSpace X] {T : X → X} {F : Set X}
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U < ⊤ := by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  rcases exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1 with ⟨s, s_cover⟩
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv V_symm zero_lt_one).trans_lt
  rw [Nat.cast_one, div_one, log_lt_top_iff, ← ENat.toENNReal_top]
  exact_mod_cast Ne.lt_top (ENat.coe_ne_top (Finset.card s))

/-! ### Cover entropy -/

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyEntourage` over entourages. Note that this supremum is approached by taking small
  entourages. This first version uses a `limsup`, and is chosen as the default definition
  for topological entropy. -/
noncomputable def coverEntropy [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, coverEntropyEntourage T F U

/-- The entropy of `T` restricted to `F`, obtained by taking the supremum
  of `coverEntropyInfEntourage` over entourages. Note that this supremum is approached by taking
  small entourages. This second version uses a `liminf`, and is chosen as an alternative
  definition for topological entropy. -/
noncomputable def coverEntropyInf [UniformSpace X] (T : X → X) (F : Set X) :=
  ⨆ U ∈ 𝓤 X, coverEntropyInfEntourage T F U

lemma coverEntropyInf_antitone (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @coverEntropyInf X u T F :=
  fun _ _ h ↦ iSup₂_mono' fun U U_uni ↦ ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

lemma coverEntropy_antitone (T : X → X) (F : Set X) :
    Antitone fun (u : UniformSpace X) ↦ @coverEntropy X u T F :=
  fun _ _ h ↦ iSup₂_mono' fun U U_uni ↦ ⟨U, (le_def.1 h) U U_uni, le_refl _⟩

variable [UniformSpace X]

lemma coverEntropyEntourage_le_coverEntropy (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U ≤ coverEntropy T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ coverEntropyEntourage T F U) U h

lemma coverEntropyInfEntourage_le_coverEntropyInf (T : X → X) (F : Set X) {U : Set (X × X)}
    (h : U ∈ 𝓤 X) :
    coverEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  le_iSup₂ (f := fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦ coverEntropyInfEntourage T F U) U h

lemma coverEntropy_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), coverEntropyEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  rcases (HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyEntourage T F (s i)) i h_i)

lemma coverEntropyInf_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → Set (X × X)}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), coverEntropyInfEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  rcases (HasBasis.mem_iff h).1 U_uni with ⟨i, h_i, si_U⟩
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyInfEntourage T F (s i)) i h_i)

lemma coverEntropyInf_le_coverEntropy (T : X → X) (F : Set X) :
    coverEntropyInf T F ≤ coverEntropy T F :=
  iSup₂_mono fun (U : Set (X × X)) (_ : U ∈ 𝓤 X) ↦
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]
lemma coverEntropy_empty {T : X → X} : coverEntropy T ∅ = ⊥ := by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]
lemma coverEntropyInf_empty {T : X → X} : coverEntropyInf T ∅ = ⊥ := by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]

lemma coverEntropyInf_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ coverEntropyInf T F :=
  (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h).symm

lemma coverEntropy_nonneg (T : X → X) {F : Set X} (h : F.Nonempty) :
    0 ≤ coverEntropy T F :=
  (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)

lemma coverEntropyInf_eq_coverEntropy (T : X → X) {F : Set X} (h : MapsTo T F F) :
    coverEntropyInf T F = coverEntropy T F := by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni ↦ ?_)
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_U⟩
  exact (coverEntropyEntourage_antitone T F V_U).trans
    (le_iSup₂_of_le V V_uni (coverEntropyEntourage_le_coverEntropyInfEntourage h V_symm))

end Dynamics
