/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.TopologicalEntropy.DynamicalEntourage
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

@[expose] public section

open Set SetRel Uniformity UniformSpace
open scoped Finset

namespace Dynamics

variable {X : Type*} {T : X → X} {U V : SetRel X X} {n : ℕ} {F s : Set X} {m n : ℕ}

/-! ### Dynamical covers -/

/-- Given a subset `F`, an entourage `U` and an integer `n`, a subset `s` is a `(U, n)`-
dynamical cover of `F` if any orbit of length `n` in `F` is `U`-shadowed by an orbit of length `n`
of a point in `s`. -/
def IsDynCoverOf (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) (s : Set X) : Prop :=
  IsCover (dynEntourage T U n) F s

lemma IsDynCoverOf.of_le (m_n : m ≤ n) (h : IsDynCoverOf T F U n s) : IsDynCoverOf T F U m s :=
  h.mono_entourage <| by gcongr

lemma IsDynCoverOf.of_entourage_subset (U_V : U ⊆ V) (h : IsDynCoverOf T F U n s) :
    IsDynCoverOf T F V n s := h.mono_entourage <| by gcongr

@[simp] lemma isDynCoverOf_empty : IsDynCoverOf T ∅ U n s := .empty

@[simp] lemma isDynCoverOf_empty_right : IsDynCoverOf T F U n ∅ ↔ F = ∅ := by simp [IsDynCoverOf]

nonrec lemma IsDynCoverOf.nonempty (h : F.Nonempty) (h' : IsDynCoverOf T F U n s) : s.Nonempty :=
  h'.nonempty h

lemma isDynCoverOf_zero (T : X → X) (F : Set X) (U : SetRel X X) (h : s.Nonempty) :
    IsDynCoverOf T F U 0 s := by simp [IsDynCoverOf, h]

lemma isDynCoverOf_univ (T : X → X) (F : Set X) (n : ℕ) (h : s.Nonempty) :
    IsDynCoverOf T F univ n s := by simp [IsDynCoverOf, h]

lemma IsDynCoverOf.nonempty_inter [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s) :
    ∃ t : Finset X, IsDynCoverOf T F U n t ∧ #t ≤ #s ∧
      ∀ x ∈ t, (ball x (dynEntourage T U n) ∩ F).Nonempty := by
  classical
  use {x ∈ s | (ball x (dynEntourage T U n) ∩ F).Nonempty}
  simp only [Finset.coe_filter, Finset.mem_filter, and_imp, imp_self, implies_true, and_true]
  refine ⟨fun y y_F ↦ ?_, Finset.card_mono (Finset.filter_subset _ s)⟩
  obtain ⟨z, z_s, y_Bz⟩ := h y_F
  exact ⟨z, ⟨z_s, _, (dynEntourage T U n).symm y_Bz, y_F⟩, y_Bz⟩

/-- From a dynamical cover `s` with entourage `U` and time `m`, we construct covers with entourage
`U ○ U` and any multiple `m * n` of `m` with controlled cardinality. This lemma is the first step
in a submultiplicative-like property of `coverMincard`, with consequences such as explicit bounds
for the topological entropy (`coverEntropyInfEntourage_le_card_div`) and an equality between
two notions of topological entropy (`coverEntropyInf_eq_coverEntropySup_of_inv`). -/
lemma IsDynCoverOf.iterate_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (n : ℕ) {s : Finset X}
    (h : IsDynCoverOf T F U m s) :
    ∃ t : Finset X, IsDynCoverOf T F (U ○ U) (m * n) t ∧ t.card ≤ s.card ^ n := by
  classical
  -- Deal with the edge cases: `F = ∅` or `m = 0`.
  rcases F.eq_empty_or_nonempty with rfl | F_nemp
  · exact ⟨∅, by simp⟩
  have _ : Nonempty X := F_nemp.nonempty
  have s_nemp := h.nonempty F_nemp
  obtain ⟨x, x_F⟩ := F_nemp
  rcases m.eq_zero_or_pos with rfl | m_pos
  · use {x}
    simp only [zero_mul, Finset.coe_singleton, Finset.card_singleton]
    exact ⟨isDynCoverOf_zero T F (U ○ U) (singleton_nonempty x),
      one_le_pow_of_one_le' (Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nemp)) n⟩
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
    · obtain ⟨y, y_int⟩ := inter_nemp
      refine ⟨y, fun z z_int ↦ ?_⟩
      simp only [ball, dynEntourage, Prod.map_iterate, mem_iInter, Set.mem_preimage, Prod.map_apply,
        mem_comp] at y_int z_int ⊢
      intro k k_mn
      replace k_mn := Nat.div_lt_of_lt_mul k_mn
      specialize z_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      specialize y_int ⟨(k / m), k_mn⟩ (k % m) (Nat.mod_lt k m_pos)
      rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_int z_int
      exact mem_comp_of_mem_ball y_int z_int
  choose! dyncover h_dyncover using this
  -- The cover we want is the set of all `dyncover t`, that is, `range dyncover`. We need to check
  -- that it is indeed a `(U ○ U, m * n)` cover, and that its cardinality is at most `card s ^ n`.
  -- Only the first point requires significant work.
  let sn := range dyncover
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
      simp only [Finset.mem_coe] at this
      obtain ⟨z, z_s, hz⟩ := this
      exact ⟨⟨z, z_s⟩, (dynEntourage T U m).symm hz⟩
    choose! t ht using key
    simp only [toFinset_range, Finset.coe_image, Finset.coe_univ, image_univ, mem_range,
      exists_exists_eq_and, sn]
    refine ⟨t, (dynEntourage T (U ○ U) (m * n)).symm <| h_dyncover t <| by simpa using ht⟩
  · rw [toFinset_card]
    apply (Fintype.card_range_le dyncover).trans
    simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, le_refl]

lemma exists_isDynCoverOf_of_isCompact_uniformContinuous [UniformSpace X]
    (F_comp : IsCompact F) (h : UniformContinuous T) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), hV, hVsymm, hVU⟩ := symm_of_uniformity U_uni
  have uni_ite := dynEntourage_mem_uniformity h hV n
  let openCover x := ball x (dynEntourage T V n)
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover openCover fun x _ ↦ ball_mem_nhds x uni_ite
  exact ⟨s, .of_entourage_subset hVU <| .of_subset_iUnion_ball s_cover⟩

lemma exists_isDynCoverOf_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    ∃ s : Finset X, IsDynCoverOf T F U n s := by
  obtain ⟨(V : SetRel X X), V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, _, s_cover⟩ := F_comp.elim_nhds_subcover (ball · V)
    fun (x : X) _ ↦ ball_mem_nhds x V_uni
  have : IsDynCoverOf T F V 1 s := .of_subset_iUnion_ball <| by simpa using s_cover
  obtain ⟨t, t_dyncover, t_card⟩ := this.iterate_le_pow F_inv n
  rw [one_mul n] at t_dyncover
  exact ⟨t, t_dyncover.of_entourage_subset V_U⟩

/-! ### Minimal cardinality of dynamical covers -/

/-- The smallest cardinality of a `(U, n)`-dynamical cover of `F`. Takes values in `ℕ∞`, and is
  infinite if and only if `F` admits no finite dynamical cover. -/
noncomputable def coverMincard (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) : ℕ∞ :=
  ⨅ (s : Finset X) (_ : IsDynCoverOf T F U n s), (s.card : ℕ∞)

lemma IsDynCoverOf.coverMincard_le_card {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverMincard T F U n ≤ s.card :=
  iInf₂_le s h

lemma coverMincard_monotone_time (T : X → X) (F : Set X) (U : SetRel X X) :
    Monotone fun n : ℕ ↦ coverMincard T F U n :=
  fun _ _ m_n ↦ biInf_mono fun _ h ↦ h.of_le m_n

lemma coverMincard_antitone (T : X → X) (F : Set X) (n : ℕ) :
    Antitone fun U : SetRel X X ↦ coverMincard T F U n :=
  fun _ _ U_V ↦ biInf_mono fun _ h ↦ h.of_entourage_subset U_V

set_option backward.isDefEq.respectTransparency false in
lemma coverMincard_finite_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T F U n < ⊤ ↔
    ∃ s : Finset X, IsDynCoverOf T F U n s ∧ s.card = coverMincard T F U n := by
  refine ⟨fun h_fin ↦ ?_, fun ⟨s, _, s_coverMincard⟩ ↦ s_coverMincard ▸ WithTop.coe_lt_top s.card⟩
  obtain ⟨k, k_min⟩ := WithTop.ne_top_iff_exists.1 h_fin.ne
  rw [← k_min]
  simp only [ENat.some_eq_coe, Nat.cast_inj]
  have : Nonempty {s : Finset X // IsDynCoverOf T F U n s} := by
    by_contra h
    apply ENat.coe_ne_top k
    rw [← ENat.some_eq_coe, k_min, coverMincard, iInf₂_eq_top]
    simp only [ENat.coe_ne_top, imp_false]
    rw [nonempty_subtype, not_exists] at h
    exact h
  have key := ciInf_mem fun s : {s : Finset X // IsDynCoverOf T F U n s} ↦ (s.val.card : ℕ∞)
  rw [coverMincard, iInf_subtype'] at k_min
  rw [← k_min, mem_range, Subtype.exists] at key
  simp only [ENat.some_eq_coe, Nat.cast_inj, exists_prop] at key
  exact key

@[simp]
lemma coverMincard_empty : coverMincard T ∅ U n = 0 :=
  (sInf_le (by simp [IsDynCoverOf])).antisymm (zero_le (coverMincard T ∅ U n))

lemma coverMincard_eq_zero_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T F U n = 0 ↔ F = ∅ := by
  simp [coverMincard, ENat.iInf_eq_zero]

lemma one_le_coverMincard_iff (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) :
    1 ≤ coverMincard T F U n ↔ F.Nonempty := by
  rw [ENat.one_le_iff_ne_zero, nonempty_iff_ne_empty, not_iff_not]
  exact coverMincard_eq_zero_iff T F U n

lemma coverMincard_zero (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    coverMincard T F U 0 = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F U 0).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_zero T F U (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]

lemma coverMincard_univ (T : X → X) (h : F.Nonempty) (n : ℕ) : coverMincard T F univ n = 1 := by
  apply le_antisymm _ ((one_le_coverMincard_iff T F univ n).2 h)
  obtain ⟨x, _⟩ := h
  have := isDynCoverOf_univ T F n (singleton_nonempty x)
  rw [← Finset.coe_singleton] at this
  apply this.coverMincard_le_card.trans_eq
  rw [Finset.card_singleton, Nat.cast_one]

lemma coverMincard_mul_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m n : ℕ) :
    coverMincard T F (U ○ U) (m * n) ≤ coverMincard T F U m ^ n := by
  rcases F.eq_empty_or_nonempty with rfl | F_nonempty
  · rw [coverMincard_empty]; exact zero_le _
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, coverMincard_zero T F_nonempty (U ○ U), pow_zero]
  rcases eq_top_or_lt_top (coverMincard T F U m) with h | h
  · simp [*]
  · obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U m).1 h
    obtain ⟨t, t_cover, t_sn⟩ := s_cover.iterate_le_pow F_inv n
    rw [← s_coverMincard]
    exact t_cover.coverMincard_le_card.trans (WithTop.coe_le_coe.2 t_sn)

lemma coverMincard_le_pow (F_inv : MapsTo T F F) [U.IsSymm] (m_pos : 0 < m) (n : ℕ) :
    coverMincard T F (U ○ U) n ≤ coverMincard T F U m ^ (n / m + 1) :=
  (coverMincard_monotone_time T F (U ○ U) (Nat.lt_mul_div_succ n m_pos).le).trans
    (coverMincard_mul_le_pow F_inv m (n / m + 1))

lemma coverMincard_finite_of_isCompact_uniformContinuous [UniformSpace X] (F_comp : IsCompact F)
    (h : UniformContinuous T) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_uniformContinuous F_comp h U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

lemma coverMincard_finite_of_isCompact_invariant [UniformSpace X] (F_comp : IsCompact F)
    (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    coverMincard T F U n < ⊤ := by
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv U_uni n
  exact s_cover.coverMincard_le_card.trans_lt (WithTop.coe_lt_top s.card)

/-- All dynamical balls of a minimal dynamical cover of `F` intersect `F`. This lemma is the key
  to relate Bowen-Dinaburg's definition of topological entropy with covers and their definition
  of topological entropy with nets. -/
lemma nonempty_inter_of_coverMincard [U.IsSymm] {s : Finset X} (h : IsDynCoverOf T F U n s)
    (h' : #s = coverMincard T F U n) :
    ∀ x ∈ s, (F ∩ ball x (dynEntourage T U n)).Nonempty := by
  -- Otherwise, there is a ball which does not intersect `F`. Removing it yields a smaller cover.
  classical
  by_contra! ⟨x, x_s, ball_empt⟩
  have smaller_cover : IsDynCoverOf T F U n (s.erase x) := by
    intro y y_F
    specialize h y_F
    simp only [s.mem_coe] at h
    simp only [s.coe_erase, mem_diff, s.mem_coe, mem_singleton_iff]
    obtain ⟨z, z_s, hz⟩ := h
    refine ⟨z, ⟨z_s, fun z_x ↦ notMem_empty y ?_⟩, hz⟩
    rw [← ball_empt]
    rw [z_x] at hz
    exact mem_inter y_F <| (dynEntourage T U n).symm hz
  apply smaller_cover.coverMincard_le_card.not_gt
  rw [← h']
  exact_mod_cast s.card_erase_lt_of_mem x_s

/-! ### Cover entropy of entourages -/

open ENNReal EReal ExpGrowth Filter

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This first version uses a `limsup`, and is chosen as the default definition. -/
noncomputable def coverEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthSup fun n : ℕ ↦ coverMincard T F U n

/-- The entropy of an entourage `U`, defined as the exponential rate of growth of the size
  of the smallest `(U, n)`-refined cover of `F`. Takes values in the space of extended real numbers
  `[-∞, +∞]`. This second version uses a `liminf`, and is chosen as an alternative definition. -/
noncomputable def coverEntropyInfEntourage (T : X → X) (F : Set X) (U : SetRel X X) :=
  expGrowthInf fun n : ℕ ↦ coverMincard T F U n

lemma coverEntropyInfEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ coverEntropyInfEntourage T F U :=
  fun _ _ U_V ↦ expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

lemma coverEntropyEntourage_antitone (T : X → X) (F : Set X) :
    Antitone fun U : SetRel X X ↦ coverEntropyEntourage T F U :=
  fun _ _ U_V ↦ expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_antitone T F n U_V)

lemma coverEntropyInfEntourage_le_coverEntropyEntourage (T : X → X) (F : Set X) (U : SetRel X X) :
    coverEntropyInfEntourage T F U ≤ coverEntropyEntourage T F U :=
  expGrowthInf_le_expGrowthSup

@[simp]
lemma coverEntropyEntourage_empty : coverEntropyEntourage T ∅ U = ⊥ := by
  simp only [coverEntropyEntourage, coverMincard_empty]
  rw [ENat.toENNReal_zero, ← Pi.zero_def, expGrowthSup_zero]

@[simp]
lemma coverEntropyInfEntourage_empty : coverEntropyInfEntourage T ∅ U = ⊥ :=
  eq_bot_mono (coverEntropyInfEntourage_le_coverEntropyEntourage T ∅ U) coverEntropyEntourage_empty

lemma coverEntropyInfEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ coverEntropyInfEntourage T F U := by
  apply Monotone.expGrowthInf_nonneg
  · exact fun _ _ m_n ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F U m_n)
  · rw [ne_eq, funext_iff.not, not_forall]
    use 0
    rw [coverMincard_zero T h U, Pi.zero_apply, ENat.toENNReal_one]
    exact one_ne_zero

lemma coverEntropyEntourage_nonneg (T : X → X) (h : F.Nonempty) (U : SetRel X X) :
    0 ≤ coverEntropyEntourage T F U :=
  (coverEntropyInfEntourage_nonneg T h U).trans
    (coverEntropyInfEntourage_le_coverEntropyEntourage T F U)

lemma coverEntropyEntourage_univ (T : X → X) (h : F.Nonempty) :
    coverEntropyEntourage T F univ = 0 := by
  rw [← expGrowthSup_const one_ne_zero one_ne_top, coverEntropyEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

lemma coverEntropyInfEntourage_univ (T : X → X) (h : F.Nonempty) :
    coverEntropyInfEntourage T F univ = 0 := by
  rw [← expGrowthInf_const one_ne_zero one_ne_top, coverEntropyInfEntourage]
  simp only [coverMincard_univ T h, ENat.toENNReal_one]

lemma coverEntropyEntourage_le_log_coverMincard_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n ≠ 0) :
    coverEntropyEntourage T F (U ○ U) ≤ log (coverMincard T F U n) / n := by
  have cv_mono : Monotone fun m ↦ (coverMincard T F (U ○ U) m).toENNReal :=
    fun _ _ k_m ↦ ENat.toENNReal_mono (coverMincard_monotone_time T F (U ○ U) k_m)
  have h := cv_mono.expGrowthSup_comp_mul n_pos
  rw [mul_comm, ← div_eq_iff (natCast_ne_bot n) (natCast_ne_top n) (Nat.cast_ne_zero.2 n_pos)] at h
  rw [coverEntropyEntourage, ← h]
  apply monotone_div_right_of_nonneg n.cast_nonneg'
  rw [← expGrowthSup_pow]
  refine expGrowthSup_monotone fun m ↦ ?_
  rw [← ENat.toENNReal_pow]
  exact ENat.toENNReal_mono (coverMincard_mul_le_pow F_inv n m)

lemma IsDynCoverOf.coverEntropyEntourage_le_log_card_div (F_inv : MapsTo T F F) [U.IsSymm]
    (n_pos : n ≠ 0) {s : Finset X} (h : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) ≤ log s.card / n := by
  apply (coverEntropyEntourage_le_log_coverMincard_div F_inv n_pos).trans
  apply monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone _)
  exact_mod_cast coverMincard_le_card h

lemma coverEntropyEntourage_le_coverEntropyInfEntourage (F_inv : MapsTo T F F) [U.IsSymm] :
    coverEntropyEntourage T F (U ○ U) ≤ coverEntropyInfEntourage T F U := by
  refine (le_liminf_of_le) (eventually_atTop.2 ⟨1, fun m m_pos ↦ ?_⟩)
  exact coverEntropyEntourage_le_log_coverMincard_div F_inv (Nat.one_le_iff_ne_zero.1 m_pos)

lemma coverEntropyEntourage_finite_of_isCompact_invariant [UniformSpace X]
    (F_comp : IsCompact F) (F_inv : MapsTo T F F) (U_uni : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U < ⊤ := by
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  obtain ⟨s, s_cover⟩ := exists_isDynCoverOf_of_isCompact_invariant F_comp F_inv V_uni 1
  apply (coverEntropyEntourage_antitone T F V_U).trans_lt
  apply (s_cover.coverEntropyEntourage_le_log_card_div F_inv one_ne_zero).trans_lt
  rw [Nat.cast_one, div_one, log_lt_top_iff, ← ENat.toENNReal_top]
  exact_mod_cast (ENat.coe_ne_top (Finset.card s)).lt_top

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

lemma coverEntropyEntourage_le_coverEntropy (T : X → X) (F : Set X)
    (h : U ∈ 𝓤 X) :
    coverEntropyEntourage T F U ≤ coverEntropy T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ coverEntropyEntourage T F U) U h

lemma coverEntropyInfEntourage_le_coverEntropyInf (T : X → X) (F : Set X)
    (h : U ∈ 𝓤 X) :
    coverEntropyInfEntourage T F U ≤ coverEntropyInf T F :=
  le_iSup₂ (f := fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦ coverEntropyInfEntourage T F U) U h

lemma coverEntropy_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropy T F = ⨆ (i : ι) (_ : p i), coverEntropyEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyEntourage T F (s i)) i h_i)

lemma coverEntropyInf_eq_iSup_basis {ι : Sort*} {p : ι → Prop} {s : ι → SetRel X X}
    (h : (𝓤 X).HasBasis p s) (T : X → X) (F : Set X) :
    coverEntropyInf T F = ⨆ (i : ι) (_ : p i), coverEntropyInfEntourage T F (s i) := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm
    (iSup₂_mono' fun i h_i ↦ ⟨s i, HasBasis.mem_of_mem h h_i, le_refl _⟩)
  obtain ⟨i, h_i, si_U⟩ := (HasBasis.mem_iff h).1 U_uni
  exact (coverEntropyInfEntourage_antitone T F si_U).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ coverEntropyInfEntourage T F (s i)) i h_i)

lemma coverEntropyInf_le_coverEntropy (T : X → X) (F : Set X) :
    coverEntropyInf T F ≤ coverEntropy T F :=
  iSup₂_mono fun (U : SetRel X X) (_ : U ∈ 𝓤 X) ↦
    coverEntropyInfEntourage_le_coverEntropyEntourage T F U

@[simp]
lemma coverEntropy_empty : coverEntropy T ∅ = ⊥ := by
  simp only [coverEntropy, coverEntropyEntourage_empty, iSup_bot]

@[simp]
lemma coverEntropyInf_empty : coverEntropyInf T ∅ = ⊥ := by
  simp only [coverEntropyInf, coverEntropyInfEntourage_empty, iSup_bot]

lemma coverEntropyInf_nonneg (T : X → X) (h : F.Nonempty) : 0 ≤ coverEntropyInf T F :=
  (coverEntropyInfEntourage_le_coverEntropyInf T F univ_mem).trans_eq'
    (coverEntropyInfEntourage_univ T h)

lemma coverEntropy_nonneg (T : X → X) (h : F.Nonempty) : 0 ≤ coverEntropy T F :=
  (coverEntropyInf_nonneg T h).trans (coverEntropyInf_le_coverEntropy T F)

lemma coverEntropyInf_eq_coverEntropy (T : X → X) (h : MapsTo T F F) :
    coverEntropyInf T F = coverEntropy T F := by
  refine le_antisymm (coverEntropyInf_le_coverEntropy T F) (iSup₂_le fun U U_uni ↦ ?_)
  obtain ⟨V, V_uni, V_symm, V_U⟩ := comp_symm_mem_uniformity_sets U_uni
  exact (coverEntropyEntourage_antitone T F V_U).trans <| le_iSup₂_of_le V V_uni <|
     coverEntropyEntourage_le_coverEntropyInfEntourage h

end Dynamics
