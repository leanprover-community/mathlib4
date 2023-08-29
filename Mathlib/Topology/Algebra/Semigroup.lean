/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.Topology.Separation

#align_import topology.algebra.semigroup from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Idempotents in topological semigroups

This file provides a sufficient condition for a semigroup `M` to contain an idempotent (i.e. an
element `m` such that `m * m = m `), namely that `M` is a nonempty compact Hausdorff space where
right-multiplication by constants is continuous.

We also state a corresponding lemma guaranteeing that a subset of `M` contains an idempotent.
-/


/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder
  collection (m m' «expr ∈ » N) -/
/-- Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
an idempotent, i.e. an `m` such that `m * m = m`. -/
@[to_additive
      "Any nonempty compact Hausdorff additive semigroup where right-addition is continuous
      contains an idempotent, i.e. an `m` such that `m + m = m`"]
theorem exists_idempotent_of_compact_t2_of_continuous_mul_left {M} [Nonempty M] [Semigroup M]
    [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (continuous_mul_left : ∀ r : M, Continuous (· * r)) : ∃ m : M, m * m = m := by
  /- We apply Zorn's lemma to the poset of nonempty closed subsemigroups of `M`.
     It will turn out that any minimal element is `{m}` for an idempotent `m : M`. -/
  let S : Set (Set M) :=
    { N | IsClosed N ∧ N.Nonempty ∧ ∀ (m) (_ : m ∈ N) (m') (_ : m' ∈ N), m * m' ∈ N }
  obtain ⟨N, ⟨N_closed, ⟨m, hm⟩, N_mul⟩, N_minimal⟩ : ∃ N ∈ S, ∀ N' ∈ S, N' ⊆ N → N' = N
  -- ⊢ ∃ N, N ∈ S ∧ ∀ (N' : Set M), N' ∈ S → N' ⊆ N → N' = N
  rotate_left -- Porting note: restore to `rsuffices`
  -- ⊢ ∃ m, m * m = m
  · use m
    -- ⊢ m * m = m
    /- We now have an element `m : M` of a minimal subsemigroup `N`, and want to show `m + m = m`.
    We first show that every element of `N` is of the form `m' + m`.-/
    have scaling_eq_self : (· * m) '' N = N := by
      apply N_minimal
      · refine' ⟨(continuous_mul_left m).isClosedMap _ N_closed, ⟨_, ⟨m, hm, rfl⟩⟩, _⟩
        rintro _ ⟨m'', hm'', rfl⟩ _ ⟨m', hm', rfl⟩
        refine' ⟨m'' * m * m', N_mul _ (N_mul _ hm'' _ hm) _ hm', mul_assoc _ _ _⟩
      · rintro _ ⟨m', hm', rfl⟩
        exact N_mul _ hm' _ hm
    /- In particular, this means that `m' * m = m` for some `m'`. We now use minimality again
       to show that this holds for all `m' ∈ N`. -/
    have absorbing_eq_self : N ∩ { m' | m' * m = m } = N := by
      apply N_minimal
      · refine' ⟨N_closed.inter ((T1Space.t1 m).preimage (continuous_mul_left m)), _, _⟩
        · rwa [← scaling_eq_self] at hm
        · rintro m'' ⟨mem'', eq'' : _ = m⟩ m' ⟨mem', eq' : _ = m⟩
          refine' ⟨N_mul _ mem'' _ mem', _⟩
          rw [Set.mem_setOf_eq, mul_assoc, eq', eq'']
      apply Set.inter_subset_left
    -- Thus `m * m = m` as desired.
    rw [← absorbing_eq_self] at hm
    -- ⊢ m * m = m
    exact hm.2
    -- 🎉 no goals
  refine' zorn_superset _ fun c hcs hc => _
  -- ⊢ ∃ lb, lb ∈ S ∧ ∀ (s : Set M), s ∈ c → lb ⊆ s
  refine'
    ⟨⋂₀ c, ⟨isClosed_sInter fun t ht => (hcs ht).1, _, fun m hm m' hm' => _⟩, fun s hs =>
      Set.sInter_subset_of_mem hs⟩
  · obtain rfl | hcnemp := c.eq_empty_or_nonempty
    -- ⊢ Set.Nonempty (⋂₀ ∅)
    · rw [Set.sInter_empty]
      -- ⊢ Set.Nonempty Set.univ
      apply Set.univ_nonempty
      -- 🎉 no goals
    convert
      @IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed _ _ _ hcnemp.coe_sort
        ((↑) : c → Set M) ?_ ?_ ?_ ?_
    · exact Set.sInter_eq_iInter
      -- 🎉 no goals
    · refine' DirectedOn.directed_val (IsChain.directedOn hc.symm)
      -- 🎉 no goals
    exacts [fun i => (hcs i.prop).2.1, fun i => (hcs i.prop).1.isCompact, fun i => (hcs i.prop).1]
    -- 🎉 no goals
  · rw [Set.mem_sInter]
    -- ⊢ ∀ (t : Set M), t ∈ c → m * m' ∈ t
    exact fun t ht => (hcs ht).2.2 m (Set.mem_sInter.mp hm t ht) m' (Set.mem_sInter.mp hm' t ht)
    -- 🎉 no goals
#align exists_idempotent_of_compact_t2_of_continuous_mul_left exists_idempotent_of_compact_t2_of_continuous_mul_left
#align exists_idempotent_of_compact_t2_of_continuous_add_left exists_idempotent_of_compact_t2_of_continuous_add_left

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning:
   expanding binder collection (x y «expr ∈ » s) -/
/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[to_additive exists_idempotent_in_compact_add_subsemigroup
      "A version of
      `exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in
      some specified nonempty compact additive subsemigroup."]
theorem exists_idempotent_in_compact_subsemigroup {M} [Semigroup M] [TopologicalSpace M] [T2Space M]
    (continuous_mul_left : ∀ r : M, Continuous (· * r)) (s : Set M) (snemp : s.Nonempty)
    (s_compact : IsCompact s) (s_add : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x * y ∈ s) :
    ∃ m ∈ s, m * m = m := by
  let M' := { m // m ∈ s }
  -- ⊢ ∃ m, m ∈ s ∧ m * m = m
  letI : Semigroup M' :=
    { mul := fun p q => ⟨p.1 * q.1, s_add _ p.2 _ q.2⟩
      mul_assoc := fun p q r => Subtype.eq (mul_assoc _ _ _) }
  haveI : CompactSpace M' := isCompact_iff_compactSpace.mp s_compact
  -- ⊢ ∃ m, m ∈ s ∧ m * m = m
  haveI : Nonempty M' := nonempty_subtype.mpr snemp
  -- ⊢ ∃ m, m ∈ s ∧ m * m = m
  have : ∀ p : M', Continuous (· * p) := fun p =>
    ((continuous_mul_left p.1).comp continuous_subtype_val).subtype_mk _
  obtain ⟨⟨m, hm⟩, idem⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left this
  -- ⊢ ∃ m, m ∈ s ∧ m * m = m
  exact ⟨m, hm, Subtype.ext_iff.mp idem⟩
  -- 🎉 no goals
#align exists_idempotent_in_compact_subsemigroup exists_idempotent_in_compact_subsemigroup
#align exists_idempotent_in_compact_add_subsemigroup exists_idempotent_in_compact_add_subsemigroup
