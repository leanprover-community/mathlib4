/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/

import Mathlib.GroupTheory.Complement
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Lemma of B. H. Neumann on coverings of a group by cosets.

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$: $$ G = ⋃_{i = 1}^n C_i g_i. $$

* `Subgroup.exists_finiteIndex_of_leftCoset_cover`
  at least one subgroup $C_i$ has finite index in $G$.

* `Subgroup.leftCoset_cover_filter_FiniteIndex`
  the cosets of subgroups of infinite index may be omitted from the covering.

* `Subgroup.one_le_sum_inv_index_of_leftCoset_cover` :
  the sum of the inverses of the indexes of the $C_i$ is greater than or equal to $1$.

* `Subgroup.exists_index_le_card_of_leftCoset_cover` :
  the index of (at least) one of these subgroups does not exceed $n$.

A corollary of `Subgroup.exists_finiteIndex_of_leftCoset_cover` is:

* `Subspace.union_ne_univ_of_lt_top` :
  a vector space over an infinite field cannot be a finite union of proper subspaces.

This can be used to show that an algebraic extension of fields is determined by the
set of all minimal polynomials (not proved here).

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

-/

open scoped Pointwise BigOperators

instance finite_option (α : Type*) [Finite α] : Finite (Option α) := by
  apply Nat.finite_of_card_ne_zero
  rw [Finite.card_option]
  exact Ne.symm (Nat.zero_ne_add_one (Nat.card α))

section leftCoset_cover_const

variable {G : Type*} [Group G]

@[to_additive]
theorem Subgroup.exists_leftTransversal_of_FiniteIndex
    {D H : Subgroup G} [D.FiniteIndex] (hD_le_H : D ≤ H) :
    ∃ t : Finset H,
      (t : Set H) ∈ Subgroup.leftTransversals (D.subgroupOf H) ∧
        ⋃ g ∈ t, (g : G) • (D : Set G) = H := by
  have ⟨t, ht⟩ := Subgroup.exists_left_transversal (D.subgroupOf H) 1
  have hf : t.Finite := (Subgroup.MemLeftTransversals.finite_iff ht.1).mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop,
    Subtype.exists, exists_and_right, SetLike.mem_coe]
  constructor
  · rintro ⟨y, ⟨hy, -⟩, d, h, rfl⟩
    exact H.mul_mem hy (hD_le_H h)
  · intro hx
    rw [Subgroup.mem_leftTransversals_iff_existsUnique_inv_mul_mem] at ht
    have ⟨y, hy⟩ := ht.1 ⟨x, hx⟩
    exact ⟨y, ⟨y.1.2, y.2⟩, Set.mem_smul_set_iff_inv_smul_mem.mpr hy.1⟩

variable {ι : Type*} {s : Set ι} {H : Subgroup G} {g : ι → G}

@[to_additive]
theorem Subgroup.mem_leftCoset_iff (g h : G) :
    g ∈ h • (H : Set G) ↔ (g : G ⧸ H) = (h : G ⧸ H) := by
  rw [_root_.mem_leftCoset_iff, eq_comm, SetLike.mem_coe, QuotientGroup.eq]

@[to_additive]
theorem Subgroup.leftCoset_cover_const_iff_surjOn :
    ⋃ i ∈ s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι → G ⧸ H) s Set.univ := by
  simp [Set.eq_univ_iff_forall, _root_.mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

variable (hcovers : ⋃ i ∈ s, g i • (H : Set G) = Set.univ)

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
@[to_additive]
theorem Subgroup.finiteIndex_of_leftCoset_cover_const [Finite s] :
    H.FiniteIndex := by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers
    (Set.finite_coe_iff.mp inferInstance)
  exact H.finiteIndex_of_finite_quotient

@[to_additive]
theorem Subgroup.index_le_of_leftCoset_cover_const [Finite s] :
    H.index ≤ Nat.card s := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ (Nat.zero_le _)
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers)

@[to_additive]
theorem Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq
    [Finite s] (hind : H.index = Nat.card s) :
    Set.PairwiseDisjoint s (fun i ↦ g i • (H : Set G)) := by
  cases H.index.eq_zero_or_pos with
  | inl h =>
    rw [h, eq_comm, Nat.card_eq_zero] at hind
    rw [Set.isEmpty_coe_sort.mp (Or.resolve_right hind (not_infinite_iff_finite.mpr inferInstance))]
    apply Set.pairwiseDisjoint_empty
  | inr h =>
    have : Fintype (G ⧸ H) :=
      Subgroup.fintypeOfIndexNeZero (Nat.not_eq_zero_of_lt h)
    suffices Function.Bijective (fun (i : s) ↦ (g i : G ⧸ H)) by
      intro i hi j hj h' c hi' hj' x hx
      specialize hi' hx
      specialize hj' hx
      rw [Subgroup.mem_leftCoset_iff] at hi' hj'
      rw [ne_eq, ← Subtype.mk.injEq (p := (· ∈ (s : Set ι))) i hi j hj] at h'
      exact h' <| this.injective <| by simp only [← hi', ← hj']
    have : Fintype s := Set.Finite.fintype s.toFinite
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · rwa [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    · simp only [Fintype.card_eq_nat_card, ← hind, Subgroup.index_eq_card]

end leftCoset_cover_const

section

/- variable {G : Type*} [Group G]
    {ι : Type*} {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (g i) • (H i : Set G) = Set.univ)
-/

structure Group.LeftCosetCover (G : Type*) [Group G] where
  carrier : Type*
  offset : carrier → G
  subgroup : carrier → Subgroup G
  covers : ⋃ i, offset i • (subgroup i : Set G) = Set.univ

structure AddGroup.LeftCosetCover (G : Type*) [AddGroup G] where
  carrier : Type*
  offset : carrier → G
  subgroup : carrier → AddSubgroup G
  covers : ⋃ i, offset i +ᵥ (subgroup i : Set G) = Set.univ

variable {G : Type*} [Group G] (c : Group.LeftCosetCover G)

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
@[to_additive]
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover_aux
    [DecidableEq (Subgroup G)]
    [Finite c.carrier]
    (j : c.carrier)
    (hcovers' : ⋃ i ∈ { i : c.carrier | (c.subgroup i = c.subgroup j)},
      c.offset i • (c.subgroup i : Set G) ≠ Set.univ) :
    ∃ i : c.carrier, c.subgroup i ≠ c.subgroup j ∧ (c.subgroup i).FiniteIndex := by
  classical
  have ⟨n, hn⟩ : ∃ n, n = Nat.card (Set.range c.subgroup) := exists_eq
  induction n using Nat.strongRec generalizing c with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i, c.subgroup i = c.subgroup j → (c.offset i : G ⧸ c.subgroup i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, _root_.mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : ∀ (y : G), y • (c.subgroup j : Set G) ⊆
        ⋃ i ∈ { i |  c.subgroup i ≠ c.subgroup j}, (y * x⁻¹ * c.offset i) • (c.subgroup i : Set G) := by
      intro y z hz
      simp only [Set.mem_iUnion, ne_eq, Set.mem_setOf_eq, exists_prop]
      have ⟨i, hi, hmem⟩ : ∃ i, x * y⁻¹ * z ∈ c.offset i • (c.subgroup i : Set G) := by
        simpa using Set.eq_univ_iff_forall.mp c.covers (x * y⁻¹ * z)
      simp only [SetLike.mem_coe, smul_eq_mul] at hmem
      rw [← inv_mul_eq_iff_eq_mul] at hmem
      simp only [mul_inv_rev, inv_inv, ← mul_assoc] at hmem
      -- rw [_root_.mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hmem
      use i
      constructor
      · intro h
        apply hx i h
        rw [eq_comm, QuotientGroup.eq]
        suffices x⁻¹ * c.offset i = y⁻¹ * z * hi⁻¹ by
          rw [this]
          apply Subgroup.mul_mem _ _ (Subgroup.inv_mem _ hmem.1)
          rw [h]
          rwa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe] at hz
        rw [← hmem.2]; group
      · simp [Set.mem_smul_set_iff_inv_smul_mem, ← hmem.2]
        group
        exact hmem.1
  -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := { i | c.subgroup i ≠ c.subgroup j} × Option { i | c.subgroup i = c.subgroup j}
    let f : κ → G
    | ⟨k₁, some k₂⟩ => c.offset k₂ * x⁻¹ * c.offset k₁
    | ⟨k₁, none⟩  => c.offset k₁
    let K (k : κ) : Subgroup G := c.subgroup k.1.val
    have hK' (k : κ) : K k ∈ (Set.range c.subgroup) ∧ K k ≠ c.subgroup j := by
      simp only [Set.mem_range, exists_apply_eq_apply, ne_eq, true_and]
      intro h
      have := k.1.property
      simp only [ne_eq, Set.mem_setOf_eq, Set.coe_setOf] at this
      apply this
      exact h
    have hK (k : κ) : K k ≠ c.subgroup j := (hK' k).right
    let c' : Group.LeftCosetCover G := {
      carrier := κ
      offset := f
      subgroup := K
      covers := by
        simp only [Set.iUnion_eq_univ_iff]
        intro y
        obtain ⟨i, hy⟩ := Set.iUnion_eq_univ_iff.mp c.covers y
        by_cases hi : c.subgroup i = c.subgroup j
        · rw [hi] at hy
          specialize hx (c.offset i) hy
          simp only [ne_eq, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop] at hx
          obtain ⟨i', hi', h⟩ := hx
          use ⟨⟨i', hi'⟩, some ⟨i, hi⟩⟩
        · use ⟨⟨i, hi⟩, none⟩ }
    -- Let `H k` be one of the subgroups in this covering.
    let hcovers := c'.covers
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, ← not_nonempty_iff] at hcovers
      exact hcovers ⟨1⟩
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcovers' : ⋃ i ∈ {i | K i = K k},  f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr (t := fun i _ ↦ f i • (K k : Set G)) fun i hi => by
        rw [hi]] at hcovers'
      exact ⟨k.1, hK k, Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn' : Nat.card (Set.range c'.subgroup) < n := hn ▸ by
      suffices Set.range c'.subgroup ⊆ Set.range c.subgroup \ {c.subgroup j} by
        simp only [Set.Nat.card_coe_set_eq]
        apply lt_of_le_of_lt (Set.ncard_le_ncard this)
        apply Set.ncard_diff_singleton_lt_of_mem
        use j
        exact Set.finite_range c.subgroup
      rintro _ ⟨i, rfl⟩
      simp only [Set.mem_diff, Set.mem_range, exists_apply_eq_apply, Set.mem_singleton_iff,
        true_and]
      exact hK i
    obtain ⟨k', _, hk'_ind⟩ := ih _ hn' c' k hcovers' rfl
    exact ⟨k'.1, hK k', hk'_ind⟩

@[to_additive]
theorem Group.LeftCosetCover.nonempty_carrier :
    Nonempty c.carrier := by
  rw [← not_isEmpty_iff]
  intro h
  exact Set.empty_ne_univ (Set.iUnion_of_empty (ι := c.carrier) _ ▸ c.covers)

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
@[to_additive]
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover
    {G : Type*} [Group G] (c : Group.LeftCosetCover G) [Finite c.carrier] :
    ∃ k, (c.subgroup k).FiniteIndex := by
  classical
  have ⟨j⟩ := c.nonempty_carrier
  by_cases hcovers' : ⋃ i ∈ { i | c.subgroup i = c.subgroup j}, c.offset i • (c.subgroup i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr (t := fun i _ ↦ c.offset i • (c.subgroup j : Set G))
      fun i hi => by rw [hi]] at hcovers'
    exact ⟨j, Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, _, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover_aux c j hcovers'
    exact ⟨i, hfi⟩

@[to_additive]
def Subgroup.LeftCosetCover.core : Subgroup G :=
  ⨅ i ∈ { i | (c.subgroup i).FiniteIndex }, (c.subgroup i)

@[to_additive]
theorem Subgroup.LeftCosetCover.core_finiteIndex [Finite c.carrier] :
    (Subgroup.LeftCosetCover.core c).FiniteIndex := by
  apply Subgroup.finiteIndex_iInf
  intro i
  by_cases h : (c.subgroup i).FiniteIndex
  · simp only [Set.mem_setOf_eq, h, iInf_pos]
  · simp only [Set.mem_setOf_eq, h, not_false_eq_true, iInf_neg]
    infer_instance

@[to_additive]
theorem Subgroup.LeftCosetCover.core_le [Finite c.carrier]
    {i : c.carrier} (hi : (c.subgroup i).FiniteIndex) :
    Subgroup.LeftCosetCover.core c ≤ c.subgroup i :=
  iInf₂_le i hi

@[to_additive]
noncomputable def Subgroup.LeftCosetCover.density : ℚ :=
  finsum fun i ↦ ((c.subgroup i).index : ℚ)⁻¹

def Set.iUnion_filter {ι : Type*} {α : Type*} (s : ι → Set α) (p : ι → Prop) :
    ⋃ i, s i = (⋃ i ∈ { i | p i}, s i) ∪ (⋃ i ∈ { i | ¬ p i}, s i) := by
  rw [← Set.biUnion_union, eq_comm]
  convert Set.biUnion_univ s
  ext i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  apply Classical.em

@[to_additive]
noncomputable def Subgroup.LeftCosetCover.sieve [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Group.LeftCosetCover G := by
  let D := Subgroup.LeftCosetCover.core c
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := Subgroup.LeftCosetCover.core_finiteIndex c
  have hD_le {i} (hfi : (c.subgroup i).FiniteIndex) : D ≤ c.subgroup i :=
    Subgroup.LeftCosetCover.core_le c hfi
  -- Each subgroup of finite index in the covering is the union of finitely many cosets of `D`.
  choose t ht using fun i hfi =>
    Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup i) (hD_le hfi)
  -- We construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  exact {
    carrier := (i : c.carrier) × { x // x ∈ if h : (c.subgroup i).FiniteIndex then t i h else {1} }
    offset := fun k ↦ c.offset k.1 * k.2.val
    subgroup := fun k ↦ if (c.subgroup k.1).FiniteIndex then D else c.subgroup k.1
    covers := by
      rw [← c.covers]
      rw [Set.iUnion_sigma]
      apply Set.iUnion_congr
      intro i
      simp only [← smul_eq_mul]
      simp_rw [smul_assoc, ← Set.smul_set_iUnion]
      apply congr_arg₂ _ rfl
      rw [Set.iUnion_subtype]
      by_cases hfi : (c.subgroup i).FiniteIndex
      · convert (ht i hfi).2
        rw [if_pos hfi]
        rw [dif_pos hfi]
      · simp only
        rw [if_neg hfi, dif_neg hfi]
        simp only [Finset.mem_singleton, SetLike.coe_mem, smul_coe_set, Set.iUnion_iUnion_eq_left] }

theorem Subgroup.LeftCosetCover.sieve_carrier_fiber_le_subgroup
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (y : (sieve c).carrier) :
    (y.snd : G) ∈ c.subgroup y.fst :=
  SetLike.coe_mem y.snd.val

/- theorem Subgroup.LeftCosetCover.sieve_carrier_of_finite_index
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (x : c.carrier) (hx : (c.subgroup x).FiniteIndex)  :
    ∃ (t : Finset (c.subgroup x)),
      ((t : Set (c.subgroup x)) ∈ Subgroup.leftTransversals
        ((Subgroup.LeftCosetCover.core c).subgroupOf (c.subgroup x)  : Set _))
      ∧ (Set.image (fun (y) ↦ (y.snd : G))
        {y : (Subgroup.LeftCosetCover.sieve c).carrier | y.fst = x})
        = (t : Set (c.subgroup x)) := by
  let D := Subgroup.LeftCosetCover.core c
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := Subgroup.LeftCosetCover.core_finiteIndex c
  have hD_le {i} (hfi : (c.subgroup i).FiniteIndex) : D ≤ c.subgroup i :=
    Subgroup.LeftCosetCover.core_le c hfi
  let t := fun i hfi ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup i) (hD_le hfi)).choose
  let ht := fun i hfi ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup i) (hD_le hfi)).choose_spec
  use t x hx
  constructor
  · exact (ht x hx).1
  · ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.coe_sort_coe, Finset.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨y, hy, hg⟩
      have : g ∈ c.subgroup x := by
        rw [← hy, ← hg]
        exact Subgroup.LeftCosetCover.sieve_carrier_fiber_le_subgroup c y
      use this
      have hy' : (⟨g, this⟩ : c.subgroup x)  ∈ t x hx := by
        convert y.snd.property
        rw [hy]
        rw [hy]
        rw [hy]
        rw [hg]
        rw [hy, dif_pos hx]
      convert hy'
    · rintro ⟨hg, hgx⟩
      use ⟨x, ⟨g, hg⟩, ?_⟩
      rw [dif_pos hx]
      exact hgx
-/

@[to_additive]
theorem Subgroup.LeftCosetCover.sieve_subgroup_eq
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (k : (Subgroup.LeftCosetCover.sieve c).carrier) :
    (Subgroup.LeftCosetCover.sieve c).subgroup k =
      if (c.subgroup k.1).FiniteIndex
      then Subgroup.LeftCosetCover.core c
      else c.subgroup k.1 := rfl

@[to_additive]
theorem Subgroup.LeftCosetCover.sieve_subgroup_finite_index_iff
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (k : (Subgroup.LeftCosetCover.sieve c).carrier) :
    ((Subgroup.LeftCosetCover.sieve c).subgroup k).FiniteIndex ↔
      (c.subgroup k.1).FiniteIndex := by
  rw [Subgroup.LeftCosetCover.sieve_subgroup_eq]
  split_ifs with h
  · simp only [Subgroup.LeftCosetCover.core_finiteIndex c, h]
  · simp only [h]

 @[to_additive]
theorem Subgroup.LeftCosetCover.sieve_subgroup_eq_core_iff
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (i : (Subgroup.LeftCosetCover.sieve c).carrier) :
    (Subgroup.LeftCosetCover.sieve c).subgroup i = Subgroup.LeftCosetCover.core c ↔
    (c.subgroup i.fst).FiniteIndex := by
  rw [Subgroup.LeftCosetCover.sieve_subgroup_eq]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h'
    exact h (h'.symm ▸ core_finiteIndex c)


@[to_additive]
instance Subgroup.LeftCosetCover.sieve_finite
    [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Finite (Subgroup.LeftCosetCover.sieve c).carrier := Finite.instSigma

-- There is at least one coset of a subgroup of finite index in the original covering.
-- Therefore a coset of `D` occurs in the new covering.
@[to_additive]
theorem Subgroup.LeftCosetCover.sieve_contains_core [Finite c.carrier]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    ∃ k, (Subgroup.LeftCosetCover.sieve c).subgroup k = Subgroup.LeftCosetCover.core c := by
  obtain ⟨k, hk⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (Subgroup.LeftCosetCover.sieve c)
  rw [sieve_subgroup_finite_index_iff, ← sieve_subgroup_eq_core_iff] at hk
  exact ⟨k, hk⟩

@[to_additive]
noncomputable def Subgroup.LeftCosetCover.normalize
    [Finite c.carrier]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Group.LeftCosetCover G where
  carrier := { k : (Subgroup.LeftCosetCover.sieve c).carrier |
    ((Subgroup.LeftCosetCover.sieve c).subgroup k).FiniteIndex }
  subgroup := fun k ↦ (Subgroup.LeftCosetCover.sieve c).subgroup k
  offset := fun k ↦ (Subgroup.LeftCosetCover.sieve c).offset k
  covers := by
    have ⟨k, hk⟩ := Subgroup.LeftCosetCover.sieve_contains_core c
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.iUnion_subtype]
    by_contra h
    have ⟨j, hj, hj'⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover_aux
      (Subgroup.LeftCosetCover.sieve c) k ?_
    · apply hj
      rw [hk, Subgroup.LeftCosetCover.sieve_subgroup_eq_core_iff,
        ← sieve_subgroup_finite_index_iff]
      exact hj'
    · intro h'
      apply h
      simp only [Set.mem_setOf_eq] at h'
      rw [← h']
      apply Set.iUnion_congr
      intro i
      apply Set.iUnion_congr_Prop ?_ (fun _ ↦ rfl)
      rw [hk, sieve_subgroup_eq_core_iff, sieve_subgroup_finite_index_iff]

@[to_additive]
instance Subgroup.LeftCosetCover.normalize_finite
    [Finite c.carrier]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Finite (Subgroup.LeftCosetCover.normalize c).carrier := Subtype.finite

-- -- to_additive is confused because of the inverse in `density`
-- @[to_additive]
theorem Subgroup.LeftCosetCover.sieve_density
    [Finite c.carrier]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Subgroup.LeftCosetCover.density (Subgroup.LeftCosetCover.sieve c)
      = Subgroup.LeftCosetCover.density c := by
  unfold density
  have _ : Fintype c.carrier := Fintype.ofFinite _
  have _ : Fintype (sieve c).carrier := Fintype.ofFinite (sieve c).carrier
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.univ)]
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.univ)]
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := fun k ↦ k.1)]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : (c.subgroup x).FiniteIndex
    · rw [Finset.sum_congr rfl (g := fun _ ↦ ((core c).index : ℚ)⁻¹)]
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      rw [mul_inv_eq_iff_eq_mul₀]
      rw [← Subgroup.relindex_mul_index (core_le c hx), mul_comm]
      simp only [Nat.cast_mul,  mul_assoc]
      rw [(mul_inv_eq_one₀ _).mpr rfl, mul_one]
      simp only [Nat.cast_inj]
      unfold sieve
      simp only [id_eq, smul_eq_mul, eq_mpr_eq_cast, cast_eq]
      have : (core c).FiniteIndex := core_finiteIndex c
      set t := fun y hy ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup y) (Subgroup.LeftCosetCover.core_le c hy)).choose with ht_eq
      let ht := fun y hy ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup y) (Subgroup.LeftCosetCover.core_le c hy)).choose_spec

      rw [Finset.card_congr (f := fun y hy ↦ (⟨y.snd, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rw [← hy]
        exact sieve_carrier_fiber_le_subgroup c y⟩ : c.subgroup x))
        (t := t x hx)]
      have := Subgroup.card_left_transversal (ht x hx).1
      simp only [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe] at this
      rw [this]
      simp only [Subgroup.subgroupOf, Subgroup.index_comap,
        Subgroup.subtype_range]
      · rintro ⟨y1, ⟨y2, hy2⟩⟩ hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy
        have hy1 : (c.subgroup y1).FiniteIndex := hy ▸ hx
        rw [dif_pos hy1] at hy2
        simp only
        have hy2 : y2 ∈ t y1 hy1 := by
          rw [ht_eq]
          exact hy2
        convert hy2
        all_goals
          rw [hy]
      · rintro ⟨y1, ⟨y2, hy2⟩⟩ ⟨y'1, ⟨y'2, hy'2⟩⟩ h h'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy'2 h h'
        simp only [Subtype.mk.injEq, Sigma.mk.inj_iff]
        intro h2
        constructor
        · rw [h, h']
        · refine (Subtype.heq_iff_coe_heq ?_ ?_).mpr ?_
          rw [h, h']
          rw [h, h']
          refine (Subtype.heq_iff_coe_heq rfl ?_).mpr ?_
          rw [h, h']
          simp only [h2, heq_eq_eq]
      · intro g hg
        have hg' : g ∈ if (c.subgroup x).FiniteIndex then t x hx else {1} := by
          rw [if_pos hx]
          exact hg
        use ⟨x, ⟨g, hg'⟩⟩
        simp only [Subtype.coe_eta, Finset.mem_filter, Finset.mem_univ, and_self, exists_const]
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact hx.finiteIndex
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact (core_finiteIndex c).finiteIndex
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, inv_inj, Nat.cast_inj]
        intro y hy
        apply congr_arg
        rw [sieve_subgroup_eq_core_iff, hy]
        exact hx
    · rw [Finset.sum_congr rfl (g := fun _ ↦ 0)]
      simp only [Finset.sum_const_zero, zero_eq_inv]
      rw [eq_comm, Nat.cast_eq_zero]
      by_contra hx'
      exact hx ⟨hx'⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, inv_eq_zero, Nat.cast_eq_zero]
        intro y hy
        suffices ¬ ((sieve c).subgroup y).FiniteIndex by
          by_contra hy'
          exact this ⟨hy'⟩
        rw [sieve_subgroup_finite_index_iff, hy]
        exact hx
  · exact fun _ _ ↦ Finset.mem_univ _
  · simp only [Finset.coe_univ, Set.subset_univ]
  · simp only [Finset.coe_univ, Set.subset_univ]

-- -- to_additive is confused because of the inverse in `density`
-- @[to_additive]
theorem Subgroup.LeftCosetCover.normalize_density
    [Finite c.carrier]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    Subgroup.LeftCosetCover.density (Subgroup.LeftCosetCover.normalize c)
      = Subgroup.LeftCosetCover.density c := by
  conv_rhs => rw [← sieve_density]
  unfold density
  have : Fintype c.carrier := Fintype.ofFinite _
  have : Fintype (sieve c).carrier := Fintype.ofFinite (sieve c).carrier
  have : Fintype (normalize c).carrier := Fintype.ofFinite (normalize c).carrier
  simp only [normalize]
  simp only [Set.coe_setOf, Set.mem_setOf_eq]
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.univ)]
  rw [finsum_eq_finset_sum_of_support_subset _ (s := Finset.univ.filter (fun x => ((sieve c).subgroup x).FiniteIndex))]
  rw [Finset.sum_of_injOn Subtype.val Set.injOn_subtype_val]
  · rintro ⟨x, hx⟩ _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hx
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_univ, Set.image_univ,
    Subtype.range_coe_subtype, Set.mem_setOf_eq, inv_eq_zero, Nat.cast_eq_zero]
    intro i hi hi'
    exfalso
    contradiction
  · exact fun i _ ↦ rfl
  · intro x
    simp only [Function.support_inv, Function.mem_support, ne_eq, Nat.cast_eq_zero,
      Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    intro hx
    exact { finiteIndex := hx }
  simp only [Function.support_inv, Finset.coe_univ, Set.subset_univ]

theorem Subgroup.LeftCosetCover.disjoint_normalize_of_density_eq_one
    [Finite c.carrier]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    (h : Subgroup.LeftCosetCover.density c = 1) :
    Set.PairwiseDisjoint { i | (c.subgroup i).FiniteIndex} (fun i ↦ c.offset i • (c.subgroup i : Set G)) := by
  rw [← Subgroup.LeftCosetCover.normalize_density] at h
  -- rw [mul_inv_eq_one₀ (Nat.cast_ne_zero.mpr hD.finiteIndex), Nat.cast_inj, Finset.coe_filter]
  intro i hi j hj hij cc hi' hj' x hx
  -- have hdisjoint := Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq hcovers' h.symm
  -- We know the `f k • K k` are pairwise disjoint and need to prove that the `g i • H i` are.
  rw [Set.mem_setOf_eq] at hi hj
  simp only [Set.le_eq_subset] at hi' hj'
  have : (core c).FiniteIndex := core_finiteIndex c
  set t := fun y hy ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup y) (Subgroup.LeftCosetCover.core_le c hy)).choose with ht_eq
  let ht := fun y hy ↦ (Subgroup.exists_leftTransversal_of_FiniteIndex (H := c.subgroup y) (Subgroup.LeftCosetCover.core_le c hy)).choose_spec
  have hk' (i : c.carrier) (hi : (c.subgroup i).FiniteIndex) (hi' : cc ≤ c.offset i • (c.subgroup i : Set G)) :
      ∃ (k : (normalize c).carrier), k.1.1 = i ∧ (normalize c).subgroup k = core c ∧ x ∈ (normalize c).offset k • (core c : Set G) := by
    rw [← (ht i hi).2] at hi'
    obtain ⟨g, hg, rfl⟩ := hi' hx
    simp only [Set.mem_iUnion, exists_prop, Subtype.exists, exists_and_right] at hg
    simp only at hx
    obtain ⟨k, ⟨hk, hk'⟩, hk''⟩ := hg
    refine ⟨⟨⟨i, ⟨k, hk⟩, dif_pos hi ▸ hk'⟩,
      by simp only [Set.mem_setOf_eq]
         unfold sieve
         simp only [if_pos hi]
         apply core_finiteIndex⟩, rfl, by
         unfold normalize
         rw [Subgroup.LeftCosetCover.sieve_subgroup_eq_core_iff]
         exact hi,
      by unfold normalize sieve
         simp only [← smul_eq_mul, smul_assoc]
         exact Set.smul_mem_smul_set hk''⟩
  have : Finite (normalize c).carrier := normalize_finite c
  have : Fintype (normalize c).carrier := Fintype.ofFinite (normalize c).carrier
  have hcovers : ⋃ i ∈ (Finset.univ :Finset  (normalize c).carrier), (normalize c).offset i • (core c :Set G) = Set.univ := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    convert (normalize c).covers with ⟨⟨i, ⟨s, hs⟩⟩, hi⟩
    simp only [Set.mem_setOf_eq, sieve_subgroup_finite_index_iff] at hi
    unfold normalize
    rw [eq_comm, sieve_subgroup_eq_core_iff]
    exact hi
  have ⟨k₁, hik₁, hk₁, hxk₁⟩ := hk' i hi hi'
  have ⟨k₂, hjk₂, hk₂, hxk₂⟩ := hk' j hj hj'
  rw [← Set.singleton_subset_iff, ← Set.le_iff_subset] at hxk₁ hxk₂ ⊢
  apply Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq hcovers
    ?_ ?_ ?_ ?_ hxk₁ hxk₂
  · unfold density at h
    rw [finsum_eq_finset_sum_of_support_subset (s := Finset.univ)] at h
    · rw [Finset.sum_congr rfl (g := fun _ ↦ ((core c).index : ℚ)⁻¹)] at h
      · rw [Finset.sum_const] at h
        rw [nsmul_eq_mul] at h
        rw [mul_inv_eq_one₀] at h
        · simp only [Nat.cast_inj] at h
          rw [← h]
          exact Eq.symm (Nat.card_eq_finsetCard Finset.univ)
        · simp only [ne_eq, Nat.cast_eq_zero]
          exact (core_finiteIndex c).finiteIndex
      · rintro ⟨⟨i, x⟩, hi⟩ _
        congr
        unfold normalize
        simpa only [sieve_subgroup_eq_core_iff, Set.mem_setOf_eq, sieve_subgroup_finite_index_iff] using hi
    · simp only [Finset.coe_univ, Set.subset_univ]

  · simp only [Finset.mem_val, Finset.mem_univ]
    trivial
  · simp only [Finset.mem_val, Finset.mem_univ]
    trivial
  · intro hk
    apply hij
    rw [← hik₁, ← hjk₂, hk]

variable {ι : Type*} {g : ι → G} {H : ι → Subgroup G} {s : Finset ι}
  (covers : ⋃ i ∈ s, g i • (H i : Set G) = Set.univ)

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
@[to_additive]
theorem Subgroup.leftCoset_cover_filter_FiniteIndex
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    ⋃ i ∈ s.filter fun i ↦ (H i).FiniteIndex, g i • (H i : Set G) = Set.univ :=
  sorry -- (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`. Then the
sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
@[to_additive one_le_sum_inv_index_of_leftCoset_cover]
theorem Subgroup.one_le_sum_inv_index_of_leftCoset_cover :
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ :=
  sorry
  -- have := Classical.decPred (Subgroup.FiniteIndex : Subgroup G → Prop)
  -- (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
If the sum of the inverses of the indexes of the subgroups `H i` is equal to 1,
then the cosets of the subgroups of finite index are pairwise disjoint -/
@[to_additive]
theorem Subgroup.pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    ∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 →
      Set.PairwiseDisjoint { i | i ∈ s ∧ (H i).FiniteIndex}
        (fun i ↦ g i • (H i : Set G)) :=
  sorry
  -- (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

/-- B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
@[to_additive]
theorem Subgroup.exists_index_le_card_of_leftCoset_cover :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ Nat.card s := by
  classical
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_lt
  by_cases hs : s = ∅
  · simp only [hs, Finset.sum_empty, show (0 : ℚ) < 1 from rfl]
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hs
  have hs' : 0 < s.card := Nat.pos_of_ne_zero (Finset.card_ne_zero.mpr hs)
  have hlt : ∀ i ∈ s, ((H i).index : ℚ)⁻¹ < (s.card : ℚ)⁻¹ := fun i hi ↦ by
    cases (H i).index.eq_zero_or_pos with
    | inl hindex =>
      rwa [hindex, Nat.cast_zero, inv_zero, inv_pos, Nat.cast_pos]
    | inr hindex =>
      exact inv_lt_inv_of_lt (by exact_mod_cast hs') (by exact_mod_cast h i hi ⟨hindex.ne'⟩)
  apply (Finset.sum_lt_sum_of_nonempty hs hlt).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul,
    mul_inv_eq_iff_eq_mul₀ (Nat.cast_ne_zero.mpr hs'.ne'), one_mul]

end

section Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : ι → Submodule R M} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (p i : Set M) = Set.univ)

theorem Submodule.exists_finiteIndex_of_cover :
    ∃ k ∈ s, (p k).toAddSubgroup.FiniteIndex :=
  have hcovers' : ⋃ i ∈ s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

end Submodule

section Subspace

variable {k E ι : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E]
    {s : Finset (Subspace k E)}

/- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
theorem Subspace.biUnion_ne_univ_of_ne_top (hs : ∀ p ∈ s, p ≠ ⊤) :
    ⋃ p ∈ s, (p : Set E) ≠ Set.univ := by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex _
  have : Nontrivial (E ⧸ p) := Submodule.Quotient.nontrivial_of_lt_top p (hs p hp).lt_top
  have : Infinite (E ⧸ p) := Module.Free.infinite k (E ⧸ p)
  exact not_finite (E ⧸ p)

/- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
theorem Subspace.exists_eq_top_of_biUnion_eq_univ (hcovers : ⋃ p ∈ s, (p : Set E) = Set.univ) :
    ∃ p ∈ s, p = ⊤ := by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_ne_top hcovers

end Subspace
