/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/

import Mathlib.GroupTheory.Complement
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

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι → G}

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
theorem Subgroup.finiteIndex_of_leftCoset_cover_const : H.FiniteIndex := by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]
theorem Subgroup.index_le_of_leftCoset_cover_const : H.index ≤ s.card := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]
theorem Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq
    (hind : H.index = s.card) :
    Set.PairwiseDisjoint s (fun i ↦ g i • (H : Set G)) := by
  cases H.index.eq_zero_or_pos with
  | inl h =>
    exfalso
    rw [h, eq_comm, Finset.card_eq_zero] at hind
    simp only [hind, Finset.not_mem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  | inr h =>
    have : Fintype (G ⧸ H) :=
      Subgroup.fintypeOfIndexNeZero (Nat.not_eq_zero_of_lt h)
    suffices Function.Bijective (fun (i : s) ↦ (g i : G ⧸ H)) by
      intro i hi j hj h
      have h' : (⟨i, hi⟩ : s) ≠ ⟨j, hj⟩ := by
        simp only [ne_eq, Subtype.mk.injEq]
        exact h
      intro c hi' hj' x hx
      apply h'
      replace hi' := hi' hx
      replace hj' := hj' hx
      simp only [Subgroup.mem_leftCoset_iff] at hi' hj'
      apply this.injective
      simp only [← hi', ← hj']
    rw [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · exact hcovers
    · simp only [Fintype.card_coe, ← hind, Subgroup.index_eq_card]
end leftCoset_cover_const

section

variable {G : Type*} [Group G]
    {ι : Type*} {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (g i) • (H i : Set G) = Set.univ)

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
@[to_additive]
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover_aux [DecidableEq (Subgroup G)]
    (j : ι) (hj : j ∈ s) (hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i ∈ s, H i ≠ H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨n, hn⟩ : ∃ n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i ∈ s, H i = H j → (g i : G ⧸ H i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, _root_.mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : ∀ (y : G), y • (H j : Set G) ⊆
        ⋃ i ∈ s.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      simp_rw [Finset.mem_filter, Set.mem_iUnion]
      have ⟨i, hi, hmem⟩ : ∃ i ∈ s, x * (y⁻¹ * z) ∈ g i • (H i : Set G) :=
        by simpa using Set.eq_univ_iff_forall.mp hcovers (x * (y⁻¹ * z))
      rw [_root_.mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hmem
      refine ⟨i, ⟨hi, fun hij => hx i hi hij ?_⟩, ?_⟩
      · rwa [hmem, eq_comm, QuotientGroup.eq, hij, inv_mul_cancel_left,
          ← SetLike.mem_coe, ← _root_.mem_leftCoset_iff]
      · simpa [_root_.mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hmem
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(s.filter (H · ≠ H j)) × Option ↥(s.filter (H · = H j))
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩  => g k₁
    let K (k : κ) : Subgroup G := H k.1.val
    have hK' (k : κ) : K k ∈ (s.image H).erase (H j) := by
      have := Finset.mem_filter.mp k.1.property
      exact Finset.mem_erase.mpr ⟨this.2, Finset.mem_image_of_mem H this.1⟩
    have hK (k : κ) : K k ≠ H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    replace hcovers : ⋃ k ∈ Finset.univ, f k • (K k : Set G) = Set.univ :=
        Set.iUnion₂_eq_univ_iff.mpr fun y => by
      rw [← s.filter_union_filter_neg_eq (H · = H j), Finset.set_biUnion_union] at hcovers
      cases (Set.mem_union _ _ _).mp (hcovers.superset (Set.mem_univ y)) with
      | inl hy =>
        have ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
        have hk' : H k = H j := And.right <| by simpa using hk
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hx (g k) (hk' ▸ hy))
        exact ⟨⟨⟨i, hi⟩, some ⟨k, hk⟩⟩, Finset.mem_univ _, hy⟩
      | inr hy =>
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨⟨⟨i, hi⟩, none⟩, Finset.mem_univ _, hy⟩
    -- Let `H k` be one of the subgroups in this covering.
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, ← not_nonempty_iff] at hcovers
      exact hcovers ⟨1⟩
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcovers' : ⋃ i ∈ Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
      exact ⟨k.1, Finset.mem_of_mem_filter k.1.1 k.1.2, hK k,
        Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn' : (Finset.univ.image K).card < n := hn ▸ by
      refine ((Finset.card_le_card fun x => ?_).trans_lt <|
        Finset.card_erase_lt_of_mem (Finset.mem_image_of_mem H hj))
      rw [mem_image_univ_iff_mem_range, Set.mem_range]
      exact fun ⟨k, hk⟩ => hk ▸ hK' k
    have ⟨k', hk'⟩ := ih _ hn' hcovers k (Finset.mem_univ k) hcovers' rfl
    exact ⟨k'.1.1, Finset.mem_of_mem_filter k'.1.1 k'.1.2, hK k', hk'.2.2⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
@[to_additive]
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover : ∃ k ∈ s, (H k).FiniteIndex := by
  classical
  have ⟨j, hj⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty,
      eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hcovers
    exact hcovers 1
  by_cases hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
    exact ⟨j, hj, Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, hi, _, hfi⟩ :=
      Subgroup.exists_finiteIndex_of_leftCoset_cover_aux hcovers j hj hcovers'
    exact ⟨i, hi, hfi⟩

-- Auxiliary to `leftCoset_cover_filter_FiniteIndex` and `one_le_sum_inv_index_of_leftCoset_cover`.
@[to_additive]
theorem Subgroup.leftCoset_cover_filter_FiniteIndex_aux
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    (⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ) ∧
      (1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹) ∧
      (∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 → Set.PairwiseDisjoint
        (s.filter (fun i => (H i).FiniteIndex)) (fun i ↦ (H i : Set G))) := by
  classical
  let D := ⨅ k ∈ s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := Subgroup.finiteIndex_iInf' _ <| by simp
  have hD_le {i} (hi : i ∈ s) (hfi : (H i).FiniteIndex) : D ≤ H i :=
    iInf₂_le i (Finset.mem_filter.mpr ⟨hi, hfi⟩)
  -- Each subgroup of finite index in the covering is the union of finitely many cosets of `D`.
  choose t ht using fun i hi hfi =>
    Subgroup.exists_leftTransversal_of_FiniteIndex (H := H i) (hD_le hi hfi)
  -- We construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : s) × { x // x ∈ if h : (H i.1).FiniteIndex then t i.1 i.2 h else {1} }
  let f (k : κ) : G := g k.1 * k.2.val
  let K (k : κ) : Subgroup G := if (H k.1).FiniteIndex then D else H k.1
  have hcovers' : ⋃ k ∈ Finset.univ, f k • (K k : Set G) = Set.univ := by
    rw [← s.filter_union_filter_neg_eq (fun i => (H i).FiniteIndex)] at hcovers
    rw [← hcovers, ← Finset.univ.filter_union_filter_neg_eq (fun k => (H k.1).FiniteIndex),
      Finset.set_biUnion_union, Finset.set_biUnion_union]
    apply congrArg₂ (· ∪ ·) <;> rw [Set.iUnion_sigma, Set.iUnion_subtype] <;>
        refine Set.iUnion_congr fun i => ?_
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [← Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc, f, K, ht, hfi]
    · by_cases hfi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hfi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨k, hkfi, hk⟩ : ∃ k, (H k.1.1).FiniteIndex ∧ K k = D :=
    have ⟨j, hj, hjfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcovers
    have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_coe_sort.mp
      (Subgroup.MemLeftTransversals.toEquiv (ht j hj hjfi).1).symm.nonempty
    ⟨⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩, hjfi, if_pos hjfi⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' : ⋃ i ∈ Finset.univ.filter (K · = D), f i • (D : Set G) = Set.univ := by
    rw [← hk, Set.iUnion₂_congr fun i hi => by rw [← (Finset.mem_filter.mp hi).2]]
    by_contra! h
    obtain ⟨i, -, hi⟩ :=
      Subgroup.exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k) h
    by_cases hfi : (H i.1.1).FiniteIndex <;> simp [K, hfi, hkfi] at hi
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  have hHD (i) : ¬(H i).FiniteIndex → H i ≠ D := fun hfi hD' => (hD' ▸ hfi) hD
  constructor
  · rw [← hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
    refine Set.iUnion_congr fun i => ?_
    rw [Finset.mem_filter, Set.iUnion_and]
    refine Set.iUnion_congr fun hi => ?_
    by_cases hfi : (H i).FiniteIndex <;>
      simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc,
        f, K, hHD, ← (ht i hi _).2, hi, hfi, hkfi]
  have hdensity : ∑ i ∈ s, ((H i).index : ℚ)⁻¹ =
    (Finset.univ.filter (K · = D)).card • (D.index : ℚ)⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun i ↦ (H i).FiniteIndex)]
    convert add_zero _
    · apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter] at hi
      rw [inv_eq_zero, Nat.cast_eq_zero]
      by_contra h'
      apply hi.2
      exact ⟨h'⟩
    · rw [Finset.sum_filter, ← Finset.sum_attach]
      rw [Finset.card_filter, nsmul_eq_mul, Nat.cast_sum,
        Finset.sum_mul,
        ← Finset.univ_sigma_univ, Finset.sum_sigma,
        Finset.sum_coe_sort_eq_attach]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hfi
      · rw [← Subgroup.relindex_mul_index (hD_le i.2 hfi), Nat.cast_mul,
          -- mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hfi.finiteIndex),
          Subgroup.relindex, ← Subgroup.card_left_transversal (ht i.1 i.2 hfi).1]
        simp only [Finset.univ_eq_attach, hfi, ↓reduceIte, Nat.cast_one, Finset.coe_sort_coe,
          Nat.card_eq_fintype_card, Fintype.card_coe, mul_inv_rev, one_mul, Finset.sum_const,
          Finset.card_attach, ↓reduceDite, nsmul_eq_mul, K]
        rw [← mul_assoc, mul_comm, ← mul_assoc,
          Rat.inv_mul_cancel _ ?_, one_mul]
        simp only [ne_eq, Nat.cast_eq_zero]
        have := Subgroup.card_left_transversal (ht i.1 i.2 hfi).1
        simp only [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe] at this
        rw [this]
        exact (instFiniteIndex_subgroupOf D (H ↑i)).finiteIndex
      · simp [K, hfi, hkfi, hHD]

  rw [hdensity]
  constructor
  · rw [nsmul_eq_mul]
    refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD.finiteIndex))
    rw [one_mul, mul_assoc, Rat.inv_mul_cancel _ ?_, mul_one]
    simp only [Nat.cast_le]
    exact Subgroup.index_le_of_leftCoset_cover_const hcovers'
    · simp only [ne_eq, Nat.cast_eq_zero]
      exact hD.finiteIndex
  · rw [nsmul_eq_mul, mul_inv_eq_one₀ ?_]
    simp only [Nat.cast_inj, Finset.coe_filter]
    · intro h
      intro i hi j hj hij
      simp only [Set.mem_setOf_eq] at hi hj
      have := Subgroup.pairwiseDisjoint_leftCoset_cover_const_of_index_eq
        hcovers' h.symm
      intro c hi' hj' x hx
      simp only [Set.le_eq_subset] at hi' hj'
      replace hi' := hi' hx
      replace hj' := hj' hx
      rw [← (ht i hi.1 hi.2).2] at hi'
      rw [← (ht j hj.1 hj.2).2] at hj'
--      have := Subgroup.mem_leftTransversals_iff_existsUnique_inv_mul_mem.mp (ht i hi.1 hi.2).1
      simp only [Set.mem_iUnion, exists_prop, Subtype.exists, exists_and_right] at hi' hj'
      obtain ⟨s, ⟨hs, hxs⟩, hx⟩ := hi'
      obtain ⟨r, ⟨hr, hxr⟩, hx'⟩ := hj'
      unfold Set.PairwiseDisjoint at this
      unfold Set.Pairwise at this
      unfold Disjoint at this
      let i' : κ := ⟨⟨i, hi.1⟩, ⟨⟨s, hs⟩, ?_⟩⟩
      let j' : κ := ⟨⟨j, hj.1⟩, ⟨⟨r, hr⟩, ?_⟩⟩
      replace this := this (x :=i') (y := j') ?_ ?_ ?_
      replace this := this (x := {x})
      simp only [Set.le_eq_subset, Set.singleton_subset_iff] at this
      apply this






      sorry
      sorry
      sorry
      sorry
      sorry
      sorry
      sorry
    · simpa only [ne_eq, Nat.cast_eq_zero] using hD.finiteIndex

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
@[to_additive]
theorem Subgroup.leftCoset_cover_filter_FiniteIndex
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)] :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ :=
  (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`. Then the
sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
@[to_additive one_le_sum_inv_index_of_leftCoset_cover]
theorem Subgroup.one_le_sum_inv_index_of_leftCoset_cover :
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ :=
  have := Classical.decPred (Subgroup.FiniteIndex : Subgroup G → Prop)
  (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).2

/-- B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
@[to_additive]
theorem Subgroup.exists_index_le_card_of_leftCoset_cover :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
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
