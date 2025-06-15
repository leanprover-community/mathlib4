/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Lemma of B. H. Neumann on coverings of a group by cosets.

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$: $$ G = ⋃_{i = 1}^n C_i g_i. $$

* `Subgroup.exists_finiteIndex_of_leftCoset_cover`
  at least one subgroup $C_i$ has finite index in $G$.

* `Subgroup.leftCoset_cover_filter_FiniteIndex`
  the cosets of subgroups of infinite index may be omitted from the covering.

* `Subgroup.exists_index_le_card_of_leftCoset_cover` :
  the index of (at least) one of these subgroups does not exceed $n$.

* `Subgroup.one_le_sum_inv_index_of_leftCoset_cover` :
  the sum of the inverses of the indexes of the $C_i$ is greater than or equal to 1.

* `Subgroup.pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one`
  If the sum of the inverses of the indexes of the subgroups $C_i$ is equal to 1,
  then the cosets of the subgroups of finite index are pairwise disjoint.

A corollary of `Subgroup.exists_finiteIndex_of_leftCoset_cover` is:

* `Subspace.biUnion_ne_univ_of_ne_top` :
  a vector space over an infinite field cannot be a finite union of proper subspaces.

This can be used to show that an algebraic extension of fields is determined by the
set of all minimal polynomials (not proved here).

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

section leftCoset_cover_const

@[to_additive]
theorem exists_leftTransversal_of_FiniteIndex
    {D H : Subgroup G} [D.FiniteIndex] (hD_le_H : D ≤ H) :
    ∃ t : Finset H,
      IsComplement (t : Set H) (D.subgroupOf H) ∧
        ⋃ g ∈ t, (g : G) • (D : Set G) = H := by
  have ⟨t, ht⟩ := (D.subgroupOf H).exists_isComplement_left 1
  have hf : t.Finite := ht.1.finite_left_iff.mpr inferInstance
  refine ⟨hf.toFinset, hf.coe_toFinset.symm ▸ ht.1, ?_⟩
  ext x
  suffices (∃ y ∈ t, ∃ d ∈ D, y * d = x) ↔ x ∈ H by simpa using this
  constructor
  · rintro ⟨⟨y, hy⟩, -, d, h, rfl⟩
    exact H.mul_mem hy (hD_le_H h)
  · intro hx
    exact ⟨_, (ht.1.toLeftFun ⟨x, hx⟩).2, _,
      ht.1.inv_toLeftFun_mul_mem ⟨x, hx⟩, mul_inv_cancel_left _ _⟩

variable {ι : Type*} {s : Finset ι} {H : Subgroup G} {g : ι → G}

@[to_additive]
theorem leftCoset_cover_const_iff_surjOn :
    ⋃ i ∈ s, g i • (H : Set G) = Set.univ ↔ Set.SurjOn (g · : ι → G ⧸ H) s Set.univ := by
  simp [Set.eq_univ_iff_forall, mem_leftCoset_iff, Set.SurjOn,
    QuotientGroup.forall_mk, QuotientGroup.eq]

variable (hcovers : ⋃ i ∈ s, g i • (H : Set G) = Set.univ)
include hcovers

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
@[to_additive]
theorem finiteIndex_of_leftCoset_cover_const : H.FiniteIndex := by
  simp_rw [leftCoset_cover_const_iff_surjOn] at hcovers
  have := Set.finite_univ_iff.mp <| Set.Finite.of_surjOn _ hcovers s.finite_toSet
  exact H.finiteIndex_of_finite_quotient

@[to_additive]
theorem index_le_of_leftCoset_cover_const : H.index ≤ s.card := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ s.card.zero_le
  | inr h =>
    rw [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
    exact (Nat.card_le_card_of_surjective _ hcovers).trans_eq (Nat.card_eq_finsetCard _)

@[to_additive]
theorem pairwiseDisjoint_leftCoset_cover_const_of_index_eq (hind : H.index = s.card) :
    Set.PairwiseDisjoint s (g · • (H : Set G)) := by
  have : Fintype (G ⧸ H) := fintypeOfIndexNeZero fun h => by
    rw [hind, Finset.card_eq_zero] at h
    rw [h, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  suffices Function.Bijective (g · : s → G ⧸ H) by
    intro i hi j hj h' c hi' hj' x hx
    specialize hi' hx
    specialize hj' hx
    rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hi' hj'
    rw [ne_eq, ← Subtype.mk.injEq (p := (· ∈ (s : Set ι))) i hi j hj] at h'
    exact h' <| this.injective <| by simp only [hi', hj']
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · rwa [leftCoset_cover_const_iff_surjOn, Set.surjOn_iff_surjective] at hcovers
  · simp only [Fintype.card_coe, ← hind, index_eq_card, Nat.card_eq_fintype_card]

end leftCoset_cover_const

section

variable {ι : Type*} {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (g i) • (H i : Set G) = Set.univ)
include hcovers

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
@[to_additive]
theorem exists_finiteIndex_of_leftCoset_cover_aux [DecidableEq (Subgroup G)]
    (j : ι) (hj : j ∈ s) (hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i ∈ s, H i ≠ H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨n, hn⟩ : ∃ n, n = (s.image H).card := exists_eq
  induction n using Nat.strongRec generalizing ι with
  | ind n ih =>
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i ∈ s, H i = H j → (g i : G ⧸ H i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : ∀ (y : G), y • (H j : Set G) ⊆
        ⋃ i ∈ s.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      simp_rw [Finset.mem_filter, Set.mem_iUnion]
      have ⟨i, hi, hmem⟩ : ∃ i ∈ s, x * (y⁻¹ * z) ∈ g i • (H i : Set G) := by
        simpa using Set.eq_univ_iff_forall.mp hcovers (x * (y⁻¹ * z))
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hmem
      refine ⟨i, ⟨hi, fun hij => hx i hi hij ?_⟩, ?_⟩
      · rwa [hmem, eq_comm, QuotientGroup.eq, hij, inv_mul_cancel_left,
          ← SetLike.mem_coe, ← mem_leftCoset_iff]
      · simpa [mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hmem
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(s.filter (H · ≠ H j)) × Option ↥(s.filter (H · = H j))
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩ => g k₁
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
      rw [Set.iUnion_of_empty] at hcovers
      exact Set.empty_ne_univ hcovers
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcovers' : ⋃ i ∈ Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
      exact ⟨k.1, Finset.mem_of_mem_filter k.1.1 k.1.2, hK k,
        finiteIndex_of_leftCoset_cover_const hcovers'⟩
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
theorem exists_finiteIndex_of_leftCoset_cover : ∃ k ∈ s, (H k).FiniteIndex := by
  classical
  have ⟨j, hj⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty] at hcovers
    exact Set.empty_ne_univ hcovers
  by_cases hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at hcovers'
    exact ⟨j, hj, finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, hi, _, hfi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers j hj hcovers'
    exact ⟨i, hi, hfi⟩

-- Auxiliary to `leftCoset_cover_filter_FiniteIndex` and `one_le_sum_inv_index_of_leftCoset_cover`.
@[to_additive]
theorem leftCoset_cover_filter_FiniteIndex_aux
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    (⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ) ∧
      (1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹) ∧
      (∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 → Set.PairwiseDisjoint
        (s.filter (fun i => (H i).FiniteIndex)) (fun i ↦ g i • (H i : Set G))) := by
  classical
  let D := ⨅ k ∈ s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := finiteIndex_iInf' _ <| by simp
  have hD_le {i} (hi : i ∈ s) (hfi : (H i).FiniteIndex) : D ≤ H i :=
    iInf₂_le i (Finset.mem_filter.mpr ⟨hi, hfi⟩)
  -- Each subgroup of finite index in the covering is the union of finitely many cosets of `D`.
  choose t ht using fun i hi hfi =>
    exists_leftTransversal_of_FiniteIndex (H := H i) (hD_le hi hfi)
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
    have ⟨j, hj, hjfi⟩ := exists_finiteIndex_of_leftCoset_cover hcovers
    have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_coe_sort.mp
      (ht j hj hjfi).1.leftQuotientEquiv.symm.nonempty
    ⟨⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩, hjfi, if_pos hjfi⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' : ⋃ i ∈ Finset.univ.filter (K · = D), f i • (D : Set G) = Set.univ := by
    rw [← hk, Set.iUnion₂_congr fun i hi => by rw [← (Finset.mem_filter.mp hi).2]]
    by_contra! h
    obtain ⟨i, -, hi⟩ :=
      exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k) h
    by_cases hfi : (H i.1.1).FiniteIndex <;> simp [K, hfi, hkfi] at hi
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  have hHD (i) : ¬(H i).FiniteIndex → H i ≠ D := fun hfi hD' => (hD' ▸ hfi) hD
  have hdensity : ∑ i ∈ s, ((H i).index : ℚ)⁻¹ =
      (Finset.univ.filter (K · = D)).card * (D.index : ℚ)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero), Finset.sum_mul,
      ← Finset.sum_attach, eq_comm, Finset.card_filter, Nat.cast_sum, ← Finset.univ_sigma_univ,
      Finset.sum_sigma, Finset.sum_coe_sort_eq_attach]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hfi : (H i).FiniteIndex
    · rw [← relindex_mul_index (hD_le i.2 hfi), Nat.cast_mul, mul_comm,
        mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hfi.index_ne_zero)]
      simpa [K, hfi] using (ht i.1 i.2 hfi).1.card_left
    · rw [of_not_not (FiniteIndex.mk.mt hfi), Nat.cast_zero, inv_zero, zero_mul]
      simpa [K, hfi] using hHD i hfi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
    refine Set.iUnion_congr fun i => ?_
    rw [Finset.mem_filter, Set.iUnion_and]
    refine Set.iUnion_congr fun hi => ?_
    by_cases hfi : (H i).FiniteIndex <;>
      simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc,
        f, K, hHD, ← (ht i hi _).2, hi, hfi, hkfi]
  · rw [hdensity]
    refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD.index_ne_zero))
    rw [one_mul, mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero), mul_one,
      Nat.cast_le]
    exact index_le_of_leftCoset_cover_const hcovers'
  · rw [hdensity, mul_inv_eq_one₀ (Nat.cast_ne_zero.mpr hD.index_ne_zero),
      Nat.cast_inj, Finset.coe_filter]
    intro h i hi j hj hij c hi' hj' x hx
    have hdisjoint := pairwiseDisjoint_leftCoset_cover_const_of_index_eq hcovers' h.symm
    -- We know the `f k • K k` are pairwise disjoint and need to prove that the `g i • H i` are.
    rw [Set.mem_setOf_eq] at hi hj
    have hk' (i) (hi : i ∈ s ∧ (H i).FiniteIndex) (hi' : c ≤ g i • (H i : Set G)) :
        ∃ (k : κ), k.1.1 = i ∧ K k = D ∧ x ∈ f k • (D : Set G) := by
      rw [← (ht i hi.1 hi.2).2] at hi'
      suffices ∃ r : H i, r ∈ t i hi.1 hi.2 ∧ x ∈ (g i * r) • (D : Set G) by
        have ⟨r, hr, hxr⟩ := this
        refine ⟨⟨⟨i, hi.1⟩, ⟨r, dif_pos hi.2 ▸ hr⟩⟩, rfl, ?_⟩
        simpa [K, f, if_pos hi.2] using hxr
      simpa [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_assoc] using hi' hx
    have ⟨k₁, hik₁, hk₁, hxk₁⟩ := hk' i hi hi'
    have ⟨k₂, hjk₂, hk₂, hxk₂⟩ := hk' j hj hj'
    rw [← Set.singleton_subset_iff, ← Set.le_iff_subset] at hxk₁ hxk₂ ⊢
    exact hdisjoint
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₁, hk₁⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k₂, hk₂⟩)
      (ne_of_apply_ne Sigma.fst (ne_of_apply_ne Subtype.val (hik₁ ▸ hjk₂ ▸ hij)))
      hxk₁ hxk₂

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
@[to_additive]
theorem leftCoset_cover_filter_FiniteIndex
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`. Then the
sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
@[to_additive one_le_sum_inv_index_of_leftCoset_cover]
theorem one_le_sum_inv_index_of_leftCoset_cover :
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ :=
  have := Classical.decPred (FiniteIndex : Subgroup G → Prop)
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
If the sum of the inverses of the indexes of the subgroups `H i` is equal to 1,
then the cosets of the subgroups of finite index are pairwise disjoint. -/
@[to_additive]
theorem pairwiseDisjoint_leftCoset_cover_of_sum_inv_index_eq_one
    [DecidablePred (FiniteIndex : Subgroup G → Prop)] :
    ∑ i ∈ s, ((H i).index : ℚ)⁻¹ = 1 →
      Set.PairwiseDisjoint (s.filter (fun i => (H i).FiniteIndex))
        (fun i ↦ g i • (H i : Set G)) :=
  (leftCoset_cover_filter_FiniteIndex_aux hcovers).2.2

/-- B. H. Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
@[to_additive]
theorem exists_index_le_card_of_leftCoset_cover :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
  by_contra! h
  apply (one_le_sum_inv_index_of_leftCoset_cover hcovers).not_gt
  cases s.eq_empty_or_nonempty with
  | inl hs => simp only [hs, Finset.sum_empty, zero_lt_one]
  | inr hs =>
  have hs' : 0 < s.card := hs.card_pos
  have hlt : ∀ i ∈ s, ((H i).index : ℚ)⁻¹ < (s.card : ℚ)⁻¹ := fun i hi ↦ by
    cases eq_or_ne (H i).index 0 with
    | inl hindex =>
      rwa [hindex, Nat.cast_zero, inv_zero, inv_pos, Nat.cast_pos]
    | inr hindex =>
      exact inv_strictAnti₀ (by exact_mod_cast hs') (by exact_mod_cast h i hi ⟨hindex⟩)
  apply (Finset.sum_lt_sum_of_nonempty hs hlt).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hs'.ne')]

end

end Subgroup

section Submodule

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : ι → Submodule R M} {s : Finset ι}

theorem Submodule.exists_finiteIndex_of_cover (hcovers : ⋃ i ∈ s, (p i : Set M) = Set.univ) :
    ∃ k ∈ s, (p k).toAddSubgroup.FiniteIndex :=
  have hcovers' : ⋃ i ∈ s, (0 : M) +ᵥ ((p i).toAddSubgroup : Set M) = Set.univ := by
    simpa only [zero_vadd] using hcovers
  AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcovers'

end Submodule

section Subspace

variable {k E : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E]
    {s : Finset (Subspace k E)}

/- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
theorem Subspace.biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) :
    ⋃ p ∈ s, (p : Set E) ≠ Set.univ := by
  intro hcovers
  have ⟨p, hp, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcovers
  have : Finite (E ⧸ p) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (E ⧸ p) :=
    Submodule.Quotient.nontrivial_of_lt_top p (ne_of_mem_of_not_mem hp hs).lt_top
  have : Infinite (E ⧸ p) := Module.Free.infinite k (E ⧸ p)
  exact not_finite (E ⧸ p)

@[deprecated (since := "2025-05-24")]
alias Subspace.biUnion_ne_univ_of_top_nmem := Subspace.biUnion_ne_univ_of_top_notMem

/- A vector space over an infinite field cannot be a finite union of proper subspaces. -/
theorem Subspace.top_mem_of_biUnion_eq_univ (hcovers : ⋃ p ∈ s, (p : Set E) = Set.univ) :
    ⊤ ∈ s := by
  contrapose! hcovers
  exact Subspace.biUnion_ne_univ_of_top_notMem hcovers

@[deprecated (since := "2024-10-29")]
alias Subspace.biUnion_ne_univ_of_ne_top := Subspace.biUnion_ne_univ_of_top_notMem
@[deprecated (since := "2024-10-29")]
alias Subspace.exists_eq_top_of_biUnion_eq_univ := Subspace.top_mem_of_biUnion_eq_univ

theorem Subspace.exists_eq_top_of_iUnion_eq_univ {ι} [Finite ι] {p : ι → Subspace k E}
    (hcovers : ⋃ i, (p i : Set E) = Set.univ) : ∃ i, p i = ⊤ := by
  have := Fintype.ofFinite (Set.range p)
  simp_rw [← Set.biUnion_range (f := p), ← Set.mem_toFinset] at hcovers
  apply Set.mem_toFinset.mp (Subspace.top_mem_of_biUnion_eq_univ hcovers)

end Subspace
