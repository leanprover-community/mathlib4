/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index


/-! # B. H. Neumann's theorem on coverings of a group by cosets

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$: $$ G = ⋃_{i = 1}^n C_i g_i. $$

* `Subgroup.one_le_sum_inv_index_of_leftCoset_cover` :
  the sum of the inverses of the indexes of the $C_i$ is greater than or equal to $1$.

* `Subgroup.exists_index_le_card_of_leftCoset_cover` :
  the index of (at least) one of these subgroups does not exceed $n$.

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

The result is also needed to show an algebraic extension of fields is
determined by the set of all minimal polynomials.

-/

open scoped Pointwise BigOperators

section leftCoset_cover_const

variable {G : Type*} [Group G]

theorem Subgroup.leftCoset_cover_const_iff_FiniteIndex {H : Subgroup G} :
    (∃ (s : Finset G), ⋃ g ∈ s, (g : G) • (H : Set G) = Set.univ) ↔ H.FiniteIndex := by
  classical
  constructor
  · intro ⟨s, h⟩
    rw [Set.iUnion_eq_univ_iff] at h
    have := Finite.of_surjective ((↑) : s → G ⧸ H) fun x =>
      QuotientGroup.induction_on x fun g => by
        simpa [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] using h g
    exact H.finiteIndex_of_finite_quotient
  · intro
    have : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
    exists Finset.univ.image (Quotient.out' : G ⧸ H → G)
    rw [← Set.univ_subset_iff]
    rintro x -
    suffices x ∈ (x : G ⧸ H).out' • (H : Set G) by simpa using ⟨(x : G ⧸ H), this⟩
    rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq]
    exact QuotientGroup.out_eq' _

theorem Subgroup.leftCoset_cover_const_of_FiniteIndex (H : Subgroup G) [H.FiniteIndex] :
    ∃ (s : Finset G), ⋃ g ∈ s, (g : G) • (H : Set G) = Set.univ :=
  Subgroup.leftCoset_cover_const_iff_FiniteIndex.mpr ‹_›

theorem Subgroup.leftCoset_cover_const_of_le_of_FiniteIndex
    {H K : Subgroup G} [H.FiniteIndex] (hle : H ≤ K) :
    ∃ s : Finset G, ⋃ g ∈ s, g • (H : Set G) = K := by
  classical
  have ⟨s, h⟩ := Subgroup.leftCoset_cover_const_of_FiniteIndex (H.subgroupOf K)
  refine ⟨s.map ⟨_, Subtype.val_injective⟩, ?_⟩
  rw [Finset.map_eq_image, Finset.set_biUnion_finset_image, Function.Embedding.coeFn_mk,
    ← Subtype.coe_image_univ (K : Set G), ← h, Set.image_iUnion₂]
  refine Set.iUnion₂_congr fun x hx => ?_
  rw [Set.image_smul_comm _ _ _ (fun k => by rw [mk_smul, smul_eq_mul, smul_eq_mul, coe_mul]),
    Subgroup.coe_subgroupOf, Subgroup.coeSubtype, Subtype.image_preimage_val,
    Set.inter_eq_self_of_subset_right hle.subset, Subgroup.smul_def]

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
theorem Subgroup.finiteIndex_of_leftCoset_cover_const {ι : Type*} [Fintype ι]
    {H : Subgroup G} {g : ι → G} (h : ⋃ i, g i • (H : Set G) = Set.univ) :
    H.FiniteIndex := by
  classical
  refine Subgroup.leftCoset_cover_const_iff_FiniteIndex.mp ⟨Finset.univ.image g, ?_⟩
  simpa [Set.iUnion_subtype] using h

theorem Subgroup.index_le_of_leftCoset_cover_const {ι : Type*}
    (H : Subgroup G) (g : ι → G) (s : Finset ι)
    (hcovers : ⋃ i ∈ s, (g i) • (H : Set G) = Set.univ) :
    H.index ≤ s.card := by
  cases H.index.eq_zero_or_pos with
  | inl h => exact h ▸ Nat.zero_le s.card
  | inr h =>
    classical
    have : Fintype (G ⧸ H) :=
      have : Finite (G ⧸ H) := And.right <| by
        rwa [← Nat.card_pos_iff, ← Subgroup.index]
      Fintype.ofFinite _
    have hsurj : s.image (((↑) : G → G ⧸ H) ∘ g) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro x
      induction' x using QuotientGroup.induction_on with x
      have : ∃ i ∈ s, x ∈ (g i) • (H : Set G) := by
        simpa [← hcovers, Set.mem_iUnion, exists_prop] using Set.mem_univ x
      obtain ⟨i, hi, ⟨h, hmem, rfl⟩⟩ := this
      refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
      simpa only [Function.comp_apply, QuotientGroup.eq', smul_eq_mul, inv_mul_cancel_left]
        using hmem
    refine le_of_eq_of_le ?_ (Finset.card_image_le (f := ((↑) : G → G ⧸ H) ∘ g))
    rw [Subgroup.index, ← Fintype.card_eq_nat_card, ← Finset.card_univ, hsurj]

end leftCoset_cover_const

variable {G : Type*} [Group G]
    [DecidableEq (Subgroup G)]
    [DecidablePred (Subgroup.FiniteIndex : Subgroup G → Prop)]
    {ι : Type*} {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, (g i) • (H i : Set G) = Set.univ)

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover_aux
    (j : ι) (hj : j ∈ s)
    (hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i ∈ s, H i ≠ H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨t, hH⟩ : ∃ t, t = s.image H := ⟨_, rfl⟩
  have ⟨n, hn⟩ : ∃ n, t.card ≤ n + 1 := ⟨t.card - 1, by rw [← Nat.sub_le_iff_le_add]⟩
  induction n generalizing ι t with
  | zero =>
    replace hH {i} (hi : i ∈ s) : H i ∈ t := hH ▸ Finset.mem_image_of_mem H hi
    have : Subsingleton { x // x ∈ t } := Finset.card_le_one_iff_subsingleton_coe.mp hn
    have {i} (hi) : H i = H j :=
      Subtype.ext_iff.mp <| Subsingleton.elim (⟨H i, hH hi⟩ : { x // x ∈ t }) ⟨H j, hH hj⟩
    refine (hcovers' ?_).elim
    simpa [and_iff_left_of_imp this] using hcovers
  | succ n ih =>
    replace hH {i} (hi : i ∈ s) : H i ∈ t := hH ▸ Finset.mem_image_of_mem H hi
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i ∈ s, H i = H j → (g i : G ⧸ H i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, mem_leftCoset_iff, ← QuotientGroup.eq] using hcovers'
    replace hx : ∀ (y : G), y • (H j : Set G) ⊆
        ⋃ i ∈ s.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      suffices ∃ i, (i ∈ s ∧ H i ≠ H j) ∧ z ∈ (y * x⁻¹ * g i) • (H i : Set G) by simpa using this
      have ⟨i, hi, hmem⟩ : ∃ i ∈ s, x * (y⁻¹ * z) ∈ g i • (H i : Set G) :=
        by simpa using Set.eq_univ_iff_forall.mp hcovers (x * (y⁻¹ * z))
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hmem
      refine ⟨i, ⟨hi, fun hij => hx i hi hij ?_⟩, ?_⟩
      · rwa [hmem, QuotientGroup.eq, hij, mul_inv_rev, inv_mul_cancel_right,
          Subgroup.inv_mem_iff, ← SetLike.mem_coe, ← mem_leftCoset_iff]
      · simpa [mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hmem
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(s.filter (H · ≠ H j)) × Option ↥(s.filter (H · = H j))
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩  => g k₁
    let K (k : κ) : Subgroup G := H k.1.val
    have hK' (k : κ) : K k ∈ t.erase (H j) := by
      have := Finset.mem_filter.mp k.1.property
      exact Finset.mem_erase.mpr ⟨this.2, hH this.1⟩
    have hK (k : κ) : K k ≠ H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    replace hcovers : ⋃ k ∈ Finset.univ, f k • (K k : Set G) = Set.univ :=
        Set.iUnion₂_eq_univ_iff.mpr fun y => by
      rw [← s.filter_union_filter_neg_eq (H · = H j), Finset.set_biUnion_union] at hcovers
      cases (Set.mem_union _ _ _).mp (hcovers.symm.subset (Set.mem_univ y)) with
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
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right],
        ← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion] at hcovers'
      exact ⟨k.1, Finset.mem_of_mem_filter k.1.1 k.1.2, hK k,
        Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn : (Finset.univ.image K).card ≤ n + 1 := by
      trans (t.erase (H j)).card
      · refine Finset.card_le_card fun x => ?_
        rw [mem_image_univ_iff_mem_range, Set.mem_range]
        exact fun ⟨k, hk⟩ => hk ▸ hK' k
      · rwa [Finset.card_erase_of_mem (hH hj), Nat.sub_le_iff_le_add]
    have ⟨k', hk'⟩ := ih hcovers k (Finset.mem_univ k) hcovers' _ rfl hn
    exact ⟨k'.1.1, Finset.mem_of_mem_filter k'.1.1 k'.1.2, hK k', hk'.2.2⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover :
    ∃ k ∈ s, (H k).FiniteIndex := by
  classical
  have ⟨j, hj⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty,
      eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hcovers
    exact hcovers 1
  by_cases hcovers' : ⋃ i ∈ s.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right],
      ← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion] at hcovers'
    refine ⟨j, hj, Subgroup.finiteIndex_of_leftCoset_cover_const hcovers'⟩
  · have ⟨i, hi, _, hfi⟩ :=
      Subgroup.exists_finiteIndex_of_leftCoset_cover_aux hcovers j hj hcovers'
    exact ⟨i, hi, hfi⟩

theorem Subgroup.exists_finite_leftTransversal
    {D H : Subgroup G} (hD : D.FiniteIndex) (hD_le_H : D ≤ H) :
    ∃ t : Finset H,
      (t : Set H) ∈ Subgroup.leftTransversals (D.subgroupOf H) ∧
        ⋃ g ∈ t, (g : G) • (D : Set G) = H := by
  obtain ⟨t, ht⟩ := Subgroup.exists_left_transversal (D.subgroupOf H) 1
  have hf : Set.Finite t := by
    change Finite t
    rw [Subgroup.MemLeftTransversals.finite_iff ht.1]
    exact instFiniteIndex_subgroupOf D H
  refine ⟨hf.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact ht.1
  · ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop,
      Subtype.exists, exists_and_right, SetLike.mem_coe]
    constructor
    · rintro ⟨y, ⟨hy, hy'⟩, h⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at h
      rw [← mul_inv_cancel_left y x]
      exact Subgroup.mul_mem H hy (hD_le_H h)
    · intro hx
      rw [Subgroup.mem_leftTransversals_iff_existsUnique_inv_mul_mem] at ht
      obtain ⟨y, hy⟩ := ht.1 ⟨x, hx⟩
      exact ⟨y, ⟨SetLike.coe_mem _, Subtype.coe_prop y⟩,
        Set.mem_smul_set_iff_inv_smul_mem.mpr hy.1⟩

-- Auxiliary to leftCoset_cover_filter_FiniteIndex and one_le_sum_inv_index_of_leftCoset_cover.
theorem Subgroup.leftCoset_cover_filter_FiniteIndex_aux :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ ∧
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ := by
  classical
  let D := ⨅ k ∈ s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf'
    simp only [Finset.mem_filter, and_imp, imp_self, implies_true]
  -- Each subgroup of finite index in the covering is union of finitely many of cosets of `D`.
  have hD_le {i} (hi : i ∈ s) (hfi : (H i).FiniteIndex) : D ≤ H i :=
    iInf₂_le i (Finset.mem_filter.mpr ⟨hi, hfi⟩)
  have (i) (hi : i ∈ s) (hfi : (H i).FiniteIndex) :
      ∃ t : Finset (H i),
        (t : Set (H i)) ∈ Subgroup.leftTransversals (D.subgroupOf (H i)) ∧
          ⋃ g ∈ t, (g : G) • (D : Set G) = H i :=
    Subgroup.exists_finite_leftTransversal hD (hD_le  hi hfi)
  choose t ht using this
  -- We construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : s) × { x // x ∈ (if h : (H i.1).FiniteIndex then t i.1 i.2 h else {1}) }
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
  have ⟨j, hj, hjfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcovers
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    specialize ht j hj hjfi
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty, eq_comm,
      Set.eq_empty_iff_forall_not_mem] at ht
    exact ht.2 1 <| SetLike.mem_coe.mpr (Subgroup.one_mem (H j))
  let k : κ := ⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  have hKD : K k = D := by simp [K, hjfi]
  replace hcovers' :
      ⋃ i ∈ Finset.univ.filter (fun x ↦ K x = K k), f i • (D : Set G) = Set.univ := by
    rw [← hKD, Set.iUnion₂_congr fun i hi => by rw [← (Finset.mem_filter.mp hi).2]]
    by_contra! h
    obtain ⟨i, -, hi⟩ :=
       Subgroup.exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k) h
    by_cases hfi : (H i.1.1).FiniteIndex <;> simp [K, hfi, hjfi] at hi
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  have hHD (i) : ¬(H i).FiniteIndex → H i ≠ D := fun h hD' => (hD' ▸ h) hD
  constructor
  · rw [← hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
    refine Set.iUnion_congr fun i => ?_
    rw [Finset.mem_filter, Set.iUnion_and]
    refine Set.iUnion_congr fun hi => ?_
    by_cases hfi : (H i).FiniteIndex <;>
      simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc,
        f, K, hHD, ← fun i hi hfi => (ht i hi hfi).2, hi, hfi, hjfi]
  · rw [← Finset.sum_filter_add_sum_filter_not _ (fun i ↦ (H i).FiniteIndex)]
    refine le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg (fun i _ ↦ by simp))
    refine le_of_mul_le_mul_left (a := (D.index : ℚ)) ?_
       (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD.finiteIndex))
    rw [mul_one]
    apply (Nat.cast_le.mpr (Subgroup.index_le_of_leftCoset_cover_const D f _ hcovers')).trans
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.univ_sigma_univ, Finset.sum_sigma,
      Finset.sum_coe_sort_eq_attach, Finset.mul_sum, Finset.sum_filter, ← s.sum_attach]
    refine (Finset.sum_congr rfl fun ⟨i, hi⟩ _ => ?_).le
    split_ifs with hfi
    · rw [← Subgroup.relindex_mul_index (hD_le hi hfi), Nat.cast_mul,
        mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hfi.finiteIndex),
        Subgroup.relindex, ← Subgroup.card_left_transversal (ht i hi hfi).1]
      simp [K, hfi, hjfi]
    · simp [K, hfi, hjfi, hHD]

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
theorem Subgroup.leftCoset_cover_filter_FiniteIndex :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ :=
  (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).1

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the sum of the inverses of the indexes of the subgroups `H i` is greater than or equal to 1. -/
theorem Subgroup.one_le_sum_inv_index_of_leftCoset_cover :
    1 ≤ ∑ i ∈ s, ((H i).index : ℚ)⁻¹ :=
  (Subgroup.leftCoset_cover_filter_FiniteIndex_aux hcovers).2

/-- BH Neumann Lemma :
If a finite family of cosets of subgroups covers the group, then at least one
of these subgroups has index not exceeding the number of cosets. -/
theorem Subgroup.exists_index_le_card_of_leftCoset_cover :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
  by_contra! h
  apply not_lt.mpr (one_le_sum_inv_index_of_leftCoset_cover hcovers)
  by_cases hs : s = ∅
  · simp only [hs, Finset.sum_empty, zero_lt_one]
  rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hs
  have hs' : 0 < s.card := Nat.zero_lt_of_ne_zero (Finset.card_ne_zero.mpr hs)
  have hlt : ∀ i ∈ s, ((H i).index : ℚ)⁻¹ < (s.card : ℚ)⁻¹ := fun i hi ↦ by
    cases (H i).index.eq_zero_or_pos with
    | inl hindex =>
      rwa [hindex, CharP.cast_eq_zero, inv_zero, inv_pos, Nat.cast_pos]
    | inr hindex =>
      apply inv_strictAntiOn
      · simpa only [Set.mem_Ioi, Nat.cast_pos] using hs'
      · simpa only [Set.mem_Ioi, Nat.cast_pos] using hindex
      · simpa only [Nat.cast_lt] using h i hi ⟨hindex.ne.symm⟩
  apply (Finset.sum_lt_sum_of_nonempty hs hlt).trans_eq
  rw [Finset.sum_const, nsmul_eq_mul,
    mul_inv_eq_iff_eq_mul₀ (Nat.cast_ne_zero.mpr hs'.ne.symm), one_mul]
