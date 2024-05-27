/-
Copyright (c) 2024 Antoine Chambert-Loir, Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Richard Copley
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index


/-! # B. H. Neumann's theorem on coverings of a group by cosets

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$: $$ G = ⋃_{i = 1}^n C_i g_i. $$

* `GroupTheory.BHNeumann` : the sum of the inverse of the indexes of the $C_i$ is greater than or equal to $1$.

* `GroupTheory.BHNeumann'` : the index of (at least) one of these subgroups does not exceed $n$.

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

The result is also needed to show an algebraic extension of fields is
determined by the set of all minimal polynomials.

-/

open scoped Pointwise

section Mathlib.GroupTheory.Index

variable {G : Type*} [Group G]

/-/
theorem Fintype.finiteIndex_iInf {ι : Type*} [Fintype ι]
    (a : ι → Subgroup G) (ha : ∀ i, (a i).FiniteIndex) :
    (⨅ i, a i).FiniteIndex :=
  ⟨Subgroup.index_iInf_ne_zero fun i => (ha i).finiteIndex⟩

theorem Finset.finiteIndex_iInf {ι : Type*}
    {s : Finset ι} (f : ι → Subgroup G) (hs : ∀ i ∈ s, (f i).FiniteIndex) :
      (⨅ i ∈ s, f i).FiniteIndex := by
  rw [iInf_subtype']
  exact Fintype.finiteIndex_iInf _ fun ⟨i, hi⟩ => hs i hi
-/

/-
instance Subgroup.instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
  ⟨fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relindex_eq_zero h⟩
-/

end Mathlib.GroupTheory.Index

open scoped Pointwise

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

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
theorem Subgroup.leftCoset_cover_filter_FiniteIndex :
    ⋃ k ∈ s.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ := by
  classical
  let D := ⨅ k ∈ s.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf'
    simp only [Finset.mem_filter, and_imp, imp_self, implies_true]
  -- Each subgroup of finite index in the covering is the finite union of cosets of `D`.
  have (i) (hi : i ∈ s) (hf : (H i).FiniteIndex) :
      ∃ t : Finset G, ⋃ g ∈ t, g • (D : Set G) = H i :=
    Subgroup.leftCoset_cover_const_of_le_of_FiniteIndex <| iInf₂_le _ <| by
      rw [Finset.mem_filter]
      exact ⟨hi, hf⟩
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
    · by_cases hi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  have ⟨j, hj, hjfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcovers
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨x, hx⟩ : (t j hj hjfi).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    specialize ht j hj hjfi
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty, eq_comm,
      Set.eq_empty_iff_forall_not_mem] at ht
    exact ht 1 <| SetLike.mem_coe.mpr (Subgroup.one_mem (H j))
  let k : κ := ⟨⟨j, hj⟩, ⟨x, dif_pos hjfi ▸ hx⟩⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' :=
    (Subgroup.exists_finiteIndex_of_leftCoset_cover_aux hcovers' k (Finset.mem_univ k)).mt
  rw [not_exists] at hcovers'
  specialize hcovers' fun ⟨i', ⟨j', hj'⟩⟩ => by
    dsimp only [K]
    rw [if_pos hjfi]
    split_ifs with h
    · exact fun habsurd => habsurd.2.1 rfl
    · exact fun habsurd => h habsurd.2.2
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  rw [← not_ne_iff.mp hcovers', Set.iUnion_sigma, Set.iUnion_subtype]
  refine Set.iUnion_congr fun i => ?_
  rw [Finset.mem_filter, Set.iUnion_and]
  refine Set.iUnion_congr fun hi => ?_
  have hD' : ¬(H i).FiniteIndex → H i ≠ D := fun h hD' => (hD' ▸ h) hD
  by_cases hfi : (H i).FiniteIndex <;>
    simp [Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc,
      f, K, hD', ← ht, hi, hfi, hj, hjfi]

theorem BHNeumann_of_subgroup (H : Subgroup G) (g : ι → G)
    (covers : ⋃ i ∈ s, (g i) • (H : Set G) = ⊤) :
    H.index ≤ s.card := by
  cases (H.index).eq_zero_or_pos with
  | inl h => exact h ▸ Nat.zero_le s.card
  | inr h =>
    classical
    haveI : Finite (G ⧸ H) := by
      change 0 < Nat.card (G ⧸ H) at h
      rw [Nat.card_pos_iff] at h
      exact h.2
    apply le_trans (le_of_eq _) (Finset.card_image_le (f := QuotientGroup.mk (s := H) ∘ g))
    rw [Subgroup.index, ← Set.ncard_univ, ← Set.ncard_coe_Finset]
    apply congr_arg
    simp only [Finset.coe_image, Function.comp_apply]
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro x _
      induction' x using QuotientGroup.induction_on with x
      have : ∃ i ∈ s, x ∈ (g i) • (H : Set G) := by
        simpa [← Set.top_eq_univ, ← covers, Set.mem_iUnion, exists_prop] using Set.mem_univ x
      obtain ⟨i, hi, ⟨h, hmem, rfl⟩⟩ := this
      use i, hi
      simpa only [Function.comp_apply, QuotientGroup.eq', smul_eq_mul, inv_mul_cancel_left]
        using hmem
    · apply Set.ncard_mono
      simp only [Set.le_eq_subset, Set.subset_univ]

/-- BH Neumann Lemma :
  If a finite family of cosets of subgroup covers the group, then
  the sum of the inverses of the indexes of these cosets is at least 1 -/
theorem BHNeumann :
    (1 : ℚ) ≤ s.sum (fun i ↦ ((H i).index : ℚ)⁻¹) := by
  classical
  have hcovers' := Subgroup.leftCoset_cover_filter_FiniteIndex hcovers
  rw [← Finset.sum_filter_add_sum_filter_not s (p := fun i ↦ (H i).FiniteIndex)]
  set s' := s.filter (fun i ↦ (H i).FiniteIndex)
  apply le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg (fun i _ ↦ by simp))
  let K := ⨅ i ∈ s', (H i)
  have hK : K.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf'
    simp? [s']
  have hK_le : ∀ i ∈  s', K ≤ H i := iInf₂_le
  let S := fun i ↦ (Subgroup.exists_left_transversal (K.subgroupOf (H i)) 1).choose
  have hS : ∀ i, S i ∈ Subgroup.leftTransversals (K.subgroupOf (H i)) :=
    fun i ↦ (Subgroup.exists_left_transversal (K.subgroupOf (H i)) 1).choose_spec.1
  have hSf : ∀ i (_ : i ∈ s'), (S i).Finite := fun i hi ↦ by
    apply Nat.finite_of_card_ne_zero
    rw [Subgroup.card_left_transversal (hS i),
      Subgroup.subgroupOf, Subgroup.index_comap, Subgroup.subtype_range]
    intro h
    apply hK.finiteIndex
    rw [← Subgroup.relindex_mul_index (hK_le i hi), h, zero_mul]
  let κ := Σ (i : s'), (hSf i.val i.prop).toFinset
  let f : κ → G := fun ⟨i, x⟩ ↦ g i * x
  have hcovers'' : ⋃ i ∈ Finset.univ, (f i) • (K : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x
    rw [Set.top_eq_univ, ← hcovers']
    suffices ∀ x_1 ∈ Finset.filter (fun i ↦ (H i).FiniteIndex) s,
        x ∈ g x_1 • (H x_1 : Set G) → ∃ i, x ∈ f i • (K : Set G) by
      simpa only [Set.mem_iUnion, exists_prop, Finset.mem_univ, Set.iUnion_true,
        forall_exists_index, and_imp] using this
    intro i hi hx
    rw [mem_leftCoset_iff] at hx
    let z := Subgroup.MemLeftTransversals.toFun (hS i) ⟨_, hx⟩
    use ⟨⟨i, hi⟩, ⟨z, by
      simp only [Set.Finite.mem_toFinset, Subtype.coe_prop]⟩⟩
    simpa [mul_smul, mem_leftCoset_iff, Set.mem_smul_set_iff_inv_smul_mem, f, z] using
      Subgroup.MemLeftTransversals.inv_toFun_mul_mem (hS i) ⟨_, hx⟩

  have := BHNeumann_of_subgroup K f hcovers''
  simp only [Finset.card_univ, Set.Finite.mem_toFinset, Fintype.card_sigma, Finset.univ_eq_attach,
    Fintype.card_coe, κ] at this
  rw [← Nat.cast_le (α := ℚ), Nat.cast_sum] at this
  rw [← Finset.sum_attach]
  apply le_of_mul_le_mul_left (a := (K.index : ℚ))
  rw [mul_one, Finset.mul_sum]
  apply le_trans this
  apply le_of_eq
  apply Finset.sum_congr rfl
  rintro ⟨i, hi⟩ _
  rw [← div_eq_mul_inv, eq_div_iff ?_]
  haveI : Finite (S i) := hSf i hi
  simp only [← Nat.cast_mul, Nat.cast_inj]
  rw [← Set.ncard_eq_toFinset_card (S i),
    ← Subgroup.relindex_mul_index (hK_le i hi)]
  apply congr_arg₂ _ _ rfl
  · rw [← Set.Nat.card_coe_set_eq, Subgroup.card_left_transversal (hS i)]
    rw [← Subgroup.comap_subtype, Subgroup.index_comap, Subgroup.subtype_range]
  · rw [← Nat.cast_zero, Function.Injective.ne_iff Nat.cast_injective]
    simp only [Finset.mem_filter, s'] at hi
    exact hi.2.finiteIndex
  · rw [← Nat.cast_zero, Nat.cast_lt]
    exact Nat.zero_lt_of_ne_zero hK.finiteIndex

/-- BH Neumann Lemma :
  If a finite family of cosets of subgroups covers the group, then
  at least one of these subgroups has index less than the number of cosets -/
theorem BHNeumann' :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
  by_contra h
  push_neg at h
  apply not_lt.mpr (BHNeumann hcovers)
  by_cases hs : s = ∅
  · simp only [hs, Finset.sum_empty, zero_lt_one]
  rw [← Finset.not_nonempty_iff_eq_empty, not_not] at hs
  have hs' : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hlt : ∀ i ∈ s, ((H i).index : ℚ)⁻¹ < (s.card : ℚ)⁻¹ := fun i hi ↦ by
    by_cases hind : (H i).index = 0
    · rw [hind, CharP.cast_eq_zero, inv_zero, inv_pos, Nat.cast_pos]
      exact Nat.zero_lt_of_ne_zero hs'
    · apply inv_strictAntiOn
      · simp only [Set.mem_Ioi, Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hs'
      · simp only [Set.mem_Ioi, Nat.cast_pos]; exact Nat.zero_lt_of_ne_zero hind
      · simp only [Nat.cast_lt]; exact h i hi ⟨hind⟩
  convert Finset.sum_lt_sum_of_nonempty hs hlt
  rw [Finset.sum_const, nsmul_eq_mul, eq_comm, mul_inv_eq_iff_eq_mul₀, one_mul]
  simpa only [ne_eq, Nat.cast_eq_zero]
