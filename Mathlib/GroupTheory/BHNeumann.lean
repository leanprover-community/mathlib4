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

* `BHNeumann` : the sum of the inverse of the indexes of the $C_i$ is greater than or equal to $1$.

* `BHNeumann'` : the index of (at least) one of these subgroups does not exceed $n$.

[1] [Neumann-1954], *Groups Covered By Permutable Subsets*, Lemma 4.1
[2] <https://mathoverflow.net/a/17398/3332>
[3] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

The result is also needed to show an algebraic extension of fields is
determined by the set of all minimal polynomials.

-/

open scoped Pointwise

section Mathlib.GroupTheory.Index

variable {G : Type*} [Group G]

theorem Fintype.finiteIndex_iInf {ι : Type*} [Fintype ι]
    (a : ι → Subgroup G) (ha : ∀ i, (a i).FiniteIndex) :
    (⨅ i, a i).FiniteIndex :=
  ⟨Subgroup.index_iInf_ne_zero fun i => (ha i).finiteIndex⟩

theorem Finset.finiteIndex_iInf {ι : Type*}
    {s : Finset ι} (f : ι → Subgroup G) (hs : ∀ i ∈ s, (f i).FiniteIndex) :
      (⨅ i ∈ s, f i).FiniteIndex := by
  rw [iInf_subtype']
  exact Fintype.finiteIndex_iInf _ fun ⟨i, hi⟩ => hs i hi

instance Subgroup.instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
  ⟨fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relindex_eq_zero h⟩

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

-- Inductive inner part of `Subgroup.exists_finiteIndex_of_leftCoset_cover`
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover_aux
    (ι : Type*) [Fintype ι] [DecidableEq (Subgroup G)]
    (H : ι → Subgroup G) (g : ι → G) (hcover : ⋃ i, g i • (H i : Set G) = Set.univ)
    (j : ι) (hj : ⋃ i ∈ Finset.univ.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i, H i ≠ H j ∧ (H i).FiniteIndex := by
  classical
  have ⟨s, hH⟩ : ∃ s, s = Finset.univ.image H := ⟨_, rfl⟩
  have ⟨n, hn⟩ : ∃ n, s.card ≤ n + 1 := ⟨s.card - 1, by rw [← Nat.sub_le_iff_le_add]⟩
  induction n generalizing ι s with
  | zero =>
    replace hH (i) : H i ∈ s := hH ▸ mem_image_univ_iff_mem_range.mpr (Set.mem_range_self i)
    have : Subsingleton { x // x ∈ s } := Finset.card_le_one_iff_subsingleton_coe.mp hn
    have (i) : H i = H j :=
      Subtype.ext_iff.mp <| Subsingleton.elim (⟨H i, hH i⟩ : { x // x ∈ s }) ⟨H j, hH j⟩
    refine (hj ?_).elim
    simpa [this] using hcover
  | succ n ih =>
    replace hH (i) : H i ∈ s := hH ▸ mem_image_univ_iff_mem_range.mpr (Set.mem_range_self i)
    -- Every left coset of `H j` is contained in a finite union of
    -- left cosets of the other subgroups `H k ≠ H j` of the covering.
    have ⟨x, hx⟩ : ∃ (x : G), ∀ i, H i = H j → (g i : G ⧸ H i) ≠ ↑x := by
      simpa [Set.eq_univ_iff_forall, mem_leftCoset_iff, ← QuotientGroup.eq] using hj
    replace hx : ∀ (y : G), y • (H j : Set G) ⊆
        ⋃ i ∈ Finset.univ.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      intro y z hz
      suffices ∃ i, H i ≠ H j ∧ z ∈ (y * x⁻¹ * g i) • (H i : Set G) by simpa using this
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Set.eq_univ_iff_forall.mp hcover (x * (y⁻¹ * z))
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] at hi
      refine ⟨i, fun hij => hx i hij ?_, ?_⟩
      . rwa [hi, QuotientGroup.eq, hij, mul_inv_rev, inv_mul_cancel_right,
          Subgroup.inv_mem_iff, ← SetLike.mem_coe, ← mem_leftCoset_iff]
      . simpa [mem_leftCoset_iff, SetLike.mem_coe, QuotientGroup.eq, mul_assoc] using hi
    -- Thus `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ := ↥(Finset.univ.filter (H · ≠ H j)) × Option ↥(Finset.univ.filter (H · = H j))
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩  => g k₁
    let K (k : κ) : Subgroup G := H k.1.val
    have hK' (k : κ) : K k ∈ s.erase (H j) :=
      Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp k.1.property).right, hH k.1.val⟩
    have hK (k : κ) : K k ≠ H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    replace hcover : ⋃ k, f k • (K k : Set G) = Set.univ := Set.iUnion_eq_univ_iff.mpr fun y => by
      rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe,
        ← Finset.univ.filter_union_filter_neg_eq (H · = H j), Finset.set_biUnion_union] at hcover
      cases (Set.mem_union _ _ _).mp (hcover.symm.subset (Set.mem_univ y)) with
      | inl hy =>
        have ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
        have hk' : H k = H j := by simpa using hk
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (hx (g k) (hk' ▸ hy))
        exact ⟨⟨⟨i, hi⟩, some ⟨k, hk⟩⟩, hy⟩
      | inr hy =>
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨⟨⟨i, hi⟩, none⟩, hy⟩
    -- Let `H k` be one of the subgroups in this covering.
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, ← not_nonempty_iff] at hcover
      exact hcover ⟨1⟩
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases hcover' : ⋃ i ∈ Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right],
        ← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion] at hcover'
      refine ⟨k.1, hK k, Subgroup.finiteIndex_of_leftCoset_cover_const hcover'⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn : (Finset.univ.image K).card ≤ n + 1 := by
      trans (s.erase (H j)).card
      · refine Finset.card_le_card fun x => ?_
        rw [mem_image_univ_iff_mem_range, Set.mem_range]
        exact fun ⟨k, hk⟩ => hk ▸ hK' k
      · rwa [Finset.card_erase_of_mem (hH j), Nat.sub_le_iff_le_add]
    have ⟨k', hk'⟩ := ih κ K f hcover k hcover' _ rfl hn
    exact ⟨k'.1, hK k', hk'.right⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
theorem Subgroup.exists_finiteIndex_of_leftCoset_cover {ι : Type*} [Fintype ι]
    {H : ι → Subgroup G} {g : ι → G} (hcover : ⋃ k, g k • (H k : Set G) = Set.univ) :
    ∃ k, (H k).FiniteIndex := by
  classical
  have ⟨j⟩ : Nonempty ι := not_isEmpty_iff.mp fun hempty => by
    rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hcover
    exact hcover 1
  by_cases hcover' : ⋃ i ∈ Finset.univ.filter (H · = H j), g i • (H i : Set G) = Set.univ
  · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right],
      ← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion] at hcover'
    refine ⟨j, Subgroup.finiteIndex_of_leftCoset_cover_const hcover'⟩
  · exact match Subgroup.exists_finiteIndex_of_leftCoset_cover_aux ι H g hcover j hcover' with
    | ⟨i, _, h⟩ => ⟨i, h⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subgroups of infinite index may be omitted from the covering. -/
theorem Subgroup.leftCoset_cover_filter_FiniteIndex {ι : Type*} [Fintype ι]
    [DecidablePred fun (H : Subgroup G) => H.FiniteIndex]
    (H : ι → Subgroup G) (g : ι → G) (hcover : ⋃ k, g k • (H k : Set G) = Set.univ) :
    ⋃ k ∈ Finset.univ.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ := by
  classical
  let D := ⨅ k ∈ Finset.univ.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := by
    unfold_let D
    rw [← Finset.iInf_finset_image]
    apply Finset.finiteIndex_iInf
    simp
  have (i) (hi : (H i).FiniteIndex) : ∃ s : Finset G, ⋃ g ∈ s, g • (D : Set G) = H i :=
    Subgroup.leftCoset_cover_const_of_le_of_FiniteIndex <| iInf₂_le _ <| by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi⟩
  choose s hs using this
  -- Construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : ι) × { x // x ∈ (if h : (H i).FiniteIndex then s i h else {1}) }
  let f (k : κ) : G := g k.1 * k.2.val
  let K (k : κ) : Subgroup G := if (H k.1).FiniteIndex then D else H k.1
  have hcover' : ⋃ k, f k • (K k : Set G) = Set.univ := by
    rw [← hcover, ← Set.biUnion_univ (α := κ), ← Set.biUnion_univ (α := ι),
     ← Finset.coe_univ, ← Finset.coe_univ, Finset.set_biUnion_coe, Finset.set_biUnion_coe,
     ← Finset.univ.filter_union_filter_neg_eq (fun i => (H i).FiniteIndex),
     ← Finset.univ.filter_union_filter_neg_eq (fun k => (H k.1).FiniteIndex),
     Finset.set_biUnion_union, Finset.set_biUnion_union]
    apply congrArg₂ (· ∪ ·) <;> (rw [Set.iUnion_sigma]; refine Set.iUnion_congr fun i => ?_)
    · by_cases hi : (H i).FiniteIndex <;>
        simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc, f, K, ← hs, hi]
    · by_cases hi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  have ⟨j, hj⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcover
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨x, hx⟩ : (s j hj).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    specialize hs j hj
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty, eq_comm,
      Set.eq_empty_iff_forall_not_mem] at hs
    exact hs 1 <| SetLike.mem_coe.mpr (Subgroup.one_mem (H j))
  let k : κ := ⟨j, ⟨x, dif_pos hj ▸ hx⟩⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcover' := (Subgroup.exists_finiteIndex_of_leftCoset_cover_aux κ K f hcover' k).mt
  rw [not_exists] at hcover'
  specialize hcover' fun ⟨i', ⟨j', hj'⟩⟩ => by
    dsimp only [K]
    rw [if_pos hj]
    split_ifs with h
    · exact fun habsurd => habsurd.left rfl
    · exact fun habsurd => h habsurd.right
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  rw [← not_ne_iff.mp hcover', Set.iUnion_sigma]
  refine Set.iUnion_congr fun i => ?_
  have hD' : ¬(H i).FiniteIndex → H i ≠ D := fun h hD' => (hD' ▸ h) hD
  by_cases hi : (H i).FiniteIndex <;>
    simp [Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc, f, K, hD', ← hs, hi, hj]

variable (G : Type*) [Group G]

variable {ι : Type*} (s : Finset ι)
    (H : ι → Subgroup G) [DecidablePred fun i ↦ (H i).FiniteIndex]
    (g : ι → G)
    (covers: ⋃ i ∈ s, (g i) • (H i : Set G) = ⊤)

-- lemma exists_of_finite_index : ∃ i, 0 < (H i).index := sorry

lemma of_finite_index_covers :
    ⋃ i ∈ s.filter (fun i ↦ (H i).FiniteIndex), (g i) • (H i : Set G) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Set.univ := Set.mem_univ x
  rw [← Subgroup.leftCoset_cover_filter_FiniteIndex
    (fun (i : s) ↦ H i) (fun (i : s) ↦ g i) ?_] at hx
  simp only [Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and, Set.mem_iUnion,
    exists_prop, Subtype.exists, exists_and_left] at hx
  simp only [Finset.mem_filter, Set.mem_iUnion, exists_prop]
  obtain ⟨i, hi, h1, h2⟩ := hx
  exact ⟨i, ⟨⟨hi, h1⟩, h2⟩⟩
  · rw [← Set.top_eq_univ, eq_top_iff]
    intro x hx
    simp only [← covers, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, hi, hx⟩ := hx
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
    exact ⟨i, hi, hx⟩

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
    apply le_trans _ (Finset.card_image_le (f := QuotientGroup.mk (s := H) ∘ g))
    apply le_of_eq
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
      simp only [Function.comp_apply, QuotientGroup.eq', smul_eq_mul, inv_mul_cancel_left]
      exact hmem
    · apply Set.ncard_mono
      simp only [Set.le_eq_subset, Set.subset_univ]

theorem Set.Finite.preimage'  {α : Type*} {β : Type*} {f : α → β} {s : Set β}
    (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

/-
theorem Set.Finite.preimage'  {α : Type*} {β : Type*} {f : α → β} {s : Set β}
    (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  apply Set.Finite.induction_on
    (C := fun s ↦ ∀ (_ : s.Finite) (_ : ∀ b ∈ s, (f ⁻¹' {b}).Finite),
      (f ⁻¹' s).Finite) h
  · intro _ _
    simp only [preimage_empty, finite_empty]
  · intro a s _ hs hrec _ hf
    rw [← singleton_union, Set.preimage_union]
    apply Set.Finite.union -- finite_biUnion''
    · exact hf a (mem_insert a s)
    · exact hrec hs (fun b hb ↦ hf b (mem_insert_of_mem a hb))
  exact h
  exact hf
-/

theorem BHNeumann :
    (1 : ℚ) ≤ s.sum (fun i ↦ (1 : ℚ) / (H i).index) := by
  classical
  have covers' := of_finite_index_covers G s H g
  rw [← Finset.sum_filter_add_sum_filter_not s (p := fun i ↦ (H i).FiniteIndex)]
  set s' := s.filter (fun i ↦ (H i).FiniteIndex)
  apply le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg (fun i _ ↦ by simp))
  let K := ⨅ i ∈ s', (H i)
  have hK : K.FiniteIndex := by
    apply Finset.finiteIndex_iInf
    intro i hi
    simp only [ne_eq, Finset.mem_filter, s'] at hi
    exact hi.2
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
  have covers'' : ⋃ i ∈ Finset.univ, (f i) • (K : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x
    rw [← covers']
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_univ, Set.iUnion_true, forall_exists_index,
      and_imp]
    intro i hi hx
    rw [mem_leftCoset_iff] at hx
    let z := Subgroup.MemLeftTransversals.toFun (hS i) ⟨_, hx⟩
    use ⟨⟨i, hi⟩, ⟨z, by
      simp only [Set.Finite.mem_toFinset, Subtype.coe_prop]⟩⟩
    simp only [f, z]
    rw [mul_smul, mem_leftCoset_iff, Set.mem_smul_set_iff_inv_smul_mem]
    exact Subgroup.MemLeftTransversals.inv_toFun_mul_mem (hS i) ⟨_, hx⟩
    exact covers

  have := BHNeumann_of_subgroup G Finset.univ K f covers''
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
  simp only [one_div, ← div_eq_mul_inv]
  rw [eq_div_iff ?_]
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

open BigOperators in
theorem BHNeumann' :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card := by
  classical
  have hf {K : Subgroup G} : K.FiniteIndex ↔ K.index ≠ 0 := ⟨fun h => h.finiteIndex, fun h => ⟨h⟩⟩
  have hsum : (1 : ℚ) ≤ ∑ i ∈ s, (1 : ℚ) / (H i).index := BHNeumann G s H g covers
  have ⟨j, hjs, hj⟩ : ∃ j ∈ s, (H j).FiniteIndex := by
    have ⟨j, hjs, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((zero_lt_one.trans_le hsum).ne.symm)
    exact ⟨j, hjs, hf.mpr <| Nat.cast_ne_zero.mp <| ne_zero_of_one_div_ne_zero h⟩
  contrapose! hsum with hlt
  suffices ∑ x ∈ Finset.filter (fun i ↦ (H i).FiniteIndex) s, (1 : ℚ) / (H x).index < 1 from by
    have h : ∑ x ∈ Finset.filter (fun a ↦ ¬(H a).FiniteIndex) s, (1 : ℚ) / ↑(H x).index = 0 := by
      simp [Finset.sum_eq_zero, hf]
    simpa [-one_div, ← s.sum_filter_add_sum_filter_not (fun i => (H i).FiniteIndex), h]
  have hs' : (0 : ℚ) < s.card := Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨j, hjs⟩
  have hi' (i) (hi : (H i).FiniteIndex) : (0 : ℚ) < (H i).index :=
    Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hi.finiteIndex
  apply lt_of_lt_of_le (b := ∑ _ ∈ s.filter (fun i => (H i).FiniteIndex), (1 : ℚ) / s.card)
  · refine Finset.sum_lt_sum (fun i hi => ?_) ?_
    · replace ⟨his, hi⟩ := Finset.mem_filter.mp hi
      simpa [-one_div, div_le_div_iff (hi' i hi) hs'] using (hlt i his hi).le
    · refine ⟨j, Finset.mem_filter.mpr ⟨hjs, hj⟩, ?_⟩
      simpa [-one_div, div_lt_div_iff (hi' j hj) hs'] using (hlt j hjs hj)
  · rw [← mul_le_mul_iff_of_pos_left hs', Finset.mul_sum, mul_one]
    trans ((s.filter fun i => (H i).FiniteIndex).card : ℚ)
    · rw [(s.filter fun i => (H i).FiniteIndex).card_eq_sum_ones]
      simp [hs'.ne.symm]
    · simp [Finset.card_filter_le]
