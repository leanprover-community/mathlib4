/-
Copyright (c) 2024 Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Copley
-/
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index

/-!

The main result (TODO) is a lemma of B. H. Neumann [1][2].

Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$: $$ G = ⋃_{i = 1}^n C_i g_i. $$
Then the index of (at least) one of these subgroups does not exceed $n$.

[1] <https://mathoverflow.net/a/17398/3332>
[2] <http://alpha.math.uga.edu/~pete/Neumann54.pdf>

The result is also needed to show an algebraic extension of fields is
determined by the set of all minimal polynomials.

-/

set_option autoImplicit true

section Mathlib.GroupTheory.Index

theorem Finset.finiteIndex_iInf {G ι : Type*} [Group G] [DecidableEq ι]
    {s : Finset ι} (f : ι → Subgroup G) (hs : ∀ i ∈ s, (f i).FiniteIndex) :
      (⨅ i ∈ s, f i).FiniteIndex := by
  induction' s using Finset.induction_on with a s _ ih
  · rw [← Finset.iInf_coe, Finset.coe_empty, iInf_emptyset]
    exact Subgroup.instFiniteIndexTop
  · have := hs a (Finset.mem_insert_self a s)
    have := ih fun a ha => hs a (Finset.mem_insert_of_mem ha)
    exact iInf_insert a s f ▸ Subgroup.instFiniteIndexInf (f a) (⨅ i ∈ s, f i)

theorem Fintype.finiteIndex_iInf {G ι : Type*} [Fintype ι] [Group G] [DecidableEq (Subgroup G)]
    (a : ι → Subgroup G) (ha : ∀ i, (a i).FiniteIndex) :
    (⨅ i, a i).FiniteIndex := by
  suffices (⨅ x ∈ Finset.univ.image a, x).FiniteIndex by
    rwa [Finset.iInf_finset_image, ← Finset.iInf_coe, Finset.coe_univ, iInf_univ] at this
  exact Finset.finiteIndex_iInf id fun x h =>
    have ⟨i, _, hi⟩ := Finset.mem_image.mp h
    hi ▸ ha i

instance Subgroup.instFiniteIndex_subgroupOf (G : Type*) [Group G]
    (H K : Subgroup G) [H.FiniteIndex] : (H.subgroupOf K).FiniteIndex := by
  apply Subgroup.FiniteIndex.mk
  show H.relindex K ≠ 0
  exact fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relindex_eq_zero h

end Mathlib.GroupTheory.Index

open scoped Pointwise

theorem Finset.covers_of_FiniteIndex (G : Type*) [Group G] [DecidableEq G]
    (H : Subgroup G) [H.FiniteIndex] :
    ∃ s : Finset G, ⋃ g ∈ s, g • (H : Set G) = Set.univ := by
  have : Fintype (G ⧸ H) := by exact H.fintypeQuotientOfFiniteIndex
  let f : (G ⧸ H) → G := Quotient.out'
  refine ⟨Finset.univ.image f, ?_⟩
  rw [← Set.univ_subset_iff]
  rintro x -
  rw [Set.mem_iUnion₂]
  refine ⟨f x, mem_image_univ_iff_mem_range.mpr (Set.mem_range_self (f := f) (x : G)), ?_⟩
  rw [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq]
  exact QuotientGroup.out_eq' _

theorem Finset.covers_subgroup {G : Type*} [Group G] [DecidableEq G]
    {H K : Subgroup G} [H.FiniteIndex] (hle : H ≤ K) :
    ∃ s : Finset G, ⋃ g ∈ s, g • (H : Set G) = K := by
  have ⟨s, h⟩ := Finset.covers_of_FiniteIndex K (H.subgroupOf K)
  refine ⟨s.map ⟨_, Subtype.val_injective⟩, ?_⟩
  rw [Finset.map_eq_image, set_biUnion_finset_image, Function.Embedding.coeFn_mk,
    ← Subtype.coe_image_univ (K : Set G), ← h, Set.image_iUnion₂]
  refine Set.iUnion₂_congr fun x hx => ?_
  rw [Subgroup.coe_subgroupOf, Subgroup.coeSubtype,
    Set.image_smul_comm Subtype.val x _ (fun _ => by exact rfl),
    Subtype.image_preimage_val, Set.inter_eq_self_of_subset_right hle, Subgroup.smul_def]

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
theorem Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ
    {G ι : Type*} [Group G] {H : Subgroup G}
    (is : Finset ι) (f : ι → G) (h : ⋃ i ∈ is, f i • (H : Set G) = Set.univ) :
    H.FiniteIndex := by
  rw [Set.iUnion₂_congr fun i _ => show f i • H = (H : Set G).image ((f · • ·) i) from rfl,
    ← Finset.set_biUnion_coe, Set.biUnion_eq_iUnion, Set.iUnion_eq_univ_iff] at h
  have := Finite.of_surjective (f · : { i // i ∈ is } → G ⧸ H) fun x =>
    QuotientGroup.induction_on x fun g => by
      simpa [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] using h g
  exact H.finiteIndex_of_finite_quotient

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
theorem Fintype.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ
    {G ι : Type*} [Group G] [Fintype ι] {H : Subgroup G}
    (f : ι → G) (h : ⋃ i : ι, f i • (H : Set G) = Set.univ) :
    H.FiniteIndex := by
  rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe] at h
  exact Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ Finset.univ f h

-- Inductive inner part of `Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ`
theorem Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ_aux
    {G : Type*} (ι : Type*) [Fintype ι] [DecidableEq ι] [Group G] [DecidableEq (Subgroup G)]
    (g : ι → G) (H : ι → Subgroup G) (hcovers : ⋃ i, g i • (H i : Set G) = Set.univ)
    (j : ι) (hj : ⋃ i ∈ Finset.univ.filter (H · = H j), g i • (H i : Set G) ≠ Set.univ) :
    ∃ i, H i ≠ H j ∧ (H i).FiniteIndex := by
  have ⟨s, hH⟩ : ∃ s, s = Finset.univ.image H := ⟨_, rfl⟩
  have ⟨n, hn⟩ : ∃ n, s.card ≤ n + 1 := ⟨s.card - 1, by rw [← Nat.sub_le_iff_le_add]⟩
  induction n generalizing ι s with
  | zero =>
    have ⟨C, hmem⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
      have : IsEmpty ι := by
        have : IsEmpty s := Finset.isEmpty_coe_sort.mpr hempty
        rwa [hH, Finset.isEmpty_coe_sort, Finset.image_eq_empty, Finset.univ_eq_empty_iff] at this
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hcovers
      exact hcovers 1
    have hC (k) : H k = C :=
      have : Subsingleton { x // x ∈ s } := Finset.card_le_one_iff_subsingleton_coe.mp hn
      have hsH (k) : H k ∈ s := hH ▸ mem_image_univ_iff_mem_range.mpr (Set.mem_range_self k)
      have hsC : s = {C} := Finset.eq_singleton_iff_unique_mem.mpr <| ⟨hmem,
        fun x hx => Subtype.ext_iff.mp (Subsingleton.elim (⟨x, hx⟩ : { x // x ∈ s}) ⟨C, hmem⟩)⟩
      (Finset.eq_singleton_iff_nonempty_unique_mem.mp hsC).2 (H k) (hsH k)
    refine (hj ?_).elim
    simp [← hcovers, hC]
  | succ n ih =>
    have hsH (k) : H k ∈ s := hH ▸ mem_image_univ_iff_mem_range.mpr (Set.mem_range_self k)
    rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe,
      ← Finset.univ.filter_union_filter_neg_eq (H · = H j), Finset.set_biUnion_union] at hcovers
    -- Since `G ≠ ⋃ k ∈ {k : H k = H j}, g k • H j`,
    -- there exists `x ∉ ⋃ k ∈ {k : H k = H j}, g k • H k`.
    have ⟨x, hx⟩ : ∃ x, x ∉ ⋃ i ∈ Finset.univ.filter (H · = H j), g i • (H i : Set G) := by
      rwa [ne_eq, Set.eq_univ_iff_forall, not_forall] at hj
    -- Then `x • H j ∩ ⋃ k ∈ {k : H k = H j}, g k • H k = ∅`.
    have : x • (H j : Set G) ∩ ⋃ k ∈ Finset.univ.filter (H · = H j), g k • (H k : Set G) = ∅ := by
      rw [Set.eq_empty_iff_forall_not_mem]
      suffices ∀ i ∈ x • (H j : Set G), ∀ (x : ι), H x = H j → i ∉ g x • (H x : Set G) by
        simpa using this
      replace hx : ∀ i, H i = H j → x ∉ g i • (H i : Set G) := by simpa using hx
      intro y hy₁ i hi hy₂
      apply hx i hi
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv] at hy₁
      rw [hi, mem_leftCoset_iff, SetLike.mem_coe] at hy₂ ⊢
      rw [← mul_inv_cancel_right (g i)⁻¹ y, mul_assoc]
      exact (H j).mul_mem hy₂ hy₁
    -- Therefore `x • H j ⊆ ⋃ k ∈ {k : H k ≠ H j}, g k • H k`.
    replace this :
        x • (H j : Set G) ⊆ ⋃ k ∈ Finset.univ.filter (H · ≠ H j), g k • (H k : Set G) := by
      rw [← Set.left_eq_inter, ← Set.empty_union (_ ∩ _), ← this,
        ← Set.inter_union_distrib_left, Set.left_eq_inter, hcovers]
      exact Set.subset_univ _
    -- Thus `y • H j ⊆ ⋃ k ∈ {k : H k ≠ H j}, (y * x⁻¹ * g k) • H k` for all `y : G`, that is,
    -- every left coset of `H j` is contained in a finite union of left cosets of the
    -- subgroups `H k ≠ H j`.
    replace this (y : G) :
        y • (H j : Set G) ⊆
          ⋃ i ∈ Finset.univ.filter (H · ≠ H j), (y * x⁻¹ * g i) • (H i : Set G) := by
      suffices ∀ z ∈ y • (H j : Set G), ∃ i, H i ≠ H j ∧ z ∈ (y * x⁻¹ * g i) • (H i : Set G) by
        simpa [Set.subset_def] using this
      replace this : ∀ z ∈ x • (H j : Set G), ∃ k, H k ≠ H j ∧ z ∈ g k • (H k : Set G) := by
        simpa [Set.subset_def] using this
      intro z hz
      rw [mem_leftCoset_iff] at hz
      have ⟨k, hk, h⟩ := this (x * y⁻¹ * z) <| by
        rwa [mem_leftCoset_iff, ← mul_assoc, ← mul_assoc, mul_left_inv, one_mul]
      refine ⟨k, hk, ?_⟩
      rwa [mem_leftCoset_iff, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc, ← mem_leftCoset_iff]
    -- Then `G` can also be covered by a finite union `U k, f k • K k` of left cosets
    -- of the subgroups `H k ≠ H j`.
    let κ :=
      { i // i ∈ Finset.univ.filter (H · ≠ H j) } ×
        Option { i // i ∈ Finset.univ.filter (H · = H j) }
    let f : κ → G
    | ⟨k₁, some k₂⟩ => g k₂ * x⁻¹ * g k₁
    | ⟨k₁, none⟩  => g k₁
    let K (k : κ) : Subgroup G := H k.fst.val
    have hK' (k : κ) : K k ∈ s.erase (H j) :=
      Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp k.fst.property).right, hsH k.fst.val⟩
    have hK (k : κ) : K k ≠ H j := ((Finset.mem_erase.mp (hK' k)).left ·)
    have hcovers : ⋃ k, f k • (K k : Set G) = Set.univ := Set.iUnion_eq_univ_iff.mpr fun y => by
      cases (Set.mem_union _ _ _).mp (hcovers.symm.subset (Set.mem_univ y)) with
      | inl hy =>
        have ⟨k, hk, hy⟩ := Set.mem_iUnion₂.mp hy
        have hk' : H k = H j := by simpa using hk
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp (this (g k) (hk' ▸ hy))
        exact ⟨⟨⟨i, hi⟩, some ⟨k, hk⟩⟩, hy⟩
      | inr hy =>
        have ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
        exact ⟨⟨⟨i, hi⟩, none⟩, hy⟩
    -- Let `H k` be one of the subgroups in this covering.
    have ⟨k⟩ : Nonempty κ := not_isEmpty_iff.mp fun hempty => by
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, ← not_nonempty_iff] at hcovers
      exact hcovers ⟨1⟩
    -- If `G` is the union of the cosets of `H k` in the new covering, we are done.
    by_cases h : ⋃ i ∈ Finset.filter (K · = K k) Finset.univ, f i • (K i : Set G) = Set.univ
    · rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at h
      exact ⟨k.fst, hK k, Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ _ _ h⟩
    -- Otherwise, by the induction hypothesis, one of the subgroups `H k ≠ H j` has finite index.
    have hn : (Finset.univ.image K).card ≤ n + 1 := by
      trans (s.erase (H j)).card
      · refine Finset.card_le_card fun x => ?_
        rw [mem_image_univ_iff_mem_range, Set.mem_range]
        exact fun ⟨k, hk⟩ => hk ▸ hK' k
      · rwa [Finset.card_erase_of_mem (hsH j), Nat.sub_le_iff_le_add]
    have ⟨k', hk'⟩ := ih κ f K hcovers k h _ rfl hn
    exact ⟨k'.fst, hK k', hk'.right⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
theorem Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ {G ι : Type*} [Group G] [Fintype ι]
    (g : ι → G) (H : ι → Subgroup G) (hcovers : ⋃ k, g k • (H k : Set G) = Set.univ) :
    ∃ k, (H k).FiniteIndex := by
  classical
  have ⟨j⟩ : Nonempty ι := not_isEmpty_iff.mp fun hempty => by
    rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hcovers
    exact hcovers 1
  have :
    ⋃ i ∈ Finset.univ.filter (H · = H j), g i • (H i : Set G) = Set.univ ∨
      ∃ i, H i ≠ H j ∧ (H i).FiniteIndex := by
    rw [or_iff_not_imp_left, ← ne_eq]
    exact Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ_aux ι g H hcovers j
  cases this with
  | inl h =>
    rw [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).right]] at h
    exact ⟨j, Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ _ _ h⟩
  | inr h =>
    exact match h with | ⟨i, _, h⟩ => ⟨i, h⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then the cosets of subsets of infinite index may be omitted from the covering. -/
theorem Fintype.covers_finiteIndex_of_covers {G ι : Type*} [Group G] [Fintype ι]
    [DecidablePred fun (H : Subgroup G) => H.FiniteIndex]
    (g : ι → G) (H : ι → Subgroup G) (hcovers : ⋃ k, g k • (H k : Set G) = Set.univ) :
    ⋃ k ∈ Finset.univ.filter (fun i => (H i).FiniteIndex), g k • (H k : Set G) = Set.univ := by
  classical
  let D := ⨅ k ∈ Finset.univ.filter (fun i => (H i).FiniteIndex), H k
  -- `D`, as the finite intersection of subgroups of finite index, also has finite index.
  have hD : D.FiniteIndex := by
    -- have ⟨k, hk⟩ := Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ G ι H g hcovers
    -- have : D ≤ H k := iInf₂_le k <| by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    have h (x) (hx : x ∈ (Finset.univ.filter (fun i => (H i).FiniteIndex)).image H) :
        x.FiniteIndex := by
      have ⟨i, hi⟩ := Finset.mem_image.mp hx
      exact hi.2 ▸ (Finset.mem_filter.mp hi.1).2
    have := Finset.finiteIndex_iInf _ h
    rwa [Finset.iInf_finset_image] at this
  -- Each subgroup of finite index in the cover is a finite union of left cosets of `D`.
  have (i) (hi : (H i).FiniteIndex) : ∃ s : Finset G, ⋃ g ∈ s, g • (D : Set G) = H i := by
    have : D ≤ H i := iInf₂_le _ <| by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi⟩
    exact Finset.covers_subgroup this
  choose s hs using this
  -- Construct a cover of `G` by the cosets of subgroups of infinite index and of `D`.
  let κ := (i : ι) × { x // x ∈ (if h : (H i).FiniteIndex then s i h else {1}) }
  let f (k : κ) : G := g k.1 * k.2.val
  let K (k : κ) : Subgroup G := if (H k.1).FiniteIndex then D else H k.1
  have hcovers' : ⋃ k, f k • (K k : Set G) = Set.univ := by
    rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe,
      ← Finset.univ.filter_union_filter_neg_eq (fun i => (H i).FiniteIndex),
      Finset.set_biUnion_union] at hcovers
    rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe,
      ← Finset.univ.filter_union_filter_neg_eq (fun k => (H k.1).FiniteIndex),
      Finset.set_biUnion_union, ← hcovers]
    apply congrArg₂ (· ∪ ·) <;> (rw [Set.iUnion_sigma]; refine Set.iUnion_congr fun i => ?_)
    · by_cases hi : (H i).FiniteIndex <;>
        simp [Set.smul_set_iUnion, Set.iUnion_subtype, ← leftCoset_assoc, f, K, ← hs, hi]
    · by_cases hi : (H i).FiniteIndex <;>
        simp [Set.iUnion_subtype, f, K, hi]
  -- There is at least one coset of a subgroup of finite index in the original covering.
  have ⟨j, hj⟩ := Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ g H hcovers
  -- Therefore a coset of `D` occurs in the new covering.
  have ⟨x, hx⟩ : (s j hj).Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hempty => by
    specialize hs j hj
    rw [hempty, ← Finset.set_biUnion_coe, Finset.coe_empty, Set.biUnion_empty, eq_comm,
      Set.eq_empty_iff_forall_not_mem] at hs
    apply hs 1
    rw [SetLike.mem_coe]
    exact Subgroup.one_mem (H j)
  let k : κ := ⟨j, ⟨x, dif_pos hj ▸ hx⟩⟩
  -- Since `D` is the unique subgroup of finite index whose cosets occur in the new covering,
  -- the cosets of the other subgroups can be omitted.
  replace hcovers' := (Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ_aux κ f K hcovers' k).mt
  rw [not_exists] at hcovers'
  specialize hcovers' fun ⟨i', ⟨j', hj'⟩⟩ => by
    dsimp only [K]
    rw [if_pos hj]
    split_ifs with h
    · exact fun habsurd => habsurd.left rfl
    · exact fun habsurd => h habsurd.right
  -- The result follows by restoring the original cosets of subgroups of finite index
  -- from the cosets of `D` into which they have been decomposed.
  rw [← not_ne_iff.mp hcovers', Set.iUnion_sigma]
  refine Set.iUnion_congr fun i => ?_
  have hD' : ¬(H i).FiniteIndex → H i ≠ D := fun h hD' => (hD' ▸ h) hD
  by_cases hi : (H i).FiniteIndex <;>
    simp [Set.smul_set_iUnion₂, Set.iUnion_subtype, ← leftCoset_assoc, f, K, hD', ← hs, hi, hj]
