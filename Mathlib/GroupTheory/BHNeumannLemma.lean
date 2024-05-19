/-
Copyright (c) 2024 Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index

open scoped Pointwise

set_option autoImplicit true

/-!

The main result (TODO) is a lemma of B. H. Neumann [1][2],

"Let the group $G$ be the union of finitely many, let us say $n$, left cosets
of subgroups $C₁$, $C₂$, ..., $Cₙ$:
$$
  G = \bigunion_{i = 1}^n C_i g_i.
$$
Then the index (at least) of one of these subgroups does not exceed $n$."

[1] https://mathoverflow.net/a/17398/3332
[2] http://alpha.math.uga.edu/%7Epete/Neumann54.pdf

The result is also needed to show an algebraic extension of fields is
determined by the set of all minimal polynomials.

-/

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
theorem Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ
    {G ι : Type*} [Group G] {H : Subgroup G} (is : Finset ι)
    (f : ι → G) (h : ⋃ i ∈ is, f i • (H : Set G) = Set.univ) :
      H.FiniteIndex := by
  rw [Set.iUnion₂_congr fun i _ => show f i • H = (H : Set G).image ((f · • ·) i) from rfl,
    ← is.set_biUnion_coe, Set.biUnion_eq_iUnion, Set.iUnion_eq_univ_iff] at h
  have := Finite.of_surjective (f · : { i // i ∈ is } → G ⧸ H) fun x =>
    QuotientGroup.induction_on x fun g => by
      simpa [mem_leftCoset_iff, SetLike.mem_coe, ← QuotientGroup.eq] using h g
  exact H.finiteIndex_of_finite_quotient

/-- If `H` is a subgroup of `G` and `G` is the union of a finite family of left cosets of `H`
then `H` has finite index. -/
theorem Fintype.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ
    {G ι : Type*} [Group G] {H : Subgroup G} [Fintype ι]
    (f : ι → G) (h : ⋃ i : ι, f i • (H : Set G) = Set.univ) :
      H.FiniteIndex := by
  rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe] at h
  exact Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ Finset.univ f h

-- Inductive inner part of `Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ`
theorem Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ_aux
    (r : ℕ) (G ι : Type*) [Group G] [Fintype ι]
    (s : Finset (Subgroup G)) (hr : s.card ≤ r + 1)
    (H : ι → s) (hH : Function.Surjective H)
    (g : ι → G) (hG : (⋃ k, g k • (H k : Set G)) = (Set.univ : Set G)) :
    ∃ k, (H k).val.FiniteIndex := by
  classical
  induction r generalizing ι s with
  | zero =>
    -- If `G` is the finite union of left cosets of a single subgroup `C` then `C` has finite index.
    have h₀ : s.card ≠ 0 := Finset.card_eq_zero.ne.mpr fun hempty => by
      have : IsEmpty s := by exact Finset.isEmpty_coe_sort.mpr hempty
      have : IsEmpty ι := H.isEmpty
      rw [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hG
      exact hG 1
    have h₁ : s.card = 1 := by omega
    have hne : s ≠ ∅ := by rwa [← Finset.nonempty_iff_ne_empty, ← Finset.card_ne_zero]
    have ⟨k⟩ : Nonempty ι := not_isEmpty_iff.mp fun _ => hne (Finset.isEmpty_coe_sort.mp hH.isEmpty)
    have ⟨C, hC⟩ : ∃ C, ∀ k, (H k).val = C := by
      have ⟨C, hs⟩ : ∃ C, s = {C} := Finset.card_eq_one.mp h₁
      exact ⟨C, fun k => (Finset.eq_singleton_iff_nonempty_unique_mem.mp hs).2 (H k).1 (H k).2⟩
    refine ⟨k, Fintype.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ g ?_⟩
    simp only [← hG, hC]
  | succ r ih =>
    -- Choose one subgroup `C` from the set `s`.
    have ⟨C⟩ : Nonempty { x // x ∈ s } := not_isEmpty_iff.mp fun hempty => by
      have : IsEmpty ι := H.isEmpty
      rewrite [Set.iUnion_of_empty, eq_comm, Set.univ_eq_empty_iff, isEmpty_iff] at hG
      exact hG 1
    have ⟨k, hk⟩ := hH C
    -- If `G = ⋃ k ∈ {k : H k = C}, g k • C` then `C` has finite index.
    by_cases h : (⋃ k ∈ Finset.univ.filter (H · = C), g k • (H k : Set G)) = Set.univ
    . rewrite [Set.iUnion₂_congr fun i hi => by rw [(Finset.mem_filter.mp hi).2]] at h
      exact ⟨k, hk ▸ Finset.finiteIndex_of_iUnion_leftCoset_same_subgroup_eq_univ
         (Finset.univ.filter (H · = C)) g h⟩
    -- Otherwise there exists `x ∈ ⋃ k ∈ {k : H k = C}, g k • H k`.
    rewrite [Set.eq_univ_iff_forall, not_forall] at h
    obtain ⟨x, hx⟩ := h
    -- Then `x • C ∩ ⋃ k ∈ {k : H k = C}, g k • H k = ∅`.
    have : x • (C : Set G) ∩ ⋃ k ∈ Finset.univ.filter (H · = C), g k • (H k : Set G) = ∅ := by
      rw [Set.eq_empty_iff_forall_not_mem]
      suffices ∀ i ∈ x • (C : Set G), ∀ (x : ι), H x = C → i ∉ g x • (H x : Set G) by
        simpa using this
      intro y hy₁ i hi hy₂
      replace hx : ∀ (i : ι), H i = C → x ∉ g i • (H i : Set G) := by simpa using hx
      apply hx i hi
      rw [mem_leftCoset_iff, SetLike.mem_coe, ← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv] at hy₁
      rw [hi, mem_leftCoset_iff, SetLike.mem_coe] at hy₂ ⊢
      rw [← mul_inv_cancel_right ((g i)⁻¹) y, mul_assoc]
      exact C.val.mul_mem hy₂ hy₁
    -- Therefore `x • C ⊆ ⋃ k ∈ {k : H k ≠ C}, g k • H k`.
    rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe,
      ← Finset.univ.filter_union_filter_neg_eq (H · = C), Finset.set_biUnion_union] at hG
    replace this : x • (C : Set G) ⊆ ⋃ k ∈ Finset.univ.filter (¬H · = C), g k • (H k : Set G) := by
      rw [← Set.left_eq_inter, ← Set.empty_union (_ ∩ _), ← this,
        ← Set.inter_union_distrib_left, Set.left_eq_inter, hG]
      exact Set.subset_univ _
    -- Thus `y • C ⊆ ⋃ k ∈ {k : H k ≠ C}, (y * x⁻¹ * g k) • H k` for all `y : G`, that is,
    -- every left coset of `C` is contained in a finite union of left cosets of the
    -- subgroups `H k ≠ C`.
    replace this : ∀ z ∈ x • (C : Set G), ∃ k, ¬H k = C ∧ z ∈ g k • (H k : Set G) := by
      simpa [Set.subset_def] using this
    replace this (y : G) :
        y • (C : Set G) ⊆
          ⋃ i ∈ Finset.univ.filter (¬H · = C), (y * x⁻¹ * g i) • (H i : Set G) := by
      suffices ∀ z ∈ y • (C : Set G), ∃ i, ¬H i = C ∧ z ∈ (y * x⁻¹ * g i) • (H i : Set G) by
        simpa [Set.subset_def] using this
      intro z hz
      rw [mem_leftCoset_iff] at hz
      obtain ⟨k, hk, h⟩ := this (x * y⁻¹ * z) <| by
        rwa [mem_leftCoset_iff, ← mul_assoc, ← mul_assoc, mul_left_inv, one_mul]
      refine ⟨k, hk, ?_⟩
      rwa [mem_leftCoset_iff, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc, ← mem_leftCoset_iff]
    -- Then `G` can also be covered by a finite union of left cosets of the subgroups `H k ≠ C`.
    let κ₁ := { i // i ∈ Finset.univ.filter (H · ≠ C) }
    let κ₂ := { i // i ∈ Finset.univ.filter (H · = C) }
    let κ := Sum (κ₂ × κ₁) κ₁
    have hκ₁ (i : κ₁) : (H i : Subgroup G) ∈ s.erase C := by
      rw [Finset.mem_erase, ← Subtype.ext_iff.ne]
      exact ⟨(Finset.mem_filter.mp i.property).right, Finset.coe_mem _⟩
    let f : κ → G | Sum.inl ⟨k, i⟩ => g k * x⁻¹ * g i | Sum.inr i => g i
    let K : κ → { x // x ∈ s.erase ↑C } | Sum.inl ⟨_, i⟩ => ⟨H i, hκ₁ i⟩ | Sum.inr i => ⟨H i, hκ₁ i⟩
    -- By the induction hypothesis, one of the subgroups `H k ≠ C` has finite index.
    specialize ih κ ((Set.range K).toFinset.map ⟨_, Subtype.val_injective⟩) <| by
      rw [Finset.card_map]
      refine le_trans ?_ ((Finset.card_erase_of_mem C.property).le.trans (by omega))
      rw [← Finset.card_attach (s := s.erase C), Finset.attach_eq_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    specialize ih (fun k => ⟨Set.rangeFactorization K k,
      Finset.mem_map.mpr ⟨K k, Set.mem_toFinset.mpr ⟨k, rfl⟩, rfl⟩⟩)
    specialize ih <| by
      intro ⟨x, hx⟩
      have ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
      have ⟨k, hk⟩ := Set.mem_toFinset.mp hy
      rw [Function.Embedding.coeFn_mk] at hyx
      exact ⟨k, by simp only [hk, hyx, Set.rangeFactorization_coe]⟩
    specialize ih f <| by
      rw [Set.iUnion_eq_univ_iff]
      intro y
      cases (Set.mem_union _ _ _).mp (hG.symm.subset (Set.mem_univ y)) with
      | inr hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨i, hi, hy⟩ := hy
        exact ⟨Sum.inr ⟨i, hi⟩, hy⟩
      | inl hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨k, hk, hy⟩ := hy
        have hk' : H k = C := by simpa using hk
        specialize this (g k) (hk' ▸ hy)
        rw [Set.mem_iUnion₂] at this
        obtain ⟨i, hi, hy⟩ := this
        have : κ := Sum.inl ⟨⟨k, hk⟩, ⟨i, hi⟩⟩
        refine ⟨Sum.inl ⟨⟨k, hk⟩, ⟨i, hi⟩⟩, hy⟩
    have ⟨k, h⟩ := ih
    exact match k with | Sum.inl ⟨_, i⟩ => ⟨i, h⟩ | Sum.inr i => ⟨i, h⟩

/-- Let the group `G` be the union of finitely many left cosets `g i • H i`.
Then at least one subgroup `H i` has finite index in `G`. -/
theorem Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ (G ι : Type*) [Group G] [Fintype ι]
    (H : ι → Subgroup G) (g : ι → G) (h : (⋃ k, g k • (H k : Set G)) = (Set.univ : Set G)) :
    ∃ k, (H k).FiniteIndex := by
  classical
  let s := (Set.range H).toFinset
  let H' : (i : ι) → s := fun i => ⟨Set.rangeFactorization H i, by
    dsimp only [Set.rangeFactorization_coe, s]
    rw [Set.mem_toFinset]
    exact Set.mem_range_self i⟩
  refine Fintype.finiteIndex_of_iUnion_leftCoset_eq_univ_aux
    (s.card - 1) G ι (Set.range H).toFinset (by unfold_let s; omega) H' ?_ g h
  unfold_let H'
  intro ⟨x, hx⟩
  have h : Function.Surjective (Set.rangeFactorization H) := Set.surjective_onto_range
  have ⟨i, hi⟩ := h ⟨x, Set.mem_toFinset.mp hx⟩
  exact ⟨i, by rw [Subtype.mk_eq_mk, hi]⟩
