/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Finite.Sum
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Fintype

/-!
# Permutations on `Fintype`s

This file contains miscellaneous lemmas about `Equiv.Perm` and `Equiv.swap`, building on top
of those in `Mathlib/Logic/Equiv/Basic.lean` and other files in `Mathlib/GroupTheory/Perm/*`.
-/

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} {β : Type v}

-- An example on how to determine the order of an element of a finite group.
-- import Mathlib.Data.Int.Order.Units
-- example : orderOf (-1 : ℤˣ) = 2 :=
--   orderOf_eq_prime (Int.units_sq _) (by decide)

namespace Equiv.Perm

section Conjugation

variable [DecidableEq α] [Fintype α] {σ τ : Perm α}

theorem isConj_of_support_equiv
    (f : { x // x ∈ (σ.support : Set α) } ≃ { x // x ∈ (τ.support : Set α) })
    (hf : ∀ (x : α) (hx : x ∈ (σ.support : Set α)),
      (f ⟨σ x, apply_mem_support.2 hx⟩ : α) = τ ↑(f ⟨x, hx⟩)) :
    IsConj σ τ := by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

end Conjugation



theorem perm_inv_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : ∀ x ∈ s, f x ∈ s) {y : α}
    (hy : y ∈ s) : f⁻¹ y ∈ s := by
  have h0 : ∀ y ∈ s, ∃ (x : _) (hx : x ∈ s), y = (fun i (_ : i ∈ s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, heq⟩ := h0 y hy
  convert hy2
  rw [heq]
  simp only [inv_apply_self]

theorem perm_inv_mapsTo_of_mapsTo (f : Perm α) {s : Set α} [Finite s] (h : Set.MapsTo f s s) :
    Set.MapsTo (f⁻¹ :) s s := by
  cases nonempty_fintype s
  exact fun x hx =>
    Set.mem_toFinset.mp <|
      perm_inv_on_of_perm_on_finset
        (fun a ha => Set.mem_toFinset.mpr (h (Set.mem_toFinset.mp ha)))
        (Set.mem_toFinset.mpr hx)

@[simp]
theorem perm_inv_mapsTo_iff_mapsTo {f : Perm α} {s : Set α} [Finite s] :
    Set.MapsTo (f⁻¹ :) s s ↔ Set.MapsTo f s s :=
  ⟨perm_inv_mapsTo_of_mapsTo f⁻¹, perm_inv_mapsTo_of_mapsTo f⟩

theorem perm_inv_on_of_perm_on_finite {f : Perm α} {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) {x : α} (hx : p x) : p (f⁻¹ x) := by
  have : Finite { x | p x } := by simpa
  simpa using perm_inv_mapsTo_of_mapsTo (s := {x | p x}) f h hx

/-- If the permutation `f` maps `{x // p x}` into itself, then this returns the permutation
  on `{x // p x}` induced by `f`. Note that the `h` hypothesis is weaker than for
  `Equiv.Perm.subtypePerm`. -/
abbrev subtypePermOfFintype (f : Perm α) {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) : Perm { x // p x } :=
  f.subtypePerm fun x => ⟨fun h₂ => f.inv_apply_self x ▸ perm_inv_on_of_perm_on_finite h h₂, h x⟩

@[simp]
theorem subtypePermOfFintype_apply (f : Perm α) {p : α → Prop} [Finite { x // p x }]
    (h : ∀ x, p x → p (f x)) (x : { x // p x }) : subtypePermOfFintype f h x = ⟨f x, h x x.2⟩ :=
  rfl

theorem subtypePermOfFintype_one (p : α → Prop) [Finite { x // p x }]
    (h : ∀ x, p x → p ((1 : Perm α) x)) : @subtypePermOfFintype α 1 p _ h = 1 :=
  rfl

theorem perm_mapsTo_inl_iff_mapsTo_inr {m n : Type*} [Finite m] [Finite n] (σ : Perm (m ⊕ n)) :
    Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) ↔
      Set.MapsTo σ (Set.range Sum.inr) (Set.range Sum.inr) := by
  constructor <;>
    ( intro h
      classical
        rw [← perm_inv_mapsTo_iff_mapsTo] at h
        intro x
        rcases hx : σ x with l | r)
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨l, rfl⟩
    rw [← hx, σ.inv_apply_self] at hy
    exact absurd hy Sum.inl_ne_inr
  · rintro _; exact ⟨r, rfl⟩
  · rintro _; exact ⟨l, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨r, rfl⟩
    rw [← hx, σ.inv_apply_self] at hy
    exact absurd hy Sum.inr_ne_inl

theorem mem_sumCongrHom_range_of_perm_mapsTo_inl {m n : Type*} [Finite m] [Finite n]
    {σ : Perm (m ⊕ n)} (h : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl)) :
    σ ∈ (sumCongrHom m n).range := by
  classical
    have h1 : ∀ x : m ⊕ n, (∃ a : m, Sum.inl a = x) → ∃ a : m, Sum.inl a = σ x := by
      rintro x ⟨a, ha⟩
      apply h
      rw [← ha]
      exact ⟨a, rfl⟩
    have h3 : ∀ x : m ⊕ n, (∃ b : n, Sum.inr b = x) → ∃ b : n, Sum.inr b = σ x := by
      rintro x ⟨b, hb⟩
      apply (perm_mapsTo_inl_iff_mapsTo_inr σ).mp h
      rw [← hb]
      exact ⟨b, rfl⟩
    let σ₁' := subtypePermOfFintype σ h1
    let σ₂' := subtypePermOfFintype σ h3
    let σ₁ := permCongr (Equiv.ofInjective _ Sum.inl_injective).symm σ₁'
    let σ₂ := permCongr (Equiv.ofInjective _ Sum.inr_injective).symm σ₂'
    rw [MonoidHom.mem_range, Prod.exists]
    use σ₁, σ₂
    rw [Perm.sumCongrHom_apply]
    ext x
    rcases x with a | b
    · rw [Equiv.sumCongr_apply, Sum.map_inl, permCongr_apply, Equiv.symm_symm,
        apply_ofInjective_symm Sum.inl_injective]
      rw [ofInjective_apply, Subtype.coe_mk, Subtype.coe_mk]
      dsimp [Set.range]
      rw [subtypePerm_apply]
    · rw [Equiv.sumCongr_apply, Sum.map_inr, permCongr_apply, Equiv.symm_symm,
        apply_ofInjective_symm Sum.inr_injective, ofInjective_apply]
      dsimp [Set.range]
      rw [subtypePerm_apply]

nonrec theorem Disjoint.orderOf {σ τ : Perm α} (hστ : Disjoint σ τ) :
    orderOf (σ * τ) = Nat.lcm (orderOf σ) (orderOf τ) :=
  haveI h : ∀ n : ℕ, (σ * τ) ^ n = 1 ↔ σ ^ n = 1 ∧ τ ^ n = 1 := fun n => by
    rw [hστ.commute.mul_pow, Disjoint.mul_eq_one_iff (hστ.pow_disjoint_pow n n)]
  Nat.dvd_antisymm hστ.commute.orderOf_mul_dvd_lcm
    (Nat.lcm_dvd
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).1)
      (orderOf_dvd_of_pow_eq_one ((h (orderOf (σ * τ))).mp (pow_orderOf_eq_one (σ * τ))).2))

theorem Disjoint.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    {σ τ : Perm α} (h : Disjoint σ τ) : Disjoint (σ.extendDomain f) (τ.extendDomain f) := by
  intro b
  by_cases pb : p b
  · refine (h (f.symm ⟨b, pb⟩)).imp ?_ ?_ <;>
      · intro h
        rw [extendDomain_apply_subtype _ _ pb, h, apply_symm_apply, Subtype.coe_mk]
  · left
    rw [extendDomain_apply_not_subtype _ _ pb]

theorem Disjoint.isConj_mul [Finite α] {σ τ π ρ : Perm α} (hc1 : IsConj σ π)
    (hc2 : IsConj τ ρ) (hd1 : Disjoint σ τ) (hd2 : Disjoint π ρ) : IsConj (σ * τ) (π * ρ) := by
  classical
    cases nonempty_fintype α
    obtain ⟨f, rfl⟩ := isConj_iff.1 hc1
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc2
    have hd1' := coe_inj.2 hd1.support_mul
    have hd2' := coe_inj.2 hd2.support_mul
    rw [coe_union] at *
    have hd1'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd1)
    have hd2'' := disjoint_coe.2 (disjoint_iff_disjoint_support.1 hd2)
    refine isConj_of_support_equiv ?_ ?_
    · refine
          ((Equiv.setCongr hd1').trans (Equiv.Set.union hd1'')).trans
            ((Equiv.sumCongr (subtypeEquiv f fun a => ?_) (subtypeEquiv g fun a => ?_)).trans
              ((Equiv.setCongr hd2').trans (Equiv.Set.union hd2'')).symm) <;>
      · simp only [Set.mem_image, toEmbedding_apply, exists_eq_right, support_conj, coe_map,
          apply_eq_iff_eq]
    · intro x hx
      simp only [trans_apply, symm_trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply,
        Equiv.sumCongr_apply]
      rw [hd1', Set.mem_union] at hx
      rcases hx with hxσ | hxτ
      · rw [mem_coe, mem_support] at hxσ
        rw [Set.union_apply_left, Set.union_apply_left]
        · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inl, comp_apply,
            Set.union_symm_apply_left, Subtype.coe_mk, apply_eq_iff_eq]
          have h := (hd2 (f x)).resolve_left ?_
          · rw [mul_apply, mul_apply] at h
            rw [h, inv_apply_self, (hd1 x).resolve_left hxσ]
          · rwa [mul_apply, mul_apply, inv_apply_self, apply_eq_iff_eq]
        · rwa [Subtype.coe_mk, mem_coe, mem_support]
        · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 x).resolve_left hxσ, mem_coe,
            apply_mem_support, mem_support]
      · rw [mem_coe, ← apply_mem_support, mem_support] at hxτ
        rw [Set.union_apply_right, Set.union_apply_right]
        · simp only [subtypeEquiv_apply, Perm.coe_mul, Sum.map_inr, comp_apply,
            Set.union_symm_apply_right, Subtype.coe_mk]
          have h := (hd2 (g (τ x))).resolve_right ?_
          · rw [mul_apply, mul_apply] at h
            rw [inv_apply_self, h, (hd1 (τ x)).resolve_right hxτ]
          · rwa [mul_apply, mul_apply, inv_apply_self, apply_eq_iff_eq]
        · rwa [Subtype.coe_mk, mem_coe, ← apply_mem_support, mem_support]
        · rwa [Subtype.coe_mk, Perm.mul_apply, (hd1 (τ x)).resolve_right hxτ,
            mem_coe, mem_support]

theorem apply_mem_fixedPoints_iff_mem_of_mem_centralizer {g p : Perm α}
    (hp : p ∈ Subgroup.centralizer {g}) {x : α} :
    p x ∈ Function.fixedPoints g ↔ x ∈ Function.fixedPoints g :=  by
  simp only [Subgroup.mem_centralizer_singleton_iff] at hp
  simp only [Function.mem_fixedPoints_iff]
  rw [← mul_apply, ← hp, mul_apply, EmbeddingLike.apply_eq_iff_eq]

@[deprecated (since := "2025-05-19")]
alias mem_fixedPoints_iff_apply_mem_of_mem_centralizer :=
  apply_mem_fixedPoints_iff_mem_of_mem_centralizer



variable [DecidableEq α]

lemma disjoint_ofSubtype_of_memFixedPoints_self {g : Perm α}
    (u : Perm (Function.fixedPoints g)) :
    Disjoint (ofSubtype u) g := by
  rw [disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x ∈ Function.fixedPoints g
  · right; exact hx
  · left; rw [ofSubtype_apply_of_not_mem u hx]

section Fintype

variable [Fintype α]

theorem support_pow_coprime {σ : Perm α} {n : ℕ} (h : Nat.Coprime n (orderOf σ)) :
    (σ ^ n).support = σ.support := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  exact
    le_antisymm (support_pow_le σ n)
      (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m))

lemma ofSubtype_support_disjoint {σ : Perm α} (x : Perm (Function.fixedPoints σ)) :
    _root_.Disjoint x.ofSubtype.support σ.support := by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  rw [mem_support] at ha hb
  exact ha (ofSubtype_apply_of_not_mem x (mt Function.mem_fixedPoints_iff.mp hb))

open Subgroup

lemma disjoint_of_disjoint_support {H K : Subgroup (Perm α)}
    (h : ∀ a ∈ H, ∀ b ∈ K, _root_.Disjoint a.support b.support) :
    _root_.Disjoint H K := by
  rw [disjoint_iff_inf_le]
  intro x ⟨hx1, hx2⟩
  specialize h x hx1 x hx2
  rwa [disjoint_self, Finset.bot_eq_empty, support_eq_empty_iff] at h

lemma support_closure_subset_union (S : Set (Perm α)) :
    ∀ a ∈ closure S, (a.support : Set α) ⊆ ⋃ b ∈ S, b.support := by
  apply closure_induction
  · exact fun x hx ↦ Set.subset_iUnion₂_of_subset x hx subset_rfl
  · simp only [support_one, Finset.coe_empty, Set.empty_subset]
  · intro a b ha hb hc hd
    refine (Finset.coe_subset.mpr (support_mul_le a b)).trans ?_
    rw [Finset.sup_eq_union, Finset.coe_union, Set.union_subset_iff]
    exact ⟨hc, hd⟩
  · simp only [support_inv, imp_self, implies_true]

lemma disjoint_support_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : ∀ a ∈ S, ∀ b ∈ T, _root_.Disjoint a.support b.support) :
    ∀ a ∈ closure S, ∀ b ∈ closure T, _root_.Disjoint a.support b.support := by
  intro a ha b hb
  have key1 := support_closure_subset_union S a ha
  have key2 := support_closure_subset_union T b hb
  have key := Set.disjoint_of_subset key1 key2
  simp_rw [Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Finset.disjoint_coe] at key
  exact key h

lemma disjoint_closure_of_disjoint_support {S T : Set (Perm α)}
    (h : ∀ a ∈ S, ∀ b ∈ T, _root_.Disjoint a.support b.support) :
    _root_.Disjoint (closure S) (closure T) := by
  apply disjoint_of_disjoint_support
  apply disjoint_support_closure_of_disjoint_support
  exact h

end Fintype

end Equiv.Perm
