/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Finset.Max

/-!
# Finitely supported functions on exactly one point

This file contains definitions and basic results on defining/updating/removing `Finsupp`s
using one point of the domain.

## Main declarations

* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.
-/


noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `single` -/

section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by
    classical
      obtain rfl | hb := eq_or_ne b 0
      · simp [Pi.single, update]
      rw [if_neg hb, mem_singleton]
      obtain rfl | ha := eq_or_ne a' a
      · simp [hb, Pi.single, update]
      simp [Pi.single_eq_of_ne' ha.symm, ha]

theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]

theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]

theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b := by
  classical
  ext
  simp [single_apply, Set.indicator, @eq_comm _ a]

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b := by
  classical exact Pi.single_eq_same (M := fun _ ↦ M) a b

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _

theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (0 : _) a b := by
  classical rw [single_eq_set_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]

theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b

@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  DFunLike.coe_injective <| by
    classical simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)

theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  rw [single_apply, single_apply]
  ext
  split_ifs with h
  · rw [h]
  · rw [zero_apply, single_apply, ite_self]

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical
  simp only [single]
  split_ifs <;> [exact empty_subset _; exact Subset.refl _]

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp; simp [single_eq_of_ne hx]]

theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `Finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`Finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_set_indicator]

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero, not_or]

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [single_zero, single_zero]

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

lemma apply_surjective (a : α) : Surjective fun f : α →₀ M ↦ f a :=
  RightInverse.surjective fun _ ↦ single_eq_same

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _

theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [DFunLike.ext_iff, single_eq_set_indicator]

theorem single_ne_zero : single a b ≠ 0 ↔ b ≠ 0 :=
  single_eq_zero.not

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical simp only [single_apply, eq_comm]

instance instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [Finsupp.unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same,
    single_eq_same]

lemma apply_single' [Zero N] [Zero P] (e : N → P) (he : e 0 = 0) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b := by
  classical
  simp only [single_apply]
  split_ifs
  · rfl
  · exact he

lemma apply_single [Zero N] [Zero P] {F : Type*} [FunLike F N P] [ZeroHomClass F N P]
    (e : F) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b :=
  apply_single' e (map_zero e) a n b

theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero _ h.1⟩

theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩

theorem card_support_eq_one {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) := by
  simp only [card_eq_one, support_eq_singleton]

theorem card_support_eq_one' {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, ∃ b ≠ 0, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

@[simp]
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  ext
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single, Equiv.symm_apply_apply]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    rw [Function.update]
    simp only [eq_rec_constant, dite_eq_ite, ne_eq]
    split_ifs with hb ha ha <;>
      try simp only [*, not_false_iff, iff_true, not_true, iff_false]
    · rw [Finset.mem_erase]
      simp
    · rw [Finset.mem_erase]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]

@[simp, norm_cast]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  delta update Function.update
  ext
  dsimp
  split_ifs <;> simp

@[simp]
theorem update_self : f.update a (f a) = f := by
  classical
    ext
    simp

@[simp]
theorem zero_update : update 0 a b = single a b := by
  classical
    ext
    rw [single_eq_update, coe_update, coe_zero]

theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  classical
  dsimp only [update]
  congr!

@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.erase a := by
  classical
  simp only [update, ite_true, mem_support_iff, ne_eq, not_not]
  congr!

variable {b}

theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) :
    support (f.update a b) = insert a f.support := by
  classical
  simp only [update, h, ite_false, mem_support_iff, ne_eq]
  congr!

theorem support_update_subset [DecidableEq α] :
    support (f.update a b) ⊆ insert a f.support := by
  classical
  rw [support_update]
  split_ifs
  · exact (erase_subset _ _).trans (subset_insert _ _)
  · rfl

theorem update_comm (f : α →₀ M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ :=
  letI := Classical.decEq α
  DFunLike.coe_injective <| Function.update_comm h _ _ _

@[simp] theorem update_idem (f : α →₀ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c :=
  letI := Classical.decEq α
  DFunLike.coe_injective <| Function.update_idem _ _ _

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    classical
    rw [mem_erase, mem_support_iff]; dsimp
    split_ifs with h
    · exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩
    · exact and_iff_right h

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} :
    (f.erase a).support = f.support.erase a := by
  classical
  dsimp only [erase]
  congr!

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 := by
  classical simp only [erase, coe_mk, ite_true]

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by
  classical simp only [erase, coe_mk, h, ite_false]

theorem erase_apply [DecidableEq α] {a a' : α} {f : α →₀ M} :
    f.erase a a' = if a' = a then 0 else f a' := by
  rw [erase, coe_mk]
  simp only [ite_eq_ite]

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same, coe_zero, Pi.zero_apply]
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
  · rw [erase_ne hs]

@[simp]
theorem erase_of_notMem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  ext b; by_cases hab : b = a
  · rwa [hab, erase_same, eq_comm, ← notMem_support_iff]
  · rw [erase_ne hab]

@[deprecated (since := "2025-05-23")] alias erase_of_not_mem_support := erase_of_notMem_support

theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  simp

theorem erase_eq_update_zero (f : α →₀ M) (a : α) : f.erase a = update f a 0 :=
  letI := Classical.decEq α
  ext fun _ => (Function.update_apply _ _ _ _).symm

-- The name matches `Finset.erase_insert_of_ne`
theorem erase_update_of_ne (f : α →₀ M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by
  rw [erase_eq_update_zero, erase_eq_update_zero, update_comm _ ha]

-- not `simp` as `erase_of_notMem_support` can prove this
theorem erase_idem (f : α →₀ M) (a : α) :
    erase a (erase a f) = erase a f := by
  rw [erase_eq_update_zero, erase_eq_update_zero, update_idem]

@[simp] theorem update_erase_eq_update (f : α →₀ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by
  rw [erase_eq_update_zero, update_idem]

@[simp] theorem erase_update_eq_erase (f : α →₀ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by
  rw [erase_eq_update_zero, erase_eq_update_zero, update_idem]

end Erase

/-! ### Declarations about `mapRange` -/

section MapRange

variable [Zero M] [Zero N] [Zero P]

@[simp]
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) :=
  ext fun a' => by
    classical simpa only [single_eq_pi_single] using Pi.apply_single _ (fun _ => hf) a _ a'

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

theorem single_of_embDomain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single_ne_zero _ hb]
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply f l, h]
      by_cases h_cases : c = d
      · simp only [Eq.symm h_cases, hc₂, single_eq_same]
      · rw [single_apply, single_apply, if_neg, if_neg h_cases]
        by_contra hfd
        exact h_cases (f.injective (hc₂.trans hfd))
    · exact hc₂

@[simp]
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  classical
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a', rfl⟩
      simp [single_apply]
    · simp only [embDomain_notin_range, h, single_apply, not_false_iff]
      rw [if_neg]
      rintro rfl
      simp at h

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

@[simp]
theorem zipWith_single_single (f : M → N → P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  ext a'
  rw [zipWith_apply]
  obtain rfl | ha' := eq_or_ne a a'
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne ha', single_eq_of_ne ha', single_eq_of_ne ha', hf]

end ZipWith

/-! ### Additive monoid structure on `α →₀ M` -/


section AddZeroClass

variable [AddZeroClass M]

@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm

theorem support_single_add {a : α} {b : M} {f : α →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (single a b + f) = cons a f.support ha := by
  classical
  have H := support_single_ne_zero a hb
  rw [support_add_eq, H, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_left]

theorem support_add_single {a : α} {b : M} {f : α →₀ M} (ha : a ∉ f.support) (hb : b ≠ 0) :
    support (f + single a b) = cons a f.support ha := by
  classical
  have H := support_single_ne_zero a hb
  rw [support_add_eq, H, union_comm, cons_eq_insert, insert_eq]
  rwa [H, disjoint_singleton_right]

lemma _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by
  rw [Finsupp.unique_single (AddEquiv.finsuppUnique.symm d), Finsupp.unique_single_eq_iff]
  simp [AddEquiv.finsuppUnique]

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `Mathlib/LinearAlgebra/Finsupp/Defs.lean` for the stronger version as a
linear map. -/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_of_ne h.symm, single_apply, h, erase_ne, h.symm]

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
    f.update a b = f.erase a + single a b := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_of_ne h.symm, single_apply, h, erase_ne, h.symm]

theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]

theorem erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_elim]
protected theorem induction {motive : (α →₀ M) → Prop} (f : α →₀ M) (zero : motive 0)
    (single_add : ∀ (a b) (f : α →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (single a b + f)) : motive f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply single_add
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]

@[elab_as_elim]
theorem induction₂ {motive : (α →₀ M) → Prop} (f : α →₀ M) (zero : motive 0)
    (add_single : ∀ (a b) (f : α →₀ M),
      a ∉ f.support → b ≠ 0 → motive f → motive (f + single a b)) : motive f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → motive f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices motive (f.erase a + single a (f a)) by rwa [erase_add_single] at this
    classical
      apply add_single
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]

@[elab_as_elim]
theorem induction_linear {motive : (α →₀ M) → Prop} (f : α →₀ M) (zero : motive 0)
    (add : ∀ f g : α →₀ M, motive f → motive g → motive (f + g))
    (single : ∀ a b, motive (single a b)) : motive f :=
  induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

section LinearOrder

variable [LinearOrder α] {p : (α →₀ M) → Prop}

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The theorem `induction_on_max₂` swaps the argument order in the sum. -/
theorem induction_on_max (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 → p f → p (single a b + f)) :
    p f := by
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase, hs, erase_insert (fun ha => (hm a ha).false)]
    rw [← single_add_erase a f]
    refine ha _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff, hs]
    exact mem_insert_self a s

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The theorem `induction_on_min₂` swaps the argument order in the sum. -/
theorem induction_on_min (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  induction_on_max (α := αᵒᵈ) f h0 ha

/-- A finitely supported function can be built by adding up `single a b` for increasing `a`.

The theorem `induction_on_max` swaps the argument order in the sum. -/
theorem induction_on_max₂ (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), (∀ c ∈ f.support, c < a) → b ≠ 0 → p f → p (f + single a b)) :
    p f := by
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  refine fun s => s.induction_on_max (fun f h => ?_) (fun a s hm hf f hs => ?_)
  · rwa [support_eq_empty.1 h]
  · have hs' : (erase a f).support = s := by
      rw [support_erase, hs, erase_insert (fun ha => (hm a ha).false)]
    rw [← erase_add_single a f]
    refine ha _ _ _ (fun c hc => hm _ <| hs'.symm ▸ hc) ?_ (hf _ hs')
    rw [← mem_support_iff, hs]
    exact mem_insert_self a s

/-- A finitely supported function can be built by adding up `single a b` for decreasing `a`.

The theorem `induction_on_min` swaps the argument order in the sum. -/
theorem induction_on_min₂ (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 → p f → p (f + single a b)) :
    p f :=
  induction_on_max₂ (α := αᵒᵈ) f h0 ha

end LinearOrder

end AddZeroClass

theorem single_add_single_eq_single_add_single [AddCommMonoid M] {k l m n : α} {u v : M}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv

theorem erase_eq_sub_single [AddGroup G] (f : α →₀ G) (a : α) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a a' with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h]

theorem update_eq_sub_add_single [AddGroup G] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]

section Group

variable [AddGroup G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem single_neg (a : α) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b

@[simp]
theorem single_sub (a : α) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂

@[simp]
theorem erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

end Group

end Finsupp
